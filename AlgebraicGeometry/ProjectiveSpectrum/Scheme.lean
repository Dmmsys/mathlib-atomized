/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.GradedAlgebra.Radical

/-!
# Proj as a scheme

This file is to prove that `Proj` is a scheme.

## Notation

* `Proj` : `Proj` as a locally ringed space
* `Proj.T` : the underlying topological space of `Proj`
* `Proj| U` : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f` : basic open set at `f` in `Proj`
* `Spec` : `Spec` as a locally ringed space
* `Spec.T` : the underlying topological space of `Spec`
* `sbo g` : basic open set at `g` in `Spec`
* `A⁰_x` : the degree zero part of localized ring `Aₓ`

## Implementation

In `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/StructureSheaf.lean`, we have given `Proj` a
structure sheaf so that `Proj` is a locally ringed space. In this file we will prove that `Proj`
equipped with this structure sheaf is a scheme. We achieve this by using an affine cover by basic
open sets in `Proj`, more specifically:

1. We prove that `Proj` can be covered by basic open sets at homogeneous elements of positive
    degree.
2. We prove that for any homogeneous element `f : A` of positive degree `m`, `Proj.T | (pbo f)` is
    homeomorphic to `Spec.T A⁰_f`:
  - forward direction `toSpec`:
    for any `x : pbo f`, i.e. a relevant homogeneous prime ideal `x`, send it to
    `A⁰_f ∩ span {g / 1 | g ∈ x}` (see `ProjIsoSpecTopComponent.ToSpec.carrier`). This ideal is
    prime, the proof is in `ProjIsoSpecTopComponent.ToSpec.toFun`. The fact that this function
    is continuous is found in `ProjIsoSpecTopComponent.toSpec`
  - backward direction `fromSpec`:
    for any `q : Spec A⁰_f`, we send it to `{a | ∀ i, aᵢᵐ/fⁱ ∈ q}`; we need this to be a
    homogeneous prime ideal that is relevant.
    * This is in fact an ideal, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal`;
    * This ideal is also homogeneous, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.homogeneous`;
    * This ideal is relevant, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.relevant`;
    * This ideal is prime, the proof can be found in
      `ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime`.
    Hence we have a well-defined function `Spec.T A⁰_f → Proj.T | (pbo f)`, this function is called
    `ProjIsoSpecTopComponent.FromSpec.toFun`. But to prove the continuity of this function, we need
    to prove `fromSpec ∘ toSpec` and `toSpec ∘ fromSpec` are both identities; these are achieved in
    `ProjIsoSpecTopComponent.fromSpec_toSpec` and `ProjIsoSpecTopComponent.toSpec_fromSpec`.
3. Then we construct a morphism of locally ringed spaces `α : Proj| (pbo f) ⟶ Spec.T A⁰_f` as the
    following: by the Gamma-Spec adjunction, it is sufficient to construct a ring map
    `A⁰_f → Γ(Proj, pbo f)` from the ring of homogeneous localization of `A` away from `f` to the
    local sections of structure sheaf of projective spectrum on the basic open set around `f`.
    The map `A⁰_f → Γ(Proj, pbo f)` is constructed in `awayToΓ` and is defined by sending
    `s ∈ A⁰_f` to the section `x ↦ s` on `pbo f`.

## Main Definitions and Statements

For a homogeneous element `f` of degree `m`
* `ProjIsoSpecTopComponent.toSpec`: the continuous map between `Proj.T| pbo f` and `Spec.T A⁰_f`
  defined by sending `x : Proj| (pbo f)` to `A⁰_f ∩ span {g / 1 | g ∈ x}`. We also denote this map
  as `ψ`.
* `ProjIsoSpecTopComponent.ToSpec.preimage_eq`: for any `a: A`, if `a/f^m` has degree zero,
  then the preimage of `sbo a/f^m` under `toSpec f` is `pbo f ∩ pbo a`.

If we further assume `m` is positive
* `ProjIsoSpecTopComponent.fromSpec`: the continuous map between `Spec.T A⁰_f` and `Proj.T| pbo f`
  defined by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}` where `aᵢ` is the `i`-th coordinate of `a`.
  We also denote this map as `φ`
* `projIsoSpecTopComponent`: the homeomorphism `Proj.T| pbo f ≅ Spec.T A⁰_f` obtained by `φ` and
  `ψ`.
* `ProjectiveSpectrum.Proj.toSpec`: the morphism of locally ringed spaces between `Proj| pbo f`
  and `Spec A⁰_f` corresponding to the ring map `A⁰_f → Γ(Proj, pbo f)` under the Gamma-Spec
  adjunction defined by sending `s` to the section `x ↦ s` on `pbo f`.

Finally,
* `AlgebraicGeometry.Proj`: for any `ℕ`-graded ring `A`, `Proj A` is locally affine, hence is a
  scheme.

## Reference
* [Robin Hartshorne, *Algebraic Geometry*][Har77]: Chapter II.2 Proposition 2.5
-/

@[expose] public section

noncomputable section


namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike.GradedMonoid Localization

open Finset hiding mk_zero

variable {A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : Nat -> σ)
variable [GradedRing 𝒜]

open TopCat TopologicalSpace

open CategoryTheory Opposite

open ProjectiveSpectrum.StructureSheaf

-- Porting note: currently require lack of hygiene to use in variable declarations
-- maybe all make into notation3?
set_option hygiene false
/-- `Proj` as a locally ringed space -/
local notation3 "Proj" => Proj.toLocallyRingedSpace 𝒜

/-- The underlying topological space of `Proj` -/
local notation3 "Proj.T" => PresheafedSpace.carrier SheafedSpace.toPresheafedSpace
 LocallyRingedSpace.toSheafedSpace Proj.toLocallyRingedSpace 𝒜

/-- `Proj` restrict to some open set -/
macro "Proj| " U:term : term =>
  `((Proj.toLocallyRingedSpace 𝒜).restrict
    (Opens.isOpenEmbedding (X := Proj.T) ($U : Opens Proj.T)))

/-- the underlying topological space of `Proj` restricted to some open set -/
local notation "Proj.T| " U => PresheafedSpace.carrier SheafedSpace.toPresheafedSpace
 LocallyRingedSpace.toSheafedSpace
 (LocallyRingedSpace.restrict Proj (Opens.isOpenEmbedding (X := Proj.T) (U : Opens Proj.T)))

/-- basic open sets in `Proj` -/
local notation "pbo " x => ProjectiveSpectrum.basicOpen 𝒜 x

/-- basic open sets in `Spec` -/
local notation "sbo " f => PrimeSpectrum.basicOpen f

/-- `Spec` as a locally ringed space -/
local notation3 "Spec " ring => Spec.locallyRingedSpaceObj (CommRingCat.of ring)

/-- the underlying topological space of `Spec` -/
local notation "Spec.T " ring =>
  (Spec.locallyRingedSpaceObj (CommRingCat.of ring)).toSheafedSpace.toPresheafedSpace.1

local notation3 "A⁰_ " f => HomogeneousLocalization.Away 𝒜 f

namespace ProjIsoSpecTopComponent

/-
This section is to construct the homeomorphism between `Proj` restricted at basic open set at
a homogeneous element `x` and `Spec A⁰ₓ` where `A⁰ₓ` is the degree zero part of the localized
ring `Aₓ`.
-/
namespace ToSpec

open Ideal

-- This section is to construct the forward direction :
-- So for any `x` in `Proj| (pbo f)`, we need some point in `Spec A⁰_f`, i.e. a prime ideal,
-- and we need this correspondence to be continuous in their Zariski topology.
variable {𝒜}
variable {f : A} {m : Nat} (x : Proj| (pbo f))

/--
Definition of `carrier` / `carrier` 的定义

English:
definition carrier
  signature: : Ideal (A⁰_ f)
  body: Ideal.comap (algebraMap (A⁰_ f) (Away f))
    (x.val.asHomogeneousIdeal.toIdeal.map (algebraMap A (Away f)))

中文:
定义 carrier
  签名: : Ideal (A⁰_ f)
  定义体: Ideal.comap (algebraMap (A⁰_ f) (Away f))
    (x.val.asHomogeneousIdeal.toIdeal.map (algebraMap A (Away f)))

Depends on / 依赖: Ideal.comap, algebraMap, asHomogeneousIdeal, toIdeal, x.val.asHomogeneousIdeal.toIdeal.map
-/
def carrier : Ideal (A⁰_ f) :=
  Ideal.comap (algebraMap (A⁰_ f) (Away f))
    (x.val.asHomogeneousIdeal.toIdeal.map (algebraMap A (Away f)))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
theorem `mk_mem_carrier` / 定理 `mk_mem_carrier`

English:
theorem mk_mem_carrier
  given: (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f))
  proof: by
  rw [carrier]; rw [Ideal.mem_comap]; rw [HomogeneousLocalization.algebraMap_apply]; rw [HomogeneousLocalization.val_mk]; rw [Localization.mk_eq_mk']; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [mul_comm]; rw [Ideal.unit_mul_mem_iff_mem]; rw [← Ideal.mem_under]; rw [IsLocalization.under_map_of_is

中文:
定理 mk_mem_carrier
  条件: (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f))
  证明: by
  rw [carrier]; rw [Ideal.mem_comap]; rw [HomogeneousLocalization.algebraMap_apply]; rw [HomogeneousLocalization.val_mk]; rw [Localization.mk_eq_mk']; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [mul_comm]; rw [Ideal.unit_mul_mem_iff_mem]; rw [← Ideal.mem_under]; rw [IsLocalization.under_map_of_is

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.val_mk, Ideal.mem_comap, Ideal.mem_under, Ideal.unit_mul_mem_iff_mem, IsLocalization, IsLocalization.mk, IsLocalization.under_map_of_isPrime_disjoint, Localization, Localization.mk_eq_mk, _eq_mul_mk, _one, algebraMap_apply, carrier, disjoint_powers_iff_notMem_of_isPrime, infer_instance, isUnit_of_invertible, mem_comap, mem_under
-/
theorem mk_mem_carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z in carrier x ↔ z.num.1 in x.1.asHomogeneousIdeal := by
  rw [carrier]; rw [Ideal.mem_comap]; rw [HomogeneousLocalization.algebraMap_apply]; rw [HomogeneousLocalization.val_mk]; rw [Localization.mk_eq_mk']; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [mul_comm]; rw [Ideal.unit_mul_mem_iff_mem]; rw [← Ideal.mem_under]; rw [IsLocalization.under_map_of_isPrime_disjoint (.powers f)]
  · rfl
  · infer_instance
  · exact (disjoint_powers_iff_notMem_of_isPrime _).mpr x.2
  · exact isUnit_of_invertible _

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isPrime_carrier` / 定理 `isPrime_carrier`

English:
theorem isPrime_carrier
  statement: Ideal.IsPrime (carrier x)
  proof: by
  refine Ideal.IsPrime.comap _ (hK := ?_)
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) _ _ inferInstance
    ((disjoint_powers_iff_notMem_of_isPrime _).mpr x.2)

中文:
定理 isPrime_carrier
  结论: Ideal.IsPrime (carrier x)
  证明: by
  refine Ideal.IsPrime.comap _ (hK := ?_)
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) _ _ inferInstance
    ((disjoint_powers_iff_notMem_of_isPrime _).mpr x.2)

Depends on / 依赖: Ideal.IsPrime.comap, IsLocalization, IsLocalization.isPrime_of_isPrime_disjoint, IsPrime, Submonoid, Submonoid.powers, disjoint_powers_iff_notMem_of_isPrime, isPrime_of_isPrime_disjoint, powers
-/
theorem isPrime_carrier : Ideal.IsPrime (carrier x) := by
  refine Ideal.IsPrime.comap _ (hK := ?_)
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) _ _ inferInstance
    ((disjoint_powers_iff_notMem_of_isPrime _).mpr x.2)

variable (f)

/-- The function between the basic open set `D(f)` in `Proj` to the corresponding basic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `TopComponent.forward`.
-/
@[simps -isSimp]
/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: (x : Proj.T| pbo f)
  body: ⟨carrier x, isPrime_carrier x⟩

中文:
定义 toFun
  签名: (x : Proj.T| pbo f)
  定义体: ⟨carrier x, isPrime_carrier x⟩

Depends on / 依赖: carrier, isPrime_carrier
-/
def toFun (x : Proj.T| pbo f) : Spec.T A⁰_ f :=
  ⟨carrier x, isPrime_carrier x⟩

/--
theorem `preimage_basicOpen` / 定理 `preimage_basicOpen`

English:
theorem preimage_basicOpen
  given: (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f))
  proof: Set.ext fun y => (mk_mem_carrier y z).not

中文:
定理 preimage_basicOpen
  条件: (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f))
  证明: Set.ext fun y => (mk_mem_carrier y z).not

Depends on / 依赖: Set.ext, mk_mem_carrier
-/
theorem preimage_basicOpen (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    toFun f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeSpectrum (A⁰_ f))) =
      Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜)) :=
  Set.ext fun y => (mk_mem_carrier y z).not

end ToSpec

section

set_option backward.isDefEq.respectTransparency false in
/-- The continuous function from the basic open set `D(f)` in `Proj`
to the corresponding basic open set in `Spec A⁰_f`. -/
@[simps! -isSimp hom_apply_asIdeal]
/--
Definition of `toSpec` / `toSpec` 的定义

English:
definition toSpec
  signature: (f : A)
  body: TopCat.ofHom
  { toFun := ToSpec.toFun f
    continuous_toFun := by
      rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
      rintro _ ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := Quotient.mk''_surjective x
      rw [ToSpec.preimage_basicOpen]
      exact (pbo (x.num : A)).2.preimage continu

中文:
定义 toSpec
  签名: (f : A)
  定义体: TopCat.ofHom
  { toFun := ToSpec.toFun f
    continuous_toFun := by
      rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
      rintro _ ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := Quotient.mk''_surjective x
      rw [ToSpec.preimage_basicOpen]
      exact (pbo (x.num : A)).2.preimage continu

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff, Quotient, Quotient.mk, ToSpec, ToSpec.preimage_basicOpen, ToSpec.toFun, TopCat, TopCat.ofHom, _surjective, continuous_iff, continuous_subtype_val, continuous_toFun, isSmall_ofHoms, isTopologicalBasis_basic_opens, preimage, preimage_basicOpen, x.num
-/
def toSpec (f : A) : (Proj.T| pbo f) ⟶ Spec.T A⁰_ f :=
  TopCat.ofHom
  { toFun := ToSpec.toFun f
    continuous_toFun := by
      rw [PrimeSpectrum.isTopologicalBasis_basic_opens.continuous_iff]
      rintro _ ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := Quotient.mk''_surjective x
      rw [ToSpec.preimage_basicOpen]
      exact (pbo (x.num : A)).2.preimage continuous_subtype_val }

variable {𝒜} in
/--
lemma `toSpec_preimage_basicOpen` / 引理 `toSpec_preimage_basicOpen`

English:
lemma toSpec_preimage_basicOpen
  given: {f} (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f))
  proof: ToSpec.preimage_basicOpen f z

中文:
引理 toSpec_preimage_basicOpen
  条件: {f} (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f))
  证明: ToSpec.preimage_basicOpen f z

Depends on / 依赖: ToSpec, ToSpec.preimage_basicOpen, preimage_basicOpen
-/
lemma toSpec_preimage_basicOpen {f} (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    toSpec 𝒜 f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeSpectrum (A⁰_ f))) =
      Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜)) :=
  ToSpec.preimage_basicOpen f z

end

namespace FromSpec

open GradedRing SetLike

open Finset hiding mk_zero

open HomogeneousLocalization

variable {𝒜}
variable {f : A} {m : Nat} (f_deg : f in 𝒜 m)

open Lean Meta Elab Tactic

/-- `mem_tac` tries to prove goals of the form `x ∈ 𝒜 i` when `x` has the form of:
* `y ^ n` where `i = n • j` and `y ∈ 𝒜 j`.
* a natural number `n`.
-/
macro "mem_tac" : tactic =>
  `(tactic| first | exact pow_mem_graded _ (SetLike.coe_mem _) | exact natCast_mem_graded _ _ |
    exact pow_mem_graded _ f_deg)

/--
Definition of `carrier` / `carrier` 的定义

English:
definition carrier
  signature: (f_deg : f in 𝒜 m) (q : Spec.T A⁰_ f)
  body: {a | forall i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.1}

中文:
定义 carrier
  签名: (f_deg : f in 𝒜 m) (q : Spec.T A⁰_ f)
  定义体: {a | forall i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.1}

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.mk, mem_tac, mul_comm, smul_eq_mul
-/
def carrier (f_deg : f in 𝒜 m) (q : Spec.T A⁰_ f) : Set A :=
  {a | forall i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.1}

/--
theorem `mem_carrier_iff` / 定理 `mem_carrier_iff`

English:
theorem mem_carrier_iff
  given: (q : Spec.T A⁰_ f) (a : A)
  proof: Iff.rfl

中文:
定理 mem_carrier_iff
  条件: (q : Spec.T A⁰_ f) (a : A)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier_iff (q : Spec.T A⁰_ f) (a : A) :
    a in carrier f_deg q ↔ forall i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by
      rw [← smul_eq_mul]; mem_tac⟩,
      ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.1 :=
  Iff.rfl

/--
theorem `mem_carrier_iff'` / 定理 `mem_carrier_iff'`

English:
theorem mem_carrier_iff'
  given: (q : Spec.T A⁰_ f) (a : A)
  proof: (mem_carrier_iff f_deg q a).trans
    (by
      constructor <;> intro h i <;> specialize h i
      · rw [Set.mem_image]; refine ⟨_, h, rfl⟩
      · rw [Set.mem_image] at h; rcases h with ⟨x, h, hx⟩
        change x in q.asIdeal at h
        convert! h
        rw [HomogeneousLocalization.ext_iff_val]

中文:
定理 mem_carrier_iff'
  条件: (q : Spec.T A⁰_ f) (a : A)
  证明: (mem_carrier_iff f_deg q a).trans
    (by
      constructor <;> intro h i <;> specialize h i
      · rw [Set.mem_image]; refine ⟨_, h, rfl⟩
      · rw [Set.mem_image] at h; rcases h with ⟨x, h, hx⟩
        change x in q.asIdeal at h
        convert! h
        rw [HomogeneousLocalization.ext_iff_val]

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk, Set.mem_image, Subtype, Subtype.coe_mk, asIdeal, coe_mk, convert, ext_iff_val, f_deg, mem_carrier_iff, mem_image, q.asIdeal, specialize, val_mk
-/
theorem mem_carrier_iff' (q : Spec.T A⁰_ f) (a : A) :
    a in carrier f_deg q ↔
      forall i, (Localization.mk (proj 𝒜 i a ^ m) ⟨f ^ i, ⟨i, rfl⟩⟩ : Localization.Away f) in
          algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) '' { s | s in q.1 } :=
  (mem_carrier_iff f_deg q a).trans
    (by
      constructor <;> intro h i <;> specialize h i
      · rw [Set.mem_image]; refine ⟨_, h, rfl⟩
      · rw [Set.mem_image] at h; rcases h with ⟨x, h, hx⟩
        change x in q.asIdeal at h
        convert! h
        rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_mk]
        dsimp only [Subtype.coe_mk]; rw [← hx]; rfl)

/--
theorem `mem_carrier_iff_of_mem` / 定理 `mem_carrier_iff_of_mem`

English:
theorem mem_carrier_iff_of_mem
  given: (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a in 𝒜 n)
  proof: by
  trans (HomogeneousLocalization.mk ⟨m * n, ⟨proj 𝒜 n a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
    ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.asIdeal
  · refine ⟨fun h => h n, fun h i => if hi : i = n then hi ▸ h else ?_⟩
    convert! zero_mem q.asIdeal
    apply HomogeneousLocali

中文:
定理 mem_carrier_iff_of_mem
  条件: (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a in 𝒜 n)
  证明: by
  trans (HomogeneousLocalization.mk ⟨m * n, ⟨proj 𝒜 n a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
    ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.asIdeal
  · refine ⟨fun h => h n, fun h i => if hi : i = n then hi ▸ h else ?_⟩
    convert! zero_mem q.asIdeal
    apply HomogeneousLocali

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.mk, HomogeneousLocalization.val_injective, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, Localization, Localization.mk_zero, Ne.symm, asIdeal, convert, decompose_of_mem_ne, hm.ne, mem_tac, mk_zero, mul_comm, proj_apply, q.asIdeal, smul_eq_mul, val_injective, val_mk
-/
theorem mem_carrier_iff_of_mem (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a in 𝒜 n) :
    a in carrier f_deg q ↔
      (HomogeneousLocalization.mk ⟨m * n, ⟨a ^ m, pow_mem_graded m hn⟩,
        ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.asIdeal := by
  trans (HomogeneousLocalization.mk ⟨m * n, ⟨proj 𝒜 n a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
    ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.asIdeal
  · refine ⟨fun h => h n, fun h i => if hi : i = n then hi ▸ h else ?_⟩
    convert! zero_mem q.asIdeal
    apply HomogeneousLocalization.val_injective
    simp only [proj_apply, decompose_of_mem_ne _ hn (Ne.symm hi), zero_pow hm.ne',
      HomogeneousLocalization.val_mk, Localization.mk_zero, HomogeneousLocalization.val_zero]
  · simp only [proj_apply, decompose_of_mem_same _ hn]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mem_carrier_iff_of_mem_mul` / 定理 `mem_carrier_iff_of_mem_mul`

English:
theorem mem_carrier_iff_of_mem_mul
  statement: (hm : 0 < m)
  proof: by
  rw [mem_carrier_iff_of_mem f_deg hm q a hn]; rw [iff_iff_eq]; rw [eq_comm]; rw [← Ideal.IsPrime.pow_mem_iff_mem (α := A⁰_ f) inferInstance m hm]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_pow,
    Localization

中文:
定理 mem_carrier_iff_of_mem_mul
  结论: (hm : 0 < m)
  证明: by
  rw [mem_carrier_iff_of_mem f_deg hm q a hn]; rw [iff_iff_eq]; rw [eq_comm]; rw [← Ideal.IsPrime.pow_mem_iff_mem (α := A⁰_ f) inferInstance m hm]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_pow,
    Localization

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.val_injective, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_pow, Ideal.IsPrime.pow_mem_iff_mem, IsPrime, Localization, Localization.mk_pow, eq_comm, f_deg, iff_iff_eq, mem_carrier_iff_of_mem, mk_pow, pow_mem_iff_mem, pow_mul, val_injective, val_mk, val_pow
-/
theorem mem_carrier_iff_of_mem_mul (hm : 0 < m)
    (q : Spec.T A⁰_ f) (a : A) {n} (hn : a in 𝒜 (n * m)) :
    a in carrier f_deg q ↔ (HomogeneousLocalization.mk ⟨m * n, ⟨a, mul_comm n m ▸ hn⟩,
        ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.asIdeal := by
  rw [mem_carrier_iff_of_mem f_deg hm q a hn]; rw [iff_iff_eq]; rw [eq_comm]; rw [← Ideal.IsPrime.pow_mem_iff_mem (α := A⁰_ f) inferInstance m hm]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_pow,
    Localization.mk_pow, pow_mul]
  rfl

/--
theorem `num_mem_carrier_iff` / 定理 `num_mem_carrier_iff`

English:
theorem num_mem_carrier_iff
  statement: (hm : 0 < m) (q : Spec.T A⁰_ f)
  proof: by
  obtain ⟨n, hn : f ^ n = _⟩ := z.den_mem
  have : f ^ n != 0 := fun e => by
    have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, e⟩
    exact IsEmpty.elim (inferInstanceAs (IsEmpty (PrimeSpectrum (A⁰_ f)))) q
  convert! mem_carrier_iff_of_mem_mul f_deg hm q z.num.1 (n := n) ?_

中文:
定理 num_mem_carrier_iff
  结论: (hm : 0 < m) (q : Spec.T A⁰_ f)
  证明: by
  obtain ⟨n, hn : f ^ n = _⟩ := z.den_mem
  have : f ^ n != 0 := fun e => by
    have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, e⟩
    exact IsEmpty.elim (inferInstanceAs (IsEmpty (PrimeSpectrum (A⁰_ f)))) q
  convert! mem_carrier_iff_of_mem_mul f_deg hm q z.num.1 (n := n) ?_

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.subsingleton, HomogeneousLocalization.val_injective, HomogeneousLocalization.val_mk, IsEmpty, IsEmpty.elim, PrimeSpectrum, SetLike, SetLike.pow_mem_graded, convert, degree_eq_of_mem_mem, den_mem, f_deg, hn.symm, mem_carrier_iff_of_mem_mul, pow_mem_graded, powers, smul_eq_mul, subsingleton, val_injective
-/
theorem num_mem_carrier_iff (hm : 0 < m) (q : Spec.T A⁰_ f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    z.num.1 in carrier f_deg q ↔ HomogeneousLocalization.mk z in q.asIdeal := by
  obtain ⟨n, hn : f ^ n = _⟩ := z.den_mem
  have : f ^ n != 0 := fun e => by
    have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, e⟩
    exact IsEmpty.elim (inferInstanceAs (IsEmpty (PrimeSpectrum (A⁰_ f)))) q
  convert! mem_carrier_iff_of_mem_mul f_deg hm q z.num.1 (n := n) ?_ using 2
  · apply HomogeneousLocalization.val_injective; simp only [hn, HomogeneousLocalization.val_mk]
  · have := degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded n f_deg) (hn.symm ▸ z.den.2) this
    rw [← smul_eq_mul]; rw [this]; exact z.num.2

/--
theorem `carrier.add_mem` / 定理 `carrier.add_mem`

English:
theorem carrier.add_mem
  statement: (q : Spec.T A⁰_ f) {a b : A} (ha : a in carrier f_deg q)
  proof: by
  refine fun i => (q.2.mem_or_mem ?_).elim id id
  change (HomogeneousLocalization.mk ⟨_, _, _, _⟩ : A⁰_ f) in q.1; dsimp only [Subtype.coe_mk]
  simp_rw [← pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul]
  let g : Nat -> A⁰_ f := fun j => (m + m).choose j •
      if h2 : m + m < j then (0 :

中文:
定理 carrier.add_mem
  结论: (q : Spec.T A⁰_ f) {a b : A} (ha : a in carrier f_deg q)
  证明: by
  refine fun i => (q.2.mem_or_mem ?_).elim id id
  change (HomogeneousLocalization.mk ⟨_, _, _, _⟩ : A⁰_ f) in q.1; dsimp only [Subtype.coe_mk]
  simp_rw [← pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul]
  let g : Nat -> A⁰_ f := fun j => (m + m).choose j •
      if h2 : m + m < j then (0 :

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.mk, Subtype, Subtype.coe_mk, add_pow, coe_mk, map_add, mem_or_mem, mem_tac, mul_comm, nsmul_eq_mul, pow_add, simp_rw
-/
theorem carrier.add_mem (q : Spec.T A⁰_ f) {a b : A} (ha : a in carrier f_deg q)
    (hb : b in carrier f_deg q) : a + b in carrier f_deg q := by
  refine fun i => (q.2.mem_or_mem ?_).elim id id
  change (HomogeneousLocalization.mk ⟨_, _, _, _⟩ : A⁰_ f) in q.1; dsimp only [Subtype.coe_mk]
  simp_rw [← pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul]
  let g : Nat -> A⁰_ f := fun j => (m + m).choose j •
      if h2 : m + m < j then (0 : A⁰_ f)
      else
        if h1 : j <= m then
          (HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i a ^ j * proj 𝒜 i b ^ (m - j), ?_⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩ : A⁰_ f) *
          (HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i b ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩ : A⁰_ f)
        else
          (HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩ : A⁰_ f) *
          (HomogeneousLocalization.mk
            ⟨m * i, ⟨proj 𝒜 i a ^ (j - m) * proj 𝒜 i b ^ (m + m - j), ?_⟩,
              ⟨_, by rw [mul_comm]; mem_tac⟩, ⟨i, rfl⟩⟩ : A⁰_ f)
  rotate_left
  · rw [(_ : m * i = _)]
    apply GradedMonoid.toGradedMul.mul_mem <;> mem_tac
    rw [← add_smul]; rw [Nat.add_sub_of_le h1]; rfl
  · rw [(_ : m * i = _)]
    apply GradedMonoid.toGradedMul.mul_mem (i := (j - m) • i) (j := (m + m - j) • i) <;> mem_tac
    rw [← add_smul]; congr; lia
  convert_to ∑ i in range (m + m + 1), g i in q.1; swap
  · refine q.1.sum_mem fun j _ => nsmul_mem ?_ _; split_ifs
    exacts [q.1.zero_mem, q.1.mul_mem_left _ (hb i), q.1.mul_mem_right _ (ha i)]
  rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_mk]
  change _ = (algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f)) _
  dsimp only [Subtype.coe_mk]; rw [map_sum, mk_sum]
  apply Finset.sum_congr rfl fun j hj => _
  intro j hj
  change _ = HomogeneousLocalization.val _
  rw [HomogeneousLocalization.val_smul]
  split_ifs with h2 h1
  · exact ((Finset.mem_range.1 hj).not_ge h2).elim
  all_goals simp only [HomogeneousLocalization.val_mul,
    HomogeneousLocalization.val_mk, Localization.mk_mul, ← smul_mk]; congr 2
  · dsimp; rw [mul_assoc, ← pow_add, add_comm (m - j), Nat.add_sub_assoc h1]
  · simp_rw [pow_add]; rfl
  · dsimp; rw [← mul_assoc, ← pow_add, Nat.add_sub_of_le (le_of_not_ge h1)]
  · simp_rw [pow_add]; rfl

variable (hm : 0 < m) (q : Spec.T A⁰_ f)
include hm

/--
theorem `carrier.zero_mem` / 定理 `carrier.zero_mem`

English:
theorem carrier.zero_mem
  statement: (0 : A) in carrier f_deg q
  proof: fun i => by
  convert Submodule.zero_mem q.1
  rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_mk]; rw [HomogeneousLocalization.val_zero]; simp_rw [map_zero, zero_pow hm.ne']
  exact Localization.mk_zero (S := Submonoid.powers f) _

中文:
定理 carrier.zero_mem
  结论: (0 : A) in carrier f_deg q
  证明: fun i => by
  convert Submodule.zero_mem q.1
  rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_mk]; rw [HomogeneousLocalization.val_zero]; simp_rw [map_zero, zero_pow hm.ne']
  exact Localization.mk_zero (S := Submonoid.powers f) _

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_zero, Localization, Localization.mk_zero, Submodule, Submodule.zero_mem, Submonoid, Submonoid.powers, convert, ext_iff_val, hm.ne, map_zero, mk_zero, powers, simp_rw, val_mk, val_zero, zero_mem
-/
theorem carrier.zero_mem : (0 : A) in carrier f_deg q := fun i => by
  convert Submodule.zero_mem q.1
  rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_mk]; rw [HomogeneousLocalization.val_zero]; simp_rw [map_zero, zero_pow hm.ne']
  exact Localization.mk_zero (S := Submonoid.powers f) _

/--
theorem `carrier.smul_mem` / 定理 `carrier.smul_mem`

English:
theorem carrier.smul_mem
  given: (c x : A) (hx : x in carrier f_deg q)
  statement: c • x in carrier f_deg q
  proof: by
  revert c
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
  · rw [zero_smul]; exact carrier.zero_mem f_deg hm _
  · rintro n ⟨a, ha⟩ i
    simp_rw [proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha]
    let product : A⁰_ f :=
      (HomogeneousLocalization.mk
          ⟨_, ⟨a

中文:
定理 carrier.smul_mem
  条件: (c x : A) (hx : x in carrier f_deg q)
  结论: c • x in carrier f_deg q
  证明: by
  revert c
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
  · rw [zero_smul]; exact carrier.zero_mem f_deg hm _
  · rintro n ⟨a, ha⟩ i
    simp_rw [proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha]
    let product : A⁰_ f :=
      (HomogeneousLocalization.mk
          ⟨_, ⟨a

Depends on / 依赖: Decomposition, DirectSum, DirectSum.Decomposition.inductionOn, HomogeneousLocalization, HomogeneousLocalization.mk, carrier, carrier.zero_mem, coe_decompose_mul_of_left_mem, convert_to, f_deg, inductionOn, mem_tac, pow_mem_graded, product, proj_apply, revert, simp_rw, smul_eq_mul, split_ifs, zero_mem
-/
theorem carrier.smul_mem (c x : A) (hx : x in carrier f_deg q) : c • x in carrier f_deg q := by
  revert c
  refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
  · rw [zero_smul]; exact carrier.zero_mem f_deg hm _
  · rintro n ⟨a, ha⟩ i
    simp_rw [proj_apply, smul_eq_mul, coe_decompose_mul_of_left_mem 𝒜 i ha]
    let product : A⁰_ f :=
      (HomogeneousLocalization.mk
          ⟨_, ⟨a ^ m, pow_mem_graded m ha⟩, ⟨_, ?_⟩, ⟨n, rfl⟩⟩ : A⁰_ f) *
        (HomogeneousLocalization.mk
          ⟨_, ⟨proj 𝒜 (i - n) x ^ m, by mem_tac⟩, ⟨_, ?_⟩, ⟨i - n, rfl⟩⟩ : A⁰_ f)
    · split_ifs with h
      · convert_to product in q.1
        · dsimp [product]
          rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_mk]; rw [HomogeneousLocalization.val_mul]; rw [HomogeneousLocalization.val_mk]; rw [HomogeneousLocalization.val_mk]
          · simp_rw [mul_pow]; rw [Localization.mk_mul]
            · congr; rw [← pow_add, Nat.add_sub_of_le h]
        · apply Ideal.mul_mem_left (α := A⁰_ f) _ _ (hx _)
          rw [(_ : m • n = _)]
          · mem_tac
          · simp only [smul_eq_mul, mul_comm]
      · simpa only [map_zero, zero_pow hm.ne'] using zero_mem f_deg hm q i
    rw [(_ : m • (i - n) = _)]
    · mem_tac
    · simp only [smul_eq_mul, mul_comm]
  · simp_rw [add_smul]; exact fun _ _ => carrier.add_mem f_deg q

/--
Definition of `carrier.asIdeal` / `carrier.asIdeal` 的定义

English:
definition carrier.asIdeal
  signature: : Ideal A where
  body: carrier f_deg q
  zero_mem' := carrier.zero_mem f_deg hm q
  add_mem' := carrier.add_mem f_deg q
  smul_mem' := carrier.smul_mem f_deg hm q

中文:
定义 carrier.asIdeal
  签名: : Ideal A where
  定义体: carrier f_deg q
  zero_mem' := carrier.zero_mem f_deg hm q
  add_mem' := carrier.add_mem f_deg q
  smul_mem' := carrier.smul_mem f_deg hm q

Depends on / 依赖: carrier, f_deg
-/
def carrier.asIdeal : Ideal A where
  carrier := carrier f_deg q
  zero_mem' := carrier.zero_mem f_deg hm q
  add_mem' := carrier.add_mem f_deg q
  smul_mem' := carrier.smul_mem f_deg hm q


/--
theorem `carrier.asIdeal.homogeneous` / 定理 `carrier.asIdeal.homogeneous`

English:
theorem carrier.asIdeal.homogeneous
  statement: (carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜
  proof: fun i a ha j =>
  (em (i = j)).elim (fun h => h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _)
    fun h => by
    simpa only [proj_apply, decompose_of_mem_ne 𝒜 (SetLike.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm.ne', map_zero] using carrier.zero_mem f_deg hm q j

中文:
定理 carrier.asIdeal.homogeneous
  结论: (carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜
  证明: fun i a ha j =>
  (em (i = j)).elim (fun h => h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _)
    fun h => by
    simpa only [proj_apply, decompose_of_mem_ne 𝒜 (SetLike.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm.ne', map_zero] using carrier.zero_mem f_deg hm q j

Depends on / 依赖: SetLike, SetLike.coe_mem, carrier, carrier.zero_mem, coe_mem, decompose, decompose_coe, decompose_of_mem_ne, f_deg, hm.ne, map_zero, of_eq_same, proj_apply, zero_mem, zero_pow
-/
theorem carrier.asIdeal.homogeneous : (carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜 :=
  fun i a ha j =>
  (em (i = j)).elim (fun h => h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _)
    fun h => by
    simpa only [proj_apply, decompose_of_mem_ne 𝒜 (SetLike.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm.ne', map_zero] using carrier.zero_mem f_deg hm q j

/--
Definition of `carrier.asHomogeneousIdeal` / `carrier.asHomogeneousIdeal` 的定义

English:
definition carrier.asHomogeneousIdeal
  signature: : HomogeneousIdeal 𝒜
  body: ⟨carrier.asIdeal f_deg hm q, carrier.asIdeal.homogeneous f_deg hm q⟩

中文:
定义 carrier.asHomogeneousIdeal
  签名: : HomogeneousIdeal 𝒜
  定义体: ⟨carrier.asIdeal f_deg hm q, carrier.asIdeal.homogeneous f_deg hm q⟩

Depends on / 依赖: asIdeal, carrier, carrier.asIdeal, carrier.asIdeal.homogeneous, f_deg, homogeneous
-/
def carrier.asHomogeneousIdeal : HomogeneousIdeal 𝒜 :=
  ⟨carrier.asIdeal f_deg hm q, carrier.asIdeal.homogeneous f_deg hm q⟩

/--
theorem `carrier.denom_notMem` / 定理 `carrier.denom_notMem`

English:
theorem carrier.denom_notMem
  statement: f ∉ carrier.asIdeal f_deg hm q
  proof: fun rid =>
q.isPrime.ne_top
    (Ideal.eq_top_iff_one _).mpr
      (by
        convert rid m
        rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_one]; rw [HomogeneousLocalization.val_mk]
        dsimp
        simp_rw [decompose_of_mem_same _ f_deg]
        simp)

中文:
定理 carrier.denom_notMem
  结论: f ∉ carrier.asIdeal f_deg hm q
  证明: fun rid =>
q.isPrime.ne_top
    (Ideal.eq_top_iff_one _).mpr
      (by
        convert rid m
        rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_one]; rw [HomogeneousLocalization.val_mk]
        dsimp
        simp_rw [decompose_of_mem_same _ f_deg]
        simp)
-/
theorem carrier.denom_notMem : f ∉ carrier.asIdeal f_deg hm q := fun rid =>
q.isPrime.ne_top
    (Ideal.eq_top_iff_one _).mpr
      (by
        convert rid m
        rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_one]; rw [HomogeneousLocalization.val_mk]
        dsimp
        simp_rw [decompose_of_mem_same _ f_deg]
        simp)

/--
theorem `carrier.relevant` / 定理 `carrier.relevant`

English:
theorem carrier.relevant
  statement: ¬HomogeneousIdeal.irrelevant 𝒜 <= carrier.asHomogeneousIdeal f_deg hm q
  proof: fun rid => carrier.denom_notMem f_deg hm q rid DirectSum.decompose_of_mem_ne 𝒜 f_deg hm.ne'

中文:
定理 carrier.relevant
  结论: ¬HomogeneousIdeal.irrelevant 𝒜 <= carrier.asHomogeneousIdeal f_deg hm q
  证明: fun rid => carrier.denom_notMem f_deg hm q rid DirectSum.decompose_of_mem_ne 𝒜 f_deg hm.ne'

Depends on / 依赖: DirectSum, DirectSum.decompose_of_mem_ne, carrier, carrier.denom_notMem, decompose_of_mem_ne, denom_notMem, f_deg, hm.ne
-/
theorem carrier.relevant : ¬HomogeneousIdeal.irrelevant 𝒜 <= carrier.asHomogeneousIdeal f_deg hm q :=
fun rid => carrier.denom_notMem f_deg hm q rid DirectSum.decompose_of_mem_ne 𝒜 f_deg hm.ne'

/--
theorem `carrier.asIdeal.ne_top` / 定理 `carrier.asIdeal.ne_top`

English:
theorem carrier.asIdeal.ne_top
  statement: carrier.asIdeal f_deg hm q != ⊤
  proof: fun rid =>
  carrier.denom_notMem f_deg hm q (rid.symm ▸ Submodule.mem_top)

中文:
定理 carrier.asIdeal.ne_top
  结论: carrier.asIdeal f_deg hm q != ⊤
  证明: fun rid =>
  carrier.denom_notMem f_deg hm q (rid.symm ▸ Submodule.mem_top)
-/
theorem carrier.asIdeal.ne_top : carrier.asIdeal f_deg hm q != ⊤ := fun rid =>
  carrier.denom_notMem f_deg hm q (rid.symm ▸ Submodule.mem_top)

/--
theorem `carrier.asIdeal.prime` / 定理 `carrier.asIdeal.prime`

English:
theorem carrier.asIdeal.prime
  statement: (carrier.asIdeal f_deg hm q).IsPrime
  proof: (carrier.asIdeal.homogeneous f_deg hm q).isPrime_of_homogeneous_mem_or_mem
    (carrier.asIdeal.ne_top f_deg hm q) fun {x y} ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy =>
    show (forall _, _ in _) ∨ forall _, _ in _ by
      rw [← and_forall_ne nx]; rw [and_iff_left]; rw [← and_forall_ne ny]; rw [and_iff_left]
     

中文:
定理 carrier.asIdeal.prime
  结论: (carrier.asIdeal f_deg hm q).IsPrime
  证明: (carrier.asIdeal.homogeneous f_deg hm q).isPrime_of_homogeneous_mem_or_mem
    (carrier.asIdeal.ne_top f_deg hm q) fun {x y} ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy =>
    show (forall _, _ in _) ∨ forall _, _ in _ by
      rw [← and_forall_ne nx]; rw [and_iff_left]; rw [← and_forall_ne ny]; rw [and_iff_left]
     

Depends on / 依赖: GradedMonoid, SetLike, SetLike.GradedMonoid.toGradedMul.mul_mem, and_forall_ne, and_iff_left, asIdeal, carrier, carrier.asIdeal.homogeneous, carrier.asIdeal.ne_top, convert, decompose_of_mem_same, f_deg, homogeneous, isPrime_of_homogeneous_mem_or_mem, mem_or_mem, mul_mem, mul_pow, ne_top, pow_add, simp_rw
-/
theorem carrier.asIdeal.prime : (carrier.asIdeal f_deg hm q).IsPrime :=
  (carrier.asIdeal.homogeneous f_deg hm q).isPrime_of_homogeneous_mem_or_mem
    (carrier.asIdeal.ne_top f_deg hm q) fun {x y} ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy =>
    show (forall _, _ in _) ∨ forall _, _ in _ by
      rw [← and_forall_ne nx]; rw [and_iff_left]; rw [← and_forall_ne ny]; rw [and_iff_left]
      · apply q.2.mem_or_mem; convert! hxy (nx + ny)
        dsimp
        simp_rw [decompose_of_mem_same 𝒜 hnx, decompose_of_mem_same 𝒜 hny,
          decompose_of_mem_same 𝒜 (SetLike.GradedMonoid.toGradedMul.mul_mem hnx hny),
          mul_pow, pow_add]
        simp only [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
          HomogeneousLocalization.val_mul, Localization.mk_mul]
        simp only [Submonoid.mk_mul_mk, mk_eq_monoidOf_mk']
      all_goals
        intro n hn; convert q.1.zero_mem
        rw [HomogeneousLocalization.ext_iff_val]; rw [HomogeneousLocalization.val_mk]; rw [HomogeneousLocalization.val_zero]; simp_rw [proj_apply]
        convert! mk_zero (S := Submonoid.powers f) _
        rw [decompose_of_mem_ne 𝒜 _ hn.symm]; rw [zero_pow hm.ne']
        · first | exact hnx | exact hny

/--
Definition of `toFun` / `toFun` 的定义

English:
definition toFun
  signature: : (Spec.T A⁰_ f) -> Proj.T| pbo f
  body: fun q =>
  ⟨⟨carrier.asHomogeneousIdeal f_deg hm q, carrier.asIdeal.prime f_deg hm q,
      carrier.relevant f_deg hm q⟩,
(ProjectiveSpectrum.mem_basicOpen _ f _).mp carrier.denom_notMem f_deg hm q⟩

中文:
定义 toFun
  签名: : (Spec.T A⁰_ f) -> Proj.T| pbo f
  定义体: fun q =>
  ⟨⟨carrier.asHomogeneousIdeal f_deg hm q, carrier.asIdeal.prime f_deg hm q,
      carrier.relevant f_deg hm q⟩,
(ProjectiveSpectrum.mem_basicOpen _ f _).mp carrier.denom_notMem f_deg hm q⟩
-/
def toFun : (Spec.T A⁰_ f) -> Proj.T| pbo f := fun q =>
  ⟨⟨carrier.asHomogeneousIdeal f_deg hm q, carrier.asIdeal.prime f_deg hm q,
      carrier.relevant f_deg hm q⟩,
(ProjectiveSpectrum.mem_basicOpen _ f _).mp carrier.denom_notMem f_deg hm q⟩

end FromSpec

section toSpecFromSpec

/--
lemma `toSpec_fromSpec` / 引理 `toSpec_fromSpec`

English:
lemma toSpec_fromSpec
  given: {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Spec.T (A⁰_ f))
  proof: by
  apply PrimeSpectrum.ext
  ext z
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [← FromSpec.num_mem_carrier_iff f_deg hm x]
  exact ToSpec.mk_mem_carrier _ z

中文:
引理 toSpec_fromSpec
  条件: {f : A} {m : 自然数} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Spec.T (A⁰_ f))
  证明: by
  apply PrimeSpectrum.ext
  ext z
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [← FromSpec.num_mem_carrier_iff f_deg hm x]
  exact ToSpec.mk_mem_carrier _ z

Depends on / 依赖: FromSpec, FromSpec.num_mem_carrier_iff, HomogeneousLocalization, HomogeneousLocalization.mk_surjective, PrimeSpectrum, PrimeSpectrum.ext, ToSpec, ToSpec.mk_mem_carrier, f_deg, mk_mem_carrier, mk_surjective, num_mem_carrier_iff
-/
lemma toSpec_fromSpec {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Spec.T (A⁰_ f)) :
    toSpec 𝒜 f (FromSpec.toFun f_deg hm x) = x := by
  apply PrimeSpectrum.ext
  ext z
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [← FromSpec.num_mem_carrier_iff f_deg hm x]
  exact ToSpec.mk_mem_carrier _ z


end toSpecFromSpec

section fromSpecToSpec

/--
lemma `fromSpec_toSpec` / 引理 `fromSpec_toSpec`

English:
lemma fromSpec_toSpec
  given: {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Proj.T| pbo f)
  proof: by
refine Subtype.ext ProjectiveSpectrum.ext HomogeneousIdeal.ext' ?_
  intro i z hzi
  refine (FromSpec.mem_carrier_iff_of_mem f_deg hm _ _ hzi).trans ?_
  exact (ToSpec.mk_mem_carrier _ _).trans (x.1.2.pow_mem_iff_mem m hm)

中文:
引理 fromSpec_toSpec
  条件: {f : A} {m : 自然数} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Proj.T| pbo f)
  证明: by
refine Subtype.ext ProjectiveSpectrum.ext HomogeneousIdeal.ext' ?_
  intro i z hzi
  refine (FromSpec.mem_carrier_iff_of_mem f_deg hm _ _ hzi).trans ?_
  exact (ToSpec.mk_mem_carrier _ _).trans (x.1.2.pow_mem_iff_mem m hm)

Depends on / 依赖: FromSpec, FromSpec.mem_carrier_iff_of_mem, HomogeneousIdeal, HomogeneousIdeal.ext, ProjectiveSpectrum, ProjectiveSpectrum.ext, Subtype, Subtype.ext, ToSpec, ToSpec.mk_mem_carrier, f_deg, mem_carrier_iff_of_mem, mk_mem_carrier, pow_mem_iff_mem
-/
lemma fromSpec_toSpec {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Proj.T| pbo f) :
    FromSpec.toFun f_deg hm (toSpec 𝒜 f x) = x := by
refine Subtype.ext ProjectiveSpectrum.ext HomogeneousIdeal.ext' ?_
  intro i z hzi
  refine (FromSpec.mem_carrier_iff_of_mem f_deg hm _ _ hzi).trans ?_
  exact (ToSpec.mk_mem_carrier _ _).trans (x.1.2.pow_mem_iff_mem m hm)

/--
lemma `toSpec_injective` / 引理 `toSpec_injective`

English:
lemma toSpec_injective
  given: {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m)
  proof: by
  intro x₁ x₂ h
  have := congr_arg (FromSpec.toFun f_deg hm) h
  rwa [fromSpec_toSpec, fromSpec_toSpec] at this

中文:
引理 toSpec_injective
  条件: {f : A} {m : 自然数} (f_deg : f in 𝒜 m) (hm : 0 < m)
  证明: by
  intro x₁ x₂ h
  have := congr_arg (FromSpec.toFun f_deg hm) h
  rwa [fromSpec_toSpec, fromSpec_toSpec] at this

Depends on / 依赖: FromSpec, FromSpec.toFun, congr_arg, f_deg, fromSpec_toSpec
-/
lemma toSpec_injective {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    Function.Injective (toSpec 𝒜 f) := by
  intro x₁ x₂ h
  have := congr_arg (FromSpec.toFun f_deg hm) h
  rwa [fromSpec_toSpec, fromSpec_toSpec] at this

/--
lemma `toSpec_surjective` / 引理 `toSpec_surjective`

English:
lemma toSpec_surjective
  given: {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m)
  proof: .mpr Function.surjective_iff_hasRightInverse
    ⟨FromSpec.toFun f_deg hm, toSpec_fromSpec 𝒜 f_deg hm⟩

中文:
引理 toSpec_surjective
  条件: {f : A} {m : 自然数} (f_deg : f in 𝒜 m) (hm : 0 < m)
  证明: .mpr Function.surjective_iff_hasRightInverse
    ⟨FromSpec.toFun f_deg hm, toSpec_fromSpec 𝒜 f_deg hm⟩

Depends on / 依赖: FromSpec, FromSpec.toFun, Function, Function.surjective_iff_hasRightInverse, f_deg, surjective_iff_hasRightInverse, toSpec_fromSpec
-/
lemma toSpec_surjective {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    Function.Surjective (toSpec 𝒜 f) :=
.mpr Function.surjective_iff_hasRightInverse
    ⟨FromSpec.toFun f_deg hm, toSpec_fromSpec 𝒜 f_deg hm⟩

/--
lemma `toSpec_bijective` / 引理 `toSpec_bijective`

English:
lemma toSpec_bijective
  given: {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m)
  proof: ⟨toSpec_injective 𝒜 f_deg hm, toSpec_surjective 𝒜 f_deg hm⟩

中文:
引理 toSpec_bijective
  条件: {f : A} {m : 自然数} (f_deg : f in 𝒜 m) (hm : 0 < m)
  证明: ⟨toSpec_injective 𝒜 f_deg hm, toSpec_surjective 𝒜 f_deg hm⟩
-/
lemma toSpec_bijective {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    Function.Bijective (toSpec (𝒜 := 𝒜) (f := f)) :=
  ⟨toSpec_injective 𝒜 f_deg hm, toSpec_surjective 𝒜 f_deg hm⟩

end fromSpecToSpec

namespace toSpec

variable {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m)
include hm f_deg

set_option backward.isDefEq.respectTransparency false in
variable {𝒜} in
/--
lemma `image_basicOpen_eq_basicOpen` / 引理 `image_basicOpen_eq_basicOpen`

English:
lemma image_basicOpen_eq_basicOpen
  given: (a : A) (i : Nat)
  proof: Set.preimage_injective.mpr (toSpec_surjective 𝒜 f_deg hm)
    Set.preimage_image_eq _ (toSpec_injective 𝒜 f_deg hm) ▸ by
  rw [Opens.carrier_eq_coe]; rw [toSpec_preimage_basicOpen]; rw [ProjectiveSpectrum.basicOpen_pow 𝒜 _ m hm]

中文:
引理 image_basicOpen_eq_basicOpen
  条件: (a : A) (i : 自然数)
  证明: Set.preimage_injective.mpr (toSpec_surjective 𝒜 f_deg hm)
    Set.preimage_image_eq _ (toSpec_injective 𝒜 f_deg hm) ▸ by
  rw [Opens.carrier_eq_coe]; rw [toSpec_preimage_basicOpen]; rw [ProjectiveSpectrum.basicOpen_pow 𝒜 _ m hm]
-/
lemma image_basicOpen_eq_basicOpen (a : A) (i : Nat) :
    toSpec 𝒜 f '' Subtype.val ⁻¹' (pbo (decompose 𝒜 a i) : Set (ProjectiveSpectrum 𝒜)) =
    (PrimeSpectrum.basicOpen (R := A⁰_ f) <|
      HomogeneousLocalization.mk
        ⟨m * i, ⟨decompose 𝒜 a i ^ m,
          smul_eq_mul m i ▸ SetLike.pow_mem_graded _ (SetLike.coe_mem _)⟩,
          ⟨f^i, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg⟩, ⟨i, rfl⟩⟩).1 :=
Set.preimage_injective.mpr (toSpec_surjective 𝒜 f_deg hm)
    Set.preimage_image_eq _ (toSpec_injective 𝒜 f_deg hm) ▸ by
  rw [Opens.carrier_eq_coe]; rw [toSpec_preimage_basicOpen]; rw [ProjectiveSpectrum.basicOpen_pow 𝒜 _ m hm]

end toSpec

set_option backward.isDefEq.respectTransparency false in
variable {𝒜} in
/--
Definition of `fromSpec` / `fromSpec` 的定义

English:
definition fromSpec
  signature: {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m)
  body: TopCat.ofHom
  { toFun := FromSpec.toFun f_deg hm
    continuous_toFun := by
      rw [isTopologicalBasis_subtype (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜)
.continuous_iff] (· in pbo f)
      rintro s ⟨_, ⟨a, rfl⟩, rfl⟩
      have h₁ : Subtype.val (p := (· in pbo f)) ⁻¹' (pbo a) =
      

中文:
定义 fromSpec
  签名: {f : A} {m : 自然数} (f_deg : f in 𝒜 m) (hm : 0 < m)
  定义体: TopCat.ofHom
  { toFun := FromSpec.toFun f_deg hm
    continuous_toFun := by
      rw [isTopologicalBasis_subtype (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜)
.continuous_iff] (· in pbo f)
      rintro s ⟨_, ⟨a, rfl⟩, rfl⟩
      have h₁ : Subtype.val (p := (· in pbo f)) ⁻¹' (pbo a) =
      

Depends on / 依赖: FromSpec, FromSpec.toFun, ProjectiveSpectrum, ProjectiveSpectrum.basicOpen_eq_union_of_projection, ProjectiveSpectrum.isTopologicalBasis_basic_opens, Subtype, Subtype.val, ToSpec, ToSpec.toFun, TopCat, TopCat.ofHom, basicOpen_eq_union_of_projection, continuous_iff, continuous_toFun, decompose, f_deg, fromSpec, isTopologicalBasis_basic_opens, isTopologicalBasis_subtype, toSpec_fromSpec
-/
def fromSpec {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    (Spec.T (A⁰_ f)) ⟶ (Proj.T| (pbo f)) :=
  TopCat.ofHom
  { toFun := FromSpec.toFun f_deg hm
    continuous_toFun := by
      rw [isTopologicalBasis_subtype (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜)
.continuous_iff] (· in pbo f)
      rintro s ⟨_, ⟨a, rfl⟩, rfl⟩
      have h₁ : Subtype.val (p := (· in pbo f)) ⁻¹' (pbo a) =
          ⋃ i : Nat, Subtype.val (p := (· in pbo f)) ⁻¹' (pbo (decompose 𝒜 a i)) := by
        simp [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 a]
      let e : _ ≃ _ :=
        ⟨FromSpec.toFun f_deg hm, ToSpec.toFun f, toSpec_fromSpec _ _ _, fromSpec_toSpec _ _ _⟩
change IsOpen e ⁻¹' _
      rw [← Equiv.image_symm_eq_preimage]; rw [h₁]; rw [Set.image_iUnion]
      exact isOpen_iUnion fun i => toSpec.image_basicOpen_eq_basicOpen f_deg hm a i ▸
        PrimeSpectrum.isOpen_basicOpen }

end ProjIsoSpecTopComponent

variable {𝒜} in
/--
Definition of `projIsoSpecTopComponent` / `projIsoSpecTopComponent` 的定义

English:
definition projIsoSpecTopComponent
  signature: {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m)
  body: ProjIsoSpecTopComponent.toSpec 𝒜 f
  inv := ProjIsoSpecTopComponent.fromSpec f_deg hm
  hom_inv_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.fromSpec_toSpec 𝒜 f_deg hm)
  inv_hom_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.toSpec_fromSpec 𝒜 f_deg hm)

中文:
定义 projIsoSpecTopComponent
  签名: {f : A} {m : 自然数} (f_deg : f in 𝒜 m) (hm : 0 < m)
  定义体: ProjIsoSpecTopComponent.toSpec 𝒜 f
  inv := ProjIsoSpecTopComponent.fromSpec f_deg hm
  hom_inv_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.fromSpec_toSpec 𝒜 f_deg hm)
  inv_hom_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.toSpec_fromSpec 𝒜 f_deg hm)

Depends on / 依赖: ProjIsoSpecTopComponent, ProjIsoSpecTopComponent.toSpec, toSpec
-/
def projIsoSpecTopComponent {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    (Proj.T| (pbo f)) ≅ (Spec.T (A⁰_ f)) where
  hom := ProjIsoSpecTopComponent.toSpec 𝒜 f
  inv := ProjIsoSpecTopComponent.fromSpec f_deg hm
  hom_inv_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.fromSpec_toSpec 𝒜 f_deg hm)
  inv_hom_id := ConcreteCategory.hom_ext _ _
    (ProjIsoSpecTopComponent.toSpec_fromSpec 𝒜 f_deg hm)

namespace ProjectiveSpectrum.Proj

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `awayToSection` / `awayToSection` 的定义

English:
definition awayToSection
  signature: (f)
  body: CommRingCat.ofHom
    -- Have to hint `S`, otherwise it gets unfolded to `structureSheafInType`
    -- causing `ext` to fail
    (S := (structureSheaf 𝒜).1.obj (op (pbo f)))
  { toFun s :=
      ⟨fun x => HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2) s, fun x => by
        obtain ⟨s,

中文:
定义 awayToSection
  签名: (f)
  定义体: CommRingCat.ofHom
    -- Have to hint `S`, otherwise it gets unfolded to `structureSheafInType`
    -- causing `ext` to fail
    (S := (structureSheaf 𝒜).1.obj (op (pbo f)))
  { toFun s :=
      ⟨fun x => HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2) s, fun x => by
        obtain ⟨s,

Depends on / 依赖: CommRingCat, CommRingCat.ofHom
-/
def awayToSection (f) : CommRingCat.of (A⁰_ f) ⟶ (structureSheaf 𝒜).1.obj (op (pbo f)) :=
  CommRingCat.ofHom
    -- Have to hint `S`, otherwise it gets unfolded to `structureSheafInType`
    -- causing `ext` to fail
    (S := (structureSheaf 𝒜).1.obj (op (pbo f)))
  { toFun s :=
      ⟨fun x => HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2) s, fun x => by
        obtain ⟨s, rfl⟩ := HomogeneousLocalization.mk_surjective s
        obtain ⟨n, hn : f ^ n = s.den.1⟩ := s.den_mem
        exact ⟨_, x.2, 𝟙 _, s.1, s.2, s.3,
          fun x hsx => x.2 (Ideal.IsPrime.mem_of_pow_mem inferInstance n (hn ▸ hsx)), fun _ => rfl⟩⟩
    map_add' _ _ := by ext; simp only [map_add, HomogeneousLocalization.val_add, Proj.add_apply]
    map_mul' _ _ := by ext; simp only [map_mul, HomogeneousLocalization.val_mul, Proj.mul_apply]
    map_zero' := by ext; simp only [map_zero, HomogeneousLocalization.val_zero, Proj.zero_apply]
    map_one' := by ext; simp only [map_one, HomogeneousLocalization.val_one, Proj.one_apply] }

/--
lemma `awayToSection_germ` / 引理 `awayToSection_germ`

English:
lemma awayToSection_germ
  given: (f x hx)
  proof: by
  ext z
  apply (Proj.stalkIso' 𝒜 x).eq_symm_apply.mpr
  apply Proj.stalkIso'_germ

中文:
引理 awayToSection_germ
  条件: (f x hx)
  证明: by
  ext z
  apply (Proj.stalkIso' 𝒜 x).eq_symm_apply.mpr
  apply Proj.stalkIso'_germ

Depends on / 依赖: Proj.stalkIso, _germ, eq_symm_apply, eq_symm_apply.mpr, stalkIso
-/
lemma awayToSection_germ (f x hx) :
    awayToSection 𝒜 f ≫ (structureSheaf 𝒜).presheaf.germ _ x hx =
      CommRingCat.ofHom (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx)) ≫
        (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv := by
  ext z
  apply (Proj.stalkIso' 𝒜 x).eq_symm_apply.mpr
  apply Proj.stalkIso'_germ

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `awayToSection_apply` / 引理 `awayToSection_apply`

English:
lemma awayToSection_apply
  given: (f : A) (x p)
  proof: by
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective x
  change (HomogeneousLocalization.mapId 𝒜 _ _).val = _
  dsimp [HomogeneousLocalization.mapId, HomogeneousLocalization.map]
  rw [Localization.mk_eq_mk']; rw [Localization.mk_eq_mk']; rw [IsLocalization.map_mk']
  rfl

中文:
引理 awayToSection_apply
  条件: (f : A) (x p)
  证明: by
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective x
  change (HomogeneousLocalization.mapId 𝒜 _ _).val = _
  dsimp [HomogeneousLocalization.mapId, HomogeneousLocalization.map]
  rw [Localization.mk_eq_mk']; rw [Localization.mk_eq_mk']; rw [IsLocalization.map_mk']
  rfl

Depends on / 依赖: Submonoid, Submonoid.powers, powers, primeCompl, toIdeal, toIdeal.primeCompl
-/
lemma awayToSection_apply (f : A) (x p) :
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).1 x).val p).val =
      IsLocalization.map (M := Submonoid.powers f) (T := p.1.1.toIdeal.primeCompl) _
        (RingHom.id _) (Submonoid.powers_le.mpr p.2) x.val := by
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective x
  change (HomogeneousLocalization.mapId 𝒜 _ _).val = _
  dsimp [HomogeneousLocalization.mapId, HomogeneousLocalization.map]
  rw [Localization.mk_eq_mk']; rw [Localization.mk_eq_mk']; rw [IsLocalization.map_mk']
  rfl

/--
Definition of `awayToΓ` / `awayToΓ` 的定义

English:
definition awayToΓ
  signature: (f)
  body: awayToSection 𝒜 f ≫ (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map
    (homOfLE (Opens.isOpenEmbedding_obj_top _).le).op

中文:
定义 awayToΓ
  签名: (f)
  定义体: awayToSection 𝒜 f ≫ (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map
    (homOfLE (Opens.isOpenEmbedding_obj_top _).le).op

Depends on / 依赖: Opens.isOpenEmbedding_obj_top, ProjectiveSpectrum, ProjectiveSpectrum.Proj.structureSheaf, awayToSection, homOfLE, isOpenEmbedding_obj_top, structureSheaf
-/
def awayToΓ (f) : CommRingCat.of (A⁰_ f) ⟶ LocallyRingedSpace.Γ.obj (op <| Proj| pbo f) :=
  awayToSection 𝒜 f ≫ (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map
    (homOfLE (Opens.isOpenEmbedding_obj_top _).le).op

set_option backward.isDefEq.respectTransparency false in
/--
lemma `awayToΓ_ΓToStalk` / 引理 `awayToΓ_ΓToStalk`

English:
lemma awayToΓ_ΓToStalk
  given: (f) (x)
  proof: by
  rw [awayToΓ]; rw [Category.assoc]; rw [← Category.assoc _ (Iso.inv _)]; rw [Iso.eq_comp_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [Presheaf.Γgerm]
  rw [LocallyRingedSpace.restrictStalkIso_hom_eq_germ]
  simp only [Proj.toLocallyRingedSpace, Proj.toSheafedSpace]
  rw [Presheaf.germ_res

中文:
引理 awayToΓ_ΓToStalk
  条件: (f) (x)
  证明: by
  rw [awayToΓ]; rw [Category.assoc]; rw [← Category.assoc _ (Iso.inv _)]; rw [Iso.eq_comp_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [Presheaf.Γgerm]
  rw [LocallyRingedSpace.restrictStalkIso_hom_eq_germ]
  simp only [Proj.toLocallyRingedSpace, Proj.toSheafedSpace]
  rw [Presheaf.germ_res

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, Iso.inv, LocallyRingedSpace, LocallyRingedSpace.restrictStalkIso_hom_eq_germ, Presheaf, Presheaf.germ_res, Proj.toLocallyRingedSpace, Proj.toSheafedSpace, awayToSection_germ, eq_comp_inv, germ_res, restrictStalkIso_hom_eq_germ, toLocallyRingedSpace, toSheafedSpace
-/
lemma awayToΓ_ΓToStalk (f) (x) :
    awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x =
      CommRingCat.ofHom (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2)) ≫
      (Proj.stalkIso' 𝒜 x.1).toCommRingCatIso.inv ≫
      ((Proj.toLocallyRingedSpace 𝒜).restrictStalkIso (Opens.isOpenEmbedding _) x).inv := by
  rw [awayToΓ]; rw [Category.assoc]; rw [← Category.assoc _ (Iso.inv _)]; rw [Iso.eq_comp_inv]; rw [Category.assoc]; rw [Category.assoc]; rw [Presheaf.Γgerm]
  rw [LocallyRingedSpace.restrictStalkIso_hom_eq_germ]
  simp only [Proj.toLocallyRingedSpace, Proj.toSheafedSpace]
  rw [Presheaf.germ_res]; rw [awayToSection_germ]
  rfl

/--
Definition of `toSpec` / `toSpec` 的定义

English:
definition toSpec
  signature: (f)
  body: ΓSpec.locallyRingedSpaceAdjunction.homEquiv (Proj| pbo f) (op (CommRingCat.of <| A⁰_ f))
    (awayToΓ 𝒜 f).op

中文:
定义 toSpec
  签名: (f)
  定义体: ΓSpec.locallyRingedSpaceAdjunction.homEquiv (Proj| pbo f) (op (CommRingCat.of <| A⁰_ f))
    (awayToΓ 𝒜 f).op

Depends on / 依赖: CommRingCat, CommRingCat.of, Spec.locallyRingedSpaceAdjunction.homEquiv, homEquiv, locallyRingedSpaceAdjunction
-/
def toSpec (f) : (Proj| pbo f) ⟶ Spec (A⁰_ f) :=
  ΓSpec.locallyRingedSpaceAdjunction.homEquiv (Proj| pbo f) (op (CommRingCat.of <| A⁰_ f))
    (awayToΓ 𝒜 f).op

open HomogeneousLocalization IsLocalRing

set_option backward.isDefEq.respectTransparency false in
/--
lemma `toSpec_base_apply_eq_comap` / 引理 `toSpec_base_apply_eq_comap`

English:
lemma toSpec_base_apply_eq_comap
  given: {f} (x : Proj| pbo f)
  proof: by
  change PrimeSpectrum.comap (awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x).hom
        (IsLocalRing.closedPoint ((Proj| pbo f).presheaf.stalk x)) = _
  rw [awayToΓ_ΓToStalk]; rw [CommRingCat.hom_comp]; rw [PrimeSpectrum.comap_comp]
  exact congr(PrimeSpectrum.comap _ $(@IsLocalRing.comap_closedP

中文:
引理 toSpec_base_apply_eq_comap
  条件: {f} (x : Proj| pbo f)
  证明: by
  change PrimeSpectrum.comap (awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x).hom
        (IsLocalRing.closedPoint ((Proj| pbo f).presheaf.stalk x)) = _
  rw [awayToΓ_ΓToStalk]; rw [CommRingCat.hom_comp]; rw [PrimeSpectrum.comap_comp]
  exact congr(PrimeSpectrum.comap _ $(@IsLocalRing.comap_closedP

Depends on / 依赖: AtPrime, CommRingCat, CommRingCat.hom_comp, HomogeneousLocalization, HomogeneousLocalization.AtPrime, IsLocalRing, IsLocalRing.closedPoint, IsLocalRing.comap_closedPoint, PrimeSpectrum, PrimeSpectrum.comap, PrimeSpectrum.comap_comp, asHomogeneousIdeal, asHomogeneousIdeal.toIdeal, closedPoint, comap_closedPoint, comap_comp, hom_comp, isLocalHom_of_isIso, presheaf, presheaf.stalk
-/
lemma toSpec_base_apply_eq_comap {f} (x : Proj| pbo f) :
    (toSpec 𝒜 f).base x = PrimeSpectrum.comap (mapId 𝒜 (Submonoid.powers_le.mpr x.2))
      (closedPoint (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)) := by
  change PrimeSpectrum.comap (awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x).hom
        (IsLocalRing.closedPoint ((Proj| pbo f).presheaf.stalk x)) = _
  rw [awayToΓ_ΓToStalk]; rw [CommRingCat.hom_comp]; rw [PrimeSpectrum.comap_comp]
  exact congr(PrimeSpectrum.comap _ $(@IsLocalRing.comap_closedPoint
    (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) _ _
    ((Proj| pbo f).presheaf.stalk x) _ _ _ (isLocalHom_of_isIso _)))

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toSpec_base_apply_eq` / 引理 `toSpec_base_apply_eq`

English:
lemma toSpec_base_apply_eq
  given: {f} (x : Proj| pbo f)
  proof: .trans PrimeSpectrum.ext Ideal.ext fun z => toSpec_base_apply_eq_comap 𝒜 x
  show ¬ IsUnit _ ↔ z in ProjIsoSpecTopComponent.ToSpec.carrier _ by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]; rw [ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier]; rw [Homogen

中文:
引理 toSpec_base_apply_eq
  条件: {f} (x : Proj| pbo f)
  证明: .trans PrimeSpectrum.ext Ideal.ext fun z => toSpec_base_apply_eq_comap 𝒜 x
  show ¬ IsUnit _ ↔ z in ProjIsoSpecTopComponent.ToSpec.carrier _ by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]; rw [ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier]; rw [Homogen

Depends on / 依赖: AtPrime, HomogeneousLocalization, HomogeneousLocalization.isUnit_iff_isUnit_val, HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, Ideal.ext, IsLocalization, IsLocalization.AtPrime.isUnit_mk, IsUnit, Localization, Localization.mk_eq_mk, PrimeSpectrum, PrimeSpectrum.ext, ProjIsoSpecTopComponent, ProjIsoSpecTopComponent.ToSpec.carrier, ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier, ToSpec, _iff, carrier, isUnit_iff_isUnit_val
-/
lemma toSpec_base_apply_eq {f} (x : Proj| pbo f) :
    (toSpec 𝒜 f).base x = ProjIsoSpecTopComponent.toSpec 𝒜 f x :=
.trans PrimeSpectrum.ext Ideal.ext fun z => toSpec_base_apply_eq_comap 𝒜 x
  show ¬ IsUnit _ ↔ z in ProjIsoSpecTopComponent.ToSpec.carrier _ by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val]; rw [ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier]; rw [HomogeneousLocalization.map_mk]; rw [HomogeneousLocalization.val_mk]; rw [Localization.mk_eq_mk']; rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  exact not_not

/--
lemma `toSpec_base_isIso` / 引理 `toSpec_base_isIso`

English:
lemma toSpec_base_isIso
  given: {f} {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  proof: by
  convert! (projIsoSpecTopComponent f_deg hm).isIso_hom
exact ConcreteCategory.hom_ext _ _ toSpec_base_apply_eq 𝒜

中文:
引理 toSpec_base_isIso
  条件: {f} {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  证明: by
  convert! (projIsoSpecTopComponent f_deg hm).isIso_hom
exact ConcreteCategory.hom_ext _ _ toSpec_base_apply_eq 𝒜

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, convert, f_deg, hom_ext, isIso_hom, projIsoSpecTopComponent, toSpec_base_apply_eq
-/
lemma toSpec_base_isIso {f} {m} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    IsIso (toSpec 𝒜 f).base := by
  convert! (projIsoSpecTopComponent f_deg hm).isIso_hom
exact ConcreteCategory.hom_ext _ _ toSpec_base_apply_eq 𝒜

/--
lemma `mk_mem_toSpec_base_apply` / 引理 `mk_mem_toSpec_base_apply`

English:
lemma mk_mem_toSpec_base_apply
  statement: {f} (x : Proj| pbo f)
  proof: (toSpec_base_apply_eq 𝒜 x).symm ▸ ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier _ _

中文:
引理 mk_mem_toSpec_base_apply
  结论: {f} (x : Proj| pbo f)
  证明: (toSpec_base_apply_eq 𝒜 x).symm ▸ ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier _ _

Depends on / 依赖: ProjIsoSpecTopComponent, ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier, ToSpec, mk_mem_carrier, toSpec_base_apply_eq
-/
lemma mk_mem_toSpec_base_apply {f} (x : Proj| pbo f)
    (z : NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z in ((toSpec 𝒜 f).base x).asIdeal ↔
      z.num.1 in x.1.asHomogeneousIdeal :=
  (toSpec_base_apply_eq 𝒜 x).symm ▸ ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier _ _

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toSpec_preimage_basicOpen` / 引理 `toSpec_preimage_basicOpen`

English:
lemma toSpec_preimage_basicOpen
  statement: {f}
  proof: Opens.ext Opens.map_coe _ _ ▸ by
  convert! (ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen f t)
  exact funext fun _ => toSpec_base_apply_eq _ _

#adaptation_note

中文:
引理 toSpec_preimage_basicOpen
  结论: {f}
  证明: Opens.ext Opens.map_coe _ _ ▸ by
  convert! (ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen f t)
  exact funext fun _ => toSpec_base_apply_eq _ _

#adaptation_note

Depends on / 依赖: Opens.ext, Opens.map_coe, ProjIsoSpecTopComponent, ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen, ToSpec, convert, map_coe, preimage_basicOpen, toSpec_base_apply_eq
-/
lemma toSpec_preimage_basicOpen {f}
    (t : NumDenSameDeg 𝒜 (.powers f)) :
    (Opens.map (toSpec 𝒜 f).base).obj (sbo (HomogeneousLocalization.mk t)) =
      Opens.comap ⟨_, continuous_subtype_val⟩ (pbo t.num.1) :=
Opens.ext Opens.map_coe _ _ ▸ by
  convert! (ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen f t)
  exact funext fun _ => toSpec_base_apply_eq _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
lemma `toOpen_toSpec_val_c_app` / 引理 `toOpen_toSpec_val_c_app`

English:
lemma toOpen_toSpec_val_c_app
  given: (f) (U)
  proof: Eq.trans (by rfl) ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app _ U

中文:
引理 toOpen_toSpec_val_c_app
  条件: (f) (U)
  证明: Eq.trans (by rfl) ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app _ U

Depends on / 依赖: Eq.trans, Spec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app, toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app
-/
lemma toOpen_toSpec_val_c_app (f) (U) :
    (Scheme.ΓSpecIso _).inv ≫ (Spec A⁰_ f).presheaf.map (homOfLE le_top).op ≫
      (toSpec 𝒜 f).c.app U =
      awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.map (homOfLE le_top).op :=
Eq.trans (by rfl) ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app _ U

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `toStalk_stalkMap_toSpec` / 引理 `toStalk_stalkMap_toSpec`

English:
lemma toStalk_stalkMap_toSpec
  given: (f) (x)
  proof: by
  dsimp
  erw [LocallyRingedSpace.stalkMap_germ (toSpec 𝒜 f) ⊤ x (by simp)]
  erw [toOpen_toSpec_val_c_app_assoc]
  rfl

中文:
引理 toStalk_stalkMap_toSpec
  条件: (f) (x)
  证明: by
  dsimp
  erw [LocallyRingedSpace.stalkMap_germ (toSpec 𝒜 f) ⊤ x (by simp)]
  erw [toOpen_toSpec_val_c_app_assoc]
  rfl

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.stalkMap_germ, stalkMap_germ, toOpen_toSpec_val_c_app_assoc, toSpec
-/
lemma toStalk_stalkMap_toSpec (f) (x) :
    (Scheme.ΓSpecIso _).inv ≫ (Spec A⁰_ f).presheaf.germ _ _ (by simp) ≫
      (toSpec 𝒜 f).stalkMap x = awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x := by
  dsimp
  erw [LocallyRingedSpace.stalkMap_germ (toSpec 𝒜 f) ⊤ x (by simp)]
  erw [toOpen_toSpec_val_c_app_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isLocalization_atPrime` / 引理 `isLocalization_atPrime`

English:
lemma isLocalization_atPrime
  given: (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  proof: by
  let : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  constructor; constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective y
    refine .of_mul_eq_one
(.mk ⟨y.deg, y.den, y.num, (mk_mem_

中文:
引理 isLocalization_atPrime
  条件: (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  证明: by
  let : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  constructor; constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective y
    refine .of_mul_eq_one
(.mk ⟨y.deg, y.den, y.num, (mk_mem_

Depends on / 依赖: Algebra, AtPrime, GradedRingHom, GradedRingHom.id_apply, HomogeneousLocalization, HomogeneousLocalization.mk_surjective, IsLocalization, IsLocalization.mk, RingHom, RingHom.algebraMap_toAlgebra, Submonoid, Submonoid.powers_le.mpr, _eq_one, _mul_mk, algebraMap_toAlgebra, asHomogeneousIdeal, asHomogeneousIdeal.toIdeal, id_apply, map_mk, mk_eq_mk
-/
lemma isLocalization_atPrime (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    @IsLocalization (Away 𝒜 f) _ ((toSpec 𝒜 f).base x).asIdeal.primeCompl
      (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) _
      (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra := by
  let : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  constructor; constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective y
    refine .of_mul_eq_one
(.mk ⟨y.deg, y.den, y.num, (mk_mem_toSpec_base_apply _ _ _).not.mp hy⟩) val_injective _ ?_
    simp only [RingHom.algebraMap_toAlgebra, map_mk, GradedRingHom.id_apply, val_mul, val_mk,
      mk_eq_mk', val_one, IsLocalization.mk'_mul_mk'_eq_one']
  · intro z
    obtain ⟨⟨i, a, ⟨b, hb⟩, (hb' : b ∉ x.1.1)⟩, rfl⟩ := z.mk_surjective
    refine ⟨⟨HomogeneousLocalization.mk ⟨i * m, ⟨a * b ^ (m - 1), ?_⟩,
        ⟨f ^ i, SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
      ⟨HomogeneousLocalization.mk ⟨i * m, ⟨b ^ m, mul_comm m i ▸ SetLike.pow_mem_graded _ hb⟩,
        ⟨f ^ i, SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
(mk_mem_toSpec_base_apply _ _ _).not.mpr x.1.1.toIdeal.primeCompl.pow_mem hb' m⟩⟩,
        val_injective _ ?_⟩
    · convert SetLike.mul_mem_graded a.2 (SetLike.pow_mem_graded (m - 1) hb)
      rw [← succ_nsmul']; rw [tsub_add_cancel_of_le (by lia)]; rw [mul_comm]; rw [smul_eq_mul]
    · simp only [RingHom.algebraMap_toAlgebra, map_mk, GradedRingHom.id_apply, val_mul, val_mk,
        mk_eq_mk', ← IsLocalization.mk'_mul, Submonoid.mk_mul_mk, IsLocalization.mk'_eq_iff_eq]
      rw [mul_comm b]; rw [mul_mul_mul_comm]; rw [← pow_succ']; rw [mul_assoc]; rw [tsub_add_cancel_of_le (by lia)]
  · intro y z e
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective y
    obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective z
    obtain ⟨i, c, hc, hc', e⟩ : exists i, exists c in 𝒜 i, c ∉ x.1.asHomogeneousIdeal ∧
        c * (z.den.1 * y.num.1) = c * (y.den.1 * z.num.1) := by
      apply_fun HomogeneousLocalization.val at e
      simp only [RingHom.algebraMap_toAlgebra, map_mk, GradedRingHom.id_apply, val_mk, mk_eq_mk',
        IsLocalization.mk'_eq_iff_eq] at e
      obtain ⟨⟨c, hcx⟩, hc⟩ := IsLocalization.exists_of_eq (M := x.1.1.toIdeal.primeCompl) e
      obtain ⟨i, hi⟩ := not_forall.mp ((x.1.1.isHomogeneous.mem_iff _).not.mp hcx)
      refine ⟨i, _, (decompose 𝒜 c i).2, hi, ?_⟩
      apply_fun fun x => (decompose 𝒜 x (i + z.deg + y.deg)).1 at hc
      conv_rhs at hc => rw [add_right_comm]
      rwa [← mul_assoc, coe_decompose_mul_add_of_right_mem, coe_decompose_mul_add_of_right_mem,
        ← mul_assoc, coe_decompose_mul_add_of_right_mem, coe_decompose_mul_add_of_right_mem,
        mul_assoc, mul_assoc] at hc
      exacts [y.den.2, z.num.2, z.den.2, y.num.2]
    refine ⟨⟨HomogeneousLocalization.mk ⟨m * i, ⟨c ^ m, SetLike.pow_mem_graded _ hc⟩,
      ⟨f ^ i, mul_comm m i ▸ SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
(mk_mem_toSpec_base_apply _ _ _).not.mpr x.1.1.toIdeal.primeCompl.pow_mem hc' _⟩,
      val_injective _ ?_⟩
    simp only [val_mul, val_mk, mk_eq_mk', ← IsLocalization.mk'_mul, Submonoid.mk_mul_mk,
      IsLocalization.mk'_eq_iff_eq, mul_assoc]
    congr 2
    rw [mul_left_comm]; rw [mul_left_comm y.den.1]; rw [← tsub_add_cancel_of_le (show 1 <= m from hm)]; rw [pow_succ]; rw [mul_assoc]; rw [mul_assoc]; rw [e]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `specStalkEquiv` / `specStalkEquiv` 的定义

English:
definition specStalkEquiv
  signature: (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  body: letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  haveI := isLocalization_atPrime 𝒜 f x f_deg hm
  (IsLocalization.algEquiv
    (R := A⁰_ f)
    (M := ((toSpec 𝒜 f).base x).asIdeal.primeCompl)
    (S := (Spec.structureShea

中文:
定义 specStalkEquiv
  签名: (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  定义体: letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  haveI := isLocalization_atPrime 𝒜 f x f_deg hm
  (IsLocalization.algEquiv
    (R := A⁰_ f)
    (M := ((toSpec 𝒜 f).base x).asIdeal.primeCompl)
    (S := (Spec.structureShea

Depends on / 依赖: Algebra, AtPrime, IsLocalization, IsLocalization.algEquiv, Spec.structureSheaf, Submonoid, Submonoid.powers_le.mpr, algEquiv, asHomogeneousIdeal, asHomogeneousIdeal.toIdeal, asIdeal, asIdeal.primeCompl, f_deg, isLocalization_atPrime, powers_le, presheaf, presheaf.stalk, primeCompl, structureSheaf, toAlgebra
-/
def specStalkEquiv (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x) ≅
      CommRingCat.of (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
  letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  haveI := isLocalization_atPrime 𝒜 f x f_deg hm
  (IsLocalization.algEquiv
    (R := A⁰_ f)
    (M := ((toSpec 𝒜 f).base x).asIdeal.primeCompl)
    (S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x))
    (Q := AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)).toRingEquiv.toCommRingCatIso

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `toStalk_specStalkEquiv` / 引理 `toStalk_specStalkEquiv`

English:
lemma toStalk_specStalkEquiv
  given: (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  proof: letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  letI := isLocalization_atPrime 𝒜 f x f_deg hm
  CommRingCat.hom_ext (IsLocalization.algEquiv
    (R := A⁰_ f)
    (M := ((toSpec 𝒜 f).base x).asIdeal.primeCompl)
    (S := 

中文:
引理 toStalk_specStalkEquiv
  条件: (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  证明: letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  letI := isLocalization_atPrime 𝒜 f x f_deg hm
  CommRingCat.hom_ext (IsLocalization.algEquiv
    (R := A⁰_ f)
    (M := ((toSpec 𝒜 f).base x).asIdeal.primeCompl)
    (S := 

Depends on / 依赖: Algebra, AtPrime, CommRingCat, CommRingCat.hom_ext, IsLocalization, IsLocalization.algEquiv, Spec.structureSheaf, Submonoid, Submonoid.powers_le.mpr, algEquiv, asHomogeneousIdeal, asHomogeneousIdeal.toIdeal, asIdeal, asIdeal.primeCompl, comp_algebraMap, f_deg, hom_ext, isLocalization_atPrime, powers_le, presheaf
-/
lemma toStalk_specStalkEquiv (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    StructureSheaf.toStalk (A⁰_ f) ((toSpec 𝒜 f).base x) ≫ (specStalkEquiv 𝒜 f x f_deg hm).hom =
      CommRingCat.ofHom (mapId _ <| Submonoid.powers_le.mpr x.2) :=
  letI : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  letI := isLocalization_atPrime 𝒜 f x f_deg hm
  CommRingCat.hom_ext (IsLocalization.algEquiv
    (R := A⁰_ f)
    (M := ((toSpec 𝒜 f).base x).asIdeal.primeCompl)
    (S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x))
    (Q := AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)).toAlgHom.comp_algebraMap

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `stalkMap_toSpec` / 引理 `stalkMap_toSpec`

English:
lemma stalkMap_toSpec
  given: (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  proof: by
refine CommRingCat.hom_ext
    IsLocalization.ringHom_ext (R := A⁰_ f) ((toSpec 𝒜 f).base x).asIdeal.primeCompl
(S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x)) ?_
  ext a
  refine congr($(toStalk_stalkMap_toSpec 𝒜 f x) _).trans ?_
  rw [awayToΓ_ΓToStalk]; rw [← toStalk_s

中文:
引理 stalkMap_toSpec
  条件: (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  证明: by
refine CommRingCat.hom_ext
    IsLocalization.ringHom_ext (R := A⁰_ f) ((toSpec 𝒜 f).base x).asIdeal.primeCompl
(S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x)) ?_
  ext a
  refine congr($(toStalk_stalkMap_toSpec 𝒜 f x) _).trans ?_
  rw [awayToΓ_ΓToStalk]; rw [← toStalk_s

Depends on / 依赖: Category, Category.assoc, CommRingCat, CommRingCat.hom_ext, IsLocalization, IsLocalization.ringHom_ext, Spec.structureSheaf, asIdeal, asIdeal.primeCompl, hom_ext, presheaf, presheaf.stalk, primeCompl, ringHom_ext, structureSheaf, toSpec, toStalk_specStalkEquiv, toStalk_stalkMap_toSpec
-/
lemma stalkMap_toSpec (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    (toSpec 𝒜 f).stalkMap x =
      (specStalkEquiv 𝒜 f x f_deg hm).hom ≫ (Proj.stalkIso' 𝒜 x.1).toCommRingCatIso.inv ≫
      ((Proj.toLocallyRingedSpace 𝒜).restrictStalkIso (Opens.isOpenEmbedding _) x).inv := by
refine CommRingCat.hom_ext
    IsLocalization.ringHom_ext (R := A⁰_ f) ((toSpec 𝒜 f).base x).asIdeal.primeCompl
(S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x)) ?_
  ext a
  refine congr($(toStalk_stalkMap_toSpec 𝒜 f x) _).trans ?_
  rw [awayToΓ_ΓToStalk]; rw [← toStalk_specStalkEquiv]; rw [Category.assoc]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `isIso_toSpec` / 引理 `isIso_toSpec`

English:
lemma isIso_toSpec
  given: (f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  proof: by
  have : IsIso (toSpec 𝒜 f).base := toSpec_base_isIso 𝒜 f_deg hm
  have _ (x) : IsIso ((toSpec 𝒜 f).stalkMap x) := by
    rw [stalkMap_toSpec 𝒜 f x f_deg hm]; infer_instance
  have : LocallyRingedSpace.IsOpenImmersion (toSpec 𝒜 f) :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso (toSpec 𝒜 f

中文:
引理 isIso_toSpec
  条件: (f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  证明: by
  have : IsIso (toSpec 𝒜 f).base := toSpec_base_isIso 𝒜 f_deg hm
  have _ (x) : IsIso ((toSpec 𝒜 f).stalkMap x) := by
    rw [stalkMap_toSpec 𝒜 f x f_deg hm]; infer_instance
  have : LocallyRingedSpace.IsOpenImmersion (toSpec 𝒜 f) :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso (toSpec 𝒜 f

Depends on / 依赖: IsOpenImmersion, LocallyRingedSpace, LocallyRingedSpace.IsOpenImmersion, LocallyRingedSpace.IsOpenImmersion.of_stalk_iso, LocallyRingedSpace.IsOpenImmersion.to_iso, TopCat, TopCat.homeoOfIso, f_deg, homeoOfIso, infer_instance, isOpenEmbedding, of_stalk_iso, stalkMap, stalkMap_toSpec, toSpec, toSpec_base_isIso, to_iso
-/
lemma isIso_toSpec (f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    IsIso (toSpec 𝒜 f) := by
  have : IsIso (toSpec 𝒜 f).base := toSpec_base_isIso 𝒜 f_deg hm
  have _ (x) : IsIso ((toSpec 𝒜 f).stalkMap x) := by
    rw [stalkMap_toSpec 𝒜 f x f_deg hm]; infer_instance
  have : LocallyRingedSpace.IsOpenImmersion (toSpec 𝒜 f) :=
    LocallyRingedSpace.IsOpenImmersion.of_stalk_iso (toSpec 𝒜 f)
      (TopCat.homeoOfIso (asIso <| (toSpec 𝒜 f).base)).isOpenEmbedding
  exact LocallyRingedSpace.IsOpenImmersion.to_iso _

end ProjectiveSpectrum.Proj

open ProjectiveSpectrum.Proj in
/--
Definition of `projIsoSpec` / `projIsoSpec` 的定义

English:
definition projIsoSpec
  signature: (f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  body: @asIso _ _ _ _ (f := toSpec 𝒜 f) (isIso_toSpec 𝒜 f f_deg hm)

中文:
定义 projIsoSpec
  签名: (f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
  定义体: @asIso _ _ _ _ (f := toSpec 𝒜 f) (isIso_toSpec 𝒜 f f_deg hm)

Depends on / 依赖: f_deg, isIso_toSpec, toSpec
-/
def projIsoSpec (f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) :
    (Proj| pbo f) ≅ (Spec (A⁰_ f)) :=
  @asIso _ _ _ _ (f := toSpec 𝒜 f) (isIso_toSpec 𝒜 f f_deg hm)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `«Proj»` / `«Proj»` 的定义

English:
definition «Proj»
  signature: : Scheme where
  body: Proj.toLocallyRingedSpace 𝒜
  local_affine (x : Proj.T) := by
    classical
    obtain ⟨f, m, f_deg, hm, hx⟩ : exists (f : A) (m : Nat) (_ : f in 𝒜 m) (_ : 0 < m), f ∉ x.1 := by
      by_contra!
      refine x.not_irrelevant_le fun z hz => ?_
      rw [← DirectSum.sum_support_decompose 𝒜 z]
exact x.

中文:
定义 «Proj»
  签名: : Scheme where
  定义体: Proj.toLocallyRingedSpace 𝒜
  local_affine (x : Proj.T) := by
    classical
    obtain ⟨f, m, f_deg, hm, hx⟩ : exists (f : A) (m : Nat) (_ : f in 𝒜 m) (_ : 0 < m), f ∉ x.1 := by
      by_contra!
      refine x.not_irrelevant_le fun z hz => ?_
      rw [← DirectSum.sum_support_decompose 𝒜 z]
exact x.
-/
def «Proj» : Scheme where
  __ := Proj.toLocallyRingedSpace 𝒜
  local_affine (x : Proj.T) := by
    classical
    obtain ⟨f, m, f_deg, hm, hx⟩ : exists (f : A) (m : Nat) (_ : f in 𝒜 m) (_ : 0 < m), f ∉ x.1 := by
      by_contra!
      refine x.not_irrelevant_le fun z hz => ?_
      rw [← DirectSum.sum_support_decompose 𝒜 z]
exact x.1.toIdeal.sum_mem fun k hk => this _ k (SetLike.coe_mem _) by_contra by aesop
    exact ⟨⟨pbo f, hx⟩, .of (A⁰_ f), ⟨projIsoSpec 𝒜 f f_deg hm⟩⟩


end AlgebraicGeometry
