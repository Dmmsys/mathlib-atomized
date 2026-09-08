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

* `Proj`      : `Proj` as a locally ringed space
* `Proj.T`    : the underlying topological space of `Proj`
* `Proj| U`   : `Proj` restricted to some open set `U`
* `Proj.T| U` : the underlying topological space of `Proj` restricted to open set `U`
* `pbo f`     : basic open set at `f` in `Proj`
* `Spec`      : `Spec` as a locally ringed space
* `Spec.T`    : the underlying topological space of `Spec`
* `sbo g`     : basic open set at `g` in `Spec`
* `A⁰_x`      : the degree zero part of localized ring `Aₓ`

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
variable (𝒜 : ℕ → σ)
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
local notation3 "Proj.T" => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace <| Proj.toLocallyRingedSpace 𝒜

/-- `Proj` restrict to some open set -/
macro "Proj| " U:term : term =>
  `((Proj.toLocallyRingedSpace 𝒜).restrict
    (Opens.isOpenEmbedding (X := Proj.T) ($U : Opens Proj.T)))

/-- the underlying topological space of `Proj` restricted to some open set -/
local notation "Proj.T| " U => PresheafedSpace.carrier <| SheafedSpace.toPresheafedSpace
  <| LocallyRingedSpace.toSheafedSpace
    <| (LocallyRingedSpace.restrict Proj (Opens.isOpenEmbedding (X := Proj.T) (U : Opens Proj.T)))

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
variable {f : A} {m : ℕ} (x : Proj| (pbo f))

/--
For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fact that this ideal
is prime is proven in `TopComponent.Forward.toFun`. -/
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec`。
形式化陈述：carrier : Ideal (A⁰_ f)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `x` in `Proj| (pbo f)`, the corresponding ideal in `Spec A⁰_f`. This fac
t that this ideal
is prime is proven in `TopComponent.Forward.toFun`.
-/
def carrier : Ideal (A⁰_ f) :=
  Ideal.comap (algebraMap (A⁰_ f) (Away f))
    (x.val.asHomogeneousIdeal.toIdeal.map (algebraMap A (Away f)))

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier** 是 Mathlib 中的
一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec`。
形式化陈述：mk_mem_carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
 HomogeneousLocalization.mk z in carrier x ↔ z.num.1 in x.1.asHomogeneousIdeal
参数：z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.carrier.eq_1`：∀ {A : Ty
pe u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddS
ubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `Ideal.mem_comap`：mem_comap [RingHomClass F R S] {x} : x in comap f K ↔ f
 x in K
· 使用定理 `HomogeneousLocalization.algebraMap_apply`：∀ {ι : Type u_1} {A : Type u_2
} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgr
oupClass σ A] [inst_3 : AddCom…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.mk'_eq_mul_mk'_one`：∀ {R : Type u_1} [inst : CommSemiring
 R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algeb
ra R S] [inst_3 : IsLoc…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Ideal.unit_mul_mem_iff_mem`：unit_mul_mem_iff_mem {x y : α} (hy : IsUnit 
y) : y * x in I ↔ x in I
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mem_under`：mem_under {x : A} : x in P.under A ↔ algebraMap A B x i
n P
· 使用定理 `IsLocalization.under_map_of_isPrime_disjoint`：under_map_of_isPrime_disjo
int {I : Ideal R} (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) : (Ideal.map (a
lgebraMap R S) I).under R = I
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.disjoint_powers_iff_notMem_of_isPrime`：disjoint_powers_iff_notMem_
of_isPrime [I.IsPrime] (y : R) : Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ 
I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_mem_carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ carrier x ↔ z.num.1 ∈ x.1.asHomogeneousIdeal := by
  rw [carrier, Ideal.mem_comap, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one,
    mul_comm, Ideal.unit_mul_mem_iff_mem, ← Ideal.mem_under,
    IsLocalization.under_map_of_isPrime_disjoint (.powers f)]
  · rfl
  · infer_instance
  · exact (disjoint_powers_iff_notMem_of_isPrime _).mpr x.2
  · exact isUnit_of_invertible _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.isPrime_carrier** 是 Mathlib 中
的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec`。
形式化陈述：isPrime_carrier : Ideal.IsPrime (carrier x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `IsLocalization.isPrime_of_isPrime_disjoint`：isPrime_of_isPrime_disjoint 
(I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) : (Ideal.map (alge
braMap R S) I).IsPrime
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.disjoint_powers_iff_notMem_of_isPrime`：disjoint_powers_iff_notMem_
of_isPrime [I.IsPrime] (y : R) : Disjoint (Submonoid.powers y : Set R) ↑I ↔ y ∉ 
I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
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
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.toFun** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec`。
形式化陈述：toFun (x : Proj.T| pbo f) : Spec.T A⁰_ f
参数：x : Proj.T| pbo f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.isPrime_carrier`：isPrim
e_carrier : Ideal.IsPrime (carrier x)

--- 原说明 ---
The function between the basic open set `D(f)` in `Proj` to the corresponding ba
sic open set in
`Spec A⁰_f`. This is bundled into a continuous map in `TopComponent.forward`.
-/
def toFun (x : Proj.T| pbo f) : Spec.T A⁰_ f :=
  ⟨carrier x, isPrime_carrier x⟩

/-
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map from `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in `Proj A`. This lemma is used to prove that the
forward map is continuous.
-/
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec`。
形式化陈述：preimage_basicOpen (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f
)) : toFun f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeSpectrum (A⁰_ f
))) = Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜))
参数：z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier`：mk_mem_
carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) : HomogeneousL
ocalization.mk z in carrier x ↔ z.num.1 in x.1.asHomo…

--- 原说明 ---
The preimage of basic open set `D(a/f^n)` in `Spec A⁰_f` under the forward map f
rom `Proj A` to
`Spec A⁰_f` is the basic open set `D(a) ∩ D(f)` in `Proj A`. This lemma is used 
to prove that the
forward map is continuous.
-/
theorem preimage_basicOpen (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    toFun f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeSpectrum (A⁰_ f))) =
      Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜)) :=
  Set.ext fun y ↦ (mk_mem_carrier y z).not

end ToSpec

section

set_option backward.isDefEq.respectTransparency false in
/-- The continuous function from the basic open set `D(f)` in `Proj`
to the corresponding basic open set in `Spec A⁰_f`. -/
@[simps! -isSimp hom_apply_asIdeal]
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.ProjIsoSpecTopComponent`。
形式化陈述：toSpec (f : A) : (Proj.T| pbo f) ⟶ Spec.T A⁰_ f
参数：f : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous function from the basic open set `D(f)` in `Proj`
to the corresponding basic open set in `Spec A⁰_f`.
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
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_preimage_basicOpen** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent`。
形式化陈述：toSpec_preimage_basicOpen {f} (z : HomogeneousLocalization.NumDenSameDeg 𝒜
 (.powers f)) : toSpec 𝒜 f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeS
pectrum (A⁰_ f))) = Subtype.val ⁻¹' (pbo z.num.1 : Set (ProjectiveSpectrum 𝒜))
参数：z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen`：pre
image_basicOpen (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) : toFu
n f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeS…
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
variable {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)

open Lean Meta Elab Tactic

/-- `mem_tac` tries to prove goals of the form `x ∈ 𝒜 i` when `x` has the form of:
* `y ^ n` where `i = n • j` and `y ∈ 𝒜 j`.
* a natural number `n`.
-/
macro "mem_tac" : tactic =>
  `(tactic| first | exact pow_mem_graded _ (SetLike.coe_mem _) | exact natCast_mem_graded _ _ |
    exact pow_mem_graded _ f_deg)

/-- The function from `Spec A⁰_f` to `Proj|D(f)` is defined by `q ↦ {a | aᵢᵐ/fⁱ ∈ q}`, i.e. sending
`q` a prime ideal in `A⁰_f` to the homogeneous prime relevant ideal containing only and all the
elements `a : A` such that for every `i`, the degree 0 element formed by dividing the `m`-th power
of the `i`-th projection of `a` by the `i`-th power of the degree-`m` homogeneous element `f`,
lies in `q`.

The set `{a | aᵢᵐ/fⁱ ∈ q}`
* is an ideal, as proved in `carrier.asIdeal`;
* is homogeneous, as proved in `carrier.asHomogeneousIdeal`;
* is prime, as proved in `carrier.asIdeal.prime`;
* is relevant, as proved in `carrier.relevant`.
-/
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier** 是 Mathlib 中的一个定义，
位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec`。
形式化陈述：carrier (f_deg : f in 𝒜 m) (q : Spec.T A⁰_ f) : Set A
参数：f_deg : f in 𝒜 m；q : Spec.T A⁰_ f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function from `Spec A⁰_f` to `Proj|D(f)` is defined by `q ↦ {a | aᵢᵐ/fⁱ ∈ q}
`, i.e. sending
`q` a prime ideal in `A⁰_f` to the homogeneous prime relevant ideal containing o
nly and all the
elements `a : A` such that for every `i`, the degree 0 element formed by dividin
g the `m`-th power
of the `i`-th projection of `a` by the `i`-th power of the degree-`m` homogeneou
s element `f`,
lies in `q`.

The set `{a | aᵢᵐ/fⁱ ∈ q}`
* is an ideal, as proved in `carrier.asIdeal`;
* is homogeneous, as proved in `carrier.asHomogeneousIdeal`;
* is prime, as proved in `carrier.asIdeal.prime`;
* is relevant, as proved in `carrier.relevant`.
-/
def carrier (f_deg : f ∈ 𝒜 m) (q : Spec.T A⁰_ f) : Set A :=
  {a | ∀ i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
              ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.1}
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec`。
形式化陈述：mem_carrier_iff (q : Spec.T A⁰_ f) (a : A) : a in carrier f_deg q ↔ forall
 i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← smul_eq_mul]; 
mem_tac⟩, ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.1
参数：q : Spec.T A⁰_ f；a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_carrier_iff (q : Spec.T A⁰_ f) (a : A) :
    a ∈ carrier f_deg q ↔ ∀ i, (HomogeneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by
      rw [← smul_eq_mul]; mem_tac⟩,
      ⟨f ^ i, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.1 :=
  Iff.rfl
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff'** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec`。
形式化陈述：mem_carrier_iff' (q : Spec.T A⁰_ f) (a : A) : a in carrier f_deg q ↔ foral
l i, (Localization.mk (proj 𝒜 i a ^ m) ⟨f ^ i, ⟨i, rfl⟩⟩ : Localization.Away f) 
in algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) '' { s | 
s in q.1 }
参数：q : Spec.T A⁰_ f；a : A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff`：mem_
carrier_iff (q : Spec.T A⁰_ f) (a : A) : a in carrier f_deg q ↔ forall i, (Homog
eneousLocalization.mk ⟨m * i, ⟨proj 𝒜 i a ^ m, by rw [← …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.ext_iff_val`：ext_iff_val (f g : HomogeneousLocal
ization 𝒜 x) : f = g ↔ f.val = g.val
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
-/
theorem mem_carrier_iff' (q : Spec.T A⁰_ f) (a : A) :
    a ∈ carrier f_deg q ↔
      ∀ i, (Localization.mk (proj 𝒜 i a ^ m) ⟨f ^ i, ⟨i, rfl⟩⟩ : Localization.Away f) ∈
          algebraMap (HomogeneousLocalization.Away 𝒜 f) (Localization.Away f) '' { s | s ∈ q.1 } :=
  (mem_carrier_iff f_deg q a).trans
    (by
      constructor <;> intro h i <;> specialize h i
      · rw [Set.mem_image]; refine ⟨_, h, rfl⟩
      · rw [Set.mem_image] at h; rcases h with ⟨x, h, hx⟩
        change x ∈ q.asIdeal at h
        convert! h
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk]
        dsimp only [Subtype.coe_mk]; rw [← hx]; rfl)
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff_of_mem** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec`。
形式化陈述：mem_carrier_iff_of_mem (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a
 in 𝒜 n) : a in carrier f_deg q ↔ (HomogeneousLocalization.mk ⟨m * n, ⟨a ^ m, po
w_mem_graded m hn⟩, ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) in q.
asIdeal
参数：hm : 0 < m；q : Spec.T A⁰_ f；a : A；hn : a in 𝒜 n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.decompose_of_mem_ne`：decompose_of_mem_ne {x : M} {i j : ι} (hx
 : x in ℳ i) (hij : i != j) : (decompose ℳ x j : M) = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Localization.mk_zero`：mk_zero (x : S) : mk 0 (x : S) = 0
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_zero`：val_zero : (0 : HomogeneousLocalizatio
n 𝒜 x).val = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `DirectSum.decompose_of_mem_same`：decompose_of_mem_same {x : M} {i : ι} (
hx : x in ℳ i) : (decompose ℳ x i : M) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_carrier_iff_of_mem (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a ∈ 𝒜 n) :
    a ∈ carrier f_deg q ↔
      (HomogeneousLocalization.mk ⟨m * n, ⟨a ^ m, pow_mem_graded m hn⟩,
        ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal := by
  trans (HomogeneousLocalization.mk ⟨m * n, ⟨proj 𝒜 n a ^ m, by rw [← smul_eq_mul]; mem_tac⟩,
    ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal
  · refine ⟨fun h ↦ h n, fun h i ↦ if hi : i = n then hi ▸ h else ?_⟩
    convert! zero_mem q.asIdeal
    apply HomogeneousLocalization.val_injective
    simp only [proj_apply, decompose_of_mem_ne _ hn (Ne.symm hi), zero_pow hm.ne',
      HomogeneousLocalization.val_mk, Localization.mk_zero, HomogeneousLocalization.val_zero]
  · simp only [proj_apply, decompose_of_mem_same _ hn]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff_of_mem_mul*
* 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec`。
形式化陈述：mem_carrier_iff_of_mem_mul (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn
 : a in 𝒜 (n * m)) : a in carrier f_deg q ↔ (HomogeneousLocalization.mk ⟨m * n, 
⟨a, mul_comm n m ▸ hn⟩, ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) i
n q.asIdeal
参数：hm : 0 < m；q : Spec.T A⁰_ f；a : A；hn : a in 𝒜 (n * m)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff_of_me
m`：mem_carrier_iff_of_mem (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a in
 𝒜 n) : a in carrier f_deg q ↔ (HomogeneousLocalization.mk ⟨m *…
· 使用定理 `iff_iff_eq`：∀ {a b : Prop}, (a ↔ b) ↔ a = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.IsPrime.pow_mem_iff_mem`：∀ {α : Type u} [inst : Semiring α] {I : I
deal α}, I.IsPrime → ∀ {r : α} (n : ℕ), 0 < n → (r ^ n ∈ I ↔ r ∈ I)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HomogeneousLocalization.val_pow`：val_pow : forall (y : HomogeneousLocali
zation 𝒜 x) (n : Nat), (y ^ n).val = y.val ^ n
· 使用定理 `Localization.mk_pow`：mk_pow (n : Nat) (a : M) (b : S) : mk a b ^ n = mk 
(a ^ n) (b ^ n)
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
-/
theorem mem_carrier_iff_of_mem_mul (hm : 0 < m)
    (q : Spec.T A⁰_ f) (a : A) {n} (hn : a ∈ 𝒜 (n * m)) :
    a ∈ carrier f_deg q ↔ (HomogeneousLocalization.mk ⟨m * n, ⟨a, mul_comm n m ▸ hn⟩,
        ⟨f ^ n, by rw [mul_comm]; mem_tac⟩, ⟨_, rfl⟩⟩ : A⁰_ f) ∈ q.asIdeal := by
  rw [mem_carrier_iff_of_mem f_deg hm q a hn, iff_iff_eq, eq_comm,
    ← Ideal.IsPrime.pow_mem_iff_mem (α := A⁰_ f) inferInstance m hm]
  congr 1
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_pow,
    Localization.mk_pow, pow_mul]
  rfl
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.num_mem_carrier_iff** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec`。
形式化陈述：num_mem_carrier_iff (hm : 0 < m) (q : Spec.T A⁰_ f) (z : HomogeneousLocali
zation.NumDenSameDeg 𝒜 (.powers f)) : z.num.1 in carrier f_deg q ↔ HomogeneousLo
calization.mk z in q.asIdeal
参数：hm : 0 < m；q : Spec.T A⁰_ f；z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.pow
ers f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用引理 `HomogeneousLocalization.subsingleton`：subsingleton (hx : 0 in x) : Subsi
ngleton (HomogeneousLocalization 𝒜 x)
· 使用定理 `DirectSum.degree_eq_of_mem_mem`：degree_eq_of_mem_mem {x : M} {i j : ι} (
hxi : x in ℳ i) (hxj : x in ℳ j) (hx : x != 0) : i = j
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff_of_me
m_mul`：mem_carrier_iff_of_mem_mul (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (h
n : a in 𝒜 (n * m)) : a in carrier f_deg q ↔ (HomogeneousLocalizati…
-/
theorem num_mem_carrier_iff (hm : 0 < m) (q : Spec.T A⁰_ f)
    (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) :
    z.num.1 ∈ carrier f_deg q ↔ HomogeneousLocalization.mk z ∈ q.asIdeal := by
  obtain ⟨n, hn : f ^ n = _⟩ := z.den_mem
  have : f ^ n ≠ 0 := fun e ↦ by
    have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, e⟩
    exact IsEmpty.elim (inferInstanceAs (IsEmpty (PrimeSpectrum (A⁰_ f)))) q
  convert! mem_carrier_iff_of_mem_mul f_deg hm q z.num.1 (n := n) ?_ using 2
  · apply HomogeneousLocalization.val_injective; simp only [hn, HomogeneousLocalization.val_mk]
  · have := degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded n f_deg) (hn.symm ▸ z.den.2) this
    rw [← smul_eq_mul, this]; exact z.num.2
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.add_mem** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
m : ℕ} (f_deg : f ∈ 𝒜 m)   (q :     ↑↑(AlgebraicGeometry.Spec.locallyRingedSpace
Obj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPresheafe
dSpace)   {a b : A},   a ∈ AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.ca
rrier f_deg q →     b ∈ AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carri
er f_deg q →       a + b ∈ AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.ca
rrier f_deg q
参数：f_deg : f ∈ 𝒜 m；q :     ↑↑(AlgebraicGeometry.Spec.locallyRingedSpaceObj      
       (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPresheafedSpace。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `add_pow`：add_pow [CommSemiring R] (x y : R) (n : Nat) : (x + y) ^ n = ∑ 
m in range (n + 1), x ^ m * y ^ (n - m) * n.choose m
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `SetLike.GradedMul.mul_mem`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3
} {inst : SetLike S R} {inst_1 : Mul R} {inst_2 : Add ι} {A : ι → S}   [self : S
etLike.GradedMu…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `HomogeneousLocalization.ext_iff_val`：ext_iff_val (f g : HomogeneousLocal
ization 𝒜 x) : f = g ↔ f.val = g.val
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Localization.mk_sum`：mk_sum {ι : Type*} (f : ι -> R) (s : Finset ι) (b :
 M) : mk (∑ i in s, f i) b = ∑ i in s, mk (f i) b
（共 52 条，此处仅展示前 30 条）
-/
theorem carrier.add_mem (q : Spec.T A⁰_ f) {a b : A} (ha : a ∈ carrier f_deg q)
    (hb : b ∈ carrier f_deg q) : a + b ∈ carrier f_deg q := by
  refine fun i => (q.2.mem_or_mem ?_).elim id id
  change (HomogeneousLocalization.mk ⟨_, _, _, _⟩ : A⁰_ f) ∈ q.1; dsimp only [Subtype.coe_mk]
  simp_rw [← pow_add, map_add, add_pow, mul_comm, ← nsmul_eq_mul]
  let g : ℕ → A⁰_ f := fun j => (m + m).choose j •
      if h2 : m + m < j then (0 : A⁰_ f)
      else
        if h1 : j ≤ m then
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
    rw [← add_smul, Nat.add_sub_of_le h1]; rfl
  · rw [(_ : m * i = _)]
    apply GradedMonoid.toGradedMul.mul_mem (i := (j - m) • i) (j := (m + m - j) • i) <;> mem_tac
    rw [← add_smul]; congr; lia
  convert_to ∑ i ∈ range (m + m + 1), g i ∈ q.1; swap
  · refine q.1.sum_mem fun j _ => nsmul_mem ?_ _; split_ifs
    exacts [q.1.zero_mem, q.1.mul_mem_left _ (hb i), q.1.mul_mem_right _ (ha i)]
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk]
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
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.zero_mem** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
m : ℕ} (f_deg : f ∈ 𝒜 m),   0 < m →     ∀       (q :         ↑↑(AlgebraicGeometr
y.Spec.locallyRingedSpaceObj                 (CommRingCat.of (HomogeneousLocaliz
ation.Away 𝒜 f))).toPresheafedSpace),       0 ∈ AlgebraicGeometry.ProjIsoSpecTop
Component.FromSpec.carrier f_deg q
参数：f_deg : f ∈ 𝒜 m；q :         ↑↑(AlgebraicGeometry.Spec.locallyRingedSpaceObj  
               (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPresheafed
Space。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.ext_iff_val`：ext_iff_val (f g : HomogeneousLocal
ization 𝒜 x) : f = g ↔ f.val = g.val
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `HomogeneousLocalization.val_zero`：val_zero : (0 : HomogeneousLocalizatio
n 𝒜 x).val = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Localization.mk_zero`：mk_zero (x : S) : mk 0 (x : S) = 0
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
theorem carrier.zero_mem : (0 : A) ∈ carrier f_deg q := fun i => by
  convert Submodule.zero_mem q.1
  rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_zero]; simp_rw [map_zero, zero_pow hm.ne']
  exact Localization.mk_zero (S := Submonoid.powers f) _
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.smul_mem** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
m : ℕ} (f_deg : f ∈ 𝒜 m),   0 < m →     ∀       (q :         ↑↑(AlgebraicGeometr
y.Spec.locallyRingedSpaceObj                 (CommRingCat.of (HomogeneousLocaliz
ation.Away 𝒜 f))).toPresheafedSpace)       (c x : A),       x ∈ AlgebraicGeometr
y.ProjIsoSpecTopComponent.FromSpec.carrier f_deg q →         c • x ∈ AlgebraicGe
ometry.ProjIsoSpecTopComponent.FromSpec.carrier f_deg q
参数：f_deg : f ∈ 𝒜 m；q :         ↑↑(AlgebraicGeometry.Spec.locallyRingedSpaceObj  
               (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPresheafed
Space；c x : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `DirectSum.Decomposition.inductionOn`：∀ {ι : Type u_1} {M : Type u_3} {σ 
: Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [inst_2 : SetLike 
σ M]   [inst_3 : AddSubmo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.zero_mem`：∀ {
A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 
: AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DirectSum.coe_decompose_mul_of_left_mem`：coe_decompose_mul_of_left_mem (
n) [Decidable (i <= n)] (a_mem : a in 𝒜 i) : (decompose 𝒜 (a * b) n : A) = if i 
<= n then a * decompose 𝒜 b (…
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.ext_iff_val`：ext_iff_val (f g : HomogeneousLocal
ization 𝒜 x) : f = g ↔ f.val = g.val
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `HomogeneousLocalization.val_mul`：val_mul : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 * y2).val = y1.val * y2.val
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `Localization.mk_mul`：mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (
a * c) (b * d)
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
（共 42 条，此处仅展示前 30 条）
-/
theorem carrier.smul_mem (c x : A) (hx : x ∈ carrier f_deg q) : c • x ∈ carrier f_deg q := by
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
      · convert_to product ∈ q.1
        · dsimp [product]
          rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
            HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk,
            HomogeneousLocalization.val_mk]
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

/-- For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as an ideal.
-/
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal** 是 Mathlib
 中的一个定义，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier`。
形式化陈述：{A : Type u_1} →   {σ : Type u_2} →     [inst : CommRing A] →       [inst_
1 : SetLike σ A] →         [inst_2 : AddSubgroupClass σ A] →           {𝒜 : ℕ → 
σ} →             [inst_3 : GradedRing 𝒜] →               {f : A} →              
   {m : ℕ} →                   f ∈ 𝒜 m →                     0 < m →            
           ↑↑(AlgebraicGeometry.Spec.locallyRingedSpaceObj                      
           (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPresheafedSpac
e →                         Ideal A
参数：AlgebraicGeometry.Spec.locallyRingedSpaceObj                                 
(CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.add_mem`：∀ {A
 : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 :
 AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.zero_mem`：∀ {
A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 
: AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.smul_mem`：∀ {
A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 
: AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…

--- 原说明 ---
For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as an ideal.
-/
def carrier.asIdeal : Ideal A where
  carrier := carrier f_deg q
  zero_mem' := carrier.zero_mem f_deg hm q
  add_mem' := carrier.add_mem f_deg q
  smul_mem' := carrier.smul_mem f_deg hm q
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.homogeneous
** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.c
arrier.asIdeal`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)   (q :     ↑↑(AlgebraicGeometry.Spec.local
lyRingedSpaceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))
).toPresheafedSpace),   Ideal.IsHomogeneous 𝒜 (AlgebraicGeometry.ProjIsoSpecTopC
omponent.FromSpec.carrier.asIdeal f_deg hm q)
参数：f_deg : f ∈ 𝒜 m；hm : 0 < m；q :     ↑↑(AlgebraicGeometry.Spec.locallyRingedSpa
ceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPreshea
fedSpace；AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal f_de
g hm q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `DirectSum.decompose_of_mem_ne`：decompose_of_mem_ne {x : M} {i j : ι} (hx
 : x in ℳ i) (hij : i != j) : (decompose ℳ x j : M) = 0
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.zero_mem`：∀ {
A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 
: AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
-/
theorem carrier.asIdeal.homogeneous : (carrier.asIdeal f_deg hm q).IsHomogeneous 𝒜 :=
  fun i a ha j =>
  (em (i = j)).elim (fun h => h ▸ by simpa only [proj_apply, decompose_coe, of_eq_same] using ha _)
    fun h => by
    simpa only [proj_apply, decompose_of_mem_ne 𝒜 (SetLike.coe_mem (decompose 𝒜 a i)) h,
      zero_pow hm.ne', map_zero] using carrier.zero_mem f_deg hm q j

/-- For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as a homogeneous ideal.
-/
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asHomogeneousIdeal*
* 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.ca
rrier`。
形式化陈述：{A : Type u_1} →   {σ : Type u_2} →     [inst : CommRing A] →       [inst_
1 : SetLike σ A] →         [inst_2 : AddSubgroupClass σ A] →           {𝒜 : ℕ → 
σ} →             [inst_3 : GradedRing 𝒜] →               {f : A} →              
   {m : ℕ} →                   f ∈ 𝒜 m →                     0 < m →            
           ↑↑(AlgebraicGeometry.Spec.locallyRingedSpaceObj                      
           (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPresheafedSpac
e →                         HomogeneousIdeal 𝒜
参数：AlgebraicGeometry.Spec.locallyRingedSpaceObj                                 
(CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.homog
eneous`：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ 
A] [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…

--- 原说明 ---
For a prime ideal `q` in `A⁰_f`, the set `{a | aᵢᵐ/fⁱ ∈ q}` as a homogeneous ide
al.
-/
def carrier.asHomogeneousIdeal : HomogeneousIdeal 𝒜 :=
  ⟨carrier.asIdeal f_deg hm q, carrier.asIdeal.homogeneous f_deg hm q⟩
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.denom_notMem** 是 Ma
thlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier`
。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)   (q :     ↑↑(AlgebraicGeometry.Spec.local
lyRingedSpaceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))
).toPresheafedSpace),   f ∉ AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.c
arrier.asIdeal f_deg hm q
参数：f_deg : f ∈ 𝒜 m；hm : 0 < m；q :     ↑↑(AlgebraicGeometry.Spec.locallyRingedSpa
ceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPreshea
fedSpace。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.ext_iff_val`：ext_iff_val (f g : HomogeneousLocal
ization 𝒜 x) : f = g ↔ f.val = g.val
· 使用定理 `HomogeneousLocalization.val_one`：val_one : (1 : HomogeneousLocalization 
𝒜 x).val = 1
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.decompose_of_mem_same`：decompose_of_mem_same {x : M} {i : ι} (
hx : x in ℳ i) : (decompose ℳ x i : M) = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Localization.mk_self_mk`：mk_self_mk (a : M) (haS : a in S) : mk a ⟨a, ha
S⟩ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem carrier.denom_notMem : f ∉ carrier.asIdeal f_deg hm q := fun rid =>
  q.isPrime.ne_top <|
    (Ideal.eq_top_iff_one _).mpr
      (by
        convert rid m
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_one,
          HomogeneousLocalization.val_mk]
        dsimp
        simp_rw [decompose_of_mem_same _ f_deg]
        simp)
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.relevant** 是 Mathli
b 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)   (q :     ↑↑(AlgebraicGeometry.Spec.local
lyRingedSpaceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))
).toPresheafedSpace),   ¬HomogeneousIdeal.irrelevant 𝒜 ≤       AlgebraicGeometry
.ProjIsoSpecTopComponent.FromSpec.carrier.asHomogeneousIdeal f_deg hm q
参数：f_deg : f ∈ 𝒜 m；hm : 0 < m；q :     ↑↑(AlgebraicGeometry.Spec.locallyRingedSpa
ceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPreshea
fedSpace。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.denom_notMem`
：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [ins
t_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `DirectSum.decompose_of_mem_ne`：decompose_of_mem_ne {x : M} {i j : ι} (hx
 : x in ℳ i) (hij : i != j) : (decompose ℳ x j : M) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem carrier.relevant : ¬HomogeneousIdeal.irrelevant 𝒜 ≤ carrier.asHomogeneousIdeal f_deg hm q :=
  fun rid => carrier.denom_notMem f_deg hm q <| rid <| DirectSum.decompose_of_mem_ne 𝒜 f_deg hm.ne'
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.ne_top** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrie
r.asIdeal`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)   (q :     ↑↑(AlgebraicGeometry.Spec.local
lyRingedSpaceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))
).toPresheafedSpace),   AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carri
er.asIdeal f_deg hm q ≠ ⊤
参数：f_deg : f ∈ 𝒜 m；hm : 0 < m；q :     ↑↑(AlgebraicGeometry.Spec.locallyRingedSpa
ceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPreshea
fedSpace。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.denom_notMem`
：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [ins
t_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem carrier.asIdeal.ne_top : carrier.asIdeal f_deg hm q ≠ ⊤ := fun rid =>
  carrier.denom_notMem f_deg hm q (rid.symm ▸ Submodule.mem_top)
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime** 是 M
athlib 中的一个定理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier
.asIdeal`。
形式化陈述：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A]
 [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] {f : A} {
m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)   (q :     ↑↑(AlgebraicGeometry.Spec.local
lyRingedSpaceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))
).toPresheafedSpace),   (AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carr
ier.asIdeal f_deg hm q).IsPrime
参数：f_deg : f ∈ 𝒜 m；hm : 0 < m；q :     ↑↑(AlgebraicGeometry.Spec.locallyRingedSpa
ceObj             (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).toPreshea
fedSpace；AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal f_de
g hm q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem`：Ideal.IsHomogeneo
us.isPrime_of_homogeneous_mem_or_mem {I : Ideal A} (hI : I.IsHomogeneous 𝒜) (I_n
e_top : I != ⊤) (homogeneous_mem_or_mem : f…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.homog
eneous`：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ 
A] [inst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.ne_to
p`：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [i
nst_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_forall_ne`：and_forall_ne (a : α) : (p a ∧ forall b, b != a -> p b) ↔
 forall b, p b
· 使用定理 `and_iff_left`：∀ {b a : Prop}, b → (a ∧ b ↔ a)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `HomogeneousLocalization.ext_iff_val`：ext_iff_val (f g : HomogeneousLocal
ization 𝒜 x) : f = g ↔ f.val = g.val
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用定理 `HomogeneousLocalization.val_zero`：val_zero : (0 : HomogeneousLocalizatio
n 𝒜 x).val = 0
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `DirectSum.decompose_of_mem_ne`：decompose_of_mem_ne {x : M} {i j : ι} (hx
 : x in ℳ i) (hij : i != j) : (decompose ℳ x j : M) = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Localization.mk_zero`：mk_zero (x : S) : mk 0 (x : S) = 0
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.decompose_of_mem_same`：decompose_of_mem_same {x : M} {i : ι} (
hx : x in ℳ i) : (decompose ℳ x i : M) = x
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `SetLike.GradedMul.mul_mem`：∀ {ι : Type u_1} {R : Type u_2} {S : Type u_3
} {inst : SetLike S R} {inst_1 : Mul R} {inst_2 : Add ι} {A : ι → S}   [self : S
etLike.GradedMu…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
（共 39 条，此处仅展示前 30 条）
-/
theorem carrier.asIdeal.prime : (carrier.asIdeal f_deg hm q).IsPrime :=
  (carrier.asIdeal.homogeneous f_deg hm q).isPrime_of_homogeneous_mem_or_mem
    (carrier.asIdeal.ne_top f_deg hm q) fun {x y} ⟨nx, hnx⟩ ⟨ny, hny⟩ hxy =>
    show (∀ _, _ ∈ _) ∨ ∀ _, _ ∈ _ by
      rw [← and_forall_ne nx, and_iff_left, ← and_forall_ne ny, and_iff_left]
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
        rw [HomogeneousLocalization.ext_iff_val, HomogeneousLocalization.val_mk,
          HomogeneousLocalization.val_zero]; simp_rw [proj_apply]
        convert! mk_zero (S := Submonoid.powers f) _
        rw [decompose_of_mem_ne 𝒜 _ hn.symm, zero_pow hm.ne']
        · first | exact hnx | exact hny

/-- The function `Spec A⁰_f → Proj|D(f)` sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`. -/
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.toFun** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec`。
形式化陈述：toFun : (Spec.T A⁰_ f) -> Proj.T| pbo f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.asIdeal.prime
`：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [in
st_2 : AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.carrier.relevant`：∀ {
A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 
: AddSubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRin…

--- 原说明 ---
The function `Spec A⁰_f → Proj|D(f)` sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
-/
def toFun : (Spec.T A⁰_ f) → Proj.T| pbo f := fun q =>
  ⟨⟨carrier.asHomogeneousIdeal f_deg hm q, carrier.asIdeal.prime f_deg hm q,
      carrier.relevant f_deg hm q⟩,
    (ProjectiveSpectrum.mem_basicOpen _ f _).mp <| carrier.denom_notMem f_deg hm q⟩

end FromSpec

section toSpecFromSpec

/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_fromSpec** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent`。
形式化陈述：toSpec_fromSpec {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Spe
c.T (A⁰_ f)) : toSpec 𝒜 f (FromSpec.toFun f_deg hm x) = x
参数：f_deg : f in 𝒜 m；hm : 0 < m；x : Spec.T (A⁰_ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.num_mem_carrier_iff`：
num_mem_carrier_iff (hm : 0 < m) (q : Spec.T A⁰_ f) (z : HomogeneousLocalization
.NumDenSameDeg 𝒜 (.powers f)) : z.num.1 in carrier f_deg q ↔…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier`：mk_mem_
carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) : HomogeneousL
ocalization.mk z in carrier x ↔ z.num.1 in x.1.asHomo…
-/
lemma toSpec_fromSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (x : Spec.T (A⁰_ f)) :
    toSpec 𝒜 f (FromSpec.toFun f_deg hm x) = x := by
  apply PrimeSpectrum.ext
  ext z
  obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [← FromSpec.num_mem_carrier_iff f_deg hm x]
  exact ToSpec.mk_mem_carrier _ z


end toSpecFromSpec

section fromSpecToSpec

/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.fromSpec_toSpec** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent`。
形式化陈述：fromSpec_toSpec {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Pro
j.T| pbo f) : FromSpec.toFun f_deg hm (toSpec 𝒜 f x) = x
参数：f_deg : f in 𝒜 m；hm : 0 < m；x : Proj.T| pbo f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `ProjectiveSpectrum.ext`：∀ {A : Type u_1} {σ : Type u_2} {inst : CommRing
 A} {inst_1 : SetLike σ A} {inst_2 : AddSubmonoidClass σ A} {𝒜 : ℕ → σ}   {inst_
3 : GradedRi…
· 使用定理 `HomogeneousIdeal.ext'`：HomogeneousIdeal.ext' {I J : HomogeneousIdeal 𝒜} 
(h : forall i, forall x in 𝒜 i, x in I ↔ x in J) : I = J
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.FromSpec.mem_carrier_iff_of_me
m`：mem_carrier_iff_of_mem (hm : 0 < m) (q : Spec.T A⁰_ f) (a : A) {n} (hn : a in
 𝒜 n) : a in carrier f_deg q ↔ (HomogeneousLocalization.mk ⟨m *…
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier`：mk_mem_
carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) : HomogeneousL
ocalization.mk z in carrier x ↔ z.num.1 in x.1.asHomo…
· 使用定理 `Ideal.IsPrime.pow_mem_iff_mem`：∀ {α : Type u} [inst : Semiring α] {I : I
deal α}, I.IsPrime → ∀ {r : α} (n : ℕ), 0 < n → (r ^ n ∈ I ↔ r ∈ I)
· 使用定理 `ProjectiveSpectrum.isPrime`：∀ {A : Type u_1} {σ : Type u_2} [inst : Comm
Ring A] [inst_1 : SetLike σ A] [inst_2 : AddSubmonoidClass σ A] {𝒜 : ℕ → σ}   [i
nst_3 : GradedRi…
-/
lemma fromSpec_toSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (x : Proj.T| pbo f) :
    FromSpec.toFun f_deg hm (toSpec 𝒜 f x) = x := by
  refine Subtype.ext <| ProjectiveSpectrum.ext <| HomogeneousIdeal.ext' ?_
  intro i z hzi
  refine (FromSpec.mem_carrier_iff_of_mem f_deg hm _ _ hzi).trans ?_
  exact (ToSpec.mk_mem_carrier _ _).trans (x.1.2.pow_mem_iff_mem m hm)
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_injective** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent`。
形式化陈述：toSpec_injective {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) : Funct
ion.Injective (toSpec 𝒜 f)
参数：f_deg : f in 𝒜 m；hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.ProjIsoSpecTopComponent.fromSpec_toSpec`：fromSpec_toSp
ec {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Proj.T| pbo f) : FromS
pec.toFun f_deg hm (toSpec 𝒜 f x) = x
-/
lemma toSpec_injective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Injective (toSpec 𝒜 f) := by
  intro x₁ x₂ h
  have := congr_arg (FromSpec.toFun f_deg hm) h
  rwa [fromSpec_toSpec, fromSpec_toSpec] at this
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_surjective** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent`。
形式化陈述：toSpec_surjective {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) : Func
tion.Surjective (toSpec 𝒜 f)
参数：f_deg : f in 𝒜 m；hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Function.surjective_iff_hasRightInverse`：surjective_iff_hasRightInverse 
: Surjective f ↔ HasRightInverse f
· 使用引理 `AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_fromSpec`：toSpec_fromSp
ec {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) (x : Spec.T (A⁰_ f)) : toSp
ec 𝒜 f (FromSpec.toFun f_deg hm x) = x
-/
lemma toSpec_surjective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Surjective (toSpec 𝒜 f) :=
  Function.surjective_iff_hasRightInverse |>.mpr
    ⟨FromSpec.toFun f_deg hm, toSpec_fromSpec 𝒜 f_deg hm⟩
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_bijective** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent`。
形式化陈述：toSpec_bijective {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) : Funct
ion.Bijective (toSpec (𝒜
参数：f_deg : f in 𝒜 m；hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用引理 `AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_injective`：toSpec_injec
tive {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) : Function.Injective (toS
pec 𝒜 f)
· 使用引理 `AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_surjective`：toSpec_surj
ective {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) : Function.Surjective (
toSpec 𝒜 f)
-/
lemma toSpec_bijective {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    Function.Bijective (toSpec (𝒜 := 𝒜) (f := f)) :=
  ⟨toSpec_injective 𝒜 f_deg hm, toSpec_surjective 𝒜 f_deg hm⟩

end fromSpecToSpec

namespace toSpec

variable {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m)
include hm f_deg

set_option backward.isDefEq.respectTransparency false in
variable {𝒜} in
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec.image_basicOpen_eq_basicOpen*
* 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec`。
形式化陈述：image_basicOpen_eq_basicOpen (a : A) (i : Nat) : toSpec 𝒜 f '' Subtype.val
 ⁻¹' (pbo (decompose 𝒜 a i) : Set (ProjectiveSpectrum 𝒜)) = (PrimeSpectrum.basic
Open (R
参数：a : A；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Set.preimage_injective`：preimage_injective : Injective (preimage f) ↔ Su
rjective f
· 使用引理 `AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_surjective`：toSpec_surj
ective {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) : Function.Surjective (
toSpec 𝒜 f)
· 使用定理 `SetLike.pow_mem_graded`：pow_mem_graded (n : Nat) {r : R} {i : ι} (h : r 
in A i) : r ^ n in A (n • i)
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `SetLike.coe_mem`：coe_mem (x : p) : (x : B) in p
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopologicalSpace.Opens.carrier_eq_coe`：∀ {α : Type u_2} [inst : Topologi
calSpace α] (U : TopologicalSpace.Opens α), U.carrier = ↑U
· 使用引理 `AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_preimage_basicOpen`：toS
pec_preimage_basicOpen {f} (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers
 f)) : toSpec 𝒜 f ⁻¹' (sbo (HomogeneousLocalization.mk z)…
· 使用定理 `ProjectiveSpectrum.basicOpen_pow`：basicOpen_pow (f : A) (n : Nat) (hn : 
0 < n) : basicOpen 𝒜 (f ^ n) = basicOpen 𝒜 f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用引理 `AlgebraicGeometry.ProjIsoSpecTopComponent.toSpec_injective`：toSpec_injec
tive {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) : Function.Injective (toS
pec 𝒜 f)
-/
lemma image_basicOpen_eq_basicOpen (a : A) (i : ℕ) :
    toSpec 𝒜 f '' Subtype.val ⁻¹' (pbo (decompose 𝒜 a i) : Set (ProjectiveSpectrum 𝒜)) =
    (PrimeSpectrum.basicOpen (R := A⁰_ f) <|
      HomogeneousLocalization.mk
        ⟨m * i, ⟨decompose 𝒜 a i ^ m,
          smul_eq_mul m i ▸ SetLike.pow_mem_graded _ (SetLike.coe_mem _)⟩,
          ⟨f^i, by rw [mul_comm]; exact SetLike.pow_mem_graded _ f_deg⟩, ⟨i, rfl⟩⟩).1 :=
  Set.preimage_injective.mpr (toSpec_surjective 𝒜 f_deg hm) <|
    Set.preimage_image_eq _ (toSpec_injective 𝒜 f_deg hm) ▸ by
  rw [Opens.carrier_eq_coe, toSpec_preimage_basicOpen, ProjectiveSpectrum.basicOpen_pow 𝒜 _ m hm]

end toSpec

set_option backward.isDefEq.respectTransparency false in
variable {𝒜} in
/-- The continuous function `Spec A⁰_f → Proj|D(f)` sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}` where
`m` is the degree of `f` -/
/-
**AlgebraicGeometry.ProjIsoSpecTopComponent.fromSpec** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.ProjIsoSpecTopComponent`。
形式化陈述：fromSpec {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) : (Spec.T (A⁰_ 
f)) ⟶ (Proj.T| (pbo f))
参数：f_deg : f in 𝒜 m；hm : 0 < m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous function `Spec A⁰_f → Proj|D(f)` sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}
` where
`m` is the degree of `f`
-/
def fromSpec {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Spec.T (A⁰_ f)) ⟶ (Proj.T| (pbo f)) :=
  TopCat.ofHom
  { toFun := FromSpec.toFun f_deg hm
    continuous_toFun := by
      rw [isTopologicalBasis_subtype (ProjectiveSpectrum.isTopologicalBasis_basic_opens 𝒜)
        (· ∈ pbo f) |>.continuous_iff]
      rintro s ⟨_, ⟨a, rfl⟩, rfl⟩
      have h₁ : Subtype.val (p := (· ∈ pbo f)) ⁻¹' (pbo a) =
          ⋃ i : ℕ, Subtype.val (p := (· ∈ pbo f)) ⁻¹' (pbo (decompose 𝒜 a i)) := by
        simp [ProjectiveSpectrum.basicOpen_eq_union_of_projection 𝒜 a]
      let e : _ ≃ _ :=
        ⟨FromSpec.toFun f_deg hm, ToSpec.toFun f, toSpec_fromSpec _ _ _, fromSpec_toSpec _ _ _⟩
      change IsOpen <| e ⁻¹' _
      rw [← Equiv.image_symm_eq_preimage, h₁, Set.image_iUnion]
      exact isOpen_iUnion fun i ↦ toSpec.image_basicOpen_eq_basicOpen f_deg hm a i ▸
        PrimeSpectrum.isOpen_basicOpen }

end ProjIsoSpecTopComponent

variable {𝒜} in
/--
The homeomorphism `Proj|D(f) ≅ Spec A⁰_f` defined by
- `φ : Proj|D(f) ⟶ Spec A⁰_f` by sending `x` to `A⁰_f ∩ span {g / 1 | g ∈ x}`
- `ψ : Spec A⁰_f ⟶ Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
-/
/-
**AlgebraicGeometry.projIsoSpecTopComponent** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry`。
形式化陈述：projIsoSpecTopComponent {f : A} {m : Nat} (f_deg : f in 𝒜 m) (hm : 0 < m) 
: (Proj.T| (pbo f)) ≅ (Spec.T (A⁰_ f)) where hom
参数：f_deg : f in 𝒜 m；hm : 0 < m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The homeomorphism `Proj|D(f) ≅ Spec A⁰_f` defined by
- `φ : Proj|D(f) ⟶ Spec A⁰_f` by sending `x` to `A⁰_f ∩ span {g / 1 | g ∈ x}`
- `ψ : Spec A⁰_f ⟶ Proj|D(f)` by sending `q` to `{a | aᵢᵐ/fⁱ ∈ q}`.
-/
def projIsoSpecTopComponent {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
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
The ring map from `A⁰_ f` to the local sections of the structure sheaf of the projective spectrum of
`A` on the basic open set `D(f)` defined by sending `s ∈ A⁰_f` to the section `x ↦ s` on `D(f)`.
-/
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：awayToSection (f) : CommRingCat.of (A⁰_ f) ⟶ (structureSheaf 𝒜).1.obj (op 
(pbo f))
参数：f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring map from `A⁰_ f` to the local sections of the structure sheaf of the pr
ojective spectrum of
`A` on the basic open set `D(f)` defined by sending `s ∈ A⁰_f` to the section `x
 ↦ s` on `D(f)`.
-/
def awayToSection (f) : CommRingCat.of (A⁰_ f) ⟶ (structureSheaf 𝒜).1.obj (op (pbo f)) :=
  CommRingCat.ofHom
    -- Have to hint `S`, otherwise it gets unfolded to `structureSheafInType`
    -- causing `ext` to fail
    (S := (structureSheaf 𝒜).1.obj (op (pbo f)))
  { toFun s :=
      ⟨fun x ↦ HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2) s, fun x ↦ by
        obtain ⟨s, rfl⟩ := HomogeneousLocalization.mk_surjective s
        obtain ⟨n, hn : f ^ n = s.den.1⟩ := s.den_mem
        exact ⟨_, x.2, 𝟙 _, s.1, s.2, s.3,
          fun x hsx ↦ x.2 (Ideal.IsPrime.mem_of_pow_mem inferInstance n (hn ▸ hsx)), fun _ ↦ rfl⟩⟩
    map_add' _ _ := by ext; simp only [map_add, HomogeneousLocalization.val_add, Proj.add_apply]
    map_mul' _ _ := by ext; simp only [map_mul, HomogeneousLocalization.val_mul, Proj.mul_apply]
    map_zero' := by ext; simp only [map_zero, HomogeneousLocalization.val_zero, Proj.zero_apply]
    map_one' := by ext; simp only [map_one, HomogeneousLocalization.val_one, Proj.one_apply] }
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_germ** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：awayToSection_germ (f x hx) : awayToSection 𝒜 f ≫ (structureSheaf 𝒜).presh
eaf.germ _ x hx = CommRingCat.ofHom (HomogeneousLocalization.mapId 𝒜 (Submonoid.
powers_le.mpr hx)) ≫ (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv
参数：f x hx。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `RingEquiv.eq_symm_apply`：eq_symm_apply (e : R ≃+* S) {x : S} {y : R} : y
 = e.symm x ↔ e y = x
· 使用定理 `AlgebraicGeometry.Proj.stalkIso'_germ`：∀ {A : Type u_1} {σ : Type u_2} [
inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ
 → σ)   [inst_3 : GradedRin…
-/
lemma awayToSection_germ (f x hx) :
    awayToSection 𝒜 f ≫ (structureSheaf 𝒜).presheaf.germ _ x hx =
      CommRingCat.ofHom (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr hx)) ≫
        (Proj.stalkIso' 𝒜 x).toCommRingCatIso.inv := by
  ext z
  apply (Proj.stalkIso' 𝒜 x).eq_symm_apply.mpr
  apply Proj.stalkIso'_germ

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToSection_apply** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：awayToSection_apply (f : A) (x p) : (((ProjectiveSpectrum.Proj.awayToSecti
on 𝒜 f).1 x).val p).val = IsLocalization.map (M
参数：f : A；x p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
-/
lemma awayToSection_apply (f : A) (x p) :
    (((ProjectiveSpectrum.Proj.awayToSection 𝒜 f).1 x).val p).val =
      IsLocalization.map (M := Submonoid.powers f) (T := p.1.1.toIdeal.primeCompl) _
        (RingHom.id _) (Submonoid.powers_le.mpr p.2) x.val := by
  obtain ⟨x, rfl⟩ := HomogeneousLocalization.mk_surjective x
  change (HomogeneousLocalization.mapId 𝒜 _ _).val = _
  dsimp [HomogeneousLocalization.mapId, HomogeneousLocalization.map]
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

/--
The ring map from `A⁰_ f` to the global sections of the structure sheaf of the projective spectrum
of `A` restricted to the basic open set `D(f)`.

Mathematically, the map is the same as `awayToSection`.
-/
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.awayTo** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.ProjectiveSpectrum.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring map from `A⁰_ f` to the global sections of the structure sheaf of the p
rojective spectrum
of `A` restricted to the basic open set `D(f)`.

Mathematically, the map is the same as `awayToSection`.
-/
def awayToΓ (f) : CommRingCat.of (A⁰_ f) ⟶ LocallyRingedSpace.Γ.obj (op <| Proj| pbo f) :=
  awayToSection 𝒜 f ≫ (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.map
    (homOfLE (Opens.isOpenEmbedding_obj_top _).le).op

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.awayTo** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.ProjectiveSpectrum.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma awayToΓ_ΓToStalk (f) (x) :
    awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x =
      CommRingCat.ofHom (HomogeneousLocalization.mapId 𝒜 (Submonoid.powers_le.mpr x.2)) ≫
      (Proj.stalkIso' 𝒜 x.1).toCommRingCatIso.inv ≫
      ((Proj.toLocallyRingedSpace 𝒜).restrictStalkIso (Opens.isOpenEmbedding _) x).inv := by
  rw [awayToΓ, Category.assoc, ← Category.assoc _ (Iso.inv _),
    Iso.eq_comp_inv, Category.assoc, Category.assoc, Presheaf.Γgerm]
  rw [LocallyRingedSpace.restrictStalkIso_hom_eq_germ]
  simp only [Proj.toLocallyRingedSpace, Proj.toSheafedSpace]
  rw [Presheaf.germ_res, awayToSection_germ]
  rfl

/--
The morphism of locally ringed space from `Proj|D(f)` to `Spec A⁰_f` induced by the ring map
`A⁰_ f → Γ(Proj, D(f))` under the gamma spec adjunction.
-/
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：toSpec (f) : (Proj| pbo f) ⟶ Spec (A⁰_ f)
参数：f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of locally ringed space from `Proj|D(f)` to `Spec A⁰_f` induced by 
the ring map
`A⁰_ f → Γ(Proj, D(f))` under the gamma spec adjunction.
-/
def toSpec (f) : (Proj| pbo f) ⟶ Spec (A⁰_ f) :=
  ΓSpec.locallyRingedSpaceAdjunction.homEquiv (Proj| pbo f) (op (CommRingCat.of <| A⁰_ f))
    (awayToΓ 𝒜 f).op

open HomogeneousLocalization IsLocalRing

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq_comap** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：toSpec_base_apply_eq_comap {f} (x : Proj| pbo f) : (toSpec 𝒜 f).base x = P
rimeSpectrum.comap (mapId 𝒜 (Submonoid.powers_le.mpr x.2)) (closedPoint (AtPrime
 𝒜 x.1.asHomogeneousIdeal.toIdeal))
参数：x : Proj| pbo f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.instIsLocalRingCarrierStalkCommRing
CatPresheaf`：∀ (X : AlgebraicGeometry.LocallyRingedSpace) (x : ↑X.toTopCat), IsL
ocalRing ↑(X.presheaf.stalk x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToΓ_ΓToStalk`：awayToΓ_ΓToS
talk (f) (x) : awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x = CommRingCat.ofHom 
(HomogeneousLocalization.mapId 𝒜 (Submonoid.powe…
· 使用引理 `CommRingCat.hom_comp`：hom_comp {R S T : CommRingCat} (f : R ⟶ S) (g : S 
⟶ T) : (f ≫ g).hom = g.hom.comp f.hom
· 使用定理 `PrimeSpectrum.comap_comp`：comap_comp (f : R ->+* S) (g : S ->+* S') : co
map (g.comp f) = (comap f).comp (comap g)
· 使用定理 `IsLocalRing.comap_closedPoint`：comap_closedPoint {S : Type v} [CommSemir
ing S] [IsLocalRing S] (f : R ->+* S) [IsLocalHom f] : PrimeSpectrum.comap f (cl
osedPoint S) = clos…
· 使用定理 `isLocalHom_of_isIso`：isLocalHom_of_isIso {R S : CommRingCat} (f : R ⟶ S)
 [IsIso f] : IsLocalHom f.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
lemma toSpec_base_apply_eq_comap {f} (x : Proj| pbo f) :
    (toSpec 𝒜 f).base x = PrimeSpectrum.comap (mapId 𝒜 (Submonoid.powers_le.mpr x.2))
      (closedPoint (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)) := by
  change PrimeSpectrum.comap (awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x).hom
        (IsLocalRing.closedPoint ((Proj| pbo f).presheaf.stalk x)) = _
  rw [awayToΓ_ΓToStalk, CommRingCat.hom_comp, PrimeSpectrum.comap_comp]
  exact congr(PrimeSpectrum.comap _ $(@IsLocalRing.comap_closedPoint
    (HomogeneousLocalization.AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) _ _
    ((Proj| pbo f).presheaf.stalk x) _ _ _ (isLocalHom_of_isIso _)))

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq** 是 Mathlib 中的一
个引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：toSpec_base_apply_eq {f} (x : Proj| pbo f) : (toSpec 𝒜 f).base x = ProjIso
SpecTopComponent.toSpec 𝒜 f x
参数：x : Proj| pbo f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq_comap`：to
Spec_base_apply_eq_comap {f} (x : Proj| pbo f) : (toSpec 𝒜 f).base x = PrimeSpec
trum.comap (mapId 𝒜 (Submonoid.powers_le.mpr x.2)) (closed…
· 使用定理 `PrimeSpectrum.ext`：∀ {R : Type u_1} {inst : CommSemiring R} {x y : Prime
Spectrum R}, x.asIdeal = y.asIdeal → x = y
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HomogeneousLocalization.isUnit_iff_isUnit_val`：isUnit_iff_isUnit_val (f 
: HomogeneousLocalization.AtPrime 𝒜 𝔭) : IsUnit f.val ↔ IsUnit f
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier`：mk_mem_
carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) : HomogeneousL
ocalization.mk z in carrier x ↔ z.num.1 in x.1.asHomo…
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用引理 `HomogeneousLocalization.map_mk`：map_mk (g : 𝒜 ->+*ᵍ ℬ) (comap_le : P <= 
Q.comap g) (x) : map g comap_le (mk x) = mk ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_
mem g x.3.2⟩, comap_…
· 使用定理 `HomogeneousLocalization.val_mk`：val_mk (i : NumDenSameDeg 𝒜 x) : val (mk
 i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.AtPrime.isUnit_mk'_iff`：∀ {R : Type u_1} [inst : CommSemi
ring R] (S : Type u_2) [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (I : Ide
al R)   [hI : I.IsPrime] [i…
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
lemma toSpec_base_apply_eq {f} (x : Proj| pbo f) :
    (toSpec 𝒜 f).base x = ProjIsoSpecTopComponent.toSpec 𝒜 f x :=
  toSpec_base_apply_eq_comap 𝒜 x |>.trans <| PrimeSpectrum.ext <| Ideal.ext fun z =>
  show ¬ IsUnit _ ↔ z ∈ ProjIsoSpecTopComponent.ToSpec.carrier _ by
  obtain ⟨z, rfl⟩ := z.mk_surjective
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val,
    ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    IsLocalization.AtPrime.isUnit_mk'_iff]
  exact not_not
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_isIso** 是 Mathlib 中的一个引理
，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：toSpec_base_isIso {f} {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : IsIso (toSpec 
𝒜 f).base
参数：f_deg : f in 𝒜 m；hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ext`：hom_ext {X Y : C} (f g : X ⟶ Y)
 (w : forall x, f x = g x) : f = g
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq`：toSpec_b
ase_apply_eq {f} (x : Proj| pbo f) : (toSpec 𝒜 f).base x = ProjIsoSpecTopCompone
nt.toSpec 𝒜 f x
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
-/
lemma toSpec_base_isIso {f} {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    IsIso (toSpec 𝒜 f).base := by
  convert! (projIsoSpecTopComponent f_deg hm).isIso_hom
  exact ConcreteCategory.hom_ext _ _ <| toSpec_base_apply_eq 𝒜
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply** 是 Mathlib
 中的一个引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：mk_mem_toSpec_base_apply {f} (x : Proj| pbo f) (z : NumDenSameDeg 𝒜 (.powe
rs f)) : HomogeneousLocalization.mk z in ((toSpec 𝒜 f).base x).asIdeal ↔ z.num.1
 in x.1.asHomogeneousIdeal
参数：x : Proj| pbo f；z : NumDenSameDeg 𝒜 (.powers f)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier`：mk_mem_
carrier (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) : HomogeneousL
ocalization.mk z in carrier x ↔ z.num.1 in x.1.asHomo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq`：toSpec_b
ase_apply_eq {f} (x : Proj| pbo f) : (toSpec 𝒜 f).base x = ProjIsoSpecTopCompone
nt.toSpec 𝒜 f x
-/
lemma mk_mem_toSpec_base_apply {f} (x : Proj| pbo f)
    (z : NumDenSameDeg 𝒜 (.powers f)) :
    HomogeneousLocalization.mk z ∈ ((toSpec 𝒜 f).base x).asIdeal ↔
      z.num.1 ∈ x.1.asHomogeneousIdeal :=
  (toSpec_base_apply_eq 𝒜 x).symm ▸ ProjIsoSpecTopComponent.ToSpec.mk_mem_carrier _ _

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_preimage_basicOpen** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：toSpec_preimage_basicOpen {f} (t : NumDenSameDeg 𝒜 (.powers f)) : (Opens.m
ap (toSpec 𝒜 f).base).obj (sbo (HomogeneousLocalization.mk t)) = Opens.comap ⟨_,
 continuous_subtype_val⟩ (pbo t.num.1)
参数：t : NumDenSameDeg 𝒜 (.powers f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_apply_eq`：toSpec_b
ase_apply_eq {f} (x : Proj| pbo f) : (toSpec 𝒜 f).base x = ProjIsoSpecTopCompone
nt.toSpec 𝒜 f x
· 使用定理 `AlgebraicGeometry.ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen`：pre
image_basicOpen (z : HomogeneousLocalization.NumDenSameDeg 𝒜 (.powers f)) : toFu
n f ⁻¹' (sbo (HomogeneousLocalization.mk z) : Set (PrimeS…
· 使用定理 `TopologicalSpace.Opens.map_coe`：map_coe (f : X ⟶ Y) (U : Opens Y) : ((ma
p f).obj U : Set X) = f ⁻¹' (U : Set Y)
-/
lemma toSpec_preimage_basicOpen {f}
    (t : NumDenSameDeg 𝒜 (.powers f)) :
    (Opens.map (toSpec 𝒜 f).base).obj (sbo (HomogeneousLocalization.mk t)) =
      Opens.comap ⟨_, continuous_subtype_val⟩ (pbo t.num.1) :=
  Opens.ext <| Opens.map_coe _ _ ▸ by
  convert! (ProjIsoSpecTopComponent.ToSpec.preimage_basicOpen f t)
  exact funext fun _ => toSpec_base_apply_eq _ _

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.toOpen_toSpec_val_c_app** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：toOpen_toSpec_val_c_app (f) (U) : (Scheme.ΓSpecIso _).inv ≫ (Spec A⁰_ f).p
resheaf.map (homOfLE le_top).op ≫ (toSpec 𝒜 f).c.app U = awayToΓ 𝒜 f ≫ (Proj| pb
o f).presheaf.map (homOfLE le_top).op
参数：f；U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用引理 `AlgebraicGeometry.ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEqui
v_app`：toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app {X : LocallyRingedS
pace} {R : Type u} [CommRing R] (f : Γ.rightOp.obj X ⟶ op (CommRing…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
lemma toOpen_toSpec_val_c_app (f) (U) :
    (Scheme.ΓSpecIso _).inv ≫ (Spec A⁰_ f).presheaf.map (homOfLE le_top).op ≫
      (toSpec 𝒜 f).c.app U =
      awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.map (homOfLE le_top).op :=
  Eq.trans (by rfl) <| ΓSpec.toOpen_comp_locallyRingedSpaceAdjunction_homEquiv_app _ U

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.toStalk_stalkMap_toSpec** 是 Mathlib 
中的一个引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：toStalk_stalkMap_toSpec (f) (x) : (Scheme.ΓSpecIso _).inv ≫ (Spec A⁰_ f).p
resheaf.germ _ _ (by simp) ≫ (toSpec 𝒜 f).stalkMap x = awayToΓ 𝒜 f ≫ (Proj| pbo 
f).presheaf.Γgerm x
参数：f；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.stalkMap_germ`：stalkMap_germ (U : O
pens Y) (x : X) (hx : f.base x in U) : Y.presheaf.germ U (f.base x) hx ≫ f.stalk
Map x = f.c.app (op U) ≫ X.presheaf.germ…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.toOpen_toSpec_val_c_app_assoc`
：∀ {A : Type u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [ins
t_2 : AddSubgroupClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRin…
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
If `x` is a point in the basic open set `D(f)` where `f` is a homogeneous element of positive
degree, then the homogeneously localized ring `A⁰ₓ` has the universal property of the localization
of `A⁰_f` at `φ(x)` where `φ : Proj|D(f) ⟶ Spec A⁰_f` is the morphism of locally ringed space
constructed as above.
-/
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：isLocalization_atPrime (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
 : @IsLocalization (Away 𝒜 f) _ ((toSpec 𝒜 f).base x).asIdeal.primeCompl (AtPrim
e 𝒜 x.1.asHomogeneousIdeal.toIdeal) _ (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).to
Algebra
参数：f；x : pbo f；f_deg : f in 𝒜 m；hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply`：mk_m
em_toSpec_base_apply {f} (x : Proj| pbo f) (z : NumDenSameDeg 𝒜 (.powers f)) : H
omogeneousLocalization.mk z in ((toSpec 𝒜 f).base x).asI…
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_mul`：val_mul : forall y1 y2 : HomogeneousLoc
alization 𝒜 x, (y1 * y2).val = y1.val * y2.val
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `IsLocalization.mk'_mul_mk'_eq_one'`：∀ {R : Type u_1} [inst : CommSemirin
g R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Alge
bra R S] [inst_3 : IsLoc…
· 使用定理 `HomogeneousLocalization.val_one`：val_one : (1 : HomogeneousLocalization 
𝒜 x).val = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `succ_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n +
 1) • a = a + n • a
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
If `x` is a point in the basic open set `D(f)` where `f` is a homogeneous elemen
t of positive
degree, then the homogeneously localized ring `A⁰ₓ` has the universal property o
f the localization
of `A⁰_f` at `φ(x)` where `φ : Proj|D(f) ⟶ Spec A⁰_f` is the morphism of locally
 ringed space
constructed as above.
-/
lemma isLocalization_atPrime (f) (x : pbo f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    @IsLocalization (Away 𝒜 f) _ ((toSpec 𝒜 f).base x).asIdeal.primeCompl
      (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) _
      (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra := by
  let : Algebra (Away 𝒜 f) (AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal) :=
    (mapId 𝒜 (Submonoid.powers_le.mpr x.2)).toAlgebra
  constructor; constructor
  · rintro ⟨y, hy⟩
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective y
    refine .of_mul_eq_one
      (.mk ⟨y.deg, y.den, y.num, (mk_mem_toSpec_base_apply _ _ _).not.mp hy⟩) <| val_injective _ ?_
    simp only [RingHom.algebraMap_toAlgebra, map_mk, GradedRingHom.id_apply, val_mul, val_mk,
      mk_eq_mk', val_one, IsLocalization.mk'_mul_mk'_eq_one']
  · intro z
    obtain ⟨⟨i, a, ⟨b, hb⟩, (hb' : b ∉ x.1.1)⟩, rfl⟩ := z.mk_surjective
    refine ⟨⟨HomogeneousLocalization.mk ⟨i * m, ⟨a * b ^ (m - 1), ?_⟩,
        ⟨f ^ i, SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
      ⟨HomogeneousLocalization.mk ⟨i * m, ⟨b ^ m, mul_comm m i ▸ SetLike.pow_mem_graded _ hb⟩,
        ⟨f ^ i, SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
        (mk_mem_toSpec_base_apply _ _ _).not.mpr <| x.1.1.toIdeal.primeCompl.pow_mem hb' m⟩⟩,
        val_injective _ ?_⟩
    · convert SetLike.mul_mem_graded a.2 (SetLike.pow_mem_graded (m - 1) hb)
      rw [← succ_nsmul', tsub_add_cancel_of_le (by lia), mul_comm, smul_eq_mul]
    · simp only [RingHom.algebraMap_toAlgebra, map_mk, GradedRingHom.id_apply, val_mul, val_mk,
        mk_eq_mk', ← IsLocalization.mk'_mul, Submonoid.mk_mul_mk, IsLocalization.mk'_eq_iff_eq]
      rw [mul_comm b, mul_mul_mul_comm, ← pow_succ', mul_assoc, tsub_add_cancel_of_le (by lia)]
  · intro y z e
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective y
    obtain ⟨z, rfl⟩ := HomogeneousLocalization.mk_surjective z
    obtain ⟨i, c, hc, hc', e⟩ : ∃ i, ∃ c ∈ 𝒜 i, c ∉ x.1.asHomogeneousIdeal ∧
        c * (z.den.1 * y.num.1) = c * (y.den.1 * z.num.1) := by
      apply_fun HomogeneousLocalization.val at e
      simp only [RingHom.algebraMap_toAlgebra, map_mk, GradedRingHom.id_apply, val_mk, mk_eq_mk',
        IsLocalization.mk'_eq_iff_eq] at e
      obtain ⟨⟨c, hcx⟩, hc⟩ := IsLocalization.exists_of_eq (M := x.1.1.toIdeal.primeCompl) e
      obtain ⟨i, hi⟩ := not_forall.mp ((x.1.1.isHomogeneous.mem_iff _).not.mp hcx)
      refine ⟨i, _, (decompose 𝒜 c i).2, hi, ?_⟩
      apply_fun fun x ↦ (decompose 𝒜 x (i + z.deg + y.deg)).1 at hc
      conv_rhs at hc => rw [add_right_comm]
      rwa [← mul_assoc, coe_decompose_mul_add_of_right_mem, coe_decompose_mul_add_of_right_mem,
        ← mul_assoc, coe_decompose_mul_add_of_right_mem, coe_decompose_mul_add_of_right_mem,
        mul_assoc, mul_assoc] at hc
      exacts [y.den.2, z.num.2, z.den.2, y.num.2]
    refine ⟨⟨HomogeneousLocalization.mk ⟨m * i, ⟨c ^ m, SetLike.pow_mem_graded _ hc⟩,
      ⟨f ^ i, mul_comm m i ▸ SetLike.pow_mem_graded _ f_deg⟩, ⟨_, rfl⟩⟩,
      (mk_mem_toSpec_base_apply _ _ _).not.mpr <| x.1.1.toIdeal.primeCompl.pow_mem hc' _⟩,
      val_injective _ ?_⟩
    simp only [val_mul, val_mk, mk_eq_mk', ← IsLocalization.mk'_mul, Submonoid.mk_mul_mk,
      IsLocalization.mk'_eq_iff_eq, mul_assoc]
    congr 2
    rw [mul_left_comm, mul_left_comm y.den.1, ← tsub_add_cancel_of_le (show 1 ≤ m from hm),
      pow_succ, mul_assoc, mul_assoc, e]

set_option backward.isDefEq.respectTransparency.types false in
/--
For an element `f ∈ A` with positive degree and a homogeneous ideal in `D(f)`, we have that the
stalk of `Spec A⁰_ f` at `y` is isomorphic to `A⁰ₓ` where `y` is the point in `Proj` corresponding
to `x`.
-/
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.specStalkEquiv** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：specStalkEquiv (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : (Spec
.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x) ≅ CommRingCat.of (
AtPrime 𝒜 x.1.asHomogeneousIdeal.toIdeal)
参数：f；x : pbo f；f_deg : f in 𝒜 m；hm : 0 < m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime`：isLoca
lization_atPrime (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : @IsLocali
zation (Away 𝒜 f) _ ((toSpec 𝒜 f).base x).asIdeal.prim…

--- 原说明 ---
For an element `f ∈ A` with positive degree and a homogeneous ideal in `D(f)`, w
e have that the
stalk of `Spec A⁰_ f` at `y` is isomorphic to `A⁰ₓ` where `y` is the point in `P
roj` corresponding
to `x`.
-/
def specStalkEquiv (f) (x : pbo f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
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
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.toStalk_specStalkEquiv** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：toStalk_specStalkEquiv (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m)
 : StructureSheaf.toStalk (A⁰_ f) ((toSpec 𝒜 f).base x) ≫ (specStalkEquiv 𝒜 f x 
f_deg hm).hom = CommRingCat.ofHom (mapId _ <| Submonoid.powers_le.mpr x.2)
参数：f；x : pbo f；f_deg : f in 𝒜 m；hm : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.isLocalization_atPrime`：isLoca
lization_atPrime (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : @IsLocali
zation (Away 𝒜 f) _ ((toSpec 𝒜 f).base x).asIdeal.prim…
-/
lemma toStalk_specStalkEquiv (f) (x : pbo f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
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
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.stalkMap_toSpec** 是 Mathlib 中的一个引理，位
于命名空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：stalkMap_toSpec (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : (toS
pec 𝒜 f).stalkMap x = (specStalkEquiv 𝒜 f x f_deg hm).hom ≫ (Proj.stalkIso' 𝒜 x.
1).toCommRingCatIso.inv ≫ ((Proj.toLocallyRingedSpace 𝒜).restrictStalkIso (Opens
.isOpenEmbedding _) x).inv
参数：f；x : pbo f；f_deg : f in 𝒜 m；hm : 0 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `IsLocalization.ringHom_ext`：ringHom_ext {P : Type*} [Semiring P] ⦃j k : 
S ->+* P⦄ (h : j.comp (algebraMap R S) = k.comp (algebraMap R S)) : j = k
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk`：∀ (R : Type u)
 [inst : CommRing R] (p : PrimeSpectrum R),   IsLocalization.AtPrime (↑((Algebra
icGeometry.Spec.structureSheaf R).presheaf.sta…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.toStalk_stalkMap_toSpec`：toSta
lk_stalkMap_toSpec (f) (x) : (Scheme.ΓSpecIso _).inv ≫ (Spec A⁰_ f).presheaf.ger
m _ _ (by simp) ≫ (toSpec 𝒜 f).stalkMap x = awayToΓ 𝒜 f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Submonoid.powers_le`：powers_le {n : M} {P : Submonoid M} : powers n <= P
 ↔ n in P
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.awayToΓ_ΓToStalk`：awayToΓ_ΓToS
talk (f) (x) : awayToΓ 𝒜 f ≫ (Proj| pbo f).presheaf.Γgerm x = CommRingCat.ofHom 
(HomogeneousLocalization.mapId 𝒜 (Submonoid.powe…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.toStalk_specStalkEquiv`：toStal
k_specStalkEquiv (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : Structure
Sheaf.toStalk (A⁰_ f) ((toSpec 𝒜 f).base x) ≫ (specSta…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma stalkMap_toSpec (f) (x : pbo f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (toSpec 𝒜 f).stalkMap x =
      (specStalkEquiv 𝒜 f x f_deg hm).hom ≫ (Proj.stalkIso' 𝒜 x.1).toCommRingCatIso.inv ≫
      ((Proj.toLocallyRingedSpace 𝒜).restrictStalkIso (Opens.isOpenEmbedding _) x).inv := by
  refine CommRingCat.hom_ext <|
    IsLocalization.ringHom_ext (R := A⁰_ f) ((toSpec 𝒜 f).base x).asIdeal.primeCompl
      (S := (Spec.structureSheaf (A⁰_ f)).presheaf.stalk ((toSpec 𝒜 f).base x)) <| ?_
  ext a
  refine congr($(toStalk_stalkMap_toSpec 𝒜 f x) _).trans ?_
  rw [awayToΓ_ΓToStalk, ← toStalk_specStalkEquiv, Category.assoc]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.ProjectiveSpectrum.Proj.isIso_toSpec** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.ProjectiveSpectrum.Proj`。
形式化陈述：isIso_toSpec (f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : IsIso (toSpec 𝒜 f)
参数：f；f_deg : f in 𝒜 m；hm : 0 < m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.toSpec_base_isIso`：toSpec_base
_isIso {f} {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : IsIso (toSpec 𝒜 f).base
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.stalkMap_toSpec`：stalkMap_toSp
ec (f) (x : pbo f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : (toSpec 𝒜 f).stalkMap x
 = (specStalkEquiv 𝒜 f x f_deg hm).hom ≫ (Proj.…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso`：of_st
alk_iso {X Y : LocallyRingedSpace} (f : X ⟶ Y) (hf : IsOpenEmbedding f.base) [st
alk_iso : forall x : X.1, IsIso (f.stalkMap x)] : Local…
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.to_iso`：to_iso [Epi
 f.base] : IsIso f
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
-/
lemma isIso_toSpec (f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
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
If `f ∈ A` is a homogeneous element of positive degree, then the projective spectrum restricted to
`D(f)` as a locally ringed space is isomorphic to `Spec A⁰_f`.
-/
/-
**AlgebraicGeometry.projIsoSpec** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：projIsoSpec (f) {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : (Proj| pbo f) ≅ (Spe
c (A⁰_ f))
参数：f；f_deg : f in 𝒜 m；hm : 0 < m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.ProjectiveSpectrum.Proj.isIso_toSpec`：isIso_toSpec (f)
 {m} (f_deg : f in 𝒜 m) (hm : 0 < m) : IsIso (toSpec 𝒜 f)

--- 原说明 ---
If `f ∈ A` is a homogeneous element of positive degree, then the projective spec
trum restricted to
`D(f)` as a locally ringed space is isomorphic to `Spec A⁰_f`.
-/
def projIsoSpec (f) {m} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) :
    (Proj| pbo f) ≅ (Spec (A⁰_ f)) :=
  @asIso _ _ _ _ (f := toSpec 𝒜 f) (isIso_toSpec 𝒜 f f_deg hm)

set_option backward.isDefEq.respectTransparency false in
/--
This is the scheme `Proj(A)` for any `ℕ`-graded ring `A`.
-/
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the scheme `Proj(A)` for any `ℕ`-graded ring `A`.
-/
def «Proj» : Scheme where
  __ := Proj.toLocallyRingedSpace 𝒜
  local_affine (x : Proj.T) := by
    classical
    obtain ⟨f, m, f_deg, hm, hx⟩ : ∃ (f : A) (m : ℕ) (_ : f ∈ 𝒜 m) (_ : 0 < m), f ∉ x.1 := by
      by_contra!
      refine x.not_irrelevant_le fun z hz ↦ ?_
      rw [← DirectSum.sum_support_decompose 𝒜 z]
      exact x.1.toIdeal.sum_mem fun k hk ↦ this _ k (SetLike.coe_mem _) <| by_contra <| by aesop
    exact ⟨⟨pbo f, hx⟩, .of (A⁰_ f), ⟨projIsoSpec 𝒜 f f_deg hm⟩⟩


end AlgebraicGeometry

