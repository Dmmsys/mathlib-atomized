/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace

/-!
# The structure sheaf on `ProjectiveSpectrum 𝒜`.

In `Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean`, we have given a topology on
`ProjectiveSpectrum 𝒜`; in this file we will construct a sheaf on `ProjectiveSpectrum 𝒜`.

## Notation
- `A` is a commutative ring;
- `σ` is a class of additive subgroups of `A`;
- `𝒜 : ℕ → σ` is the grading of `A`;
- `U` is opposite object of some open subset of `ProjectiveSpectrum.top`.

## Main definitions and results
We define the structure sheaf as the subsheaf of all dependent function
`f : Π x : U, HomogeneousLocalization 𝒜 x` such that `f` is locally expressible as ratio of two
elements of the *same grading*, i.e. `∀ y ∈ U, ∃ (V ⊆ U) (i : ℕ) (a b ∈ 𝒜 i), ∀ z ∈ V, f z = a / b`.

* `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.isLocallyFraction`: the predicate that
  a dependent function is locally expressible as a ratio of two elements of the same grading.
* `AlgebraicGeometry.ProjectiveSpectrum.StructureSheaf.sectionsSubring`: the dependent functions
  satisfying the above local property forms a subring of all dependent functions
  `Π x : U, HomogeneousLocalization 𝒜 x`.
* `AlgebraicGeometry.Proj.StructureSheaf`: the sheaf with `U ↦ sectionsSubring U` and natural
  restriction map.

Then we establish that `Proj 𝒜` is a `LocallyRingedSpace`:
* `AlgebraicGeometry.Proj.stalkIso'`: for any `x : ProjectiveSpectrum 𝒜`, the stalk of
  `Proj.StructureSheaf` at `x` is isomorphic to `HomogeneousLocalization 𝒜 x`.
* `AlgebraicGeometry.Proj.toLocallyRingedSpace`: `Proj` as a locally ringed space.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

@[expose] public section


noncomputable section

namespace AlgebraicGeometry

open scoped DirectSum Pointwise

open DirectSum SetLike Localization TopCat TopologicalSpace CategoryTheory Opposite

variable {A σ : Type*}
variable [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : Nat -> σ) [GradedRing 𝒜]

local notation3 "at " x =>
  HomogeneousLocalization.AtPrime 𝒜
    (HomogeneousIdeal.toIdeal (ProjectiveSpectrum.asHomogeneousIdeal x))

namespace ProjectiveSpectrum.StructureSheaf

set_option backward.isDefEq.respectTransparency.types false in
variable {𝒜} in
/--
Definition of `IsFraction` / `IsFraction` 的定义

English:
definition IsFraction
  signature: {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : forall x : U, at x.1)
  body: exists (i : Nat) (r s : 𝒜 i) (s_nin : forall x : U, s.1 ∉ x.1.asHomogeneousIdeal),
    forall x : U, f x = .mk ⟨i, r, s, s_nin x⟩

中文:
定义 IsFraction
  签名: {U : Opens (射影谱.top 𝒜)} (f : 对任意 x : U, at x.1)
  定义体: exists (i : Nat) (r s : 𝒜 i) (s_nin : forall x : U, s.1 ∉ x.1.asHomogeneousIdeal),
    forall x : U, f x = .mk ⟨i, r, s, s_nin x⟩

Depends on / 依赖: asHomogeneousIdeal, backward, backward.isDefEq.respectTransparency.types, isDefEq, respectTransparency, s_nin, set_option
-/
def IsFraction {U : Opens (ProjectiveSpectrum.top 𝒜)} (f : forall x : U, at x.1) : Prop :=
  exists (i : Nat) (r s : 𝒜 i) (s_nin : forall x : U, s.1 ∉ x.1.asHomogeneousIdeal),
    forall x : U, f x = .mk ⟨i, r, s, s_nin x⟩
set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isFractionPrelocal` / `isFractionPrelocal` 的定义

English:
definition isFractionPrelocal
  signature: : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x where
  body: IsFraction f
  res := by rintro V U i f ⟨j, r, s, h, w⟩; exact ⟨j, r, s, (h <| i ·), (w <| i ·)⟩

中文:
定义 isFractionPrelocal
  签名: : PrelocalPredicate fun x : 射影谱.top 𝒜 => at x where
  定义体: IsFraction f
  res := by rintro V U i f ⟨j, r, s, h, w⟩; exact ⟨j, r, s, (h <| i ·), (w <| i ·)⟩

Depends on / 依赖: IsFraction
-/
def isFractionPrelocal : PrelocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x where
  pred f := IsFraction f
  res := by rintro V U i f ⟨j, r, s, h, w⟩; exact ⟨j, r, s, (h <| i ·), (w <| i ·)⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `isLocallyFraction` / `isLocallyFraction` 的定义

English:
definition isLocallyFraction
  signature: : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x
  body: (isFractionPrelocal 𝒜).sheafify

中文:
定义 isLocallyFraction
  签名: : LocalPredicate fun x : 射影谱.top 𝒜 => at x
  定义体: (isFractionPrelocal 𝒜).sheafify

Depends on / 依赖: isFractionPrelocal, sheafify
-/
def isLocallyFraction : LocalPredicate fun x : ProjectiveSpectrum.top 𝒜 => at x :=
  (isFractionPrelocal 𝒜).sheafify

namespace SectionSubring

variable {𝒜}

open Submodule SetLike.GradedMonoid HomogeneousLocalization

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `zero_mem'` / 定理 `zero_mem'`

English:
theorem zero_mem'
  given: (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
  proof: fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

中文:
定理 zero_mem'
  条件: (U : (Opens (射影谱.top 𝒜))ᵒᵖ)
  证明: fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩
-/
theorem zero_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (0 : forall x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨0, zero_mem _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `one_mem'` / 定理 `one_mem'`

English:
theorem one_mem'
  given: (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
  proof: fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨1, one_mem_graded _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

中文:
定理 one_mem'
  条件: (U : (Opens (射影谱.top 𝒜))ᵒᵖ)
  证明: fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨1, one_mem_graded _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩
-/
theorem one_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    (isLocallyFraction 𝒜).pred (1 : forall x : U.unop, at x.1) := fun x =>
  ⟨unop U, x.2, 𝟙 (unop U), ⟨0, ⟨1, one_mem_graded _⟩, ⟨1, one_mem_graded _⟩, _, fun _ => rfl⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `add_mem'` / 定理 `add_mem'`

English:
theorem add_mem'
  statement: (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : forall x : U.unop, at x.1)
  proof: fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨sb * ra + sa * rb,
        add_mem (add_comm jb ja ▸ mul_mem_graded sb_mem ra_mem : sb * ra in 𝒜 (ja + jb))
          (mul_mem_graded sa_mem rb_mem)⟩,
      ⟨sa * sb, mul_mem_graded sa_mem sb_mem⟩, fun y =>
        y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, add_mk, add_comm (sa * rb)]

中文:
定理 add_mem'
  结论: (U : (Opens (射影谱.top 𝒜))ᵒᵖ) (a b : 对任意 x : U.unop, at x.1)
  证明: fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨sb * ra + sa * rb,
        add_mem (add_comm jb ja ▸ mul_mem_graded sb_mem ra_mem : sb * ra in 𝒜 (ja + jb))
          (mul_mem_graded sa_mem rb_mem)⟩,
      ⟨sa * sb, mul_mem_graded sa_mem sb_mem⟩, fun y =>
        y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, add_mk, add_comm (sa * rb)]

Depends on / 依赖: Opens.infLELeft, add_comm, add_mem, asHomogeneousIdeal, asHomogeneousIdeal.toIdeal.primeCompl.mul_mem, infLELeft, mul_mem, mul_mem_graded, primeCompl, ra_mem, rb_mem, sa_mem, sb_mem, toIdeal
-/
theorem add_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : forall x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a + b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨sb * ra + sa * rb,
        add_mem (add_comm jb ja ▸ mul_mem_graded sb_mem ra_mem : sb * ra in 𝒜 (ja + jb))
          (mul_mem_graded sa_mem rb_mem)⟩,
      ⟨sa * sb, mul_mem_graded sa_mem sb_mem⟩, fun y =>
        y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, add_mk, add_comm (sa * rb)]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `neg_mem'` / 定理 `neg_mem'`

English:
theorem neg_mem'
  statement: (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : forall x : U.unop, at x.1)
  proof: fun x => by
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, nin, hy⟩
  refine ⟨V, m, i, j, ⟨-r, neg_mem r_mem⟩, ⟨s, s_mem⟩, nin, fun y => ?_⟩
  simp only [ext_iff_val, val_mk] at hy
  simp only [Pi.neg_apply, ext_iff_val, val_neg, hy, val_mk, neg_mk]

中文:
定理 neg_mem'
  结论: (U : (Opens (射影谱.top 𝒜))ᵒᵖ) (a : 对任意 x : U.unop, at x.1)
  证明: fun x => by
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, nin, hy⟩
  refine ⟨V, m, i, j, ⟨-r, neg_mem r_mem⟩, ⟨s, s_mem⟩, nin, fun y => ?_⟩
  simp only [ext_iff_val, val_mk] at hy
  simp only [Pi.neg_apply, ext_iff_val, val_neg, hy, val_mk, neg_mk]

Depends on / 依赖: Pi.neg_apply, ext_iff_val, neg_apply, neg_mem, neg_mk, r_mem, s_mem, val_mk, val_neg
-/
theorem neg_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a : forall x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) : (isLocallyFraction 𝒜).pred (-a) := fun x => by
  rcases ha x with ⟨V, m, i, j, ⟨r, r_mem⟩, ⟨s, s_mem⟩, nin, hy⟩
  refine ⟨V, m, i, j, ⟨-r, neg_mem r_mem⟩, ⟨s, s_mem⟩, nin, fun y => ?_⟩
  simp only [ext_iff_val, val_mk] at hy
  simp only [Pi.neg_apply, ext_iff_val, val_neg, hy, val_mk, neg_mk]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `mul_mem'` / 定理 `mul_mem'`

English:
theorem mul_mem'
  statement: (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : forall x : U.unop, at x.1)
  proof: fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨ra * rb, SetLike.mul_mem_graded ra_mem rb_mem⟩,
      ⟨sa * sb, SetLike.mul_mem_graded sa_mem sb_mem⟩, fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, Localization.mk_mul]

中文:
定理 mul_mem'
  结论: (U : (Opens (射影谱.top 𝒜))ᵒᵖ) (a b : 对任意 x : U.unop, at x.1)
  证明: fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨ra * rb, SetLike.mul_mem_graded ra_mem rb_mem⟩,
      ⟨sa * sb, SetLike.mul_mem_graded sa_mem sb_mem⟩, fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, Localization.mk_mul]

Depends on / 依赖: Opens.apply_mk, Opens.infLELeft, SetLike, SetLike.mul_mem_graded, Subtype, Subtype.forall, apply_mk, asHomogeneousIdeal, asHomogeneousIdeal.toIdeal.primeCompl.mul_mem, infLELeft, mul_mem, mul_mem_graded, primeCompl, ra_mem, rb_mem, sa_mem, sb_mem, toIdeal
-/
theorem mul_mem' (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) (a b : forall x : U.unop, at x.1)
    (ha : (isLocallyFraction 𝒜).pred a) (hb : (isLocallyFraction 𝒜).pred b) :
    (isLocallyFraction 𝒜).pred (a * b) := fun x => by
  rcases ha x with ⟨Va, ma, ia, ja, ⟨ra, ra_mem⟩, ⟨sa, sa_mem⟩, hwa, wa⟩
  rcases hb x with ⟨Vb, mb, ib, jb, ⟨rb, rb_mem⟩, ⟨sb, sb_mem⟩, hwb, wb⟩
  refine
    ⟨Va ⊓ Vb, ⟨ma, mb⟩, Opens.infLELeft _ _ ≫ ia, ja + jb,
      ⟨ra * rb, SetLike.mul_mem_graded ra_mem rb_mem⟩,
      ⟨sa * sb, SetLike.mul_mem_graded sa_mem sb_mem⟩, fun y =>
      y.1.asHomogeneousIdeal.toIdeal.primeCompl.mul_mem (hwa ⟨y.1, y.2.1⟩) (hwb ⟨y.1, y.2.2⟩), ?_⟩
  rintro ⟨y, hy⟩
  simp only [Subtype.forall, Opens.apply_mk] at wa wb
  simp [wa y hy.1, wb y hy.2, ext_iff_val, Localization.mk_mul]

end SectionSubring

section

open SectionSubring

variable {𝒜}

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `sectionsSubring` / `sectionsSubring` 的定义

English:
definition sectionsSubring
  signature: (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
  body: {f | (isLocallyFraction 𝒜).pred f}
  zero_mem' := zero_mem' U
  one_mem' := one_mem' U
  add_mem' := add_mem' U _ _
  neg_mem' := neg_mem' U _
  mul_mem' := mul_mem' U _ _

中文:
定义 sectionsSubring
  签名: (U : (Opens (射影谱.top 𝒜))ᵒᵖ)
  定义体: {f | (isLocallyFraction 𝒜).pred f}
  zero_mem' := zero_mem' U
  one_mem' := one_mem' U
  add_mem' := add_mem' U _ _
  neg_mem' := neg_mem' U _
  mul_mem' := mul_mem' U _ _

Depends on / 依赖: isLocallyFraction
-/
def sectionsSubring (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    Subring (forall x : U.unop, at x.1) where
  carrier := {f | (isLocallyFraction 𝒜).pred f}
  zero_mem' := zero_mem' U
  one_mem' := one_mem' U
  add_mem' := add_mem' U _ _
  neg_mem' := neg_mem' U _
  mul_mem' := mul_mem' U _ _

end

/--
Definition of `structureSheafInType` / `structureSheafInType` 的定义

English:
definition structureSheafInType
  signature: : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜)
  body: subsheafToTypes (isLocallyFraction 𝒜)

中文:
定义 structureSheafInType
  签名: : 层 (类型 _) (射影谱.top 𝒜)
  定义体: subsheafToTypes (isLocallyFraction 𝒜)

Depends on / 依赖: isLocallyFraction, subsheafToTypes
-/
def structureSheafInType : Sheaf (Type _) (ProjectiveSpectrum.top 𝒜) :=
  subsheafToTypes (isLocallyFraction 𝒜)

/--
Instance `commRingStructureSheafInTypeObj` / 实例 `commRingStructureSheafInTypeObj`

English:
instance commRingStructureSheafInTypeObj
  signature: (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ)
  body: (sectionsSubring U).toCommRing

中文:
实例 commRingStructureSheafInTypeObj
  签名: (U : (Opens (射影谱.top 𝒜))ᵒᵖ)
  定义体: (sectionsSubring U).toCommRing

Depends on / 依赖: sectionsSubring, toCommRing
-/
instance commRingStructureSheafInTypeObj (U : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ) :
    CommRing ((structureSheafInType 𝒜).1.obj U) :=
  (sectionsSubring U).toCommRing

/-- The structure presheaf, valued in `CommRing`, constructed by dressing up the `Type`-valued
structure presheaf. -/
@[simps obj_carrier]
/--
Definition of `structurePresheafInCommRing` / `structurePresheafInCommRing` 的定义

English:
definition structurePresheafInCommRing
  signature: : Presheaf CommRingCat (ProjectiveSpectrum.top 𝒜) where
  body: CommRingCat.of ((structureSheafInType 𝒜).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType 𝒜).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

中文:
定义 structurePresheafInCommRing
  签名: : 预层 交换环范畴 (射影谱.top 𝒜) where
  定义体: CommRingCat.of ((structureSheafInType 𝒜).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType 𝒜).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

Depends on / 依赖: CommRingCat, CommRingCat.of, structureSheafInType
-/
def structurePresheafInCommRing : Presheaf CommRingCat (ProjectiveSpectrum.top 𝒜) where
  obj U := CommRingCat.of ((structureSheafInType 𝒜).1.obj U)
  map i := CommRingCat.ofHom
    { toFun := (structureSheafInType 𝒜).1.map i
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/--
Definition of `structurePresheafCompForget` / `structurePresheafCompForget` 的定义

English:
definition structurePresheafCompForget
  signature: :
  body: NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

中文:
定义 structurePresheafCompForget
  签名: :
  定义体: NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, cat_disch, ofComponents
-/
def structurePresheafCompForget :
    structurePresheafInCommRing 𝒜 ⋙ forget CommRingCat ≅ (structureSheafInType 𝒜).1 :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by cat_disch)

end ProjectiveSpectrum.StructureSheaf

namespace ProjectiveSpectrum

open TopCat.Presheaf ProjectiveSpectrum.StructureSheaf Opens

/--
Definition of `Proj.structureSheaf` / `Proj.structureSheaf` 的定义

English:
definition Proj.structureSheaf
  signature: : Sheaf CommRingCat (ProjectiveSpectrum.top 𝒜)
  body: ⟨structurePresheafInCommRing 𝒜,
    (-- We check the sheaf condition under `forget CommRing`.
          isSheaf_iff_isSheaf_comp
          _ _).mpr
      (isSheaf_of_iso (structurePresheafCompForget 𝒜).symm (structureSheafInType 𝒜).property)⟩

中文:
定义 Proj.structureSheaf
  签名: : 层 交换环范畴 (射影谱.top 𝒜)
  定义体: ⟨structurePresheafInCommRing 𝒜,
    (-- We check the sheaf condition under `forget CommRing`.
          isSheaf_iff_isSheaf_comp
          _ _).mpr
      (isSheaf_of_iso (structurePresheafCompForget 𝒜).symm (structureSheafInType 𝒜).property)⟩

Depends on / 依赖: CommRing, condition, forget, isSheaf_iff_isSheaf_comp, isSheaf_of_iso, property, structurePresheafCompForget, structurePresheafInCommRing, structureSheafInType
-/
def Proj.structureSheaf : Sheaf CommRingCat (ProjectiveSpectrum.top 𝒜) :=
  ⟨structurePresheafInCommRing 𝒜,
    (-- We check the sheaf condition under `forget CommRing`.
          isSheaf_iff_isSheaf_comp
          _ _).mpr
      (isSheaf_of_iso (structurePresheafCompForget 𝒜).symm (structureSheafInType 𝒜).property)⟩

end ProjectiveSpectrum

section

open AlgebraicGeometry.ProjectiveSpectrum ProjectiveSpectrum.StructureSheaf Opens

section
variable {U V : (Opens (ProjectiveSpectrum.top 𝒜))ᵒᵖ} (i : V ⟶ U)
    (s t : (Proj.structureSheaf 𝒜).1.obj V) (x : V.unop)

@[simp]
/--
theorem `Proj.res_apply` / 定理 `Proj.res_apply`

English:
theorem Proj.res_apply
  given: (x)
  statement: ((Proj.structureSheaf 𝒜).1.map i s).1 x = s.1 (i.unop x)
  proof: rfl

中文:
定理 Proj.res_apply
  条件: (x)
  结论: ((Proj.structureSheaf 𝒜).1.map i s).1 x = s.1 (i.unop x)
  证明: rfl
-/
theorem Proj.res_apply (x) : ((Proj.structureSheaf 𝒜).1.map i s).1 x = s.1 (i.unop x) := rfl

/--
theorem `Proj.ext` / 定理 `Proj.ext`

English:
theorem Proj.ext
  given: (h : s.1 = t.1)
  statement: s = t
  proof: Subtype.ext h

中文:
定理 Proj.ext
  条件: (h : s.1 = t.1)
  结论: s = t
  证明: Subtype.ext h
-/
@[ext] theorem Proj.ext (h : s.1 = t.1) : s = t := Subtype.ext h
/--
theorem `Proj.add_apply` / 定理 `Proj.add_apply`

English:
theorem Proj.add_apply
  statement: (s + t).1 x = s.1 x + t.1 x
  proof: rfl

中文:
定理 Proj.add_apply
  结论: (s + t).1 x = s.1 x + t.1 x
  证明: rfl
-/
@[simp] theorem Proj.add_apply : (s + t).1 x = s.1 x + t.1 x := rfl
/--
theorem `Proj.mul_apply` / 定理 `Proj.mul_apply`

English:
theorem Proj.mul_apply
  statement: (s * t).1 x = s.1 x * t.1 x
  proof: rfl

中文:
定理 Proj.mul_apply
  结论: (s * t).1 x = s.1 x * t.1 x
  证明: rfl
-/
@[simp] theorem Proj.mul_apply : (s * t).1 x = s.1 x * t.1 x := rfl
/--
theorem `Proj.sub_apply` / 定理 `Proj.sub_apply`

English:
theorem Proj.sub_apply
  statement: (s - t).1 x = s.1 x - t.1 x
  proof: rfl

中文:
定理 Proj.sub_apply
  结论: (s - t).1 x = s.1 x - t.1 x
  证明: rfl
-/
@[simp] theorem Proj.sub_apply : (s - t).1 x = s.1 x - t.1 x := rfl
/--
theorem `Proj.pow_apply` / 定理 `Proj.pow_apply`

English:
theorem Proj.pow_apply
  given: (n : Nat)
  statement: (s ^ n).1 x = s.1 x ^ n
  proof: rfl

中文:
定理 Proj.pow_apply
  条件: (n : 自然数)
  结论: (s ^ n).1 x = s.1 x ^ n
  证明: rfl
-/
@[simp] theorem Proj.pow_apply (n : Nat) : (s ^ n).1 x = s.1 x ^ n := rfl
/--
theorem `Proj.zero_apply` / 定理 `Proj.zero_apply`

English:
theorem Proj.zero_apply
  statement: (0 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 0
  proof: rfl

中文:
定理 Proj.zero_apply
  结论: (0 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 0
  证明: rfl
-/
@[simp] theorem Proj.zero_apply : (0 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 0 := rfl
/--
theorem `Proj.one_apply` / 定理 `Proj.one_apply`

English:
theorem Proj.one_apply
  statement: (1 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 1
  proof: rfl

中文:
定理 Proj.one_apply
  结论: (1 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 1
  证明: rfl
-/
@[simp] theorem Proj.one_apply : (1 : (Proj.structureSheaf 𝒜).1.obj V).1 x = 1 := rfl

end

/--
Definition of `Proj.toSheafedSpace` / `Proj.toSheafedSpace` 的定义

English:
definition Proj.toSheafedSpace
  signature: : SheafedSpace CommRingCat where
  body: TopCat.of (ProjectiveSpectrum 𝒜)
  presheaf := (Proj.structureSheaf 𝒜).1
  IsSheaf := (Proj.structureSheaf 𝒜).2

中文:
定义 Proj.toSheafedSpace
  签名: : Sheafed空间 交换环范畴 where
  定义体: TopCat.of (ProjectiveSpectrum 𝒜)
  presheaf := (Proj.structureSheaf 𝒜).1
  IsSheaf := (Proj.structureSheaf 𝒜).2

Depends on / 依赖: ProjectiveSpectrum, TopCat, TopCat.of
-/
def Proj.toSheafedSpace : SheafedSpace CommRingCat where
  carrier := TopCat.of (ProjectiveSpectrum 𝒜)
  presheaf := (Proj.structureSheaf 𝒜).1
  IsSheaf := (Proj.structureSheaf 𝒜).2

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `openToLocalization` / `openToLocalization` 的定义

English:
definition openToLocalization
  signature: (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜)
  body: CommRingCat.ofHom
  { toFun s := (s.1 ⟨x, hx⟩ :)
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }

中文:
定义 openToLocalization
  签名: (U : Opens (射影谱.top 𝒜)) (x : 射影谱.top 𝒜)
  定义体: CommRingCat.ofHom
  { toFun s := (s.1 ⟨x, hx⟩ :)
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, map_add, map_mul, map_one, map_zero
-/
def openToLocalization (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜)
    (hx : x in U) : (Proj.structureSheaf 𝒜).1.obj (op U) ⟶ CommRingCat.of (at x) :=
  CommRingCat.ofHom
  { toFun s := (s.1 ⟨x, hx⟩ :)
    map_one' := rfl
    map_mul' _ _ := rfl
    map_zero' := rfl
    map_add' _ _ := rfl }

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `stalkToFiberRingHom` / `stalkToFiberRingHom` 的定义

English:
definition stalkToFiberRingHom
  signature: (x : ProjectiveSpectrum.top 𝒜)
  body: Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (Proj.structureSheaf 𝒜).1)
    { pt := _
      ι :=
        { app := fun U =>
            openToLocalization 𝒜 ((OpenNhds.inclusion _).obj U.unop) x U.unop.2 } }

@[simp]

中文:
定义 stalkToFiberRingHom
  签名: (x : 射影谱.top 𝒜)
  定义体: Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (Proj.structureSheaf 𝒜).1)
    { pt := _
      ι :=
        { app := fun U =>
            openToLocalization 𝒜 ((OpenNhds.inclusion _).obj U.unop) x U.unop.2 } }

@[simp]

Depends on / 依赖: Limits, Limits.colimit.desc, OpenNhds, OpenNhds.inclusion, Proj.structureSheaf, U.unop, colimit, inclusion, openToLocalization, structureSheaf
-/
def stalkToFiberRingHom (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ⟶ CommRingCat.of (at x) :=
  Limits.colimit.desc ((OpenNhds.inclusion x).op ⋙ (Proj.structureSheaf 𝒜).1)
    { pt := _
      ι :=
        { app := fun U =>
            openToLocalization 𝒜 ((OpenNhds.inclusion _).obj U.unop) x U.unop.2 } }

@[simp]
/--
theorem `germ_comp_stalkToFiberRingHom` / 定理 `germ_comp_stalkToFiberRingHom`

English:
theorem germ_comp_stalkToFiberRingHom
  proof: Limits.colimit.ι_desc _ _

@[simp]

中文:
定理 germ_comp_stalkToFiberRingHom
  证明: Limits.colimit.ι_desc _ _

@[simp]

Depends on / 依赖: Limits, Limits.colimit, colimit
-/
theorem germ_comp_stalkToFiberRingHom
    (U : Opens (ProjectiveSpectrum.top 𝒜)) (x : ProjectiveSpectrum.top 𝒜) (hx : x in U) :
    (Proj.structureSheaf 𝒜).presheaf.germ U x hx ≫ stalkToFiberRingHom 𝒜 x =
      openToLocalization 𝒜 U x hx :=
  Limits.colimit.ι_desc _ _

@[simp]
/--
theorem `stalkToFiberRingHom_germ` / 定理 `stalkToFiberRingHom_germ`

English:
theorem stalkToFiberRingHom_germ
  statement: (U : Opens (ProjectiveSpectrum.top 𝒜))
  proof: RingHom.ext_iff.1 (CommRingCat.hom_ext_iff.mp (germ_comp_stalkToFiberRingHom 𝒜 U x hx)) s

中文:
定理 stalkToFiberRingHom_germ
  结论: (U : Opens (射影谱.top 𝒜))
  证明: RingHom.ext_iff.1 (CommRingCat.hom_ext_iff.mp (germ_comp_stalkToFiberRingHom 𝒜 U x hx)) s

Depends on / 依赖: CommRingCat, CommRingCat.hom_ext_iff.mp, RingHom, RingHom.ext_iff, ext_iff, germ_comp_stalkToFiberRingHom, hom_ext_iff
-/
theorem stalkToFiberRingHom_germ (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x in U) (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    stalkToFiberRingHom 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ _ x hx s) = s.1 ⟨x, hx⟩ :=
  RingHom.ext_iff.1 (CommRingCat.hom_ext_iff.mp (germ_comp_stalkToFiberRingHom 𝒜 U x hx)) s

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_basicOpen_den` / 定理 `mem_basicOpen_den`

English:
theorem mem_basicOpen_den
  statement: (x : ProjectiveSpectrum.top 𝒜)
  proof: by
  rw [ProjectiveSpectrum.mem_basicOpen]
  exact f.den_mem

中文:
定理 mem_basicOpen_den
  结论: (x : 射影谱.top 𝒜)
  证明: by
  rw [ProjectiveSpectrum.mem_basicOpen]
  exact f.den_mem

Depends on / 依赖: ProjectiveSpectrum, ProjectiveSpectrum.mem_basicOpen, den_mem, f.den_mem, mem_basicOpen
-/
theorem mem_basicOpen_den (x : ProjectiveSpectrum.top 𝒜)
    (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl) :
    x in ProjectiveSpectrum.basicOpen 𝒜 f.den := by
  rw [ProjectiveSpectrum.mem_basicOpen]
  exact f.den_mem

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `sectionInBasicOpen` / `sectionInBasicOpen` 的定义

English:
definition sectionInBasicOpen
  signature: (x : ProjectiveSpectrum.top 𝒜)
  body: fun f =>
  ⟨fun y => HomogeneousLocalization.mk ⟨f.deg, f.num, f.den, y.2⟩, fun y =>
    ⟨ProjectiveSpectrum.basicOpen 𝒜 f.den, y.2,
      ⟨𝟙 _, ⟨f.deg, ⟨f.num, f.den, _, fun _ => rfl⟩⟩⟩⟩⟩

中文:
定义 sectionInBasicOpen
  签名: (x : 射影谱.top 𝒜)
  定义体: fun f =>
  ⟨fun y => HomogeneousLocalization.mk ⟨f.deg, f.num, f.den, y.2⟩, fun y =>
    ⟨ProjectiveSpectrum.basicOpen 𝒜 f.den, y.2,
      ⟨𝟙 _, ⟨f.deg, ⟨f.num, f.den, _, fun _ => rfl⟩⟩⟩⟩⟩

Depends on / 依赖: HomogeneousLocalization, HomogeneousLocalization.mk, ProjectiveSpectrum, ProjectiveSpectrum.basicOpen, basicOpen, f.deg, f.den, f.num
-/
def sectionInBasicOpen (x : ProjectiveSpectrum.top 𝒜) :
    forall f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.toIdeal.primeCompl,
    (Proj.structureSheaf 𝒜).1.obj (op (ProjectiveSpectrum.basicOpen 𝒜 f.den)) :=
  fun f =>
  ⟨fun y => HomogeneousLocalization.mk ⟨f.deg, f.num, f.den, y.2⟩, fun y =>
    ⟨ProjectiveSpectrum.basicOpen 𝒜 f.den, y.2,
      ⟨𝟙 _, ⟨f.deg, ⟨f.num, f.den, _, fun _ => rfl⟩⟩⟩⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
open HomogeneousLocalization in
/--
Definition of `homogeneousLocalizationToStalk` / `homogeneousLocalizationToStalk` 的定义

English:
definition homogeneousLocalizationToStalk
  signature: (x : ProjectiveSpectrum.top 𝒜) (y : at x)
  body: Quotient.liftOn' y (fun f =>
  (Proj.structureSheaf 𝒜).presheaf.germ _ x (mem_basicOpen_den _ x f) (sectionInBasicOpen _ x f))
  fun f g (e : f.embedding = g.embedding) => by
    simp only [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq,
      IsLocalization.eq_iff_exists x.asHomogeneousIdeal.toIdeal.primeCompl] at e
    obtain ⟨⟨c, hc⟩, hc'⟩ := e
    apply (Proj.structureSheaf 𝒜).presheaf.germ_ext
      (ProjectiveSpectrum.basicOpen 𝒜 f.den.1 ⊓
        ProjectiveSpectrum.basicOpen 𝒜 g.den.1 ⊓ ProjectiveSpectrum.basicOpen 𝒜 c)
      ⟨⟨mem_basicOpen_den _ x f, mem_basicOpen_den _ x g⟩, hc⟩
      (homOfLE inf_le_left ≫ homOfLE inf_le_left) (homOfLE inf_le_left ≫ homOfLE inf_le_right)
    apply Subtype.ext
    ext ⟨t, ⟨htf, htg⟩, ht'⟩
    rw [Proj.res_apply]; rw [Proj.res_apply]
    simp only [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq]
    apply (IsLocalization.map_units (M := t.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization t.asHomogeneousIdeal.toIdeal.primeCompl) ⟨c, ht'⟩).mul_left_cancel
    rw [← map_mul]; rw [← map_mul]; rw [hc']

中文:
定义 homogeneousLocalizationToStalk
  签名: (x : 射影谱.top 𝒜) (y : at x)
  定义体: Quotient.liftOn' y (fun f =>
  (Proj.structureSheaf 𝒜).presheaf.germ _ x (mem_basicOpen_den _ x f) (sectionInBasicOpen _ x f))
  fun f g (e : f.embedding = g.embedding) => by
    simp only [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq,
      IsLocalization.eq_iff_exists x.asHomogeneousIdeal.toIdeal.primeCompl] at e
    obtain ⟨⟨c, hc⟩, hc'⟩ := e
    apply (Proj.structureSheaf 𝒜).presheaf.germ_ext
      (ProjectiveSpectrum.basicOpen 𝒜 f.den.1 ⊓
        ProjectiveSpectrum.basicOpen 𝒜 g.den.1 ⊓ ProjectiveSpectrum.basicOpen 𝒜 c)
      ⟨⟨mem_basicOpen_den _ x f, mem_basicOpen_den _ x g⟩, hc⟩
      (homOfLE inf_le_left ≫ homOfLE inf_le_left) (homOfLE inf_le_left ≫ homOfLE inf_le_right)
    apply Subtype.ext
    ext ⟨t, ⟨htf, htg⟩, ht'⟩
    rw [Proj.res_apply]; rw [Proj.res_apply]
    simp only [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq]
    apply (IsLocalization.map_units (M := t.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization t.asHomogeneousIdeal.toIdeal.primeCompl) ⟨c, ht'⟩).mul_left_cancel
    rw [← map_mul]; rw [← map_mul]; rw [hc']

Depends on / 依赖: Quotient, Quotient.liftOn, liftOn
-/
def homogeneousLocalizationToStalk (x : ProjectiveSpectrum.top 𝒜) (y : at x) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x := Quotient.liftOn' y (fun f =>
  (Proj.structureSheaf 𝒜).presheaf.germ _ x (mem_basicOpen_den _ x f) (sectionInBasicOpen _ x f))
  fun f g (e : f.embedding = g.embedding) => by
    simp only [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq,
      IsLocalization.eq_iff_exists x.asHomogeneousIdeal.toIdeal.primeCompl] at e
    obtain ⟨⟨c, hc⟩, hc'⟩ := e
    apply (Proj.structureSheaf 𝒜).presheaf.germ_ext
      (ProjectiveSpectrum.basicOpen 𝒜 f.den.1 ⊓
        ProjectiveSpectrum.basicOpen 𝒜 g.den.1 ⊓ ProjectiveSpectrum.basicOpen 𝒜 c)
      ⟨⟨mem_basicOpen_den _ x f, mem_basicOpen_den _ x g⟩, hc⟩
      (homOfLE inf_le_left ≫ homOfLE inf_le_left) (homOfLE inf_le_left ≫ homOfLE inf_le_right)
    apply Subtype.ext
    ext ⟨t, ⟨htf, htg⟩, ht'⟩
    rw [Proj.res_apply]; rw [Proj.res_apply]
    simp only [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_iff_eq]
    apply (IsLocalization.map_units (M := t.asHomogeneousIdeal.toIdeal.primeCompl)
      (Localization t.asHomogeneousIdeal.toIdeal.primeCompl) ⟨c, ht'⟩).mul_left_cancel
    rw [← map_mul]; rw [← map_mul]; rw [hc']

/--
lemma `homogeneousLocalizationToStalk_stalkToFiberRingHom` / 引理 `homogeneousLocalizationToStalk_stalkToFiberRingHom`

English:
lemma homogeneousLocalizationToStalk_stalkToFiberRingHom
  given: (x z)
  proof: by
  obtain ⟨U, hxU, s, rfl⟩ := (Proj.structureSheaf 𝒜).presheaf.exists_germ_eq z
  change homogeneousLocalizationToStalk 𝒜 x ((stalkToFiberRingHom 𝒜 x).hom
      (((Proj.structureSheaf 𝒜).presheaf.germ U x hxU) s)) =
    ((Proj.structureSheaf 𝒜).presheaf.germ U x hxU) s
  obtain ⟨V, hxV, i, n, a, b, h, e⟩ := s.2 ⟨x, hxU⟩
  simp only [Subtype.forall, apply_mk] at e
  rw [stalkToFiberRingHom_germ]; rw [homogeneousLocalizationToStalk]; rw [e x hxV]; rw [Quotient.liftOn'_mk'']
  refine Presheaf.germ_ext (C := CommRingCat) _ V hxV (homOfLE <| fun _ h' => h ⟨_, h'⟩) i ?_
  change ((Proj.structureSheaf 𝒜).presheaf.map (homOfLE <| fun _ h' => h ⟨_, h'⟩).op) _ =
    ((Proj.structureSheaf 𝒜).presheaf.map i.op) s
  apply Subtype.ext
  ext ⟨t, ht⟩
  rw [Proj.res_apply]; rw [Proj.res_apply]
  simp [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk', e t ht]

中文:
引理 homogeneousLocalizationToStalk_stalkToFiberRingHom
  条件: (x z)
  证明: by
  obtain ⟨U, hxU, s, rfl⟩ := (Proj.structureSheaf 𝒜).presheaf.exists_germ_eq z
  change homogeneousLocalizationToStalk 𝒜 x ((stalkToFiberRingHom 𝒜 x).hom
      (((Proj.structureSheaf 𝒜).presheaf.germ U x hxU) s)) =
    ((Proj.structureSheaf 𝒜).presheaf.germ U x hxU) s
  obtain ⟨V, hxV, i, n, a, b, h, e⟩ := s.2 ⟨x, hxU⟩
  simp only [Subtype.forall, apply_mk] at e
  rw [stalkToFiberRingHom_germ]; rw [homogeneousLocalizationToStalk]; rw [e x hxV]; rw [Quotient.liftOn'_mk'']
  refine Presheaf.germ_ext (C := CommRingCat) _ V hxV (homOfLE <| fun _ h' => h ⟨_, h'⟩) i ?_
  change ((Proj.structureSheaf 𝒜).presheaf.map (homOfLE <| fun _ h' => h ⟨_, h'⟩).op) _ =
    ((Proj.structureSheaf 𝒜).presheaf.map i.op) s
  apply Subtype.ext
  ext ⟨t, ht⟩
  rw [Proj.res_apply]; rw [Proj.res_apply]
  simp [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk', e t ht]

Depends on / 依赖: CommRingCa, Presheaf, Presheaf.germ_ext, Proj.structureSheaf, Quotient, Quotient.liftOn, Subtype, Subtype.forall, apply_mk, exists_germ_eq, germ_ext, homogeneousLocalizationToStalk, liftOn, presheaf, presheaf.exists_germ_eq, presheaf.germ, stalkToFiberRingHom, stalkToFiberRingHom_germ, structureSheaf
-/
lemma homogeneousLocalizationToStalk_stalkToFiberRingHom (x z) :
    homogeneousLocalizationToStalk 𝒜 x (stalkToFiberRingHom 𝒜 x z) = z := by
  obtain ⟨U, hxU, s, rfl⟩ := (Proj.structureSheaf 𝒜).presheaf.exists_germ_eq z
  change homogeneousLocalizationToStalk 𝒜 x ((stalkToFiberRingHom 𝒜 x).hom
      (((Proj.structureSheaf 𝒜).presheaf.germ U x hxU) s)) =
    ((Proj.structureSheaf 𝒜).presheaf.germ U x hxU) s
  obtain ⟨V, hxV, i, n, a, b, h, e⟩ := s.2 ⟨x, hxU⟩
  simp only [Subtype.forall, apply_mk] at e
  rw [stalkToFiberRingHom_germ]; rw [homogeneousLocalizationToStalk]; rw [e x hxV]; rw [Quotient.liftOn'_mk'']
  refine Presheaf.germ_ext (C := CommRingCat) _ V hxV (homOfLE <| fun _ h' => h ⟨_, h'⟩) i ?_
  change ((Proj.structureSheaf 𝒜).presheaf.map (homOfLE <| fun _ h' => h ⟨_, h'⟩).op) _ =
    ((Proj.structureSheaf 𝒜).presheaf.map i.op) s
  apply Subtype.ext
  ext ⟨t, ht⟩
  rw [Proj.res_apply]; rw [Proj.res_apply]
  simp [sectionInBasicOpen, HomogeneousLocalization.val_mk, Localization.mk_eq_mk', e t ht]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `stalkToFiberRingHom_homogeneousLocalizationToStalk` / 引理 `stalkToFiberRingHom_homogeneousLocalizationToStalk`

English:
lemma stalkToFiberRingHom_homogeneousLocalizationToStalk
  given: (x z)
  proof: by
  obtain ⟨z, rfl⟩ := Quotient.mk''_surjective z
  rw [homogeneousLocalizationToStalk]; rw [Quotient.liftOn'_mk'']; rw [stalkToFiberRingHom_germ]; rw [sectionInBasicOpen]

中文:
引理 stalkToFiberRingHom_homogeneousLocalizationToStalk
  条件: (x z)
  证明: by
  obtain ⟨z, rfl⟩ := Quotient.mk''_surjective z
  rw [homogeneousLocalizationToStalk]; rw [Quotient.liftOn'_mk'']; rw [stalkToFiberRingHom_germ]; rw [sectionInBasicOpen]

Depends on / 依赖: Quotient, Quotient.liftOn, Quotient.mk, _surjective, homogeneousLocalizationToStalk, liftOn, sectionInBasicOpen, stalkToFiberRingHom_germ
-/
lemma stalkToFiberRingHom_homogeneousLocalizationToStalk (x z) :
    stalkToFiberRingHom 𝒜 x (homogeneousLocalizationToStalk 𝒜 x z) = z := by
  obtain ⟨z, rfl⟩ := Quotient.mk''_surjective z
  rw [homogeneousLocalizationToStalk]; rw [Quotient.liftOn'_mk'']; rw [stalkToFiberRingHom_germ]; rw [sectionInBasicOpen]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Proj.stalkIso'` / `Proj.stalkIso'` 的定义

English:
definition Proj.stalkIso'
  signature: (x : ProjectiveSpectrum.top 𝒜)
  body: (stalkToFiberRingHom _ x).hom
  invFun := homogeneousLocalizationToStalk 𝒜 x
  left_inv := homogeneousLocalizationToStalk_stalkToFiberRingHom 𝒜 x
  right_inv := stalkToFiberRingHom_homogeneousLocalizationToStalk 𝒜 x

@[simp]

中文:
定义 Proj.stalkIso'
  签名: (x : 射影谱.top 𝒜)
  定义体: (stalkToFiberRingHom _ x).hom
  invFun := homogeneousLocalizationToStalk 𝒜 x
  left_inv := homogeneousLocalizationToStalk_stalkToFiberRingHom 𝒜 x
  right_inv := stalkToFiberRingHom_homogeneousLocalizationToStalk 𝒜 x

@[simp]

Depends on / 依赖: stalkToFiberRingHom
-/
def Proj.stalkIso' (x : ProjectiveSpectrum.top 𝒜) :
    (Proj.structureSheaf 𝒜).presheaf.stalk x ≃+* at x where
  __ := (stalkToFiberRingHom _ x).hom
  invFun := homogeneousLocalizationToStalk 𝒜 x
  left_inv := homogeneousLocalizationToStalk_stalkToFiberRingHom 𝒜 x
  right_inv := stalkToFiberRingHom_homogeneousLocalizationToStalk 𝒜 x

@[simp]
/--
theorem `Proj.stalkIso'_germ` / 定理 `Proj.stalkIso'_germ`

English:
theorem Proj.stalkIso'_germ
  statement: (U : Opens (ProjectiveSpectrum.top 𝒜))
  proof: stalkToFiberRingHom_germ 𝒜 U x hx s

@[simp]

中文:
定理 Proj.stalkIso'_germ
  结论: (U : Opens (射影谱.top 𝒜))
  证明: stalkToFiberRingHom_germ 𝒜 U x hx s

@[simp]
-/
theorem Proj.stalkIso'_germ (U : Opens (ProjectiveSpectrum.top 𝒜))
    (x : ProjectiveSpectrum.top 𝒜) (hx : x in U) (s : (Proj.structureSheaf 𝒜).1.obj (op U)) :
    Proj.stalkIso' 𝒜 x ((Proj.structureSheaf 𝒜).presheaf.germ _ x hx s) = s.1 ⟨x, hx⟩ :=
  stalkToFiberRingHom_germ 𝒜 U x hx s

@[simp]
/--
theorem `Proj.stalkIso'_symm_mk` / 定理 `Proj.stalkIso'_symm_mk`

English:
theorem Proj.stalkIso'_symm_mk
  given: (x) (f)
  proof: rfl

中文:
定理 Proj.stalkIso'_symm_mk
  条件: (x) (f)
  证明: rfl
-/
theorem Proj.stalkIso'_symm_mk (x) (f) :
    (Proj.stalkIso' 𝒜 x).symm (.mk f) = (Proj.structureSheaf 𝒜).presheaf.germ _
      x (mem_basicOpen_den _ x f) (sectionInBasicOpen _ x f) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Proj.toLocallyRingedSpace` / `Proj.toLocallyRingedSpace` 的定义

English:
definition Proj.toLocallyRingedSpace
  signature: : LocallyRingedSpace
  body: { Proj.toSheafedSpace 𝒜 with
    isLocalRing := fun x =>
      @RingEquiv.isLocalRing _ _ _ (show IsLocalRing (at x) from inferInstance) _
        (Proj.stalkIso' 𝒜 x).symm }

中文:
定义 Proj.toLocallyRingedSpace
  签名: : LocallyRinged空间
  定义体: { Proj.toSheafedSpace 𝒜 with
    isLocalRing := fun x =>
      @RingEquiv.isLocalRing _ _ _ (show IsLocalRing (at x) from inferInstance) _
        (Proj.stalkIso' 𝒜 x).symm }

Depends on / 依赖: IsLocalRing, Proj.stalkIso, Proj.toSheafedSpace, RingEquiv, RingEquiv.isLocalRing, isLocalRing, stalkIso, toSheafedSpace
-/
def Proj.toLocallyRingedSpace : LocallyRingedSpace :=
  { Proj.toSheafedSpace 𝒜 with
    isLocalRing := fun x =>
      @RingEquiv.isLocalRing _ _ _ (show IsLocalRing (at x) from inferInstance) _
        (Proj.stalkIso' 𝒜 x).symm }

end

end AlgebraicGeometry
