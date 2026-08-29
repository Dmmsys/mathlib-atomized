/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Ideal.Height

/-!
# Basic properties of schemes

We provide some basic properties of schemes

## Main definition
* `AlgebraicGeometry.IsIntegral`: A scheme is integral if it is nontrivial and all nontrivial
  components of the structure sheaf are integral domains.
* `AlgebraicGeometry.IsReduced`: A scheme is reduced if all the components of the structure sheaf
  are reduced.
-/

public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737

universe u

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits TopCat Topology

namespace AlgebraicGeometry

variable (X : Scheme)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T0Space X
  body: T0Space.of_open_cover fun x => ⟨_, X.affineCover.covers x,
    (X.affineCover.f _).opensRange.2, IsEmbedding.t0Space (Y := PrimeSpectrum _)
    (isAffineOpen_opensRange (X.affineCover.f _)).isoSpec.schemeIsoToHomeo.isEmbedding⟩

中文:
实例 :
  签名: T0Space X
  定义体: T0Space.of_open_cover fun x => ⟨_, X.affineCover.covers x,
    (X.affineCover.f _).opensRange.2, IsEmbedding.t0Space (Y := PrimeSpectrum _)
    (isAffineOpen_opensRange (X.affineCover.f _)).isoSpec.schemeIsoToHomeo.isEmbedding⟩

Depends on / 依赖: IsEmbedding, IsEmbedding.t0Space, PrimeSpectrum, T0Space, T0Space.of_open_cover, X.affineCover.covers, X.affineCover.f, affineCover, covers, isAffineOpen_opensRange, isEmbedding, isoSpec, isoSpec.schemeIsoToHomeo.isEmbedding, of_open_cover, opensRange, schemeIsoToHomeo, t0Space
-/
instance : T0Space X :=
  T0Space.of_open_cover fun x => ⟨_, X.affineCover.covers x,
    (X.affineCover.f _).opensRange.2, IsEmbedding.t0Space (Y := PrimeSpectrum _)
    (isAffineOpen_opensRange (X.affineCover.f _)).isoSpec.schemeIsoToHomeo.isEmbedding⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: QuasiSober X
  body: by
  apply +allowSynthFailures
    quasiSober_of_open_cover (Set.range fun x => Set.range <| (X.affineCover.f x))
  · rintro ⟨_, i, rfl⟩; exact (X.affineCover.f i).isOpenEmbedding.isOpen_range
  · rintro ⟨_, i, rfl⟩
    exact @IsOpenEmbedding.quasiSober _ _ _ _ _
      (X.affineCover.f i).isOpenEmbe

中文:
实例 :
  签名: QuasiSober X
  定义体: by
  apply +allowSynthFailures
    quasiSober_of_open_cover (Set.range fun x => Set.range <| (X.affineCover.f x))
  · rintro ⟨_, i, rfl⟩; exact (X.affineCover.f i).isOpenEmbedding.isOpen_range
  · rintro ⟨_, i, rfl⟩
    exact @IsOpenEmbedding.quasiSober _ _ _ _ _
      (X.affineCover.f i).isOpenEmbe

Depends on / 依赖: IsOpenEmbedding, IsOpenEmbedding.quasiSober, PrimeSpectrum, PrimeSpectrum.quasiSober, Set.eq_univ_iff_forall, Set.range, Set.sUnion_range, Set.top_eq_univ, X.affineCover.covers, X.affineCover.f, affineCover, allowSynthFailures, covers, eq_univ_iff_forall, isEmbedding, isOpenEmbedding, isOpenEmbedding.isEmbedding.toHomeomorph.symm.isOpenEmbedding, isOpenEmbedding.isOpen_range, isOpen_range, quasiSober
-/
instance : QuasiSober X := by
  apply +allowSynthFailures
    quasiSober_of_open_cover (Set.range fun x => Set.range <| (X.affineCover.f x))
  · rintro ⟨_, i, rfl⟩; exact (X.affineCover.f i).isOpenEmbedding.isOpen_range
  · rintro ⟨_, i, rfl⟩
    exact @IsOpenEmbedding.quasiSober _ _ _ _ _
      (X.affineCover.f i).isOpenEmbedding.isEmbedding.toHomeomorph.symm.isOpenEmbedding
        PrimeSpectrum.quasiSober
  · rw [Set.top_eq_univ, Set.sUnion_range, Set.eq_univ_iff_forall]
    intro x; exact ⟨_, ⟨_, rfl⟩, X.affineCover.covers x⟩

instance {X : Scheme.{u}} : PrespectralSpace X :=
  have (Y : Scheme.{u}) (_ : IsAffine Y) : PrespectralSpace Y :=
    .of_isClosedEmbedding (Y := PrimeSpectrum _) _
      Y.isoSpec.hom.homeomorph.isClosedEmbedding
  have (i : _) : PrespectralSpace (X.affineCover.f i).opensRange.1 :=
    this (X.affineCover.f i).opensRange (isAffineOpen_opensRange (X.affineCover.f i))
  .of_isOpenCover X.affineCover.isOpenCover_opensRange

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IrreducibleSpace ·)
  body: ⟨fun e => e.hom.homeomorph.irreducibleSpace_iff.mp⟩

中文:
实例 :
  签名: Object命题erty.IsClosedUnderIsomorphisms (C := Scheme) (IrreducibleSpace ·)
  定义体: ⟨fun e => e.hom.homeomorph.irreducibleSpace_iff.mp⟩

Depends on / 依赖: IrreducibleSpace, Scheme
-/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IrreducibleSpace ·) :=
  ⟨fun e => e.hom.homeomorph.irreducibleSpace_iff.mp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (ConnectedSpace ·)
  body: ⟨fun e => e.hom.homeomorph.connectedSpace_iff.mp⟩

中文:
实例 :
  签名: Object命题erty.IsClosedUnderIsomorphisms (C := Scheme) (ConnectedSpace ·)
  定义体: ⟨fun e => e.hom.homeomorph.connectedSpace_iff.mp⟩

Depends on / 依赖: ConnectedSpace, Scheme
-/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (ConnectedSpace ·) :=
  ⟨fun e => e.hom.homeomorph.connectedSpace_iff.mp⟩

/--
Definition of `IsReduced` / `IsReduced` 的定义

English:
class IsReduced
  parameters: : Prop where
  axioms and operations (1):
    - component_reduced : forall U, _root_.IsReduced Γ(X, U)  [default: by infer_instance]

中文:
类 IsReduced
  参数: : 命题 where
  公理与运算 (1 个):
    - component_reduced : 对任意 U, _root_.IsReduced Γ(X, U)  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsReduced : Prop where
  component_reduced : forall U, _root_.IsReduced Γ(X, U) := by infer_instance

attribute [instance] IsReduced.component_reduced

/--
theorem `isReduced_of_isReduced_stalk` / 定理 `isReduced_of_isReduced_stalk`

English:
theorem isReduced_of_isReduced_stalk
  given: [forall x : X, _root_.IsReduced (X.presheaf.stalk x)]
  proof: by
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  apply Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  change X.presheaf.germ U x hx s = 0
  exact (hs.map _).eq_zero

中文:
定理 isReduced_of_isReduced_stalk
  条件: [对任意 x : X, _root_.IsReduced (X.presheaf.stalk x)]
  证明: by
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  apply Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  change X.presheaf.germ U x hx s = 0
  exact (hs.map _).eq_zero

Depends on / 依赖: Presheaf, Presheaf.section_ext, X.presheaf.germ, X.sheaf, X.sheaf.presheaf.germ, eq_zero, hs.map, map_zero, presheaf, section_ext
-/
theorem isReduced_of_isReduced_stalk [forall x : X, _root_.IsReduced (X.presheaf.stalk x)] :
    IsReduced X := by
  refine ⟨fun U => ⟨fun s hs => ?_⟩⟩
  apply Presheaf.section_ext X.sheaf U s 0
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  change X.presheaf.germ U x hx s = 0
  exact (hs.map _).eq_zero

/--
Instance `isReduced_stalk_of_isReduced` / 实例 `isReduced_stalk_of_isReduced`

English:
instance isReduced_stalk_of_isReduced
  signature: [IsReduced X] (x : X)
  body: by
  constructor
  rintro g ⟨n, e⟩
  obtain ⟨U, hxU, s, (rfl : (X.presheaf.germ U x hxU) s = g)⟩ := X.presheaf.exists_germ_eq g
  rw [← map_pow]; rw [← map_zero (X.presheaf.germ _ x hxU).hom] at e
  obtain ⟨V, hxV, iU, iV, (e' : (X.presheaf.map iU.op) (s ^ n) = (X.presheaf.map iV.op) 0)⟩ :=
    X.pr

中文:
实例 isReduced_stalk_of_isReduced
  签名: [IsReduced X] (x : X)
  定义体: by
  constructor
  rintro g ⟨n, e⟩
  obtain ⟨U, hxU, s, (rfl : (X.presheaf.germ U x hxU) s = g)⟩ := X.presheaf.exists_germ_eq g
  rw [← map_pow]; rw [← map_zero (X.presheaf.germ _ x hxU).hom] at e
  obtain ⟨V, hxV, iU, iV, (e' : (X.presheaf.map iU.op) (s ^ n) = (X.presheaf.map iV.op) 0)⟩ :=
    X.pr

Depends on / 依赖: CommRingCat, CommRingCat.comp_apply, IsNilpotent, IsNilpotent.mk, X.presheaf.exists_germ_eq, X.presheaf.germ, X.presheaf.germ_eq, X.presheaf.germ_res, X.presheaf.map, comp_apply, eq_zero, exists_germ_eq, germ_eq, germ_res, iU.op, iV.op, map_pow, map_zero, presheaf, replace
-/
instance isReduced_stalk_of_isReduced [IsReduced X] (x : X) :
    _root_.IsReduced (X.presheaf.stalk x) := by
  constructor
  rintro g ⟨n, e⟩
  obtain ⟨U, hxU, s, (rfl : (X.presheaf.germ U x hxU) s = g)⟩ := X.presheaf.exists_germ_eq g
  rw [← map_pow]; rw [← map_zero (X.presheaf.germ _ x hxU).hom] at e
  obtain ⟨V, hxV, iU, iV, (e' : (X.presheaf.map iU.op) (s ^ n) = (X.presheaf.map iV.op) 0)⟩ :=
    X.presheaf.germ_eq x hxU hxU _ 0 e
  rw [map_pow]; rw [map_zero] at e'
  replace e' := (IsNilpotent.mk _ _ e').eq_zero (R := Γ(X, V))
  rw [← X.presheaf.germ_res iU x hxV]; rw [CommRingCat.comp_apply]; rw [e']; rw [map_zero]

/--
theorem `isReduced_of_isOpenImmersion` / 定理 `isReduced_of_isOpenImmersion`

English:
theorem isReduced_of_isOpenImmersion
  statement: {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: by
  constructor
  intro U
  rw [← f.preimage_image_eq U]
  exact isReduced_of_injective (inv <| f.app (f ''ᵁ U)).hom
    (asIso <| f.app (f ''ᵁ U) : Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.injective

中文:
定理 isReduced_of_isOpenImmersion
  结论: {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
  证明: by
  constructor
  intro U
  rw [← f.preimage_image_eq U]
  exact isReduced_of_injective (inv <| f.app (f ''ᵁ U)).hom
    (asIso <| f.app (f ''ᵁ U) : Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.injective

Depends on / 依赖: commRingCatIsoToRingEquiv, f.app, f.preimage_image_eq, injective, isReduced_of_injective, preimage_image_eq, symm.commRingCatIsoToRingEquiv.injective
-/
theorem isReduced_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsReduced Y] : IsReduced X := by
  constructor
  intro U
  rw [← f.preimage_image_eq U]
  exact isReduced_of_injective (inv <| f.app (f ''ᵁ U)).hom
    (asIso <| f.app (f ''ᵁ U) : Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.injective

instance {X : Scheme} {U : X.Opens} [IsReduced X] : IsReduced U :=
    isReduced_of_isOpenImmersion U.ι

instance {𝒰 : X.OpenCover} [IsReduced X] (i : 𝒰.I₀) : IsReduced (𝒰.X i) :=
  isReduced_of_isOpenImmersion (𝒰.f i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IsReduced ·)
  body: ⟨fun e _ => isReduced_of_isOpenImmersion e.inv⟩

中文:
实例 :
  签名: Object命题erty.IsClosedUnderIsomorphisms (C := Scheme) (IsReduced ·)
  定义体: ⟨fun e _ => isReduced_of_isOpenImmersion e.inv⟩

Depends on / 依赖: IsReduced, Scheme
-/
instance : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) (IsReduced ·) :=
  ⟨fun e _ => isReduced_of_isOpenImmersion e.inv⟩

set_option backward.isDefEq.respectTransparency.types false in
instance {R : CommRingCat.{u}} [H : _root_.IsReduced R] : IsReduced (Spec R) := by
  apply +allowSynthFailures isReduced_of_isReduced_stalk
  intro x
  have : _root_.IsReduced (CommRingCat.of <| Localization.AtPrime (PrimeSpectrum.asIdeal x)) := by
    dsimp; infer_instance
  exact isReduced_of_injective (Spec.stalkIso R x).hom.hom
    (Spec.stalkIso R x).commRingCatIsoToRingEquiv.injective

/--
theorem `affine_isReduced_iff` / 定理 `affine_isReduced_iff`

English:
theorem affine_isReduced_iff
  given: (R : CommRingCat)
  proof: by
  refine ⟨?_, fun h => inferInstance⟩
  intro h
  exact isReduced_of_injective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective

中文:
定理 affine_isReduced_iff
  条件: (R : CommRingCat)
  证明: by
  refine ⟨?_, fun h => inferInstance⟩
  intro h
  exact isReduced_of_injective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective

Depends on / 依赖: Scheme, commRingCatIsoToRingEquiv, injective, inv.hom, isReduced_of_injective, symm.commRingCatIsoToRingEquiv.injective
-/
theorem affine_isReduced_iff (R : CommRingCat) :
    IsReduced (Spec R) ↔ _root_.IsReduced R := by
  refine ⟨?_, fun h => inferInstance⟩
  intro h
  exact isReduced_of_injective (Scheme.ΓSpecIso R).inv.hom
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.injective

/--
theorem `isReduced_of_isAffine_isReduced` / 定理 `isReduced_of_isAffine_isReduced`

English:
theorem isReduced_of_isAffine_isReduced
  given: [IsAffine X] [_root_.IsReduced Γ(X, ⊤)]
  proof: isReduced_of_isOpenImmersion X.isoSpec.hom

中文:
定理 isReduced_of_isAffine_isReduced
  条件: [IsAffine X] [_root_.IsReduced Γ(X, ⊤)]
  证明: isReduced_of_isOpenImmersion X.isoSpec.hom

Depends on / 依赖: X.isoSpec.hom, isReduced_of_isOpenImmersion, isoSpec
-/
theorem isReduced_of_isAffine_isReduced [IsAffine X] [_root_.IsReduced Γ(X, ⊤)] :
    IsReduced X :=
  isReduced_of_isOpenImmersion X.isoSpec.hom

/--
theorem `IsReduced.of_openCover` / 定理 `IsReduced.of_openCover`

English:
theorem IsReduced.of_openCover
  given: (𝒰 : X.OpenCover) [forall i, IsReduced (𝒰.X i)]
  statement: IsReduced X
  proof: by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    exact isReduced_of_injective _
      (asIso <| (𝒰.f i).stalkMap x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

中文:
定理 IsReduced.of_openCover
  条件: (𝒰 : X.OpenCover) [对任意 i, IsReduced (𝒰.X i)]
  结论: IsReduced X
  证明: by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    exact isReduced_of_injective _
      (asIso <| (𝒰.f i).stalkMap x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

Depends on / 依赖: IsReduced, X.presheaf.stalk, _root_, _root_.IsReduced, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.injective, exists_eq, injective, isReduced_of_injective, isReduced_of_isReduced_stalk, presheaf, stalkMap
-/
theorem IsReduced.of_openCover (𝒰 : X.OpenCover) [forall i, IsReduced (𝒰.X i)] : IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq x
    exact isReduced_of_injective _
      (asIso <| (𝒰.f i).stalkMap x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk _

/--
theorem `IsReduced.iff_of_openCover` / 定理 `IsReduced.iff_of_openCover`

English:
theorem IsReduced.iff_of_openCover
  given: (𝒰 : X.OpenCover)
  statement: IsReduced X ↔ forall i, IsReduced (𝒰.X i)
  proof: ⟨fun _ => inferInstance, fun _ => of_openCover X 𝒰⟩

中文:
定理 IsReduced.iff_of_openCover
  条件: (𝒰 : X.OpenCover)
  结论: IsReduced X ↔ 对任意 i, IsReduced (𝒰.X i)
  证明: ⟨fun _ => inferInstance, fun _ => of_openCover X 𝒰⟩

Depends on / 依赖: of_openCover
-/
theorem IsReduced.iff_of_openCover (𝒰 : X.OpenCover) : IsReduced X ↔ forall i, IsReduced (𝒰.X i) :=
  ⟨fun _ => inferInstance, fun _ => of_openCover X 𝒰⟩

/-- To show that a statement `P` holds for all open subsets of all schemes, it suffices to show that
1. In any scheme `X`, if `P` holds for an open cover of `U`, then `P` holds for `U`.
2. For an open immersion `f : X ⟶ Y`, if `P` holds for the entire space of `X`, then `P` holds for
  the image of `f`.
3. `P` holds for the entire space of an affine scheme.
-/
@[elab_as_elim]
/--
theorem `reduce_to_affine_global` / 定理 `reduce_to_affine_global`

English:
theorem reduce_to_affine_global
  statement: (P : forall {X : Scheme} (_ : X.Opens), Prop)
  proof: by
  apply h₁
  intro x
  obtain ⟨_, ⟨j, rfl⟩, hx, i⟩ :=
    X.affineBasisCover_is_basis.exists_subset_of_mem_open (SetLike.mem_coe.2 x.prop) U.isOpen
  let U' : Opens _ := ⟨_, (X.affineBasisCover.f j).isOpenEmbedding.isOpen_range⟩
  let i' : U' ⟶ U := homOfLE i
  refine ⟨U', hx, i', ?_⟩
  obtain ⟨_

中文:
定理 reduce_to_affine_global
  结论: (P : 对任意 {X : Scheme} (_ : X.Opens), 命题)
  证明: by
  apply h₁
  intro x
  obtain ⟨_, ⟨j, rfl⟩, hx, i⟩ :=
    X.affineBasisCover_is_basis.exists_subset_of_mem_open (SetLike.mem_coe.2 x.prop) U.isOpen
  let U' : Opens _ := ⟨_, (X.affineBasisCover.f j).isOpenEmbedding.isOpen_range⟩
  let i' : U' ⟶ U := homOfLE i
  refine ⟨U', hx, i', ?_⟩
  obtain ⟨_

Depends on / 依赖: SetLike, SetLike.mem_coe, U.isOpen, X.affineBasisCover.f, X.affineBasisCover_is_basis.exists_subset_of_mem_open, affineBasisCover, affineBasisCover_is_basis, exists_subset_of_mem_open, homOfLE, isOpen, isOpenEmbedding, isOpenEmbedding.isOpen_range, isOpen_range, mem_coe, x.prop
-/
theorem reduce_to_affine_global (P : forall {X : Scheme} (_ : X.Opens), Prop)
    {X : Scheme} (U : X.Opens)
    (h₁ : forall (X : Scheme) (U : X.Opens),
      (forall x : U, exists (V : _) (_ : x.1 in V) (_ : V ⟶ U), P V) -> P U)
    (h₂ : forall (X Y) (f : X ⟶ Y) [IsOpenImmersion f],
      exists (U : X.Opens) (V : Y.Opens), U = ⊤ ∧ V = f.opensRange ∧ (P U -> P V))
    (h₃ : forall R : CommRingCat, P (X := Spec R) ⊤) : P U := by
  apply h₁
  intro x
  obtain ⟨_, ⟨j, rfl⟩, hx, i⟩ :=
    X.affineBasisCover_is_basis.exists_subset_of_mem_open (SetLike.mem_coe.2 x.prop) U.isOpen
  let U' : Opens _ := ⟨_, (X.affineBasisCover.f j).isOpenEmbedding.isOpen_range⟩
  let i' : U' ⟶ U := homOfLE i
  refine ⟨U', hx, i', ?_⟩
  obtain ⟨_, _, rfl, rfl, h₂'⟩ := h₂ _ _ (X.affineBasisCover.f j)
  apply h₂'
  apply h₃

/--
theorem `reduce_to_affine_nbhd` / 定理 `reduce_to_affine_nbhd`

English:
theorem reduce_to_affine_nbhd
  statement: (P : forall (X : Scheme) (_ : X), Prop)
  proof: by
  intro X x
  obtain ⟨y, e⟩ := X.affineCover.covers x
  convert! h₂ (X.affineCover.f (X.affineCover.idx x)) y _
  · rw [e]
  apply h₁

中文:
定理 reduce_to_affine_nbhd
  结论: (P : 对任意 (X : Scheme) (_ : X), 命题)
  证明: by
  intro X x
  obtain ⟨y, e⟩ := X.affineCover.covers x
  convert! h₂ (X.affineCover.f (X.affineCover.idx x)) y _
  · rw [e]
  apply h₁

Depends on / 依赖: X.affineCover.covers, X.affineCover.f, X.affineCover.idx, affineCover, convert, covers
-/
theorem reduce_to_affine_nbhd (P : forall (X : Scheme) (_ : X), Prop)
    (h₁ : forall R x, P (Spec R) x)
    (h₂ : forall {X Y} (f : X ⟶ Y) [IsOpenImmersion f] (x : X), P X x -> P Y (f x)) :
    forall (X : Scheme) (x : X), P X x := by
  intro X x
  obtain ⟨y, e⟩ := X.affineCover.covers x
  convert! h₂ (X.affineCover.f (X.affineCover.idx x)) y _
  · rw [e]
  apply h₁

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eq_zero_of_basicOpen_eq_bot` / 定理 `eq_zero_of_basicOpen_eq_bot`

English:
theorem eq_zero_of_basicOpen_eq_bot
  statement: {X : Scheme} [hX : IsReduced X] {U : X.Opens}
  proof: by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  induction U using reduce_to_affine_global generalizing hX with
  | h₁ X U H =>
    obtain ⟨V, hx, i, H⟩ := H ⟨x, hx⟩
    specialize H (X.preshe

中文:
定理 eq_zero_of_basicOpen_eq_bot
  结论: {X : Scheme} [hX : IsReduced X] {U : X.Opens}
  证明: by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  induction U using reduce_to_affine_global generalizing hX with
  | h₁ X U H =>
    obtain ⟨V, hx, i, H⟩ := H ⟨x, hx⟩
    specialize H (X.preshe

Depends on / 依赖: Presheaf, Scheme, Scheme.basicOpen_res, TopCat, TopCat.Presheaf.section_ext, X.presheaf.map, X.sheaf, X.sheaf.presheaf.germ, X.sheaf.presheaf.germ_res_apply, basicOpen_res, f.opensRange, generalizing, germ_res_apply, i.op, inf_bot_eq, map_zero, opensRange, presheaf, reduce_to_affine_global, section_ext
-/
theorem eq_zero_of_basicOpen_eq_bot {X : Scheme} [hX : IsReduced X] {U : X.Opens}
    (s : Γ(X, U)) (hs : X.basicOpen s = ⊥) : s = 0 := by
  apply TopCat.Presheaf.section_ext X.sheaf U
  intro x hx
  change (X.sheaf.presheaf.germ U x hx) s = (X.sheaf.presheaf.germ U x hx) 0
  rw [map_zero]
  induction U using reduce_to_affine_global generalizing hX with
  | h₁ X U H =>
    obtain ⟨V, hx, i, H⟩ := H ⟨x, hx⟩
    specialize H (X.presheaf.map i.op s)
    rw [Scheme.basicOpen_res]; rw [hs] at H
    specialize H (inf_bot_eq _) x hx
    rw [← X.sheaf.presheaf.germ_res_apply i x hx s]
    exact H
  | h₂ X Y f =>
    refine ⟨f ⁻¹ᵁ f.opensRange, f.opensRange, by simp, rfl, ?_⟩
    rintro H hX s hs _ ⟨x, rfl⟩
    have := isReduced_of_isOpenImmersion f
    specialize H (f.app _ s) _ x ⟨x, rfl⟩
    · rw [← Scheme.preimage_basicOpen, hs]; ext1; simp [Opens.map]
    · have H : (X.presheaf.germ _ x _).hom _ = 0 := H
      rw [← Scheme.Hom.germ_stalkMap_apply f ⟨_]; rw [_⟩ x] at H
apply_fun inv f.stalkMap x at H
      rw [← CommRingCat.comp_apply]; rw [CategoryTheory.IsIso.hom_inv_id]; rw [map_zero] at H
      exact H
  | h₃ R =>
    rw [basicOpen_eq_of_affine']; rw [PrimeSpectrum.basicOpen_eq_bot_iff] at hs
    replace hs := (hs.map (Scheme.ΓSpecIso R).inv.hom).eq_zero
    rw [← CommRingCat.comp_apply]; rw [Iso.hom_inv_id]; rw [CommRingCat.id_apply] at hs
    rw [hs]; rw [map_zero]

@[simp]
/--
theorem `basicOpen_eq_bot_iff` / 定理 `basicOpen_eq_bot_iff`

English:
theorem basicOpen_eq_bot_iff
  statement: {X : Scheme} [IsReduced X] {U : X.Opens}
  proof: by
  refine ⟨eq_zero_of_basicOpen_eq_bot s, ?_⟩
  rintro rfl
  simp

中文:
定理 basicOpen_eq_bot_iff
  结论: {X : Scheme} [IsReduced X] {U : X.Opens}
  证明: by
  refine ⟨eq_zero_of_basicOpen_eq_bot s, ?_⟩
  rintro rfl
  simp

Depends on / 依赖: eq_zero_of_basicOpen_eq_bot
-/
theorem basicOpen_eq_bot_iff {X : Scheme} [IsReduced X] {U : X.Opens}
    (s : Γ(X, U)) : X.basicOpen s = ⊥ ↔ s = 0 := by
  refine ⟨eq_zero_of_basicOpen_eq_bot s, ?_⟩
  rintro rfl
  simp

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `isField_stalk_of_closure_mem_irreducibleComponents` / 引理 `isField_stalk_of_closure_mem_irreducibleComponents`

English:
lemma isField_stalk_of_closure_mem_irreducibleComponents
  proof: by
  wlog hX : exists R, X = Spec R
  · obtain ⟨i, x, rfl⟩ := X.affineCover.exists_eq x
    have inst : IsReduced (X.affineCover.X i) := isReduced_of_isOpenImmersion (X.affineCover.f i)
    refine (asIso <| (X.affineCover.f i).stalkMap x).commRingCatIsoToRingEquiv.isField
      (this _ x ?_ ⟨_, rfl⟩

中文:
引理 isField_stalk_of_closure_mem_irreducibleComponents
  证明: by
  wlog hX : exists R, X = Spec R
  · obtain ⟨i, x, rfl⟩ := X.affineCover.exists_eq x
    have inst : IsReduced (X.affineCover.X i) := isReduced_of_isOpenImmersion (X.affineCover.f i)
    refine (asIso <| (X.affineCover.f i).stalkMap x).commRingCatIsoToRingEquiv.isField
      (this _ x ?_ ⟨_, rfl⟩

Depends on / 依赖: IsReduced, Set.image_singleton, X.affineCover.X, X.affineCover.exists_eq, X.affineCover.f, affineCover, closure_eq_preimage_closure_image, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.isField, exists_eq, image_singleton, isField, isOpenEmbedding, isOpenEmbedding.closure_eq_preimage_closure_image, isReduced_of_isOpenImmersion, preimage_mem_irreducibleComponents, stalkMap, subset_closur
-/
lemma isField_stalk_of_closure_mem_irreducibleComponents
    (x : X) (hx : closure {x} in irreducibleComponents X) [IsReduced X] :
    IsField (X.presheaf.stalk x) := by
  wlog hX : exists R, X = Spec R
  · obtain ⟨i, x, rfl⟩ := X.affineCover.exists_eq x
    have inst : IsReduced (X.affineCover.X i) := isReduced_of_isOpenImmersion (X.affineCover.f i)
    refine (asIso <| (X.affineCover.f i).stalkMap x).commRingCatIsoToRingEquiv.isField
      (this _ x ?_ ⟨_, rfl⟩)
    rw [(X.affineCover.f i).isOpenEmbedding.closure_eq_preimage_closure_image]; rw [Set.image_singleton]
    exact preimage_mem_irreducibleComponents hx (X.affineCover.f i).isOpenEmbedding
      ⟨X.affineCover.f i x, subset_closure rfl, _, rfl⟩
  obtain ⟨R, rfl⟩ := hX
  replace hx : x.asIdeal in minimalPrimes R := by
    rwa [← PrimeSpectrum.vanishingIdeal_singleton, PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]
  rw [← PrimeSpectrum.subsingleton_iff_isField_of_isReduced]
  exact IsLocalization.subsingleton_primeSpectrum_of_mem_minimalPrimes _ hx
    ((Spec.structureSheaf R).presheaf.stalk x)

/--
Definition of `IsIntegral` / `IsIntegral` 的定义

English:
class IsIntegral
  parameters: : Prop where
  axioms and operations (2):
    - nonempty : Nonempty X  [default: by infer_instance]
    - component_integral : forall (U : X.Opens) [Nonempty U], IsDomain Γ(X, U)  [default: by infer_instance]

中文:
类 IsIntegral
  参数: : 命题 where
  公理与运算 (2 个):
    - nonempty : Nonempty X  [默认: by infer_instance]
    - component_integral : 对任意 (U : X.Opens) [Nonempty U], IsDomain Γ(X, U)  [默认: by infer_instance]

Depends on / 依赖: IsDomain, Nonempty, X.Opens, component_integral, infer_instance
-/
class IsIntegral : Prop where
  nonempty : Nonempty X := by infer_instance
  component_integral : forall (U : X.Opens) [Nonempty U], IsDomain Γ(X, U) := by infer_instance

attribute [instance] IsIntegral.component_integral IsIntegral.nonempty

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIntegral
  signature: X] : IsDomain Γ(X, ⊤)
  body: @IsIntegral.component_integral _ _ _ ⟨Nonempty.some inferInstance, trivial⟩

中文:
实例 [IsIntegral
  签名: X] : IsDomain Γ(X, ⊤)
  定义体: @IsIntegral.component_integral _ _ _ ⟨Nonempty.some inferInstance, trivial⟩

Depends on / 依赖: IsIntegral, IsIntegral.component_integral, Nonempty, Nonempty.some, component_integral
-/
instance [IsIntegral X] : IsDomain Γ(X, ⊤) :=
  @IsIntegral.component_integral _ _ _ ⟨Nonempty.some inferInstance, trivial⟩

instance (priority := 900) isReduced_of_isIntegral [IsIntegral X] : IsReduced X := by
  constructor
  intro U
  rcases U.1.eq_empty_or_nonempty with h | h
  · have : U = ⊥ := SetLike.ext' h
    have : Subsingleton Γ(X, U) :=
      CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty this)
    infer_instance
  · have : Nonempty U := by simpa
    infer_instance

/--
Instance `Scheme.component_nontrivial` / 实例 `Scheme.component_nontrivial`

English:
instance Scheme.component_nontrivial
  signature: (X : Scheme.{u}) (U : X.Opens) [Nonempty U]
  body: LocallyRingedSpace.component_nontrivial (hU := ‹_›)

中文:
实例 Scheme.component_nontrivial
  签名: (X : Scheme.{u}) (U : X.Opens) [Nonempty U]
  定义体: LocallyRingedSpace.component_nontrivial (hU := ‹_›)

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.component_nontrivial, component_nontrivial
-/
instance Scheme.component_nontrivial (X : Scheme.{u}) (U : X.Opens) [Nonempty U] :
    Nontrivial Γ(X, U) :=
  LocallyRingedSpace.component_nontrivial (hU := ‹_›)

/--
Instance `irreducibleSpace_of_isIntegral` / 实例 `irreducibleSpace_of_isIntegral`

English:
instance irreducibleSpace_of_isIntegral
  signature: [IsIntegral X]
  body: by
  by_contra H
  replace H : ¬IsPreirreducible .univ := fun h =>
    H { toPreirreducibleSpace := ⟨h⟩
        toNonempty := inferInstance }
  simp_rw [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at H
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  rw [Set.not_univ_subset] at h₂ 

中文:
实例 irreducibleSpace_of_isIntegral
  签名: [Is整数egral X]
  定义体: by
  by_contra H
  replace H : ¬IsPreirreducible .univ := fun h =>
    H { toPreirreducibleSpace := ⟨h⟩
        toNonempty := inferInstance }
  simp_rw [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at H
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  rw [Set.not_univ_subset] at h₂ 

Depends on / 依赖: IsPreirreducible, Nonempty, Or.inl, Set.not_univ_subset, X.Opens, choose_spec, isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or, not_univ_subset, replace, simp_rw, toNonempty, toPreirreducibleSpace
-/
instance irreducibleSpace_of_isIntegral [IsIntegral X] : IrreducibleSpace X := by
  by_contra H
  replace H : ¬IsPreirreducible .univ := fun h =>
    H { toPreirreducibleSpace := ⟨h⟩
        toNonempty := inferInstance }
  simp_rw [isPreirreducible_iff_isClosed_union_isClosed, not_forall, not_or] at H
  rcases H with ⟨S, T, hS, hT, h₁, h₂, h₃⟩
  rw [Set.not_univ_subset] at h₂ h₃
  have : Nonempty (⟨Sᶜ, hS.1⟩ : X.Opens) := ⟨⟨_, h₂.choose_spec⟩⟩
  have : Nonempty (⟨Tᶜ, hT.1⟩ : X.Opens) := ⟨⟨_, h₃.choose_spec⟩⟩
  have : Nonempty (⟨Sᶜ, hS.1⟩ ⊔ ⟨Tᶜ, hT.1⟩ : X.Opens) := ⟨⟨_, Or.inl h₂.choose_spec⟩⟩
  let e : Γ(X, _) ≅ CommRingCat.of _ :=
    (X.sheaf.isProductOfDisjoint ⟨_, hS.1⟩ ⟨_, hT.1⟩ ?_).conePointUniqueUpToIso
      (CommRingCat.prodFanIsLimit _ _)
  · have : IsDomain (Γ(X, ⟨Sᶜ, hS.1⟩) × Γ(X, ⟨Tᶜ, hT.1⟩)) :=
      e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
    exact false_of_nontrivial_of_product_domain Γ(X, ⟨Sᶜ, hS.1⟩) Γ(X, ⟨Tᶜ, hT.1⟩)
  · ext x
    constructor
    · rintro ⟨hS, hT⟩
      rcases h₁ (show x in ⊤ by trivial) with h | h
      exacts [hS h, hT h]
    · simp

/--
theorem `isIntegral_of_irreducibleSpace_of_isReduced` / 定理 `isIntegral_of_irreducibleSpace_of_isReduced`

English:
theorem isIntegral_of_irreducibleSpace_of_isReduced
  given: [IsReduced X] [H : IrreducibleSpace X]
  proof: by
  constructor; · infer_instance
  intro U hU
  have := (@LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace U hU).1
  have : NoZeroDivisors
      (X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf.obj (op U)) := by
    refine ⟨fun {a b} e => ?_⟩
    simp_rw [← basicOpen

中文:
定理 isIntegral_of_irreducibleSpace_of_isReduced
  条件: [IsReduced X] [H : IrreducibleSpace X]
  证明: by
  constructor; · infer_instance
  intro U hU
  have := (@LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace U hU).1
  have : NoZeroDivisors
      (X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf.obj (op U)) := by
    refine ⟨fun {a b} e => ?_⟩
    simp_rw [← basicOpen

Depends on / 依赖: LocallyRingedSpace, LocallyRingedSpace.component_nontrivial, NoZeroDivisors, Opens.not_nonempty_iff_eq_bot, X.basicOpen, X.presheaf.germ, X.toLocallyRingedSpace, X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf.obj, basicOpen, basicOpen_eq_bot_iff, component_nontrivial, congr_arg, infer_instance, nonempty_preirreducible_inter, not_nonempty_iff_eq_bot, presheaf, replace, simp_rw, toLocallyRingedSpace, toPresheafedSpace
-/
theorem isIntegral_of_irreducibleSpace_of_isReduced [IsReduced X] [H : IrreducibleSpace X] :
    IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  have := (@LocallyRingedSpace.component_nontrivial X.toLocallyRingedSpace U hU).1
  have : NoZeroDivisors
      (X.toLocallyRingedSpace.toSheafedSpace.toPresheafedSpace.presheaf.obj (op U)) := by
    refine ⟨fun {a b} e => ?_⟩
    simp_rw [← basicOpen_eq_bot_iff, ← Opens.not_nonempty_iff_eq_bot]
    by_contra! h
    obtain ⟨x, ⟨hxU, hx₁⟩, _, hx₂⟩ :=
      nonempty_preirreducible_inter (X.basicOpen a).2 (X.basicOpen b).2 h.1 h.2
    replace e := congr_arg (X.presheaf.germ U x hxU) e
    rw [map_mul]; rw [map_zero] at e
    refine zero_ne_one' (X.presheaf.stalk x) (isUnit_zero_iff.1 ?_)
    convert! hx₁.mul hx₂
    exact e.symm
  exact NoZeroDivisors.to_isDomain _

/--
theorem `isIntegral_iff_irreducibleSpace_and_isReduced` / 定理 `isIntegral_iff_irreducibleSpace_and_isReduced`

English:
theorem isIntegral_iff_irreducibleSpace_and_isReduced
  proof: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isIntegral_of_irreducibleSpace_of_isReduced X⟩

中文:
定理 isIntegral_iff_irreducibleSpace_and_isReduced
  证明: ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isIntegral_of_irreducibleSpace_of_isReduced X⟩

Depends on / 依赖: isIntegral_of_irreducibleSpace_of_isReduced
-/
theorem isIntegral_iff_irreducibleSpace_and_isReduced :
    IsIntegral X ↔ IrreducibleSpace X ∧ IsReduced X :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ =>
    isIntegral_of_irreducibleSpace_of_isReduced X⟩

/--
theorem `isIntegral_of_isOpenImmersion` / 定理 `isIntegral_of_isOpenImmersion`

English:
theorem isIntegral_of_isOpenImmersion
  statement: {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
  proof: by
  constructor; · infer_instance
  intro U hU
  rw [← f.preimage_image_eq U]
  have : IsDomain Γ(Y, f ''ᵁ U) := by
    apply +allowSynthFailures IsIntegral.component_integral
    exact ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact (asIso <| f.app (f ''ᵁ U) :
    Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingE

中文:
定理 isIntegral_of_isOpenImmersion
  结论: {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
  证明: by
  constructor; · infer_instance
  intro U hU
  rw [← f.preimage_image_eq U]
  have : IsDomain Γ(Y, f ''ᵁ U) := by
    apply +allowSynthFailures IsIntegral.component_integral
    exact ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact (asIso <| f.app (f ''ᵁ U) :
    Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingE

Depends on / 依赖: IsDomain, IsIntegral, IsIntegral.component_integral, allowSynthFailures, commRingCatIsoToRingEquiv, component_integral, f.app, f.preimage_image_eq, hU.some.prop, infer_instance, isDomain, preimage_image_eq, symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain, toMulEquiv
-/
theorem isIntegral_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    [IsIntegral Y] [Nonempty X] : IsIntegral X := by
  constructor; · infer_instance
  intro U hU
  rw [← f.preimage_image_eq U]
  have : IsDomain Γ(Y, f ''ᵁ U) := by
    apply +allowSynthFailures IsIntegral.component_integral
    exact ⟨⟨_, _, hU.some.prop, rfl⟩⟩
  exact (asIso <| f.app (f ''ᵁ U) :
    Γ(Y, f ''ᵁ U) ≅ _).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _

/--
lemma `IsIntegral.of_isIso` / 引理 `IsIntegral.of_isIso`

English:
lemma IsIntegral.of_isIso
  given: {X Y : Scheme.{u}} [h : IsIntegral X] (f : X ⟶ Y) [IsIso f]
  proof: by
  suffices Nonempty Y from isIntegral_of_isOpenImmersion (inv f)
  exact Nonempty.map f inferInstance

中文:
引理 IsIntegral.of_isIso
  条件: {X Y : Scheme.{u}} [h : Is整数egral X] (f : X ⟶ Y) [IsIso f]
  证明: by
  suffices Nonempty Y from isIntegral_of_isOpenImmersion (inv f)
  exact Nonempty.map f inferInstance

Depends on / 依赖: Nonempty, Nonempty.map, isIntegral_of_isOpenImmersion
-/
lemma IsIntegral.of_isIso {X Y : Scheme.{u}} [h : IsIntegral X] (f : X ⟶ Y) [IsIso f] :
    IsIntegral Y := by
  suffices Nonempty Y from isIntegral_of_isOpenImmersion (inv f)
  exact Nonempty.map f inferInstance

instance {R : CommRingCat} [IsDomain R] : IrreducibleSpace (Spec R) := by
  convert! PrimeSpectrum.irreducibleSpace (R := R)

instance {R : CommRingCat} [IsDomain R] : IsIntegral (Spec R) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

/--
theorem `affine_isIntegral_iff` / 定理 `affine_isIntegral_iff`

English:
theorem affine_isIntegral_iff
  given: (R : CommRingCat)
  proof: ⟨fun _ => MulEquiv.isDomain Γ(Spec R, ⊤)
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.toMulEquiv, fun _ => inferInstance⟩

中文:
定理 affine_isIntegral_iff
  条件: (R : CommRingCat)
  证明: ⟨fun _ => MulEquiv.isDomain Γ(Spec R, ⊤)
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.toMulEquiv, fun _ => inferInstance⟩

Depends on / 依赖: MulEquiv, MulEquiv.isDomain, Scheme, commRingCatIsoToRingEquiv, isDomain, symm.commRingCatIsoToRingEquiv.toMulEquiv, toMulEquiv
-/
theorem affine_isIntegral_iff (R : CommRingCat) :
    IsIntegral (Spec R) ↔ IsDomain R :=
  ⟨fun _ => MulEquiv.isDomain Γ(Spec R, ⊤)
    (Scheme.ΓSpecIso R).symm.commRingCatIsoToRingEquiv.toMulEquiv, fun _ => inferInstance⟩

/--
theorem `isIntegral_of_isAffine_of_isDomain` / 定理 `isIntegral_of_isAffine_of_isDomain`

English:
theorem isIntegral_of_isAffine_of_isDomain
  given: [IsAffine X] [Nonempty X] [IsDomain Γ(X, ⊤)]
  proof: isIntegral_of_isOpenImmersion X.isoSpec.hom

中文:
定理 isIntegral_of_isAffine_of_isDomain
  条件: [IsAffine X] [Nonempty X] [IsDomain Γ(X, ⊤)]
  证明: isIntegral_of_isOpenImmersion X.isoSpec.hom

Depends on / 依赖: X.isoSpec.hom, isIntegral_of_isOpenImmersion, isoSpec
-/
theorem isIntegral_of_isAffine_of_isDomain [IsAffine X] [Nonempty X] [IsDomain Γ(X, ⊤)] :
    IsIntegral X :=
  isIntegral_of_isOpenImmersion X.isoSpec.hom

/--
theorem `map_injective_of_isIntegral` / 定理 `map_injective_of_isIntegral`

English:
theorem map_injective_of_isIntegral
  statement: [IsIntegral X] {U V : X.Opens} (i : U ⟶ V)
  proof: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← basicOpen_eq_bot_iff] at hx ⊢
  rw [Scheme.basicOpen_res] at hx
  revert hx
  contrapose!
  simp_rw [Ne, ← Opens.not_nonempty_iff_eq_bot, Classical.not_not]
  apply nonempty_preirreducible_inter U.isOpen (RingedSpace.basicOpen _ _).isOpen
  si

中文:
定理 map_injective_of_isIntegral
  结论: [Is整数egral X] {U V : X.Opens} (i : U ⟶ V)
  证明: by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← basicOpen_eq_bot_iff] at hx ⊢
  rw [Scheme.basicOpen_res] at hx
  revert hx
  contrapose!
  simp_rw [Ne, ← Opens.not_nonempty_iff_eq_bot, Classical.not_not]
  apply nonempty_preirreducible_inter U.isOpen (RingedSpace.basicOpen _ _).isOpen
  si

Depends on / 依赖: Classical, Classical.not_not, Opens.not_nonempty_iff_eq_bot, RingedSpace, RingedSpace.basicOpen, Scheme, Scheme.basicOpen_res, U.isOpen, basicOpen, basicOpen_eq_bot_iff, basicOpen_res, contrapose, injective_iff_map_eq_zero, isOpen, nonempty_preirreducible_inter, not_nonempty_iff_eq_bot, not_not, revert, simp_rw
-/
theorem map_injective_of_isIntegral [IsIntegral X] {U V : X.Opens} (i : U ⟶ V)
    [H : Nonempty U] : Function.Injective (X.presheaf.map i.op) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← basicOpen_eq_bot_iff] at hx ⊢
  rw [Scheme.basicOpen_res] at hx
  revert hx
  contrapose!
  simp_rw [Ne, ← Opens.not_nonempty_iff_eq_bot, Classical.not_not]
  apply nonempty_preirreducible_inter U.isOpen (RingedSpace.basicOpen _ _).isOpen
  simpa using H

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsIntegral
  signature: X] : OrderTop X where
  body: genericPoint X
  le_top a := genericPoint_specializes a

中文:
实例 [IsIntegral
  签名: X] : OrderTop X where
  定义体: genericPoint X
  le_top a := genericPoint_specializes a

Depends on / 依赖: genericPoint
-/
instance [IsIntegral X] : OrderTop X where
  top := genericPoint X
  le_top a := genericPoint_specializes a

open IrreducibleCloseds Set in
@[stacks 02I4]
/--
lemma `coheight_eq_of_isOpenImmersion` / 引理 `coheight_eq_of_isOpenImmersion`

English:
lemma coheight_eq_of_isOpenImmersion
  given: {U X : Scheme} {x : U} (f : U ⟶ X) [IsOpenImmersion f]
  proof: f.isOpenEmbedding.coheight_eq

中文:
引理 coheight_eq_of_isOpenImmersion
  条件: {U X : Scheme} {x : U} (f : U ⟶ X) [IsOpenImmersion f]
  证明: f.isOpenEmbedding.coheight_eq

Depends on / 依赖: coheight_eq, f.isOpenEmbedding.coheight_eq, isOpenEmbedding
-/
lemma coheight_eq_of_isOpenImmersion {U X : Scheme} {x : U} (f : U ⟶ X) [IsOpenImmersion f] :
    Order.coheight (f.base x) = Order.coheight x := f.isOpenEmbedding.coheight_eq

set_option backward.isDefEq.respectTransparency.types false in
open Order in
/--
lemma `idealHeight_eq_coheight` / 引理 `idealHeight_eq_coheight`

English:
lemma idealHeight_eq_coheight
  given: (R : CommRingCat) (x : Spec R)
  proof: by
  rw [PrimeSpectrum.height_eq_orderHeight]; rw [← Order.coheight_orderIso (specOrderIsoPrimeSpectrum R)]; rw [← height_ofDual]; rw [specOrderIsoPrimeSpectrum_apply]; rw [OrderDual.ofDual_toDual]

中文:
引理 idealHeight_eq_coheight
  条件: (R : CommRingCat) (x : Spec R)
  证明: by
  rw [PrimeSpectrum.height_eq_orderHeight]; rw [← Order.coheight_orderIso (specOrderIsoPrimeSpectrum R)]; rw [← height_ofDual]; rw [specOrderIsoPrimeSpectrum_apply]; rw [OrderDual.ofDual_toDual]

Depends on / 依赖: Order.coheight_orderIso, OrderDual, OrderDual.ofDual_toDual, PrimeSpectrum, PrimeSpectrum.height_eq_orderHeight, coheight_orderIso, height_eq_orderHeight, height_ofDual, ofDual_toDual, specOrderIsoPrimeSpectrum, specOrderIsoPrimeSpectrum_apply
-/
lemma idealHeight_eq_coheight (R : CommRingCat) (x : Spec R) :
    x.asIdeal.height = coheight x := by
  rw [PrimeSpectrum.height_eq_orderHeight]; rw [← Order.coheight_orderIso (specOrderIsoPrimeSpectrum R)]; rw [← height_ofDual]; rw [specOrderIsoPrimeSpectrum_apply]; rw [OrderDual.ofDual_toDual]

set_option backward.isDefEq.respectTransparency.types false in
open Order in
@[stacks 02IZ]
/--
lemma `ringKrullDim_stalk_eq_coheight` / 引理 `ringKrullDim_stalk_eq_coheight`

English:
lemma ringKrullDim_stalk_eq_coheight
  given: {X : Scheme} (x : X)
  proof: by
  wlog h : exists R, X = Spec R
  · obtain ⟨R, f, hf, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (show x in ⊤ from trivial)
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hsub.1
    rw [coheight_eq_of_isOpenImmersion]; rw [← this _ ⟨R]; rw [rfl⟩]
    exact Order.krullDim_eq_of_orderI

中文:
引理 ringKrullDim_stalk_eq_coheight
  条件: {X : Scheme} (x : X)
  证明: by
  wlog h : exists R, X = Spec R
  · obtain ⟨R, f, hf, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (show x in ⊤ from trivial)
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hsub.1
    rw [coheight_eq_of_isOpenImmersion]; rw [← this _ ⟨R]; rw [rfl⟩]
    exact Order.krullDim_eq_of_orderI

Depends on / 依赖: Algebra, IsLocalization, IsLocalization.AtP, Order.krullDim_eq_of_orderIso, PrimeSpectrum, PrimeSpectrum.comapEquiv, Scheme, Scheme.Hom.stalkMap, Scheme.exists_affine_mem_range_and_range_subset, Set.mem_range.mp, StructureSheaf, StructureSheaf.stalkAlgebra, coheight_eq_of_isOpenImmersion, comapEquiv, commRingCatIsoToRingEquiv, exists_affine_mem_range_and_range_subset, krullDim_eq_of_orderIso, mem_range, presheaf, presheaf.stalk
-/
lemma ringKrullDim_stalk_eq_coheight {X : Scheme} (x : X) :
    ringKrullDim (X.presheaf.stalk x) = coheight x := by
  wlog h : exists R, X = Spec R
  · obtain ⟨R, f, hf, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (show x in ⊤ from trivial)
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hsub.1
    rw [coheight_eq_of_isOpenImmersion]; rw [← this _ ⟨R]; rw [rfl⟩]
    exact Order.krullDim_eq_of_orderIso
      (PrimeSpectrum.comapEquiv (asIso (Scheme.Hom.stalkMap f y)).commRingCatIsoToRingEquiv)
  obtain ⟨R, rfl⟩ := h
  let k : Algebra ↑R ↑((Spec R).presheaf.stalk x) := StructureSheaf.stalkAlgebra (↑R) x
  have : IsLocalization.AtPrime (↑((Spec R).presheaf.stalk x)) x.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R x
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height x.asIdeal ((Spec R).presheaf.stalk x)]
  apply WithBot.coe_eq_coe.mpr
  exact idealHeight_eq_coheight R x

open Order in
variable {X} in
/--
lemma `krullDimLE_of_coheight_le` / 引理 `krullDimLE_of_coheight_le`

English:
lemma krullDimLE_of_coheight_le
  proof: by
  rw [Ring.krullDimLE_iff]; rw [ringKrullDim_stalk_eq_coheight z]
  exact_mod_cast hz

中文:
引理 krullDimLE_of_coheight_le
  证明: by
  rw [Ring.krullDimLE_iff]; rw [ringKrullDim_stalk_eq_coheight z]
  exact_mod_cast hz

Depends on / 依赖: Ring.krullDimLE_iff, krullDimLE_iff, ringKrullDim_stalk_eq_coheight
-/
lemma krullDimLE_of_coheight_le
    {z : X} {n : Nat} (hz : coheight z <= n) : Ring.KrullDimLE n (X.presheaf.stalk z) := by
  rw [Ring.krullDimLE_iff]; rw [ringKrullDim_stalk_eq_coheight z]
  exact_mod_cast hz

/--
lemma `isField_of_isIntegral_of_subsingleton` / 引理 `isField_of_isIntegral_of_subsingleton`

English:
lemma isField_of_isIntegral_of_subsingleton
  given: (X : Scheme.{u}) [IsIntegral X] [Subsingleton X]
  proof: by
  rw [← PrimeSpectrum.t1Space_iff_isField]
  apply X.isoSpec.hom.homeomorph.t1Space

中文:
引理 isField_of_isIntegral_of_subsingleton
  条件: (X : Scheme.{u}) [Is整数egral X] [Subsingleton X]
  证明: by
  rw [← PrimeSpectrum.t1Space_iff_isField]
  apply X.isoSpec.hom.homeomorph.t1Space

Depends on / 依赖: PrimeSpectrum, PrimeSpectrum.t1Space_iff_isField, X.isoSpec.hom.homeomorph.t1Space, homeomorph, isoSpec, t1Space, t1Space_iff_isField
-/
lemma isField_of_isIntegral_of_subsingleton (X : Scheme.{u}) [IsIntegral X] [Subsingleton X] :
    IsField Γ(X, ⊤) := by
  rw [← PrimeSpectrum.t1Space_iff_isField]
  apply X.isoSpec.hom.homeomorph.t1Space

end AlgebraicGeometry
