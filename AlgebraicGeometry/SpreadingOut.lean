/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Spreading out morphisms

Under certain conditions, a morphism on stalks `Spec 𝒪_{X, x} ⟶ Spec 𝒪_{Y, y}` can be spread
out into a neighborhood of `x`.

## Main result
Given `S`-schemes `X Y` and points `x : X` `y : Y` over `s : S`.
Suppose we have the following diagram of `S`-schemes
```
Spec 𝒪_{X, x} ⟶ X
    |
  Spec(φ)
    ↓
Spec 𝒪_{Y, y} ⟶ Y
```
We would like to spread `Spec(φ)` out to an `S`-morphism on an open subscheme `U ⊆ X`
```
Spec 𝒪_{X, x} ⟶ U ⊆ X
    | |
  Spec(φ) |
    ↓ ↓
Spec 𝒪_{Y, y} ⟶ Y
```
- `AlgebraicGeometry.spread_out_unique_of_isGermInjective`:
  The lift is "unique" if the germ map is injective at `x`.
- `AlgebraicGeometry.spread_out_of_isGermInjective`:
  The lift exists if `Y` is locally of finite type and the germ map is injective at `x`.

## TODO

Show that certain morphism properties can also be spread out.

-/

public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}} (f : X ⟶ Y) (sX : X ⟶ S) (sY : Y ⟶ S) {R A : CommRingCat.{u}}

/--
Definition of `Scheme.IsGermInjectiveAt` / `Scheme.IsGermInjectiveAt` 的定义

English:
class Scheme.IsGermInjectiveAt
  parameters: (X : Scheme.{u}) (x : X)
  axioms and operations (1):
    - cond : exists (U : X.Opens) (hx : x in U), IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx)

中文:
类 概形.是GermInjectiveAt
  参数: (X : 概形.{u}) (x : X)
  公理与运算 (1 个):
    - cond : 存在 (U : X.Opens) (hx : x in U), 是仿射开集 U ∧ 函数.单射 (X.presheaf.germ U x hx)
-/
class Scheme.IsGermInjectiveAt (X : Scheme.{u}) (x : X) : Prop where
  cond : exists (U : X.Opens) (hx : x in U), IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx)

/--
lemma `injective_germ_basicOpen` / 引理 `injective_germ_basicOpen`

English:
lemma injective_germ_basicOpen
  statement: (U : X.Opens) (hU : IsAffineOpen U)
  proof: by
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero] at H ⊢
  intro t ht
  have := hU.isLocalization_basicOpen f
  obtain ⟨t, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) t
  rw [← RingHom.mem_ker]; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [Ideal.mul_unit_mem_iff_

中文:
引理 injective_germ_basicOpen
  结论: (U : X.Opens) (hU : 是仿射开集 U)
  证明: by
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero] at H ⊢
  intro t ht
  have := hU.isLocalization_basicOpen f
  obtain ⟨t, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) t
  rw [← RingHom.mem_ker]; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [Ideal.mul_unit_mem_iff_

Depends on / 依赖: Ideal.mul_unit_mem_iff_mem, IsLoca, IsLocalization, IsLocalization.exists_mk, IsLocalization.invertible_mk, IsLocalization.mk, Presheaf, RingHom, RingHom.algebraMap_toAlgebra, RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero, RingHom.mem_ker, TopCat, TopCat.Presheaf.germ_res_apply, _eq_mul_mk, _one, algebraMap_toAlgebra, exists_mk, germ_res_apply, hU.isLocalization_basicOpen
-/
lemma injective_germ_basicOpen (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x in U) (f : Γ(X, U))
    (hf : x in X.basicOpen f)
    (H : Function.Injective (X.presheaf.germ U x hx)) :
    Function.Injective (X.presheaf.germ (X.basicOpen f) x hf) := by
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero] at H ⊢
  intro t ht
  have := hU.isLocalization_basicOpen f
  obtain ⟨t, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers f) t
  rw [← RingHom.mem_ker]; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [Ideal.mul_unit_mem_iff_mem]; rw [RingHom.mem_ker]; rw [RingHom.algebraMap_toAlgebra]; rw [TopCat.Presheaf.germ_res_apply] at ht
  swap; · exact @isUnit_of_invertible _ _ _ (@IsLocalization.invertible_mk'_one ..)
  rw [H _ ht]; rw [IsLocalization.mk'_zero]

/--
lemma `Scheme.exists_germ_injective` / 引理 `Scheme.exists_germ_injective`

English:
lemma Scheme.exists_germ_injective
  given: (X : Scheme.{u}) (x : X) [X.IsGermInjectiveAt x]
  proof: Scheme.IsGermInjectiveAt.cond

中文:
引理 概形.存在_germ_injective
  条件: (X : 概形.{u}) (x : X) [X.是GermInjectiveAt x]
  证明: Scheme.IsGermInjectiveAt.cond

Depends on / 依赖: IsGermInjectiveAt, Scheme, Scheme.IsGermInjectiveAt.cond
-/
lemma Scheme.exists_germ_injective (X : Scheme.{u}) (x : X) [X.IsGermInjectiveAt x] :
    exists (U : X.Opens) (hx : x in U),
      IsAffineOpen U ∧ Function.Injective (X.presheaf.germ U x hx) :=
  Scheme.IsGermInjectiveAt.cond

/--
lemma `Scheme.exists_le_and_germ_injective` / 引理 `Scheme.exists_le_and_germ_injective`

English:
lemma Scheme.exists_le_and_germ_injective
  statement: (X : Scheme.{u}) (x : X) [X.IsGermInjectiveAt x]
  proof: by
  obtain ⟨U, hx, hU, H⟩ := Scheme.IsGermInjectiveAt.cond (x := x)
  obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  exact ⟨X.basicOpen f, hxf, hU.basicOpen f, hf, injective_germ_basicOpen U hU x hx f hxf H⟩

中文:
引理 概形.存在_le_and_germ_injective
  结论: (X : 概形.{u}) (x : X) [X.是GermInjectiveAt x]
  证明: by
  obtain ⟨U, hx, hU, H⟩ := Scheme.IsGermInjectiveAt.cond (x := x)
  obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  exact ⟨X.basicOpen f, hxf, hU.basicOpen f, hf, injective_germ_basicOpen U hU x hx f hxf H⟩

Depends on / 依赖: IsGermInjectiveAt, Scheme, Scheme.IsGermInjectiveAt.cond, X.basicOpen, basicOpen, exists_basicOpen_le, hU.basicOpen, hU.exists_basicOpen_le, injective_germ_basicOpen
-/
lemma Scheme.exists_le_and_germ_injective (X : Scheme.{u}) (x : X) [X.IsGermInjectiveAt x]
    (V : X.Opens) (hxV : x in V) :
    exists (U : X.Opens) (hx : x in U),
      IsAffineOpen U ∧ U <= V ∧ Function.Injective (X.presheaf.germ U x hx) := by
  obtain ⟨U, hx, hU, H⟩ := Scheme.IsGermInjectiveAt.cond (x := x)
  obtain ⟨f, hf, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  exact ⟨X.basicOpen f, hxf, hU.basicOpen f, hf, injective_germ_basicOpen U hU x hx f hxf H⟩

set_option backward.isDefEq.respectTransparency.types false in
instance (x : X) [X.IsGermInjectiveAt x] [IsOpenImmersion f] :
    Y.IsGermInjectiveAt (f x) := by
  obtain ⟨U, hxU, hU, H⟩ := X.exists_germ_injective x
  refine ⟨⟨f ''ᵁ U, ⟨x, hxU, rfl⟩, hU.image_of_isOpenImmersion f, ?_⟩⟩
  refine ((MorphismProperty.injective CommRingCat).cancel_right_of_respectsIso _
    (f.stalkMap x)).mp ?_
  refine ((MorphismProperty.injective CommRingCat).cancel_left_of_respectsIso
    (f.appIso U).inv _).mp ?_
  simpa

set_option backward.isDefEq.respectTransparency.types false in
variable {f} in
/--
lemma `isGermInjectiveAt_iff_of_isOpenImmersion` / 引理 `isGermInjectiveAt_iff_of_isOpenImmersion`

English:
lemma isGermInjectiveAt_iff_of_isOpenImmersion
  given: {x : X} [IsOpenImmersion f]
  proof: by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  obtain ⟨U, hxU, hU, hU', H⟩ :=
    Y.exists_le_and_germ_injective (f x) (V := f.opensRange) ⟨x, rfl⟩
  obtain ⟨V, hV⟩ := (IsOpenImmersion.affineOpensEquiv f).surjective ⟨⟨U, hU⟩, hU'⟩
  obtain rfl : f ''ᵁ V = U := Subtype.ext_iff.mp (Subtype.ext_if

中文:
引理 isGermInjectiveAt_iff_of_isOpenImmersion
  条件: {x : X} [是开浸入 f]
  证明: by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  obtain ⟨U, hxU, hU, hU', H⟩ :=
    Y.exists_le_and_germ_injective (f x) (V := f.opensRange) ⟨x, rfl⟩
  obtain ⟨V, hV⟩ := (IsOpenImmersion.affineOpensEquiv f).surjective ⟨⟨U, hU⟩, hU'⟩
  obtain rfl : f ''ᵁ V = U := Subtype.ext_iff.mp (Subtype.ext_if

Depends on / 依赖: CommRingCat, IsOpenImmersion, IsOpenImmersion.affineOpensEquiv, MorphismProperty, MorphismProperty.injective, Subtype, Subtype.ext_iff.mp, Y.exists_le_and_germ_injective, affineOpensEquiv, cancel_right_of_respectsIso, exists_le_and_germ_injective, ext_iff, f.isOpenEmbedding.injective, f.opensRange, f.stalkMap, injective, isOpenEmbedding, opensRange, replace, stalkMap
-/
lemma isGermInjectiveAt_iff_of_isOpenImmersion {x : X} [IsOpenImmersion f] :
    Y.IsGermInjectiveAt (f x) ↔ X.IsGermInjectiveAt x := by
  refine ⟨fun H => ?_, fun _ => inferInstance⟩
  obtain ⟨U, hxU, hU, hU', H⟩ :=
    Y.exists_le_and_germ_injective (f x) (V := f.opensRange) ⟨x, rfl⟩
  obtain ⟨V, hV⟩ := (IsOpenImmersion.affineOpensEquiv f).surjective ⟨⟨U, hU⟩, hU'⟩
  obtain rfl : f ''ᵁ V = U := Subtype.ext_iff.mp (Subtype.ext_iff.mp hV)
  obtain ⟨y, hy, e : f y = f x⟩ := hxU
  obtain rfl := f.isOpenEmbedding.injective e
  refine ⟨V, hy, V.2, ?_⟩
  replace H := ((MorphismProperty.injective CommRingCat).cancel_right_of_respectsIso _
    (f.stalkMap y)).mpr H
  replace H := ((MorphismProperty.injective CommRingCat).cancel_left_of_respectsIso
    (f.appIso V).inv _).mpr H
  simpa using! H

/--
Definition of `Scheme.IsGermInjective` / `Scheme.IsGermInjective` 的定义

English:
abbreviation Scheme.IsGermInjective
  signature: (X : Scheme.{u})
  body: forall x : X, X.IsGermInjectiveAt x

中文:
缩写 概形.IsGermInjective
  签名: (X : 概形.{u})
  定义体: forall x : X, X.IsGermInjectiveAt x

Depends on / 依赖: IsGermInjectiveAt, X.IsGermInjectiveAt
-/
abbrev Scheme.IsGermInjective (X : Scheme.{u}) := forall x : X, X.IsGermInjectiveAt x

/--
lemma `Scheme.IsGermInjective.of_openCover` / 引理 `Scheme.IsGermInjective.of_openCover`

English:
lemma Scheme.IsGermInjective.of_openCover
  proof: by
  intro x
  rw [← (𝒰.covers x).choose_spec]
  infer_instance

中文:
引理 概形.IsGermInjective.of_openCover
  证明: by
  intro x
  rw [← (𝒰.covers x).choose_spec]
  infer_instance

Depends on / 依赖: choose_spec, covers, infer_instance
-/
lemma Scheme.IsGermInjective.of_openCover
    {X : Scheme.{u}} (𝒰 : X.OpenCover) [forall i, (𝒰.X i).IsGermInjective] : X.IsGermInjective := by
  intro x
  rw [← (𝒰.covers x).choose_spec]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
protected
/--
lemma `Scheme.IsGermInjective.Spec` / 引理 `Scheme.IsGermInjective.Spec`

English:
lemma Scheme.IsGermInjective.Spec
  proof: by
  refine fun p => ⟨?_⟩
  obtain ⟨f, hf, H⟩ := H p.asIdeal p.2
  refine ⟨PrimeSpectrum.basicOpen f, hf, ?_, ?_⟩
  · rw [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Spec R)).basicOpen _
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x,

中文:
引理 概形.IsGermInjective.Spec
  证明: by
  refine fun p => ⟨?_⟩
  obtain ⟨f, hf, H⟩ := H p.asIdeal p.2
  refine ⟨PrimeSpectrum.basicOpen f, hf, ?_, ?_⟩
  · rw [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Spec R)).basicOpen _
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x,

Depends on / 依赖: Ideal.mul_unit_mem_, IsLocalization, IsLocalization.exists_mk, IsLocalization.mk, PrimeSpectrum, PrimeSpectrum.basicOpen, RingHom, RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero, RingHom.mem_ker, Spec.structureSheaf, _eq_mul_mk, _one, asIdeal, basicOpen, basicOpen_eq_of_affine, exists_mk, injective_iff_ker_eq_bot, isAffineOpen_top, ker_eq_bot_iff_eq_zero
-/
lemma Scheme.IsGermInjective.Spec
    (H : forall I : Ideal R, I.IsPrime ->
      exists f : R, f ∉ I ∧ forall (x y : R), y * x = 0 -> y ∉ I -> exists n, f ^ n * x = 0) :
    (Spec R).IsGermInjective := by
  refine fun p => ⟨?_⟩
  obtain ⟨f, hf, H⟩ := H p.asIdeal p.2
  refine ⟨PrimeSpectrum.basicOpen f, hf, ?_, ?_⟩
  · rw [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Spec R)).basicOpen _
  rw [RingHom.injective_iff_ker_eq_bot]; rw [RingHom.ker_eq_bot_iff_eq_zero]
  intro x hx
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq
    (S := ((Spec.structureSheaf R).obj.obj (.op <| PrimeSpectrum.basicOpen f))) (.powers f) x
  rw [← RingHom.mem_ker]; rw [IsLocalization.mk'_eq_mul_mk'_one]; rw [Ideal.mul_unit_mem_iff_mem]; rw [RingHom.mem_ker] at hx
  swap; · exact @isUnit_of_invertible _ _ _ (@IsLocalization.invertible_mk'_one ..)
  -- There is an `Opposite.unop (Opposite.op _)` in `hx` which doesn't seem removable using
  -- `simp`/`rw`.
  erw [elementwise_of% StructureSheaf.algebraMap_germ] at hx
  obtain ⟨⟨y, hy⟩, hy'⟩ := (IsLocalization.map_eq_zero_iff p.asIdeal.primeCompl
    ((Spec.structureSheaf R).presheaf.stalk p) _).mp hx
  obtain ⟨n, hn⟩ := H x y hy' hy
  refine (@IsLocalization.mk'_eq_zero_iff ..).mpr ?_
  exact ⟨⟨_, n, rfl⟩, hn⟩

instance (priority := 100) [IsIntegral X] : X.IsGermInjective := by
  refine fun x => ⟨⟨(X.affineCover.f _).opensRange, X.affineCover.covers x,
    (isAffineOpen_opensRange (X.affineCover.f _)), ?_⟩⟩
  have : Nonempty (X.affineCover.f _).opensRange := ⟨⟨_, X.affineCover.covers x⟩⟩
  have := (isAffineOpen_opensRange (X.affineCover.f _)).isLocalization_stalk
    ⟨_, X.affineCover.covers x⟩
  exact @IsLocalization.injective _ _ _ _ _ (show _ from _) this
    (Ideal.primeCompl_le_nonZeroDivisors _)

set_option backward.isDefEq.respectTransparency.types false in
instance (priority := 100) [IsLocallyNoetherian X] : X.IsGermInjective := by
  suffices forall (R : CommRingCat.{u}) (_ : IsNoetherianRing R), (Spec R).IsGermInjective by
    refine @Scheme.IsGermInjective.of_openCover _ (X.affineOpenCover.openCover) (fun i => this _ ?_)
    exact isLocallyNoetherian_Spec.mp
      (isLocallyNoetherian_of_isOpenImmersion (X.affineOpenCover.f i))
  refine fun R hR => Scheme.IsGermInjective.Spec fun I hI => ?_
let J := RingHom.ker algebraMap R (Localization.AtPrime I)
  have hJ (x) : x in J ↔ exists y : I.primeCompl, y * x = 0 :=
    IsLocalization.map_eq_zero_iff I.primeCompl _ x
  choose f hf using fun x => (hJ x).mp
  obtain ⟨s, hs⟩ := (isNoetherianRing_iff_ideal_fg R).mp ‹_› J
  have hs' : (s : Set R) subseteq J := hs ▸ Ideal.subset_span
  refine ⟨_, (s.attach.prod fun x => f x (hs' x.2)).2, fun x y e hy => ⟨1, ?_⟩⟩
  rw [pow_one]; rw [mul_comm]; rw [← smul_eq_mul]; rw [← Submodule.mem_annihilator_span_singleton]
  refine SetLike.le_def.mp ?_ ((hJ x).mpr ⟨⟨y, hy⟩, e⟩)
  rw [← hs]; rw [Ideal.span_le]
  intro i hi
  rw [SetLike.mem_coe]; rw [Submodule.mem_annihilator_span_singleton]; rw [smul_eq_mul]; rw [mul_comm]; rw [← smul_eq_mul]; rw [← Submodule.mem_annihilator_span_singleton]; rw [Submonoid.coe_finsetProd]
  refine Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (s.mem_attach ⟨i, hi⟩)) ?_
  rw [Submodule.mem_annihilator_span_singleton]; rw [smul_eq_mul]
  exact hf i _

set_option backward.isDefEq.respectTransparency.types false in
/--
Let `x : X` and `f g : X ⟶ Y` be two morphisms such that `f x = g x`.
If `f` and `g` agree on the stalk of `x`, then they agree on an open neighborhood of `x`,
provided `X` is "germ-injective" at `x` (e.g. when it's integral or locally Noetherian).

TODO: The condition on `X` is unnecessary when `Y` is locally of finite type.
-/
@[stacks 0BX6]
/--
lemma `spread_out_unique_of_isGermInjective` / 引理 `spread_out_unique_of_isGermInjective`

English:
lemma spread_out_unique_of_isGermInjective
  statement: {x : X} [X.IsGermInjectiveAt x]
  proof: by
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  have hxV' : g x in V := e ▸ hxV
  obtain ⟨U, hxU, _, hUV, HU⟩ := X.exists_le_and_germ_injective x (f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V) ⟨hxV, hxV'⟩
  refine ⟨U, hxU, ?_⟩
  rw [← Sc

中文:
引理 spread_out_unique_of_isGermInjective
  结论: {x : X} [X.是GermInjectiveAt x]
  证明: by
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  have hxV' : g x in V := e ▸ hxV
  obtain ⟨U, hxU, _, hUV, HU⟩ := X.exists_le_and_germ_injective x (f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V) ⟨hxV, hxV'⟩
  refine ⟨U, hxU, ?_⟩
  rw [← Sc

Depends on / 依赖: IsAffine, Scheme, Scheme.Hom.resLE_comp_, Set.mem_univ, X.exists_le_and_germ_injective, Y.Opens, Y.isBasis_affineOpens.exists_subset_of_mem_open, exists_le_and_germ_injective, exists_subset_of_mem_open, f.appLE, hUV.trans, inf_le_left, inf_le_right, isBasis_affineOpens, isOpen_univ, mem_univ
-/
lemma spread_out_unique_of_isGermInjective {x : X} [X.IsGermInjectiveAt x]
    (f g : X ⟶ Y) (e : f x = g x)
    (H : f.stalkMap x =
      Y.presheaf.stalkSpecializes (Inseparable.of_eq e.symm).specializes ≫ g.stalkMap x) :
    exists (U : X.Opens), x in U ∧ U.ι ≫ f = U.ι ≫ g := by
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  have hxV' : g x in V := e ▸ hxV
  obtain ⟨U, hxU, _, hUV, HU⟩ := X.exists_le_and_germ_injective x (f ⁻¹ᵁ V ⊓ g ⁻¹ᵁ V) ⟨hxV, hxV'⟩
  refine ⟨U, hxU, ?_⟩
  rw [← Scheme.Hom.resLE_comp_ι _ (hUV.trans inf_le_left)]; rw [← Scheme.Hom.resLE_comp_ι _ (hUV.trans inf_le_right)]
  congr 1
  have : IsAffine V := hV
  suffices forall (U₀ V₀) (eU : U = U₀) (eV : V = V₀),
      f.appLE V₀ U₀ (eU ▸ eV ▸ hUV.trans inf_le_left) =
        g.appLE V₀ U₀ (eU ▸ eV ▸ hUV.trans inf_le_right) by
    rw [← cancel_mono V.toScheme.isoSpec.hom]
    simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_naturality,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.resLE_appLE]
    congr 2
    apply this <;> simp
  rintro U V rfl rfl
  have := ConcreteCategory.mono_of_injective _ HU
  rw [← cancel_mono (X.presheaf.germ U x hxU)]
  simp only [Scheme.Hom.appLE, Category.assoc, X.presheaf.germ_res', ← Scheme.Hom.germ_stalkMap, H]
  simp only [TopCat.Presheaf.germ_stalkSpecializes_assoc, Scheme.Hom.germ_stalkMap]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `spread_out_unique_of_isGermInjective'` / 引理 `spread_out_unique_of_isGermInjective'`

English:
lemma spread_out_unique_of_isGermInjective'
  statement: {x : X} [X.IsGermInjectiveAt x]
  proof: by
  fapply spread_out_unique_of_isGermInjective
  · simpa using congr($e (IsLocalRing.closedPoint _))
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk _)]
    simpa [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

中文:
引理 spread_out_unique_of_isGermInjective'
  结论: {x : X} [X.是GermInjectiveAt x]
  证明: by
  fapply spread_out_unique_of_isGermInjective
  · simpa using congr($e (IsLocalRing.closedPoint _))
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk _)]
    simpa [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

Depends on / 依赖: IsLocalRing, IsLocalRing.closedPoint, Scheme, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Spec.map_injective, SpecMap_stalkSpecializes_fromSpecStalk, Y.fromSpecStalk, cancel_mono, closedPoint, fapply, fromSpecStalk, map_injective, spread_out_unique_of_isGermInjective
-/
lemma spread_out_unique_of_isGermInjective' {x : X} [X.IsGermInjectiveAt x]
    (f g : X ⟶ Y)
    (e : X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) :
    exists (U : X.Opens), x in U ∧ U.ι ≫ f = U.ι ≫ g := by
  fapply spread_out_unique_of_isGermInjective
  · simpa using congr($e (IsLocalRing.closedPoint _))
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk _)]
    simpa [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

/--
lemma `exists_lift_of_germInjective_aux` / 引理 `exists_lift_of_germInjective_aux`

English:
lemma exists_lift_of_germInjective_aux
  statement: {U : X.Opens} {x : X} (hxU)
  proof: by
  let := φRA.hom.toAlgebra
  obtain ⟨s, hs⟩ := hφRA
  choose W hxW f hf using fun t => X.presheaf.exists_germ_eq (φ t)
  have H : x in s.inf W ⊓ U := by
    rw [← SetLike.mem_coe]; rw [TopologicalSpace.Opens.coe_inf]; rw [TopologicalSpace.Opens.coe_finset_inf]
    exact ⟨by simpa using fun x _ =>

中文:
引理 存在_lift_of_germInjective_aux
  结论: {U : X.Opens} {x : X} (hxU)
  证明: by
  let := φRA.hom.toAlgebra
  obtain ⟨s, hs⟩ := hφRA
  choose W hxW f hf using fun t => X.presheaf.exists_germ_eq (φ t)
  have H : x in s.inf W ⊓ U := by
    rw [← SetLike.mem_coe]; rw [TopologicalSpace.Opens.coe_inf]; rw [TopologicalSpace.Opens.coe_finset_inf]
    exact ⟨by simpa using fun x _ =>

Depends on / 依赖: RA.hom.toAlgebra, RX.hom.toAlgebra, SetLike, SetLike.mem_coe, TopologicalSpace, TopologicalSpace.Opens.coe_finset_inf, TopologicalSpace.Opens.coe_inf, X.presheaf.exists_germ_eq, X.presheaf.germ, X.presheaf.map, coe_finset_inf, coe_inf, exists_germ_eq, hom.toAlge, hom.toAlgebra, homOfLE, inf_le_right, mem_coe, presheaf, s.inf
-/
lemma exists_lift_of_germInjective_aux {U : X.Opens} {x : X} (hxU)
    (φ : A ⟶ X.presheaf.stalk x) (φRA : R ⟶ A) (φRX : R ⟶ Γ(X, U))
    (hφRA : RingHom.FiniteType φRA.hom)
    (e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU) :
    exists (V : X.Opens) (hxV : x in V),
      V <= U ∧ RingHom.range φ.hom <= RingHom.range (X.presheaf.germ V x hxV).hom := by
  let := φRA.hom.toAlgebra
  obtain ⟨s, hs⟩ := hφRA
  choose W hxW f hf using fun t => X.presheaf.exists_germ_eq (φ t)
  have H : x in s.inf W ⊓ U := by
    rw [← SetLike.mem_coe]; rw [TopologicalSpace.Opens.coe_inf]; rw [TopologicalSpace.Opens.coe_finset_inf]
    exact ⟨by simpa using fun x _ => hxW x, hxU⟩
  refine ⟨s.inf W ⊓ U, H, inf_le_right, ?_⟩
  let := φRX.hom.toAlgebra
  let := (φRX ≫ X.presheaf.germ U x hxU).hom.toAlgebra
  let := (φRX ≫ X.presheaf.map (homOfLE (inf_le_right (a := s.inf W))).op).hom.toAlgebra
  let φ' : A ->ₐ[R] X.presheaf.stalk x :=
    { φ.hom with commutes' := DFunLike.congr_fun (congr_arg CommRingCat.Hom.hom e) }
  let ψ : Γ(X, s.inf W ⊓ U) ->ₐ[R] X.presheaf.stalk x :=
    { (X.presheaf.germ _ x H).hom with commutes' := fun x => X.presheaf.germ_res_apply _ _ _ _ }
  change AlgHom.range φ' <= AlgHom.range ψ
  rw [← Algebra.map_top]; rw [← hs]; rw [AlgHom.map_adjoin]; rw [Algebra.adjoin_le_iff]
  rintro _ ⟨i, hi, rfl : φ i = _⟩
  refine ⟨X.presheaf.map (homOfLE (inf_le_left.trans (Finset.inf_le hi))).op (f i), ?_⟩
  exact (X.presheaf.germ_res_apply _ _ _ _).trans (hf _)

/--
lemma `exists_lift_of_germInjective` / 引理 `exists_lift_of_germInjective`

English:
lemma exists_lift_of_germInjective
  statement: {x : X} [X.IsGermInjectiveAt x] {U : X.Opens} (hxU : x in U)
  proof: by
  obtain ⟨V, hxV, iVU, hV⟩ := exists_lift_of_germInjective_aux hxU φ φRA φRX hφRA e
  obtain ⟨V', hxV', hV', iV'V, H⟩ := X.exists_le_and_germ_injective x V hxV
  let f := X.presheaf.germ V' x hxV'
  have hf' : RingHom.range (X.presheaf.germ V x hxV).hom <= RingHom.range f.hom := by
    rw [← X.pr

中文:
引理 存在_lift_of_germInjective
  结论: {x : X} [X.是GermInjectiveAt x] {U : X.Opens} (hxU : x in U)
  证明: by
  obtain ⟨V, hxV, iVU, hV⟩ := exists_lift_of_germInjective_aux hxU φ φRA φRX hφRA e
  obtain ⟨V', hxV', hV', iV'V, H⟩ := X.exists_le_and_germ_injective x V hxV
  let f := X.presheaf.germ V' x hxV'
  have hf' : RingHom.range (X.presheaf.germ V x hxV).hom <= RingHom.range f.hom := by
    rw [← X.pr

Depends on / 依赖: CommRingCat, CommRingCat.ofHom, H.hasLeftInverse.choose_spec, RingEquiv, RingEquiv.ofLeftInverse, RingHom, RingHom.range, Set.range_comp_subset_range, V.hom, V.hom.op, X.exists_le_and_germ_injective, X.presheaf.germ, X.presheaf.germ_res, X.presheaf.map, choose_spec, e.symm.toRingHo, exists_le_and_germ_injective, exists_lift_of_germInjective_aux, f.hom, germ_res
-/
lemma exists_lift_of_germInjective {x : X} [X.IsGermInjectiveAt x] {U : X.Opens} (hxU : x in U)
    (φ : A ⟶ X.presheaf.stalk x) (φRA : R ⟶ A) (φRX : R ⟶ Γ(X, U))
    (hφRA : RingHom.FiniteType φRA.hom)
    (e : φRA ≫ φ = φRX ≫ X.presheaf.germ U x hxU) :
    exists (V : X.Opens) (hxV : x in V) (φ' : A ⟶ Γ(X, V)) (i : V <= U), IsAffineOpen V ∧
      φ = φ' ≫ X.presheaf.germ V x hxV ∧ φRX ≫ X.presheaf.map i.hom.op = φRA ≫ φ' := by
  obtain ⟨V, hxV, iVU, hV⟩ := exists_lift_of_germInjective_aux hxU φ φRA φRX hφRA e
  obtain ⟨V', hxV', hV', iV'V, H⟩ := X.exists_le_and_germ_injective x V hxV
  let f := X.presheaf.germ V' x hxV'
  have hf' : RingHom.range (X.presheaf.germ V x hxV).hom <= RingHom.range f.hom := by
    rw [← X.presheaf.germ_res iV'V.hom _ hxV']
    exact Set.range_comp_subset_range (X.presheaf.map iV'V.hom.op) f
  let e := RingEquiv.ofLeftInverse H.hasLeftInverse.choose_spec
  refine ⟨V', hxV', CommRingCat.ofHom (e.symm.toRingHom.comp
    (φ.hom.codRestrict _ (fun x => hf' (hV ⟨x, rfl⟩)))), iV'V.trans iVU, hV', ?_, ?_⟩
  · ext a
    change φ a = (e (e.symm _)).1
    simp only [RingEquiv.apply_symm_apply]
    rfl
  · ext a
    apply e.injective
    change e _ = e (e.symm _)
    rw [RingEquiv.apply_symm_apply]
    ext
    change X.presheaf.germ _ _ _ (X.presheaf.map _ _) = (φRA ≫ φ) a
    rw [TopCat.Presheaf.germ_res_apply]; rw [‹φRA ≫ φ = _›]
    rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
Given `S`-schemes `X Y` and points `x : X` `y : Y` over `s : S`.
Suppose we have the following diagram of `S`-schemes
```
Spec 𝒪_{X, x} ⟶ X
    |
  Spec(φ)
    ↓
Spec 𝒪_{Y, y} ⟶ Y
```
Then the map `Spec(φ)` spreads out to an `S`-morphism on an open subscheme `U ⊆ X`,
```
Spec 𝒪_{X, x} ⟶ U ⊆ X
    | |
  Spec(φ) |
    ↓ ↓
Spec 𝒪_{Y, y} ⟶ Y
```
provided that `Y` is locally of finite type over `S` and
`X` is "germ-injective" at `x` (e.g. when it's integral or locally Noetherian).

TODO: The condition on `X` is unnecessary when `Y` is locally of finite presentation.
-/
@[stacks 0BX6]
/--
lemma `spread_out_of_isGermInjective` / 引理 `spread_out_of_isGermInjective`

English:
lemma spread_out_of_isGermInjective
  statement: [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x] {y : Y}
  proof: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (sX x)) isOpen_univ
  have hyU : sY y in U := e ▸ hxU
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, iVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (sY ⁻¹ᵁ U).2
  have : sY.appLE U 

中文:
引理 spread_out_of_isGermInjective
  结论: [局部有限型 sY] {x : X} [X.是GermInjectiveAt x] {y : Y}
  证明: by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (sX x)) isOpen_univ
  have hyU : sY y in U := e ▸ hxU
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, iVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (sY ⁻¹ᵁ U).2
  have : sY.appLE U 

Depends on / 依赖: Category, Category.assoc, S.isBasis_affineOpens.exists_subset_of_mem_open, Scheme, Scheme.Hom.appLE, Scheme.Hom.germ_stalkMap_assoc, Set.mem_univ, X.presheaf.germ, Y.Opens, Y.isBasis_affineOpens.exists_subset_of_mem_open, Y.presheaf.germ, Y.presheaf.germ_res_assoc, exists_subset_of_mem_open, germ_res_assoc, germ_stalkMap_assoc, isBasis_affineOpens, isOpen_univ, mem_univ, presheaf, sX.app
-/
lemma spread_out_of_isGermInjective [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x] {y : Y}
    (e : sX x = sY y) (φ : Y.presheaf.stalk y ⟶ X.presheaf.stalk x)
    (h : sY.stalkMap y ≫ φ =
      S.presheaf.stalkSpecializes (Inseparable.of_eq e).specializes ≫ sX.stalkMap x) :
    exists (U : X.Opens) (hxU : x in U) (f : U.toScheme ⟶ Y),
      Spec.map φ ≫ Y.fromSpecStalk y = U.fromSpecStalkOfMem x hxU ≫ f ∧
      f ≫ sY = U.ι ≫ sX := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (sX x)) isOpen_univ
  have hyU : sY y in U := e ▸ hxU
  obtain ⟨_, ⟨V : Y.Opens, hV, rfl⟩, hyV, iVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyU (sY ⁻¹ᵁ U).2
  have : sY.appLE U V iVU ≫ Y.presheaf.germ V y hyV ≫ φ =
      sX.app U ≫ X.presheaf.germ (sX ⁻¹ᵁ U) x hxU := by
    rw [Scheme.Hom.appLE]; rw [Category.assoc]; rw [Y.presheaf.germ_res_assoc]; rw [← Scheme.Hom.germ_stalkMap_assoc]; rw [h]
    simp
  obtain ⟨W, hxW, φ', i, hW, h₁, h₂⟩ :=
    exists_lift_of_germInjective (R := Γ(S, U)) (A := Γ(Y, V)) (U := sX ⁻¹ᵁ U) (x := x) hxU
    (Y.presheaf.germ _ y hyV ≫ φ) (sY.appLE U V iVU) (sX.app U)
    (sY.finiteType_appLE hU hV _) this
  refine ⟨W, hxW, W.toSpecΓ ≫ Spec.map φ' ≫ hV.fromSpec, ?_, ?_⟩
  · rw [W.fromSpecStalkOfMem_toSpecΓ_assoc x hxW, ← Spec.map_comp_assoc, ← h₁,
      Spec.map_comp, Category.assoc, ← IsAffineOpen.fromSpecStalk,
      IsAffineOpen.fromSpecStalk_eq_fromSpecStalk]
  · simp only [Category.assoc]
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec sY hU hV iVU]; rw [← Spec.map_comp_assoc]; rw [← h₂]; rw [← Scheme.Hom.appLE]; rw [← hW.isoSpec_hom]; rw [IsAffineOpen.SpecMap_appLE_fromSpec sX hU hW i]; rw [← Iso.eq_inv_comp]; rw [IsAffineOpen.isoSpec_inv_ι_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `spread_out_of_isGermInjective'` / 引理 `spread_out_of_isGermInjective'`

English:
lemma spread_out_of_isGermInjective'
  statement: [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x]
  proof: by
  have := spread_out_of_isGermInjective sX sY ?_ (Scheme.stalkClosedPointTo φ) ?_
  · simpa only [Scheme.Spec_stalkClosedPointTo_fromSpecStalk] using this
  · rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  · apply Spec.map_injective
    rw [← cancel_mon

中文:
引理 spread_out_of_isGermInjective'
  结论: [局部有限型 sY] {x : X} [X.是GermInjectiveAt x]
  证明: by
  have := spread_out_of_isGermInjective sX sY ?_ (Scheme.stalkClosedPointTo φ) ?_
  · simpa only [Scheme.Spec_stalkClosedPointTo_fromSpecStalk] using this
  · rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  · apply Spec.map_injective
    rw [← cancel_mon

Depends on / 依赖: Category, Category.assoc, S.fromSpecStalk, Scheme, Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc, Scheme.fromSpecStalk_closedPoint, Scheme.stalkClosedPointTo, Spec.map_comp, Spec.map_injective, SpecMap_stalkMap_fromSpecStalk, SpecMap_stalkSpecializes_fromSpecStalk, Spec_stalkClosedPointTo_fromSpecStalk, Spec_stalkClosedPointTo_fromSpecStalk_assoc, cancel_mono, comp_apply, fromSpecStalk
-/
lemma spread_out_of_isGermInjective' [LocallyOfFiniteType sY] {x : X} [X.IsGermInjectiveAt x]
    (φ : Spec (X.presheaf.stalk x) ⟶ Y)
    (h : φ ≫ sY = X.fromSpecStalk x ≫ sX) :
    exists (U : X.Opens) (hxU : x in U) (f : U.toScheme ⟶ Y),
      φ = U.fromSpecStalkOfMem x hxU ≫ f ∧ f ≫ sY = U.ι ≫ sX := by
  have := spread_out_of_isGermInjective sX sY ?_ (Scheme.stalkClosedPointTo φ) ?_
  · simpa only [Scheme.Spec_stalkClosedPointTo_fromSpecStalk] using this
  · rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply, Scheme.fromSpecStalk_closedPoint]
  · apply Spec.map_injective
    rw [← cancel_mono (S.fromSpecStalk _)]
    simpa only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk_assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

end AlgebraicGeometry
