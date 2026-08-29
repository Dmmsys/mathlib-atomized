/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.Topology.Category.TopCat.Limits.Pullbacks
public import Mathlib.CategoryTheory.Limits.VanKampen
public import Mathlib.CategoryTheory.Limits.MonoCoprod
public import Mathlib.CategoryTheory.Limits.Shapes.DisjointCoproduct

/-!

# Extensive categories

## Main definitions
- `CategoryTheory.FinitaryExtensive`: A category is (finitary) extensive if it has finite
  coproducts, and binary coproducts are van Kampen.

## Main Results
- `CategoryTheory.hasStrictInitialObjects_of_finitaryExtensive`: The initial object
  in extensive categories is strict.
- `CategoryTheory.FinitaryExtensive.mono_inr_of_isColimit`: Coproduct injections are monic in
  extensive categories.
- `CategoryTheory.BinaryCofan.isPullback_initial_to_of_isVanKampen`: In extensive categories,
  sums are disjoint, i.e. the pullback of `X ⟶ X ⨿ Y` and `Y ⟶ X ⨿ Y` is the initial object.
- `CategoryTheory.types.finitaryExtensive`: The category of types is extensive.
- `CategoryTheory.FinitaryExtensive_TopCat`:
  The category `Top` is extensive.
- `CategoryTheory.FinitaryExtensive_functor`: The category `C ⥤ D` is extensive if `D`
  has all pullbacks and is extensive.
- `CategoryTheory.FinitaryExtensive.isVanKampen_finiteCoproducts`: Finite coproducts in a
  finitary extensive category are van Kampen.

## References
- https://ncatlab.org/nlab/show/extensive+category
- [Carboni et al, Introduction to extensive and distributive categories][CARBONI1993145]

-/

@[expose] public section

open CategoryTheory.Limits Topology

namespace CategoryTheory

universe v' u' v u v'' u''

variable {J : Type v'} [Category.{u'} J] {C : Type u} [Category.{v} C]
variable {D : Type u''} [Category.{v''} D]

section Extensive

variable {X Y : C}

/--
Definition of `HasPullbacksOfInclusions` / `HasPullbacksOfInclusions` 的定义

English:
class HasPullbacksOfInclusions
  parameters: (C : Type u) [Category.{v} C] [HasBinaryCoproducts C]
  axioms and operations (1):
    - [hasPullbackInl : forall {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]

中文:
类 HasPullbacksOfInclusions
  参数: (C : 类型u) [Category.{v} C] [HasBinaryCoproducts C]
  公理与运算 (1 个):
    - [hasPullbackInl : 对任意 {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]
-/
class HasPullbacksOfInclusions (C : Type u) [Category.{v} C] [HasBinaryCoproducts C] : Prop where
  [hasPullbackInl : forall {X Y Z : C} (f : Z ⟶ X ⨿ Y), HasPullback coprod.inl f]

attribute [instance] HasPullbacksOfInclusions.hasPullbackInl

/--
Definition of `PreservesPullbacksOfInclusions` / `PreservesPullbacksOfInclusions` 的定义

English:
class PreservesPullbacksOfInclusions
  parameters: {C : Type*} [Category* C] {D : Type*} [Category* D]
  axioms and operations (1):
    - [preservesPullbackInl : forall {X Y Z : C} (f : Z ⟶ X ⨿ Y), PreservesLimit (cospan coprod.inl f) F]

中文:
类 PreservesPullbacksOfInclusions
  参数: {C : 类型} [Category* C] {D : 类型} [Category* D]
  公理与运算 (1 个):
    - [preservesPullbackInl : 对任意 {X Y Z : C} (f : Z ⟶ X ⨿ Y), PreservesLimit (cospan coprod.inl f) F]
-/
class PreservesPullbacksOfInclusions {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) [HasBinaryCoproducts C] where
  [preservesPullbackInl : forall {X Y Z : C} (f : Z ⟶ X ⨿ Y), PreservesLimit (cospan coprod.inl f) F]

attribute [instance] PreservesPullbacksOfInclusions.preservesPullbackInl

/--
Definition of `FinitaryPreExtensive` / `FinitaryPreExtensive` 的定义

English:
class FinitaryPreExtensive
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (3):
    - [hasFiniteCoproducts : HasFiniteCoproducts C]
    - [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
    - universal' : forall {X Y : C} (c : BinaryCofan X Y), IsColimit c -> IsUniversalColimit c

中文:
类 FinitaryPreExtensive
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (3 个):
    - [hasFiniteCoproducts : HasFiniteCoproducts C]
    - [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
    - universal' : 对任意 {X Y : C} (c : BinaryCofan X Y), IsColimit c -> IsUniversalColimit c
-/
class FinitaryPreExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all coproducts are van Kampen -/
  universal' : forall {X Y : C} (c : BinaryCofan X Y), IsColimit c -> IsUniversalColimit c

attribute [instance] FinitaryPreExtensive.hasFiniteCoproducts
attribute [instance] FinitaryPreExtensive.hasPullbacksOfInclusions

/--
Definition of `FinitaryExtensive` / `FinitaryExtensive` 的定义

English:
class FinitaryExtensive
  parameters: (C : Type u) [Category.{v} C]
  axioms and operations (3):
    - [hasFiniteCoproducts : HasFiniteCoproducts C]
    - [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
    - van_kampen' : forall {X Y : C} (c : BinaryCofan X Y), IsColimit c -> IsVanKampenColimit c

中文:
类 FinitaryExtensive
  参数: (C : 类型u) [Category.{v} C]
  公理与运算 (3 个):
    - [hasFiniteCoproducts : HasFiniteCoproducts C]
    - [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
    - van_kampen' : 对任意 {X Y : C} (c : BinaryCofan X Y), IsColimit c -> IsVanKampenColimit c
-/
class FinitaryExtensive (C : Type u) [Category.{v} C] : Prop where
  [hasFiniteCoproducts : HasFiniteCoproducts C]
  [hasPullbacksOfInclusions : HasPullbacksOfInclusions C]
  /-- In a finitary extensive category, all coproducts are van Kampen -/
  van_kampen' : forall {X Y : C} (c : BinaryCofan X Y), IsColimit c -> IsVanKampenColimit c

attribute [instance] FinitaryExtensive.hasFiniteCoproducts
attribute [instance] FinitaryExtensive.hasPullbacksOfInclusions

/--
theorem `FinitaryExtensive.vanKampen` / 定理 `FinitaryExtensive.vanKampen`

English:
theorem FinitaryExtensive.vanKampen
  statement: [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
  proof: by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X, Y]
  clear_value X Y
  subst this
  exact FinitaryExtensive.van_kampen' c hc

中文:
定理 FinitaryExtensive.vanKampen
  结论: [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
  证明: by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X, Y]
  clear_value X Y
  subst this
  exact FinitaryExtensive.van_kampen' c hc

Depends on / 依赖: F.obj, FinitaryExtensive, FinitaryExtensive.van_kampen, Functor, Functor.hext, WalkingPair, WalkingPair.left, WalkingPair.right, clear_value, van_kampen
-/
theorem FinitaryExtensive.vanKampen [FinitaryExtensive C] {F : Discrete WalkingPair ⥤ C}
    (c : Cocone F) (hc : IsColimit c) : IsVanKampenColimit c := by
  let X := F.obj ⟨WalkingPair.left⟩
  let Y := F.obj ⟨WalkingPair.right⟩
  have : F = pair X Y := by
    apply Functor.hext
    · rintro ⟨⟨⟩⟩ <;> rfl
    · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp [X, Y]
  clear_value X Y
  subst this
  exact FinitaryExtensive.van_kampen' c hc

namespace HasPullbacksOfInclusions

instance (priority := 100) [HasBinaryCoproducts C] [HasPullbacks C] :
    HasPullbacksOfInclusions C := ⟨⟩

variable [HasBinaryCoproducts C] [HasPullbacksOfInclusions C] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

/--
Instance `preservesPullbackInl'` / 实例 `preservesPullbackInl'`

English:
instance preservesPullbackInl'
  signature: :
  body: hasPullback_symmetry _ _

中文:
实例 preservesPullbackInl'
  签名: :
  定义体: hasPullback_symmetry _ _

Depends on / 依赖: hasPullback_symmetry
-/
instance preservesPullbackInl' :
    HasPullback f coprod.inl :=
  hasPullback_symmetry _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `hasPullbackInr'` / 实例 `hasPullbackInr'`

English:
instance hasPullbackInr'
  signature: :
  body: by
  have : IsPullback (𝟙 _) (f ≫ (coprod.braiding X Y).hom) f (coprod.braiding Y X).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := (IsPullback.of_hasPullback (f ≫ (coprod.braiding X Y).hom) coprod.inl).paste_horiz this
  simp only [coprod.braiding_hom, Category.comp_id, colimit.ι_desc,
  

中文:
实例 hasPullbackInr'
  签名: :
  定义体: by
  have : IsPullback (𝟙 _) (f ≫ (coprod.braiding X Y).hom) f (coprod.braiding Y X).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := (IsPullback.of_hasPullback (f ≫ (coprod.braiding X Y).hom) coprod.inl).paste_horiz this
  simp only [coprod.braiding_hom, Category.comp_id, colimit.ι_desc,
  

Depends on / 依赖: BinaryCofan, BinaryCofan.mk_inl, Category, Category.comp_id, IsPullback, IsPullback.of_hasPullback, IsPullback.of_horiz_isIso, braiding, braiding_hom, colimit, comp_id, coprod, coprod.braiding, coprod.braiding_hom, coprod.inl, isLimit, mk_inl, of_hasPullback, of_horiz_isIso, paste_horiz
-/
instance hasPullbackInr' :
    HasPullback f coprod.inr := by
  have : IsPullback (𝟙 _) (f ≫ (coprod.braiding X Y).hom) f (coprod.braiding Y X).hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  have := (IsPullback.of_hasPullback (f ≫ (coprod.braiding X Y).hom) coprod.inl).paste_horiz this
  simp only [coprod.braiding_hom, Category.comp_id, colimit.ι_desc,
    BinaryCofan.ι_app_left, BinaryCofan.mk_inl] at this
  exact ⟨⟨⟨_, this.isLimit⟩⟩⟩

/--
Instance `hasPullbackInr` / 实例 `hasPullbackInr`

English:
instance hasPullbackInr
  signature: :
  body: hasPullback_symmetry _ _

中文:
实例 hasPullbackInr
  签名: :
  定义体: hasPullback_symmetry _ _

Depends on / 依赖: hasPullback_symmetry
-/
instance hasPullbackInr :
    HasPullback coprod.inr f :=
  hasPullback_symmetry _ _

end HasPullbacksOfInclusions

namespace PreservesPullbacksOfInclusions

variable {D : Type*} [Category* D] [HasBinaryCoproducts C] (F : C ⥤ D)

noncomputable
instance (priority := 100) [PreservesLimitsOfShape WalkingCospan F] :
    PreservesPullbacksOfInclusions F := ⟨⟩

variable [PreservesPullbacksOfInclusions F] {X Y Z : C} (f : Z ⟶ X ⨿ Y)

noncomputable
/--
Instance `preservesPullbackInl'` / 实例 `preservesPullbackInl'`

English:
instance preservesPullbackInl'
  signature: :
  body: preservesPullback_symmetry _ _ _

中文:
实例 preservesPullbackInl'
  签名: :
  定义体: preservesPullback_symmetry _ _ _

Depends on / 依赖: preservesPullback_symmetry
-/
instance preservesPullbackInl' :
    PreservesLimit (cospan f coprod.inl) F :=
  preservesPullback_symmetry _ _ _

set_option backward.isDefEq.respectTransparency false in
noncomputable
/--
Instance `preservesPullbackInr'` / 实例 `preservesPullbackInr'`

English:
instance preservesPullbackInr'
  signature: :
  body: by
  apply preservesLimit_of_iso_diagram (K₁ := cospan (f ≫ (coprod.braiding X Y).hom) coprod.inl)
  apply cospanExt (Iso.refl _) (Iso.refl _) (coprod.braiding X Y).symm <;> simp

noncomputable

中文:
实例 preservesPullbackInr'
  签名: :
  定义体: by
  apply preservesLimit_of_iso_diagram (K₁ := cospan (f ≫ (coprod.braiding X Y).hom) coprod.inl)
  apply cospanExt (Iso.refl _) (Iso.refl _) (coprod.braiding X Y).symm <;> simp

noncomputable

Depends on / 依赖: Iso.refl, braiding, coprod, coprod.braiding, coprod.inl, cospan, cospanExt, preservesLimit_of_iso_diagram
-/
instance preservesPullbackInr' :
    PreservesLimit (cospan f coprod.inr) F := by
  apply preservesLimit_of_iso_diagram (K₁ := cospan (f ≫ (coprod.braiding X Y).hom) coprod.inl)
  apply cospanExt (Iso.refl _) (Iso.refl _) (coprod.braiding X Y).symm <;> simp

noncomputable
/--
Instance `preservesPullbackInr` / 实例 `preservesPullbackInr`

English:
instance preservesPullbackInr
  signature: :
  body: preservesPullback_symmetry _ _ _

中文:
实例 preservesPullbackInr
  签名: :
  定义体: preservesPullback_symmetry _ _ _

Depends on / 依赖: preservesPullback_symmetry
-/
instance preservesPullbackInr :
    PreservesLimit (cospan coprod.inr f) F :=
  preservesPullback_symmetry _ _ _

end PreservesPullbacksOfInclusions

instance (priority := 100) FinitaryExtensive.toFinitaryPreExtensive [FinitaryExtensive C] :
    FinitaryPreExtensive C :=
  ⟨fun c hc => (FinitaryExtensive.van_kampen' c hc).isUniversal⟩

/--
theorem `FinitaryExtensive.mono_inr_of_isColimit` / 定理 `FinitaryExtensive.mono_inr_of_isColimit`

English:
theorem FinitaryExtensive.mono_inr_of_isColimit
  statement: [FinitaryExtensive C] {c : BinaryCofan X Y}
  proof: BinaryCofan.mono_inr_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

中文:
定理 FinitaryExtensive.mono_inr_of_isColimit
  结论: [FinitaryExtensive C] {c : BinaryCofan X Y}
  证明: BinaryCofan.mono_inr_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

Depends on / 依赖: BinaryCofan, BinaryCofan.mono_inr_of_isVanKampen, FinitaryExtensive, FinitaryExtensive.vanKampen, mono_inr_of_isVanKampen, vanKampen
-/
theorem FinitaryExtensive.mono_inr_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inr :=
  BinaryCofan.mono_inr_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

/--
theorem `FinitaryExtensive.mono_inl_of_isColimit` / 定理 `FinitaryExtensive.mono_inl_of_isColimit`

English:
theorem FinitaryExtensive.mono_inl_of_isColimit
  statement: [FinitaryExtensive C] {c : BinaryCofan X Y}
  proof: FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)

中文:
定理 FinitaryExtensive.mono_inl_of_isColimit
  结论: [FinitaryExtensive C] {c : BinaryCofan X Y}
  证明: FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)

Depends on / 依赖: BinaryCofan, BinaryCofan.isColimitFlip, FinitaryExtensive, FinitaryExtensive.mono_inr_of_isColimit, isColimitFlip, mono_inr_of_isColimit
-/
theorem FinitaryExtensive.mono_inl_of_isColimit [FinitaryExtensive C] {c : BinaryCofan X Y}
    (hc : IsColimit c) : Mono c.inl :=
  FinitaryExtensive.mono_inr_of_isColimit (BinaryCofan.isColimitFlip hc)

instance (priority := low) [FinitaryExtensive C] : MonoCoprod C where
  binaryCofan_inl _ _ _ hc := BinaryCofan.mono_inr_of_isVanKampen
    (FinitaryExtensive.vanKampen _ (BinaryCofan.isColimitFlip hc))

/--
theorem `FinitaryExtensive.isPullback_initial_to_binaryCofan` / 定理 `FinitaryExtensive.isPullback_initial_to_binaryCofan`

English:
theorem FinitaryExtensive.isPullback_initial_to_binaryCofan
  statement: [FinitaryExtensive C]
  proof: BinaryCofan.isPullback_initial_to_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

中文:
定理 FinitaryExtensive.isPullback_initial_to_binaryCofan
  结论: [FinitaryExtensive C]
  证明: BinaryCofan.isPullback_initial_to_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

Depends on / 依赖: BinaryCofan, BinaryCofan.isPullback_initial_to_of_isVanKampen, FinitaryExtensive, FinitaryExtensive.vanKampen, isPullback_initial_to_of_isVanKampen, vanKampen
-/
theorem FinitaryExtensive.isPullback_initial_to_binaryCofan [FinitaryExtensive C]
    {c : BinaryCofan X Y} (hc : IsColimit c) :
    IsPullback (initial.to _) (initial.to _) c.inl c.inr :=
  BinaryCofan.isPullback_initial_to_of_isVanKampen (FinitaryExtensive.vanKampen c hc)

set_option backward.defeqAttrib.useBackward true in
instance (priority := 100) hasStrictInitialObjects_of_finitaryPreExtensive
    [FinitaryPreExtensive C] : HasStrictInitialObjects C :=
  hasStrictInitial_of_isUniversal (FinitaryPreExtensive.universal' _
    ((BinaryCofan.isColimit_iff_isIso_inr initialIsInitial _).mpr (by
      dsimp
      infer_instance)).some)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finitaryExtensive_iff_of_isTerminal` / 定理 `finitaryExtensive_iff_of_isTerminal`

English:
theorem finitaryExtensive_iff_of_isTerminal
  statement: (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
  proof: by
  refine ⟨fun H => H.van_kampen' c₀ hc₀, fun H => ?_⟩
  constructor
  simp_rw [BinaryCofan.isVanKampen_iff] at H ⊢
  intro X Y c hc X' Y' c' αX αY f hX hY
  obtain ⟨d, hd, hd'⟩ :=
    Limits.BinaryCofan.IsColimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫

中文:
定理 finitaryExtensive_iff_of_isTerminal
  结论: (C : 类型u) [Category.{v} C] [HasFiniteCoproducts C]
  证明: by
  refine ⟨fun H => H.van_kampen' c₀ hc₀, fun H => ?_⟩
  constructor
  simp_rw [BinaryCofan.isVanKampen_iff] at H ⊢
  intro X Y c hc X' Y' c' αX αY f hX hY
  obtain ⟨d, hd, hd'⟩ :=
    Limits.BinaryCofan.IsColimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫

Depends on / 依赖: BinaryCofan, BinaryCofan.isVanKampen_iff, Category, Category.assoc, H.van_kampen, HT.from, IsColimit, Limits, Limits.BinaryCofan.IsColimit.desc, hd.symm, hl.paste_v, isVanKampen_iff, paste_v, reassoc_of, simp_rw, van_kampen
-/
theorem finitaryExtensive_iff_of_isTerminal (C : Type u) [Category.{v} C] [HasFiniteCoproducts C]
    [HasPullbacksOfInclusions C]
    (T : C) (HT : IsTerminal T) (c₀ : BinaryCofan T T) (hc₀ : IsColimit c₀) :
    FinitaryExtensive C ↔ IsVanKampenColimit c₀ := by
  refine ⟨fun H => H.van_kampen' c₀ hc₀, fun H => ?_⟩
  constructor
  simp_rw [BinaryCofan.isVanKampen_iff] at H ⊢
  intro X Y c hc X' Y' c' αX αY f hX hY
  obtain ⟨d, hd, hd'⟩ :=
    Limits.BinaryCofan.IsColimit.desc' hc (HT.from _ ≫ c₀.inl) (HT.from _ ≫ c₀.inr)
  rw [H c' (αX ≫ HT.from _) (αY ≫ HT.from _) (f ≫ d) (by rw [← reassoc_of% hX]; rw [hd]; rw [Category.assoc])
      (by rw [← reassoc_of% hY, hd', Category.assoc])]
  obtain ⟨hl, hr⟩ := (H c (HT.from _) (HT.from _) d hd.symm hd'.symm).mp ⟨hc⟩
  rw [hl.paste_vert_iff hX.symm]; rw [hr.paste_vert_iff hY.symm]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `types.finitaryExtensive` / 实例 `types.finitaryExtensive`

English:
instance types.finitaryExtensive
  signature: : FinitaryExtensive (Type u)
  body: by
  classical
  rw [finitaryExtensive_iff_of_isTerminal (Type u) PUnit Types.isTerminalPUnit _
      (Types.binaryCoproductColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => Types.binaryCoproductColimit X Y) _
      fun f g => (Limits.Types.pullbackLimitCone f g).2
  · intro _ _ _ _ f

中文:
实例 types.finitaryExtensive
  签名: : FinitaryExtensive (类型u)
  定义体: by
  classical
  rw [finitaryExtensive_iff_of_isTerminal (Type u) PUnit Types.isTerminalPUnit _
      (Types.binaryCoproductColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => Types.binaryCoproductColimit X Y) _
      fun f g => (Limits.Types.pullbackLimitCone f g).2
  · intro _ _ _ _ f

Depends on / 依赖: BinaryCofan, BinaryCofan.isVanKampen_mk, Concre, Limits, Limits.Types.pullbackLimitCone, PullbackCone, PullbackCone.isLimitAux, Sum.inl, Types.binaryCoproductColimit, Types.isTerminalPUnit, X.symm, apply_fun, binaryCoproductColimit, classical, finitaryExtensive_iff_of_isTerminal, isLimitAux, isTerminalPUnit, isVanKampen_mk, pullbackLimitCone, s.fst
-/
instance types.finitaryExtensive : FinitaryExtensive (Type u) := by
  classical
  rw [finitaryExtensive_iff_of_isTerminal (Type u) PUnit Types.isTerminalPUnit _
      (Types.binaryCoproductColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => Types.binaryCoproductColimit X Y) _
      fun f g => (Limits.Types.pullbackLimitCone f g).2
  · intro _ _ _ _ f hαX hαY
    constructor
    · refine ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : forall x, exists! y, s.fst x = Sum.inl y := by
        intro x
        rcases h : s.fst x with val | val
        · simp
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαY val :).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨↾(l), ?_, Types.isTerminalPUnit.hom_ext _ _, fun {l'} h₁ _ => ?_⟩
      · ext x
        exact (hl x).symm
      · ext x
        exact hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm
    · refine ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : forall x, exists! y, s.fst x = Sum.inr y := by
        intro x
        rcases h : s.fst x with val | val
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαX val :).symm
        · simp
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨↾l, ?_, Types.isTerminalPUnit.hom_ext _ _, fun {l'} h₁ _ => ?_⟩
      · ext x
        exact (hl x).symm
      · ext x
        exact hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm
  · intro Z f
    dsimp [Limits.Types.binaryCoproductCocone]
    have : forall x, f x = Sum.inl PUnit.unit ∨ f x = Sum.inr PUnit.unit := by
      intro x
      rcases f x with (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
      exacts [Or.inl rfl, Or.inr rfl]
    let eX : { p : Z × PUnit // f p.fst = Sum.inl p.snd } ≃ { x : Z // f x = Sum.inl PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, by convert! p.2⟩, fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext; rfl,
        fun _ => by ext; rfl⟩
    let eY : { p : Z × PUnit // f p.fst = Sum.inr p.snd } ≃ { x : Z // f x = Sum.inr PUnit.unit } :=
      ⟨fun p => ⟨p.1.1, p.2.trans (congr_arg Sum.inr <| Subsingleton.elim _ _)⟩,
        fun x => ⟨⟨_, _⟩, x.2⟩, fun _ => by ext; rfl, fun _ => by ext; rfl⟩
    fapply BinaryCofan.isColimitMk
    · exact fun s => ↾fun x => dite _ (fun h => s.inl <| eX.symm ⟨x, h⟩)
fun h => s.inr eY.symm ⟨x, (this x).resolve_left h⟩
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, _⟩
      dsimp
      split_ifs with h <;> tauto
    · intro s
      ext ⟨⟨x, ⟨⟩⟩, hx⟩
      dsimp
      split_ifs with h
      · cases h.symm.trans hx
      · rfl
    · intro s m e₁ e₂
      ext x
      simp only [TypeCat.Fun.toFun_apply, Types.binaryCoproductCocone_pt, pair_obj_left,
        Functor.const_obj_obj, pair_obj_right, ConcreteCategory.hom_ofHom, TypeCat.Fun.coe_mk]
      split_ifs
      · rw [← e₁]
        rfl
      · rw [← e₂]
        rfl

section TopCat

/--
Definition of `finitaryExtensiveTopCatAux` / `finitaryExtensiveTopCatAux` 的定义

English:
definition finitaryExtensiveTopCatAux
  signature: (Z : TopCat.{u})
  body: by
  have h₁ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inl) =
      f ⁻¹' Set.range Sum.inl := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  have h₂ : Set.range (

中文:
定义 finitaryExtensiveTopCatAux
  签名: (Z : TopCat.{u})
  定义体: by
  have h₁ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inl) =
      f ⁻¹' Set.range Sum.inl := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  have h₂ : Set.range (

Depends on / 依赖: PUnit.unit, Set.range, Sum.inl, Sum.inr, TopCat, TopCat.binaryCofan, TopCat.pullbackFst, binaryCofan, hx.s, hx.symm, le_antisymm, pullbackFst
-/
noncomputable def finitaryExtensiveTopCatAux (Z : TopCat.{u})
    (f : Z ⟶ TopCat.of (PUnit.{u + 1} oplus PUnit.{u + 1})) :
    IsColimit (BinaryCofan.mk
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inl)
      (TopCat.pullbackFst f (TopCat.binaryCofan (TopCat.of PUnit) (TopCat.of PUnit)).inr)) := by
  have h₁ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inl) =
      f ⁻¹' Set.range Sum.inl := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  have h₂ : Set.range (TopCat.pullbackFst f (TopCat.binaryCofan (.of PUnit) (.of PUnit)).inr) =
      f ⁻¹' Set.range Sum.inr := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ⟨PUnit.unit, x.2.symm⟩
    · rintro x ⟨⟨⟩, hx⟩; refine ⟨⟨⟨x, PUnit.unit⟩, hx.symm⟩, rfl⟩
  refine ((TopCat.binaryCofan_isColimit_iff _).mpr ⟨?_, ?_, ?_⟩).some
  · refine ⟨(Homeomorph.prodPUnit Z).isEmbedding.comp .subtypeVal, ?_⟩
    convert! f.hom.2.1 _ isOpen_range_inl
  · refine ⟨(Homeomorph.prodPUnit Z).isEmbedding.comp .subtypeVal, ?_⟩
    convert! f.hom.2.1 _ isOpen_range_inr
  · convert! Set.isCompl_range_inl_range_inr.preimage f

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `finitaryExtensive_TopCat` / 实例 `finitaryExtensive_TopCat`

English:
instance finitaryExtensive_TopCat
  signature: : FinitaryExtensive TopCat.{u}
  body: by
  rw [finitaryExtensive_iff_of_isTerminal TopCat.{u} _ TopCat.isTerminalPUnit _
      (TopCat.binaryCofanIsColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => TopCat.binaryCofanIsColimit X Y) _
      fun f g => TopCat.pullbackConeIsLimit f g
  · intro X' Y' αX αY f hαX hαY
    constr

中文:
实例 finitaryExtensive_TopCat
  签名: : FinitaryExtensive TopCat.{u}
  定义体: by
  rw [finitaryExtensive_iff_of_isTerminal TopCat.{u} _ TopCat.isTerminalPUnit _
      (TopCat.binaryCofanIsColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => TopCat.binaryCofanIsColimit X Y) _
      fun f g => TopCat.pullbackConeIsLimit f g
  · intro X' Y' αX αY f hαX hαY
    constr

Depends on / 依赖: BinaryCofan, BinaryCofan.isVanKampen_mk, PullbackCone, PullbackCone.isLimitAux, Sum.inl, Sum.inl_injective, TopCat, TopCat.binaryCofanIsColimit, TopCat.isTerminalPUnit, TopCat.pullbackConeIsLimit, X.symm, binaryCofanIsColimit, finitaryExtensive_iff_of_isTerminal, h.symm, inl_injective, isLimitAux, isTerminalPUnit, isVanKampen_mk, pullbackConeIsLimit, s.fst
-/
instance finitaryExtensive_TopCat : FinitaryExtensive TopCat.{u} := by
  rw [finitaryExtensive_iff_of_isTerminal TopCat.{u} _ TopCat.isTerminalPUnit _
      (TopCat.binaryCofanIsColimit _ _)]
  apply BinaryCofan.isVanKampen_mk _ _ (fun X Y => TopCat.binaryCofanIsColimit X Y) _
      fun f g => TopCat.pullbackConeIsLimit f g
  · intro X' Y' αX αY f hαX hαY
    constructor
    · refine ⟨⟨hαX.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : forall x, exists! y, s.fst x = Sum.inl y := by
        intro x
        rcases h : s.fst x with val | val
        · exact ⟨val, rfl, fun y h => Sum.inl_injective h.symm⟩
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαY val :).symm
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨TopCat.ofHom ⟨l, ?_⟩, TopCat.ext fun a => (hl a).symm,
        TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ => TopCat.ext fun x =>
          hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (IsEmbedding.inl (X := X') (Y := Y')).isInducing.continuous_iff.mpr
      convert! s.fst.hom.2 using 1
      exact (funext hl).symm
    · refine ⟨⟨hαY.symm⟩, ⟨PullbackCone.isLimitAux' _ ?_⟩⟩
      intro s
      have : forall x, exists! y, s.fst x = Sum.inr y := by
        intro x
        rcases h : s.fst x with val | val
        · apply_fun f at h
          cases ((ConcreteCategory.congr_hom s.condition x).symm.trans h).trans
            (ConcreteCategory.congr_hom hαX val :).symm
        · exact ⟨val, rfl, fun y h => Sum.inr_injective h.symm⟩
      delta ExistsUnique at this
      choose l hl hl' using this
      refine ⟨TopCat.ofHom ⟨l, ?_⟩, TopCat.ext fun a => (hl a).symm,
        TopCat.isTerminalPUnit.hom_ext _ _,
        fun {l'} h₁ _ =>
          TopCat.ext fun x => hl' x (l' x) (ConcreteCategory.congr_hom h₁ x).symm⟩
      apply (IsEmbedding.inr (X := X') (Y := Y')).isInducing.continuous_iff.mpr
      convert! s.fst.hom.2 using 1
      exact (funext hl).symm
  · intro Z f
    exact finitaryExtensiveTopCatAux Z f

end TopCat

section Functor

set_option backward.defeqAttrib.useBackward true in
/--
theorem `finitaryExtensive_of_reflective` / 定理 `finitaryExtensive_of_reflective`

English:
theorem finitaryExtensive_of_reflective
  proof: by
  have : PreservesColimitsOfSize Gl := adj.leftAdjoint_preservesColimits
  constructor
  intro X Y c hc
  apply (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp
  have : forall (Z : C) (i : Discrete WalkingPair) (f : Z ⟶ (

中文:
定理 finitaryExtensive_of_reflective
  证明: by
  have : PreservesColimitsOfSize Gl := adj.leftAdjoint_preservesColimits
  constructor
  intro X Y c hc
  apply (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp
  have : forall (Z : C) (i : Discrete WalkingPair) (f : Z ⟶ (

Depends on / 依赖: Discrete, Functor, Functor.hext, Functor.isoWhiskerLeft, Functor.rightUnitor, Gr.obj, IsVanKampenColimit, IsVanKampenColimit.precompose_isIso_iff, PreservesColimitsOfSize, PreservesLimit, WalkingPair, adj.counit, adj.leftAdjoint_preservesColimits, cocone, colimit, colimit.cocone, cospan, counit, isoWhiskerLeft, leftAdjoint_preservesColimits
-/
theorem finitaryExtensive_of_reflective
    [HasFiniteCoproducts D] [HasPullbacksOfInclusions D] [FinitaryExtensive C]
    {Gl : C ⥤ D} {Gr : D ⥤ C} (adj : Gl ⊣ Gr) [Gr.Full] [Gr.Faithful]
    [forall X Y (f : X ⟶ Gl.obj Y), HasPullback (Gr.map f) (adj.unit.app Y)]
    [forall X Y (f : X ⟶ Gl.obj Y), PreservesLimit (cospan (Gr.map f) (adj.unit.app Y)) Gl]
    [PreservesPullbacksOfInclusions Gl] :
    FinitaryExtensive D := by
  have : PreservesColimitsOfSize Gl := adj.leftAdjoint_preservesColimits
  constructor
  intro X Y c hc
  apply (IsVanKampenColimit.precompose_isIso_iff
    (Functor.isoWhiskerLeft _ (asIso adj.counit) ≪≫ Functor.rightUnitor _).hom).mp
  have : forall (Z : C) (i : Discrete WalkingPair) (f : Z ⟶ (colimit.cocone (pair X Y ⋙ Gr)).pt),
        PreservesLimit (cospan f ((colimit.cocone (pair X Y ⋙ Gr)).ι.app i)) Gl := by
    have : pair X Y ⋙ Gr = pair (Gr.obj X) (Gr.obj Y) := by
      apply Functor.hext
      · rintro ⟨⟨⟩⟩ <;> rfl
      · rintro ⟨⟨⟩⟩ ⟨j⟩ ⟨⟨rfl : _ = j⟩⟩ <;> simp
    rw [this]
    rintro Z ⟨_ | _⟩ f <;> dsimp <;> infer_instance
  refine ((FinitaryExtensive.vanKampen _ (colimit.isColimit <| pair X Y ⋙ _)).map_reflective
    adj).of_iso (IsColimit.uniqueUpToIso ?_ ?_)
  · exact isColimitOfPreserves Gl (colimit.isColimit _)
  · exact (IsColimit.precomposeHomEquiv _ _).symm hc

/--
Instance `finitaryExtensive_functor` / 实例 `finitaryExtensive_functor`

English:
instance finitaryExtensive_functor
  signature: [HasPullbacks C] [FinitaryExtensive C]
  body: haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
FinitaryExtensive.vanKampen _ isColimitOfPreserves _ hc⟩

中文:
实例 finitaryExtensive_functor
  签名: [HasPullbacks C] [FinitaryExtensive C]
  定义体: haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
FinitaryExtensive.vanKampen _ isColimitOfPreserves _ hc⟩

Depends on / 依赖: FinitaryExtensive, FinitaryExtensive.vanKampen, HasFiniteCoproducts, Limits, Limits.functorCategoryHasColimitsOfShape, functorCategoryHasColimitsOfShape, isColimitOfPreserves, isVanKampenColimit_of_evaluation, vanKampen
-/
instance finitaryExtensive_functor [HasPullbacks C] [FinitaryExtensive C] :
    FinitaryExtensive (D ⥤ C) :=
  haveI : HasFiniteCoproducts (D ⥤ C) := ⟨fun _ => Limits.functorCategoryHasColimitsOfShape⟩
  ⟨fun c hc => isVanKampenColimit_of_evaluation _ c fun _ =>
FinitaryExtensive.vanKampen _ isColimitOfPreserves _ hc⟩

instance {C} [Category* C] {D} [Category* D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso f] : PreservesLimit (cospan f g) F :=
  have := hasPullback_of_left_iso f g
  preservesLimit_of_preserves_limit_cone (IsPullback.of_hasPullback f g).isLimit
    ((isLimitMapConePullbackConeEquiv _ pullback.condition).symm
      (IsPullback.of_vert_isIso ⟨by simp only [← F.map_comp, pullback.condition]⟩).isLimit)

instance {C} [Category* C] {D} [Category* D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g] : PreservesLimit (cospan f g) F :=
  preservesPullback_symmetry _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finitaryExtensive_of_preserves_and_reflects` / 定理 `finitaryExtensive_of_preserves_and_reflects`

English:
theorem finitaryExtensive_of_preserves_and_reflects
  statement: (F : C ⥤ D) [FinitaryExtensive D]
  proof: by
  constructor
  intro X Y c hc
  refine IsVanKampenColimit.of_iso ?_ (hc.uniqueUpToIso (coprodIsCoprod X Y)).symm
  have (i : Discrete WalkingPair) (Z : C) (f : Z ⟶ X ⨿ Y) :
    PreservesLimit (cospan f ((BinaryCofan.mk coprod.inl coprod.inr).ι.app i)) F := by
    rcases i with ⟨_ | _⟩ <;> dsimp 

中文:
定理 finitaryExtensive_of_preserves_and_reflects
  结论: (F : C ⥤ D) [FinitaryExtensive D]
  证明: by
  constructor
  intro X Y c hc
  refine IsVanKampenColimit.of_iso ?_ (hc.uniqueUpToIso (coprodIsCoprod X Y)).symm
  have (i : Discrete WalkingPair) (Z : C) (f : Z ⟶ X ⨿ Y) :
    PreservesLimit (cospan f ((BinaryCofan.mk coprod.inl coprod.inr).ι.app i)) F := by
    rcases i with ⟨_ | _⟩ <;> dsimp 

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, Discrete, FinitaryExtensive, FinitaryExtensive.vanKampen, IsVanKampenColimit, IsVanKampenColimit.of_iso, PreservesLimit, WalkingPair, coprod, coprod.inl, coprod.inr, coprodIsCoprod, cospan, hc.uniqueUpToIso, infer_instance, isColimitOfPreserves, of_iso, of_mapCocone, uniqueUpToIso
-/
theorem finitaryExtensive_of_preserves_and_reflects (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacksOfInclusions C]
    [PreservesPullbacksOfInclusions F]
    [ReflectsLimitsOfShape WalkingCospan F] [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [ReflectsColimitsOfShape (Discrete WalkingPair) F] : FinitaryExtensive C := by
  constructor
  intro X Y c hc
  refine IsVanKampenColimit.of_iso ?_ (hc.uniqueUpToIso (coprodIsCoprod X Y)).symm
  have (i : Discrete WalkingPair) (Z : C) (f : Z ⟶ X ⨿ Y) :
    PreservesLimit (cospan f ((BinaryCofan.mk coprod.inl coprod.inr).ι.app i)) F := by
    rcases i with ⟨_ | _⟩ <;> dsimp <;> infer_instance
  refine (FinitaryExtensive.vanKampen _
    (isColimitOfPreserves F (coprodIsCoprod X Y))).of_mapCocone F

/--
theorem `finitaryExtensive_of_preserves_and_reflects_isomorphism` / 定理 `finitaryExtensive_of_preserves_and_reflects_isomorphism`

English:
theorem finitaryExtensive_of_preserves_and_reflects_isomorphism
  statement: (F : C ⥤ D) [FinitaryExtensive D]
  proof: by
  have : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F

中文:
定理 finitaryExtensive_of_preserves_and_reflects_isomorphism
  结论: (F : C ⥤ D) [FinitaryExtensive D]
  证明: by
  have : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F

Depends on / 依赖: Discrete, ReflectsColimitsOfShape, ReflectsLimitsOfShape, WalkingCospan, WalkingPair, finitaryExtensive_of_preserves_and_reflects, reflectsColimitsOfShape_of_reflectsIsomorphisms, reflectsLimitsOfShape_of_reflectsIsomorphisms
-/
theorem finitaryExtensive_of_preserves_and_reflects_isomorphism (F : C ⥤ D) [FinitaryExtensive D]
    [HasFiniteCoproducts C] [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F]
    [PreservesColimitsOfShape (Discrete WalkingPair) F] [F.ReflectsIsomorphisms] :
    FinitaryExtensive C := by
  have : ReflectsLimitsOfShape WalkingCospan F := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : ReflectsColimitsOfShape (Discrete WalkingPair) F :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact finitaryExtensive_of_preserves_and_reflects F

end Functor

section FiniteCoproducts

set_option backward.defeqAttrib.useBackward true in
/--
theorem `FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin` / 定理 `FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin`

English:
theorem FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin
  statement: [FinitaryPreExtensive C] {n : Nat}
  proof: by
  let f : Fin n -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact (isVanKampenColimit_of_isEmpty _ hc).isUniversal
  | succ n IH =>
    refi

中文:
定理 FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin
  结论: [FinitaryPreExtensive C] {n : 自然数}
  证明: by
  let f : Fin n -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact (isVanKampenColimit_of_isEmpty _ hc).isUniversal
  | succ n IH =>
    refi

Depends on / 依赖: Discrete, Discrete.functor, Discrete.mk, F.obj, FinitaryPreExtensive, FinitaryPreExtensive.universal, Functor, Functor.hext, IsUniversalColimit, IsUniversalColimit.of_iso, clear_value, coprodIsCoprod, coproductIsCoproduct, extendCofanIsColimit, functor, isUniversal, isUniversalColimit_extendCofan, isVanKampenColimit_of_isEmpty, of_iso, universal
-/
theorem FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin [FinitaryPreExtensive C] {n : Nat}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  let f : Fin n -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact (isVanKampenColimit_of_isEmpty _ hc).isUniversal
  | succ n IH =>
    refine IsUniversalColimit.of_iso (@isUniversalColimit_extendCofan _ _ _ _ _ _
      (IH _ (coproductIsCoproduct _)) (FinitaryPreExtensive.universal' _ (coprodIsCoprod _ _)) ?_)
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    · dsimp
      infer_instance

/--
theorem `FinitaryPreExtensive.isUniversal_finiteCoproducts` / 定理 `FinitaryPreExtensive.isUniversal_finiteCoproducts`

English:
theorem FinitaryPreExtensive.isUniversal_finiteCoproducts
  statement: [FinitaryPreExtensive C] {ι : Type*}
  proof: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsUniversalColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

中文:
定理 FinitaryPreExtensive.isUniversal_finiteCoproducts
  结论: [FinitaryPreExtensive C] {ι : 类型}
  证明: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsUniversalColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

Depends on / 依赖: Discrete, Discrete.equivalence, FinitaryPreExtensive, FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin, Finite, Finite.exists_equiv_fin, IsColimit, IsColimit.whiskerEquivalenceEquiv, IsSplitMono, IsSplitMono.mk, IsUniversalColimit, IsUniversalColimit.whiskerEquivalence_iff, equivalence, exists_equiv_fin, isUniversal_finiteCoproducts_Fin, prod.fst, retraction, whiskerEquivalenceEquiv, whiskerEquivalence_iff
-/
theorem FinitaryPreExtensive.isUniversal_finiteCoproducts [FinitaryPreExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsUniversalColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsUniversalColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryPreExtensive.isUniversal_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

set_option backward.defeqAttrib.useBackward true in
/--
theorem `FinitaryExtensive.isVanKampen_finiteCoproducts_Fin` / 定理 `FinitaryExtensive.isVanKampen_finiteCoproducts_Fin`

English:
theorem FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  statement: [FinitaryExtensive C] {n : Nat}
  proof: by
  let f : Fin n -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact isVanKampenColimit_of_isEmpty _ hc
  | succ n IH =>
    apply IsVanKampenC

中文:
定理 FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  结论: [FinitaryExtensive C] {n : 自然数}
  证明: by
  let f : Fin n -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact isVanKampenColimit_of_isEmpty _ hc
  | succ n IH =>
    apply IsVanKampenC

Depends on / 依赖: Discrete, Discrete.functor, Discrete.mk, F.obj, FinitaryExt, Functor, Functor.hext, IsVanKampenColimit, IsVanKampenColimit.of_iso, clear_value, coprodIsCoprod, coproductIsCoproduct, extendCofanIsColimit, functor, isVanKampenColimit_extendCofan, isVanKampenColimit_of_isEmpty, of_iso, uniqueUpToIso
-/
theorem FinitaryExtensive.isVanKampen_finiteCoproducts_Fin [FinitaryExtensive C] {n : Nat}
    {F : Discrete (Fin n) ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  let f : Fin n -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun _ => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  induction n with
  | zero => exact isVanKampenColimit_of_isEmpty _ hc
  | succ n IH =>
    apply IsVanKampenColimit.of_iso _
      ((extendCofanIsColimit f (coproductIsCoproduct _) (coprodIsCoprod _ _)).uniqueUpToIso hc)
    apply @isVanKampenColimit_extendCofan _ _ _ _ _ _ _ _ ?_
    · apply IH
      exact coproductIsCoproduct _
    · apply FinitaryExtensive.van_kampen'
      exact coprodIsCoprod _ _
    · dsimp
      infer_instance

/--
theorem `FinitaryExtensive.isVanKampen_finiteCoproducts` / 定理 `FinitaryExtensive.isVanKampen_finiteCoproducts`

English:
theorem FinitaryExtensive.isVanKampen_finiteCoproducts
  statement: [FinitaryExtensive C] {ι : Type*}
  proof: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsVanKampenColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

中文:
定理 FinitaryExtensive.isVanKampen_finiteCoproducts
  结论: [FinitaryExtensive C] {ι : 类型}
  证明: by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsVanKampenColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

Depends on / 依赖: Discrete, Discrete.equivalence, FinitaryExtensive, FinitaryExtensive.isVanKampen_finiteCoproducts_Fin, Finite, Finite.exists_equiv_fin, IsColimit, IsColimit.whiskerEquivalenceEquiv, IsVanKampenColimit, IsVanKampenColimit.whiskerEquivalence_iff, equivalence, exists_equiv_fin, isVanKampen_finiteCoproducts_Fin, whiskerEquivalenceEquiv, whiskerEquivalence_iff
-/
theorem FinitaryExtensive.isVanKampen_finiteCoproducts [FinitaryExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) : IsVanKampenColimit c := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  apply (IsVanKampenColimit.whiskerEquivalence_iff (Discrete.equivalence e).symm).mp
  apply FinitaryExtensive.isVanKampen_finiteCoproducts_Fin
  exact (IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e).symm) hc

set_option backward.isDefEq.respectTransparency false in
/--
lemma `FinitaryPreExtensive.hasPullbacks_of_is_coproduct` / 引理 `FinitaryPreExtensive.hasPullbacks_of_is_coproduct`

English:
lemma FinitaryPreExtensive.hasPullbacks_of_is_coproduct
  statement: [FinitaryPreExtensive C] {ι : Type*}
  proof: by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  change Cofan f at c
  obtain ⟨i⟩ := i
  let e : ∐ f ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) => f j) :=
  { 

中文:
引理 FinitaryPreExtensive.hasPullbacks_of_is_coproduct
  结论: [FinitaryPreExtensive C] {ι : 类型}
  证明: by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  change Cofan f at c
  obtain ⟨i⟩ := i
  let e : ∐ f ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) => f j) :=
  { 

Depends on / 依赖: Discrete, Discrete.functor, Discrete.mk, F.obj, Functor, Functor.hext, Sigma.desc, classical, clear_value, congr_arg, coprod, coprod.desc, coprod.inl, coprod.inr, eqToHom, functor, hom_in
-/
lemma FinitaryPreExtensive.hasPullbacks_of_is_coproduct [FinitaryPreExtensive C] {ι : Type*}
    [Finite ι] {F : Discrete ι ⥤ C} {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) {X : C}
    (g : X ⟶ _) : HasPullback g (c.ι.app i) := by
  classical
  let f : ι -> C := F.obj ∘ Discrete.mk
  have : F = Discrete.functor f :=
    Functor.hext (fun i => rfl) (by rintro ⟨i⟩ ⟨j⟩ ⟨⟨rfl : i = j⟩⟩; simp [f])
  clear_value f
  subst this
  change Cofan f at c
  obtain ⟨i⟩ := i
  let e : ∐ f ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) => f j) :=
  { hom := Sigma.desc (fun j => if h : j = i then eqToHom (congr_arg f h) ≫ coprod.inl else
      Sigma.ι (fun j : ({i}ᶜ : Set ι) => f j) ⟨j, h⟩ ≫ coprod.inr)
    inv := coprod.desc (Sigma.ι f i) (Sigma.desc fun j => Sigma.ι f j)
    hom_inv_id := by cat_disch
    inv_hom_id := by
      ext j
      · simp
      · simp only [coprod.desc_comp, colimit.ι_desc, Cofan.mk_ι_app,
          eqToHom_refl, Category.id_comp, dite_true, BinaryCofan.ι_app_right,
          BinaryCofan.mk_inr, colimit.ι_desc_assoc, Discrete.functor_obj, Category.comp_id]
        exact dif_neg j.prop }
  let e' : c.pt ≅ f i ⨿ (∐ fun j : ({i}ᶜ : Set ι) => f j) :=
    hc.coconePointUniqueUpToIso (getColimitCocone _).2 ≪≫ e
  have : coprod.inl ≫ e'.inv = c.ι.app ⟨i⟩ := by
    simp only [e, e', Iso.trans_inv, coprod.desc_comp, colimit.ι_desc,
      BinaryCofan.ι_app_left, BinaryCofan.mk_inl]
    exact colimit.comp_coconePointUniqueUpToIso_inv _ _
  clear_value e'
  rw [← this]
  have : IsPullback (𝟙 _) (g ≫ e'.hom) g e'.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact ⟨⟨⟨_, ((IsPullback.of_hasPullback (g ≫ e'.hom) coprod.inl).paste_horiz this).isLimit⟩⟩⟩

/--
lemma `FinitaryExtensive.mono_ι` / 引理 `FinitaryExtensive.mono_ι`

English:
lemma FinitaryExtensive.mono_ι
  statement: [FinitaryExtensive C] {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
  proof: mono_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) _

中文:
引理 FinitaryExtensive.mono_ι
  结论: [FinitaryExtensive C] {ι : 类型} [Finite ι] {F : Discrete ι ⥤ C}
  证明: mono_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) _

Depends on / 依赖: isVanKampen_finiteCoproducts, mono_of_cofan_isVanKampen
-/
lemma FinitaryExtensive.mono_ι [FinitaryExtensive C] {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (i : Discrete ι) :
    Mono (c.ι.app i) :=
  mono_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [FinitaryExtensive
  signature: C] {ι
  body: FinitaryExtensive.mono_ι (coproductIsCoproduct _) ⟨i⟩

中文:
实例 [FinitaryExtensive
  签名: C] {ι
  定义体: FinitaryExtensive.mono_ι (coproductIsCoproduct _) ⟨i⟩

Depends on / 依赖: FinitaryExtensive, FinitaryExtensive.mono_, coproductIsCoproduct
-/
instance [FinitaryExtensive C] {ι : Type*} [Finite ι] (X : ι -> C) (i : ι) :
    Mono (Sigma.ι X i) :=
  FinitaryExtensive.mono_ι (coproductIsCoproduct _) ⟨i⟩

/--
lemma `FinitaryExtensive.isPullback_initial_to` / 引理 `FinitaryExtensive.isPullback_initial_to`

English:
lemma FinitaryExtensive.isPullback_initial_to
  statement: [FinitaryExtensive C]
  proof: isPullback_initial_to_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) i j e

中文:
引理 FinitaryExtensive.isPullback_initial_to
  结论: [FinitaryExtensive C]
  证明: isPullback_initial_to_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) i j e

Depends on / 依赖: isPullback_initial_to_of_cofan_isVanKampen, isVanKampen_finiteCoproducts
-/
lemma FinitaryExtensive.isPullback_initial_to [FinitaryExtensive C]
    {ι : Type*} [Finite ι] {F : Discrete ι ⥤ C}
    {c : Cocone F} (hc : IsColimit c) (i j : Discrete ι) (e : i != j) :
    IsPullback (initial.to _) (initial.to _) (c.ι.app i) (c.ι.app j) :=
  isPullback_initial_to_of_cofan_isVanKampen (isVanKampen_finiteCoproducts hc) i j e

/--
lemma `FinitaryExtensive.isPullback_initial_to_sigma_ι` / 引理 `FinitaryExtensive.isPullback_initial_to_sigma_ι`

English:
lemma FinitaryExtensive.isPullback_initial_to_sigma_ι
  statement: [FinitaryExtensive C] {ι : Type*} [Finite ι]
  proof: FinitaryExtensive.isPullback_initial_to (coproductIsCoproduct _) ⟨i⟩ ⟨j⟩
    (ne_of_apply_ne Discrete.as e)

中文:
引理 FinitaryExtensive.isPullback_initial_to_sigma_ι
  结论: [FinitaryExtensive C] {ι : 类型} [Finite ι]
  证明: FinitaryExtensive.isPullback_initial_to (coproductIsCoproduct _) ⟨i⟩ ⟨j⟩
    (ne_of_apply_ne Discrete.as e)

Depends on / 依赖: Discrete, Discrete.as, FinitaryExtensive, FinitaryExtensive.isPullback_initial_to, coproductIsCoproduct, isPullback_initial_to, ne_of_apply_ne
-/
lemma FinitaryExtensive.isPullback_initial_to_sigma_ι [FinitaryExtensive C] {ι : Type*} [Finite ι]
    (X : ι -> C) (i j : ι) (e : i != j) :
    IsPullback (initial.to _) (initial.to _) (Sigma.ι X i) (Sigma.ι X j) :=
  FinitaryExtensive.isPullback_initial_to (coproductIsCoproduct _) ⟨i⟩ ⟨j⟩
    (ne_of_apply_ne Discrete.as e)

-- TODO: generalize to arbitrary `ι` if `HasCoproductsOfShape ι C`.
instance (priority := low) [FinitaryExtensive C] {ι : Type*} [Finite ι] :
    CoproductsOfShapeDisjoint C ι where
  coproductDisjoint X := by
    refine ⟨fun {c} hc i j e s hs => ?_, fun hc i => FinitaryExtensive.mono_ι hc ⟨i⟩⟩
    exact ⟨initialIsInitial.ofIso ((FinitaryExtensive.isPullback_initial_to hc ⟨i⟩ ⟨j⟩
      (by simpa)).isoIsPullback _ _ (IsPullback.of_isLimit hs))⟩

/--
Instance `FinitaryPreExtensive.hasPullbacks_of_inclusions` / 实例 `FinitaryPreExtensive.hasPullbacks_of_inclusions`

English:
instance FinitaryPreExtensive.hasPullbacks_of_inclusions
  signature: [FinitaryPreExtensive C] {X Z : C}
  body: by
  apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct (c := Cofan.mk Z i)
  exact @IsColimit.ofPointIso (t := Cofan.mk Z i) (P := _) (i := hi)

中文:
实例 FinitaryPreExtensive.hasPullbacks_of_inclusions
  签名: [FinitaryPreExtensive C] {X Z : C}
  定义体: by
  apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct (c := Cofan.mk Z i)
  exact @IsColimit.ofPointIso (t := Cofan.mk Z i) (P := _) (i := hi)

Depends on / 依赖: Cofan.mk, FinitaryPreExtensive, FinitaryPreExtensive.hasPullbacks_of_is_coproduct, IsColimit, IsColimit.ofPointIso, hasPullbacks_of_is_coproduct, ofPointIso
-/
instance FinitaryPreExtensive.hasPullbacks_of_inclusions [FinitaryPreExtensive C] {X Z : C}
    {α : Type*} (f : X ⟶ Z) {Y : (a : α) -> C} (i : (a : α) -> Y a ⟶ Z) [Finite α]
    [hi : IsIso (Sigma.desc i)] (a : α) : HasPullback f (i a) := by
  apply FinitaryPreExtensive.hasPullbacks_of_is_coproduct (c := Cofan.mk Z i)
  exact @IsColimit.ofPointIso (t := Cofan.mk Z i) (P := _) (i := hi)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `FinitaryPreExtensive.isIso_sigmaDesc_fst` / 引理 `FinitaryPreExtensive.isIso_sigmaDesc_fst`

English:
lemma FinitaryPreExtensive.isIso_sigmaDesc_fst
  statement: [FinitaryPreExtensive C] {α : Type} [Finite α]
  proof: by
  let c := (Cofan.mk _ ((fun _ => pullback.fst _ _) : (a : α) -> pullback f (π a) ⟶ _))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk X π) := FinitaryPreExtensive.isUniversal_finiteCoproducts
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr

中文:
引理 FinitaryPreExtensive.isIso_sigmaDesc_fst
  结论: [FinitaryPreExtensive C] {α : Type} [Finite α]
  证明: by
  let c := (Cofan.mk _ ((fun _ => pullback.fst _ _) : (a : α) -> pullback f (π a) ⟶ _))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk X π) := FinitaryPreExtensive.isUniversal_finiteCoproducts
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr

Depends on / 依赖: Cofan.mk, Cofan.nonempty_isColimit_iff_isIso_sigmaDesc, FinitaryPreExtensive, FinitaryPreExtensive.isUniversal_finiteCoproducts, IsPullback, IsPullback.id_horiz, IsUniversalColimit, Iso.refl, PullbackCone, PullbackCone.mk, c.nonempty_isColimit_iff_isIso_sigmaDesc.mp, hau.nonempty_isColimit_of_pullbackCone_left, id_horiz, isLimit, isUniversal_finiteCoproducts, nonempty_isColimit_iff_isIso_sigmaDesc, nonempty_isColimit_of_pullbackCone_left, pullba, pullback, pullback.fst
-/
lemma FinitaryPreExtensive.isIso_sigmaDesc_fst [FinitaryPreExtensive C] {α : Type} [Finite α]
    {X : C} {Z : α -> C} (π : (a : α) -> Z a ⟶ X) {Y : C} (f : Y ⟶ X) (hπ : IsIso (Sigma.desc π)) :
    IsIso (Sigma.desc ((fun _ => pullback.fst _ _) : (a : α) -> pullback f (π a) ⟶ _)) := by
  let c := (Cofan.mk _ ((fun _ => pullback.fst _ _) : (a : α) -> pullback f (π a) ⟶ _))
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  have hau : IsUniversalColimit (Cofan.mk X π) := FinitaryPreExtensive.isUniversal_finiteCoproducts
    ((Cofan.nonempty_isColimit_iff_isIso_sigmaDesc _).mpr hπ).some
  refine hau.nonempty_isColimit_of_pullbackCone_left _ (𝟙 _) _ _ (fun i => ?_)
    (PullbackCone.mk (𝟙 _) f (by simp)) (IsPullback.id_horiz f).isLimit _ (Iso.refl _)
    (by simp) (by simp [c]) (by simp [pullback.condition, c])
  exact pullback.isLimit _ _

set_option backward.isDefEq.respectTransparency false in
/--
Instance `FinitaryPreExtensive.isIso_sigmaDesc_map` / 实例 `FinitaryPreExtensive.isIso_sigmaDesc_map`

English:
instance FinitaryPreExtensive.isIso_sigmaDesc_map
  signature: [HasPullbacks C] [FinitaryPreExtensive C]
  body: by
let c : Cofan _ := Cofan.mk _ fun (p : ι × ι') =>
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackC

中文:
实例 FinitaryPreExtensive.isIso_sigmaDesc_map
  签名: [HasPullbacks C] [FinitaryPreExtensive C]
  定义体: by
let c : Cofan _ := Cofan.mk _ fun (p : ι × ι') =>
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackC

Depends on / 依赖: Cofan.mk, IsUniversalColimit, IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone, Sigma.desc, c.nonempty_isColimit_iff_isIso_sigmaDesc.mp, isLimit, nonempty_isColimit_iff_isIso_sigmaDesc, nonempty_isColimit_prod_of_pullbackCone, pullba, pullback, pullback.cone, pullback.isLimit, pullback.map
-/
instance FinitaryPreExtensive.isIso_sigmaDesc_map [HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι -> C} {Y : ι' -> C}
    (f : forall i, X i ⟶ S) (g : forall i, Y i ⟶ S) :
    IsIso (Sigma.desc fun (p : ι × ι') =>
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)) := by
let c : Cofan _ := Cofan.mk _ fun (p : ι × ι') =>
      pullback.map (f p.1) (g p.2) (Sigma.desc f) (Sigma.desc g) (Sigma.ι _ p.1)
        (Sigma.ι _ p.2) (𝟙 S) (by simp) (by simp)
  apply c.nonempty_isColimit_iff_isIso_sigmaDesc.mp
  refine IsUniversalColimit.nonempty_isColimit_prod_of_pullbackCone
      (a := Cofan.mk _ <| fun i => Sigma.ι _ i) (b := Cofan.mk _ <| fun i => Sigma.ι _ i)
      ?_ ?_ f g (Sigma.desc f) (Sigma.desc g) (fun i j => (pullback.cone (f i) (g j)))
      (fun i j => pullback.isLimit (f i) (g j)) (pullback.cone _ _) ?_ (Iso.refl _)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)
  · exact pullback.isLimit (Sigma.desc f) (Sigma.desc g)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `FinitaryPreExtensive.isPullback_sigmaDesc` / 引理 `FinitaryPreExtensive.isPullback_sigmaDesc`

English:
lemma FinitaryPreExtensive.isPullback_sigmaDesc
  statement: [HasPullbacks C] [FinitaryPreExtensive C]
  proof: by
  convert!
    IsUniversalColimit.isPullback_prod_of_isColimit (d :=
      Cofan.mk _ (Sigma.ι fun (p : ι × ι') => pullback (f p.1) (g p.2))) (hd :=
      coproductIsCoproduct (fun (p : ι × ι') => pullback (f p.1) (g p.2))) (a :=
Cofan.mk _ fun i => Sigma.ι _ i) (b := Cofan.mk _ fun i => Sigma.ι 

中文:
引理 FinitaryPreExtensive.isPullback_sigmaDesc
  结论: [HasPullbacks C] [FinitaryPreExtensive C]
  证明: by
  convert!
    IsUniversalColimit.isPullback_prod_of_isColimit (d :=
      Cofan.mk _ (Sigma.ι fun (p : ι × ι') => pullback (f p.1) (g p.2))) (hd :=
      coproductIsCoproduct (fun (p : ι × ι') => pullback (f p.1) (g p.2))) (a :=
Cofan.mk _ fun i => Sigma.ι _ i) (b := Cofan.mk _ fun i => Sigma.ι 

Depends on / 依赖: Cofan.IsColimit.desc, Cofan.mk, IsColimit, IsPullback, IsPullback.of_hasPullback, IsUniversalColimit, IsUniversalColimit.isPullback_prod_of_isColimit, Sigma.desc, convert, coproductIsCop, coproductIsCoproduct, isPullback_prod_of_isColimit, of_hasPullback, pullback
-/
lemma FinitaryPreExtensive.isPullback_sigmaDesc [HasPullbacks C] [FinitaryPreExtensive C]
    {ι ι' : Type*} [Finite ι] [Finite ι'] {S : C} {X : ι -> C} {Y : ι' -> C}
    (f : forall i, X i ⟶ S) (g : forall i, Y i ⟶ S) :
    IsPullback
      (Limits.Sigma.desc fun (p : ι × ι') => pullback.fst (f p.1) (g p.2) ≫ Sigma.ι X p.1)
      (Limits.Sigma.desc fun (p : ι × ι') => pullback.snd (f p.1) (g p.2) ≫ Sigma.ι Y p.2)
      (Limits.Sigma.desc f) (Limits.Sigma.desc g) := by
  convert!
    IsUniversalColimit.isPullback_prod_of_isColimit (d :=
      Cofan.mk _ (Sigma.ι fun (p : ι × ι') => pullback (f p.1) (g p.2))) (hd :=
      coproductIsCoproduct (fun (p : ι × ι') => pullback (f p.1) (g p.2))) (a :=
Cofan.mk _ fun i => Sigma.ι _ i) (b := Cofan.mk _ fun i => Sigma.ι _ i) ?_ ?_ f g
      (Sigma.desc f) (Sigma.desc g) (fun i j => IsPullback.of_hasPullback (f i) (g j))
  · ext
    simp [Cofan.IsColimit.desc, Sigma.ι, coproductIsCoproduct]
  · ext
    simp [Cofan.IsColimit.desc, Sigma.ι, coproductIsCoproduct]
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X)
  · exact FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct Y)

end FiniteCoproducts

end Extensive

end CategoryTheory
