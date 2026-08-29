/-
Copyright (c) 2024 Christian Merten, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!

# Proper morphisms

A morphism of schemes is proper if it is separated, universally closed and (locally) of finite type.
Note that we don't require quasi-compact, since this is implied by universally closed.

## Main results
- `AlgebraicGeometry.isField_of_universallyClosed`:
  If `X` is an integral scheme that is universally closed over `Spec K`, then `Γ(X, ⊤)` is a field.
- `AlgebraicGeometry.finite_appTop_of_universallyClosed`:
  If `X` is an integral scheme that is universally closed and of finite type over `Spec K`,
  then `Γ(X, ⊤)` is finite dimensional over `K`.

-/

public section


noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y Z S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism is proper if it is separated, universally closed and locally of finite type. -/
@[mk_iff]
/--
Definition of `IsProper` / `IsProper` 的定义

English:
class IsProper
  parameters: : Prop extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f where
  extends: IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f
  (no additional axioms)

中文:
类 是真
  参数: : 命题 extends 是分离 f, 普遍闭 f, 局部有限型 f where
  继承: 是分离 f, 普遍闭 f, 局部有限型 f
  (无附加公理)
-/
class IsProper : Prop extends IsSeparated f, UniversallyClosed f, LocallyOfFiniteType f where

/--
lemma `isProper_eq` / 引理 `isProper_eq`

English:
lemma isProper_eq
  statement: @IsProper =
  proof: by
  ext X Y f
  rw [isProper_iff]; rw [← and_assoc]
  rfl

中文:
引理 isProper_eq
  结论: @是真 =
  证明: by
  ext X Y f
  rw [isProper_iff]; rw [← and_assoc]
  rfl

Depends on / 依赖: and_assoc, isProper_iff
-/
lemma isProper_eq : @IsProper =
    (@IsSeparated ⊓ @UniversallyClosed : MorphismProperty Scheme) ⊓ @LocallyOfFiniteType := by
  ext X Y f
  rw [isProper_iff]; rw [← and_assoc]
  rfl

namespace IsProper

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.RespectsIso @IsProper
  body: by
  rw [isProper_eq]
  infer_instance

中文:
实例 :
  签名: MorphismProperty.RespectsIso @是真
  定义体: by
  rw [isProper_eq]
  infer_instance

Depends on / 依赖: infer_instance, isProper_eq
-/
instance : MorphismProperty.RespectsIso @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `stableUnderComposition` / 实例 `stableUnderComposition`

English:
instance stableUnderComposition
  signature: : MorphismProperty.IsStableUnderComposition @IsProper
  body: by
  rw [isProper_eq]
  infer_instance

中文:
实例 stableUnderComposition
  签名: : MorphismProperty.是StableUnderComposition @是真
  定义体: by
  rw [isProper_eq]
  infer_instance

Depends on / 依赖: infer_instance, isProper_eq
-/
instance stableUnderComposition : MorphismProperty.IsStableUnderComposition @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative @IsProper
  body: by
  rw [isProper_eq]
  infer_instance

中文:
实例 :
  签名: MorphismProperty.是Multiplicative @是真
  定义体: by
  rw [isProper_eq]
  infer_instance

Depends on / 依赖: infer_instance, isProper_eq
-/
instance : MorphismProperty.IsMultiplicative @IsProper := by
  rw [isProper_eq]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsProper
  signature: f] [IsProper g] : IsProper (f ≫ g) where

中文:
实例 [是真
  签名: f] [是真 g] : 是真 (f ≫ g) where
-/
instance [IsProper f] [IsProper g] : IsProper (f ≫ g) where

instance (priority := 900) [IsFinite f] : IsProper f where

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isStableUnderBaseChange` / 实例 `isStableUnderBaseChange`

English:
instance isStableUnderBaseChange
  signature: : MorphismProperty.IsStableUnderBaseChange @IsProper
  body: by
  rw [isProper_eq]
  infer_instance

中文:
实例 isStableUnderBaseChange
  签名: : MorphismProperty.是StableUnderBaseChange @是真
  定义体: by
  rw [isProper_eq]
  infer_instance

Depends on / 依赖: infer_instance, isProper_eq
-/
instance isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @IsProper := by
  rw [isProper_eq]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtTarget @IsProper
  body: by
  rw [isProper_eq]
  infer_instance

中文:
实例 :
  签名: IsZariskiLocalAtTarget @是真
  定义体: by
  rw [isProper_eq]
  infer_instance

Depends on / 依赖: infer_instance, isProper_eq
-/
instance : IsZariskiLocalAtTarget @IsProper := by
  rw [isProper_eq]
  infer_instance

instance (f : X ⟶ S) (g : Y ⟶ S) [IsProper g] : IsProper (Limits.pullback.fst f g) where

instance (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] : IsProper (Limits.pullback.snd f g) where

instance (f : X ⟶ Y) (V : Y.Opens) [IsProper f] : IsProper (f ∣_ V) where

end IsProper

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `IsFinite.eq_isProper_inf_isAffineHom` / 引理 `IsFinite.eq_isProper_inf_isAffineHom`

English:
lemma IsFinite.eq_isProper_inf_isAffineHom
  proof: by
  have : (@IsAffineHom ⊓ @IsSeparated : MorphismProperty _) = @IsAffineHom :=
    inf_eq_left.mpr fun _ _ _ _ => inferInstance
  rw [inf_comm]; rw [isProper_eq]; rw [inf_assoc]; rw [← inf_assoc]; rw [this]; rw [eq_inf]; rw [IsIntegralHom.eq_universallyClosed_inf_isAffineHom]; rw [inf_assoc]; rw [

中文:
引理 是有限.eq_isProper_inf_isAffineHom
  证明: by
  have : (@IsAffineHom ⊓ @IsSeparated : MorphismProperty _) = @IsAffineHom :=
    inf_eq_left.mpr fun _ _ _ _ => inferInstance
  rw [inf_comm]; rw [isProper_eq]; rw [inf_assoc]; rw [← inf_assoc]; rw [this]; rw [eq_inf]; rw [IsIntegralHom.eq_universallyClosed_inf_isAffineHom]; rw [inf_assoc]; rw [

Depends on / 依赖: IsAffineHom, IsIntegralHom, IsIntegralHom.eq_universallyClosed_inf_isAffineHom, IsSeparated, MorphismProperty, eq_inf, eq_universallyClosed_inf_isAffineHom, inf_assoc, inf_comm, inf_eq_left, inf_eq_left.mpr, inf_left_comm, isProper_eq
-/
lemma IsFinite.eq_isProper_inf_isAffineHom :
    @IsFinite = (@IsProper ⊓ @IsAffineHom : MorphismProperty _) := by
  have : (@IsAffineHom ⊓ @IsSeparated : MorphismProperty _) = @IsAffineHom :=
    inf_eq_left.mpr fun _ _ _ _ => inferInstance
  rw [inf_comm]; rw [isProper_eq]; rw [inf_assoc]; rw [← inf_assoc]; rw [this]; rw [eq_inf]; rw [IsIntegralHom.eq_universallyClosed_inf_isAffineHom]; rw [inf_assoc]; rw [inf_left_comm]

variable {f} in
/--
lemma `IsFinite.iff_isProper_and_isAffineHom` / 引理 `IsFinite.iff_isProper_and_isAffineHom`

English:
lemma IsFinite.iff_isProper_and_isAffineHom
  proof: by
  rw [eq_isProper_inf_isAffineHom]
  rfl

中文:
引理 是有限.iff_isProper_and_isAffineHom
  证明: by
  rw [eq_isProper_inf_isAffineHom]
  rfl

Depends on / 依赖: eq_isProper_inf_isAffineHom
-/
lemma IsFinite.iff_isProper_and_isAffineHom :
    IsFinite f ↔ IsProper f ∧ IsAffineHom f := by
  rw [eq_isProper_inf_isAffineHom]
  rfl

instance (priority := 100) [IsFinite f] : IsProper f :=
  (IsFinite.iff_isProper_and_isAffineHom.mp ‹_›).1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @UniversallyClosed @IsSeparated
  body: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (UniversallyClosed _)

@[stacks 01W6 "(1)"]

中文:
实例 :
  签名: MorphismProperty.有OfPostcompProperty @普遍闭 @是分离
  定义体: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (UniversallyClosed _)

@[stacks 01W6 "(1)"]

Depends on / 依赖: MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr, UniversallyClosed, hasOfPostcompProperty_iff_le_diagonal
-/
instance : MorphismProperty.HasOfPostcompProperty @UniversallyClosed @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (UniversallyClosed _)

@[stacks 01W6 "(1)"]
/--
lemma `UniversallyClosed.of_comp_of_isSeparated` / 引理 `UniversallyClosed.of_comp_of_isSeparated`

English:
lemma UniversallyClosed.of_comp_of_isSeparated
  given: [UniversallyClosed (f ≫ g)] [IsSeparated g]
  proof: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

中文:
引理 普遍闭.of_comp_of_isSeparated
  条件: [普遍闭 (f ≫ g)] [是分离 g]
  证明: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

Depends on / 依赖: MorphismProperty, MorphismProperty.of_postcomp, of_postcomp
-/
lemma UniversallyClosed.of_comp_of_isSeparated [UniversallyClosed (f ≫ g)] [IsSeparated g] :
    UniversallyClosed f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.HasOfPostcompProperty @IsProper @IsSeparated
  body: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsProper _)

中文:
实例 :
  签名: MorphismProperty.有OfPostcompProperty @是真 @是分离
  定义体: MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsProper _)

Depends on / 依赖: IsProper, MorphismProperty, MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr, hasOfPostcompProperty_iff_le_diagonal
-/
instance : MorphismProperty.HasOfPostcompProperty @IsProper @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ => inferInstanceAs (IsProper _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [UniversallyClosed
  signature: f] : UniversallyClosed f.toImage
  body: have : UniversallyClosed (f.toImage ≫ f.imageι) := by simpa
  .of_comp_of_isSeparated _ f.imageι

@[stacks 01W6 "(2)"]

中文:
实例 [普遍闭
  签名: f] : 普遍闭 f.toImage
  定义体: have : UniversallyClosed (f.toImage ≫ f.imageι) := by simpa
  .of_comp_of_isSeparated _ f.imageι

@[stacks 01W6 "(2)"]

Depends on / 依赖: UniversallyClosed, f.image, f.toImage, of_comp_of_isSeparated, toImage
-/
instance [UniversallyClosed f] : UniversallyClosed f.toImage :=
  have : UniversallyClosed (f.toImage ≫ f.imageι) := by simpa
  .of_comp_of_isSeparated _ f.imageι

@[stacks 01W6 "(2)"]
/--
lemma `IsProper.of_comp` / 引理 `IsProper.of_comp`

English:
lemma IsProper.of_comp
  given: [IsProper (f ≫ g)] [IsSeparated g]
  statement: IsProper f
  proof: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

中文:
引理 是真.of_comp
  条件: [是真 (f ≫ g)] [是分离 g]
  结论: 是真 f
  证明: MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

Depends on / 依赖: MorphismProperty, MorphismProperty.of_postcomp, of_postcomp
-/
lemma IsProper.of_comp [IsProper (f ≫ g)] [IsSeparated g] : IsProper f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

/--
lemma `IsProper.comp_iff` / 引理 `IsProper.comp_iff`

English:
lemma IsProper.comp_iff
  given: {f : X ⟶ Y} {g : Y ⟶ Z} [IsProper g]
  proof: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

中文:
引理 是真.comp_iff
  条件: {f : X ⟶ Y} {g : Y ⟶ Z} [是真 g]
  证明: ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

Depends on / 依赖: of_comp
-/
lemma IsProper.comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsProper g] :
    IsProper (f ≫ g) ↔ IsProper f :=
  ⟨fun _ => .of_comp f g, fun _ => inferInstance⟩

section GlobalSection

variable (K : Type u) [Field K]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `isIntegral_appTop_of_universallyClosed` / 定理 `isIntegral_appTop_of_universallyClosed`

English:
theorem isIntegral_appTop_of_universallyClosed
  given: (f : X ⟶ Y) [UniversallyClosed f] [IsAffine Y]
  proof: by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have : UniversallyClosed X.toSpecΓ :

中文:
定理 is整数egral_appTop_of_universallyClosed
  条件: (f : X ⟶ Y) [普遍闭 f] [是仿射 Y]
  证明: by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have : UniversallyClosed X.toSpecΓ :

Depends on / 依赖: CompactSpace, IsIntegralHom, IsIntegralHom.SpecMap_iff, IsIntegralHom.iff_universallyClosed_and_isAffineHom, MorphismProperty, MorphismProperty.cancel_right_of_respectsIso, Scheme, Scheme.toSpec, Spec.map, SpecMap_iff, UniversallyClosed, X.toSpec, appTop, cancel_right_of_respectsIso, f.appTop, iff_universallyClosed_and_isAffineHom, of_comp_of_isSeparated, of_comp_surjective, quasiCompact_iff_compactSpace
-/
theorem isIntegral_appTop_of_universallyClosed (f : X ⟶ Y) [UniversallyClosed f] [IsAffine Y] :
    f.appTop.hom.IsIntegral := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : UniversallyClosed (X.toSpecΓ ≫ Spec.map f.appTop) := by
    rwa [← Scheme.toSpecΓ_naturality,
      MorphismProperty.cancel_right_of_respectsIso (P := @UniversallyClosed)]
  have : UniversallyClosed X.toSpecΓ := .of_comp_of_isSeparated _ (Spec.map f.appTop)
  rw [← IsIntegralHom.SpecMap_iff]; rw [IsIntegralHom.iff_universallyClosed_and_isAffineHom]
  exact ⟨.of_comp_surjective X.toSpecΓ _, inferInstance⟩

/--
theorem `isField_of_universallyClosed` / 定理 `isField_of_universallyClosed`

English:
theorem isField_of_universallyClosed
  statement: (f : X ⟶ (Spec <| .of K))
  proof: by
  let F := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  exact isField_of_isIntegral_of_isField' (Fie

中文:
定理 isField_of_universallyClosed
  结论: (f : X ⟶ (Spec <| .of K))
  证明: by
  let F := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  exact isField_of_isIntegral_of_isField' (Fie

Depends on / 依赖: F.hom, F.hom.IsIntegral, Field.toIsField, IsIntegral, RingHom, RingHom.isIntegral_respectsIso, Scheme, algebraize, appTop, commRingCatIsoToRingEquiv, f.appTop, isField_of_isIntegral_of_isField, isIntegral_appTop_of_universallyClosed, isIntegral_respectsIso, symm.commRingCatIsoToRingEquiv, toIsField
-/
theorem isField_of_universallyClosed (f : X ⟶ (Spec <| .of K))
    [IsIntegral X] [UniversallyClosed f] : IsField Γ(X, ⊤) := by
  let F := (Scheme.ΓSpecIso _).inv ≫ f.appTop
  have : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  algebraize [F.hom]
  exact isField_of_isIntegral_of_isField' (Field.toIsField K)

/--
theorem `finite_appTop_of_universallyClosed` / 定理 `finite_appTop_of_universallyClosed`

English:
theorem finite_appTop_of_universallyClosed
  statement: (f : X ⟶ (Spec <| .of K))
  proof: by
  have x : X := Nonempty.some inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  let := (isField_of

中文:
定理 finite_appTop_of_universallyClosed
  结论: (f : X ⟶ (Spec <| .of K))
  证明: by
  have x : X := Nonempty.some inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  let := (isField_of

Depends on / 依赖: Field.toIsField, Nonempty, Nonempty.some, RingHom, RingHom.finite_of_algHom_finiteType_of_isJacobsonRing, Scheme, Set.mem_univ, X.isBasis_affineOpens.exists_subset_of_mem_open, X.presheaf.map, commRingCatIsoToRingEquiv, commRingCatIsoToRingEquiv.toMulEquiv.isField, exists_subset_of_mem_open, f.finiteType_appLE, finiteType_appLE, finite_of_algHom_finiteType_of_isJacobsonRing, homOfLE, isBasis_affineOpens, isField, isField_of_universallyClosed, isOpen_univ
-/
theorem finite_appTop_of_universallyClosed (f : X ⟶ (Spec <| .of K))
    [IsIntegral X] [UniversallyClosed f] [LocallyOfFiniteType f] :
    f.appTop.hom.Finite := by
  have x : X := Nonempty.some inferInstance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  let := (isField_of_universallyClosed K f).toField
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  apply RingHom.finite_of_algHom_finiteType_of_isJacobsonRing (A := Γ(X, U))
    (g := (X.presheaf.map (homOfLE le_top).op).hom)
  exact f.finiteType_appLE (isAffineOpen_top _) hU (by simp)

end GlobalSection

end AlgebraicGeometry
