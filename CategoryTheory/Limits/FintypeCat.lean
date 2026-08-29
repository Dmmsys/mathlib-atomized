/-
Copyright (c) 2023 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.CategoryTheory.Limits.Creates
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.Data.Finite.Prod
public import Mathlib.Data.Finite.Sigma

/-!
# (Co)limits in the category of finite types

We show that finite (co)limits exist in `FintypeCat` and that they are preserved by the natural
inclusion `FintypeCat.incl`.
-/

@[expose] public section

open CategoryTheory Limits Functor

universe u

namespace CategoryTheory.Limits.FintypeCat

instance {J : Type} [SmallCategory J] (K : J ⥤ FintypeCat.{u}) (j : J) :
    Finite ((K ⋙ FintypeCat.incl.{u}).obj j) := by
  simp only [comp_obj, FintypeCat.incl_obj]
  infer_instance

/--
Instance `finiteLimitOfFiniteDiagram` / 实例 `finiteLimitOfFiniteDiagram`

English:
instance finiteLimitOfFiniteDiagram
  signature: {J : Type} [SmallCategory J] [FinCategory J]
  body: by
  have : Fintype (sections K) := Fintype.ofFinite (sections K)
  exact Fintype.ofEquiv (sections K) (Types.limitEquivSections K).symm

中文:
实例 finiteLimitOfFiniteDiagram
  签名: {J : 类型} [小范畴 J] [有限范畴 J]
  定义体: by
  have : Fintype (sections K) := Fintype.ofFinite (sections K)
  exact Fintype.ofEquiv (sections K) (Types.limitEquivSections K).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, Fintype.ofFinite, Types.limitEquivSections, limitEquivSections, ofEquiv, ofFinite, sections
-/
noncomputable instance finiteLimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) [forall j, Finite (K.obj j)] : Fintype (limit K) := by
  have : Fintype (sections K) := Fintype.ofFinite (sections K)
  exact Fintype.ofEquiv (sections K) (Types.limitEquivSections K).symm

/--
Instance `inclusionCreatesFiniteLimits` / 实例 `inclusionCreatesFiniteLimits`

English:
instance inclusionCreatesFiniteLimits
  signature: {J : Type} [SmallCategory J] [FinCategory J]
  body: createsLimitOfFullyFaithfulOfIso
    (FintypeCat.of <| limit <| K ⋙ FintypeCat.incl) (Iso.refl _)

中文:
实例 inclusionCreatesFiniteLimits
  签名: {J : 类型} [小范畴 J] [有限范畴 J]
  定义体: createsLimitOfFullyFaithfulOfIso
    (FintypeCat.of <| limit <| K ⋙ FintypeCat.incl) (Iso.refl _)

Depends on / 依赖: createsLimitOfFullyFaithfulOfIso
-/
noncomputable instance inclusionCreatesFiniteLimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J FintypeCat.incl.{u} where
  CreatesLimit {K} := createsLimitOfFullyFaithfulOfIso
    (FintypeCat.of <| limit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/-- Help typeclass inference to infer creation of finite limits for the forgetful functor. -/
noncomputable instance {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesLimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteLimits

instance {J : Type} [SmallCategory J] [FinCategory J] : HasLimitsOfShape J FintypeCat.{u} where
  has_limit F := hasLimit_of_created F FintypeCat.incl

/--
Instance `hasFiniteLimits` / 实例 `hasFiniteLimits`

English:
instance hasFiniteLimits
  signature: : HasFiniteLimits FintypeCat.{u} where
  body: inferInstance

中文:
实例 hasFiniteLimits
  签名: : 有有限极限 FintypeCat.{u} where
  定义体: inferInstance
-/
instance hasFiniteLimits : HasFiniteLimits FintypeCat.{u} where
  out _ := inferInstance

/--
Instance `inclusion_preservesFiniteLimits` / 实例 `inclusion_preservesFiniteLimits`

English:
instance inclusion_preservesFiniteLimits
  signature: :
  body: preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape FintypeCat.incl

中文:
实例 inclusion_preservesFiniteLimits
  签名: :
  定义体: preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape FintypeCat.incl

Depends on / 依赖: FintypeCat, FintypeCat.incl, cancel_epi, comp_smul, congr_arg, preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape, smul_comp, smul_smul
-/
noncomputable instance inclusion_preservesFiniteLimits :
    PreservesFiniteLimits FintypeCat.incl.{u} where
  preservesFiniteLimits _ :=
    preservesLimitOfShape_of_createsLimitsOfShape_and_hasLimitsOfShape FintypeCat.incl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteLimits (forget FintypeCat)
  body: FintypeCat.inclusion_preservesFiniteLimits

中文:
实例 :
  签名: 保持FiniteLimits (forget FintypeCat)
  定义体: FintypeCat.inclusion_preservesFiniteLimits

Depends on / 依赖: FintypeCat, FintypeCat.inclusion_preservesFiniteLimits, cancel_mono, comp_smul, congr_arg, inclusion_preservesFiniteLimits, smul_comp, smul_smul
-/
noncomputable instance : PreservesFiniteLimits (forget FintypeCat) :=
  FintypeCat.inclusion_preservesFiniteLimits

/--
Definition of `productEquiv` / `productEquiv` 的定义

English:
definition productEquiv
  signature: {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u})
  body: have : Fintype ι := Fintype.ofFinite _
  haveI : Small.{u} ι :=
    ⟨ULift (Fin (Fintype.card ι)), ⟨(Fintype.equivFin ι).trans Equiv.ulift.symm⟩⟩
  let is₁ : FintypeCat.incl.obj (∏ᶜ fun i => X i) ≅ (∏ᶜ fun i => X i) :=
    PreservesProduct.iso FintypeCat.incl (fun i => X i)
  let is₂ : (∏ᶜ fun i => 

中文:
定义 productEquiv
  签名: {ι : 类型} [有限 ι] (X : ι -> FintypeCat.{u})
  定义体: have : Fintype ι := Fintype.ofFinite _
  haveI : Small.{u} ι :=
    ⟨ULift (Fin (Fintype.card ι)), ⟨(Fintype.equivFin ι).trans Equiv.ulift.symm⟩⟩
  let is₁ : FintypeCat.incl.obj (∏ᶜ fun i => X i) ≅ (∏ᶜ fun i => X i) :=
    PreservesProduct.iso FintypeCat.incl (fun i => X i)
  let is₂ : (∏ᶜ fun i => 

Depends on / 依赖: Equiv.ulift.symm, Fintype, Fintype.card, Fintype.equivFin, Fintype.ofFinite, FintypeCat, FintypeCat.incl, FintypeCat.incl.obj, PreservesProduct, PreservesProduct.iso, Shrink, Types.Small.productIso, equivEquivIso, equivEquivIso.symm, equivFin, equivShrink, ofFinite, productIso
-/
noncomputable def productEquiv {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u}) :
    (∏ᶜ X : FintypeCat) ≃ forall i, X i :=
  have : Fintype ι := Fintype.ofFinite _
  haveI : Small.{u} ι :=
    ⟨ULift (Fin (Fintype.card ι)), ⟨(Fintype.equivFin ι).trans Equiv.ulift.symm⟩⟩
  let is₁ : FintypeCat.incl.obj (∏ᶜ fun i => X i) ≅ (∏ᶜ fun i => X i) :=
    PreservesProduct.iso FintypeCat.incl (fun i => X i)
  let is₂ : (∏ᶜ fun i => X i : Type _) ≅ (Shrink.{u} (forall i, X i)) :=
    Types.Small.productIso (fun i => X i)
  let e : (forall i, X i) ≃ Shrink.{u} (forall i, X i) := equivShrink _
  (equivEquivIso.symm is₁).trans ((equivEquivIso.symm is₂).trans e.symm)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `productEquiv_apply` / 引理 `productEquiv_apply`

English:
lemma productEquiv_apply
  statement: {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u})
  proof: by
  simpa [productEquiv, equivEquivIso, equivIsoIso, Iso.toEquiv] using!
    piComparison_comp_π_apply FintypeCat.incl X i x

@[simp]

中文:
引理 productEquiv_apply
  结论: {ι : 类型} [有限 ι] (X : ι -> FintypeCat.{u})
  证明: by
  simpa [productEquiv, equivEquivIso, equivIsoIso, Iso.toEquiv] using!
    piComparison_comp_π_apply FintypeCat.incl X i x

@[simp]

Depends on / 依赖: FintypeCat, FintypeCat.incl, Iso.toEquiv, equivEquivIso, equivIsoIso, productEquiv, toEquiv
-/
lemma productEquiv_apply {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u})
    (x : (∏ᶜ X : FintypeCat)) (i : ι) : productEquiv X x i = Pi.π X i x := by
  simpa [productEquiv, equivEquivIso, equivIsoIso, Iso.toEquiv] using!
    piComparison_comp_π_apply FintypeCat.incl X i x

@[simp]
/--
lemma `productEquiv_symm_comp_π_apply` / 引理 `productEquiv_symm_comp_π_apply`

English:
lemma productEquiv_symm_comp_π_apply
  statement: {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u})
  proof: by
  rw [← productEquiv_apply]; rw [Equiv.apply_symm_apply]

中文:
引理 productEquiv_symm_comp_π_apply
  结论: {ι : 类型} [有限 ι] (X : ι -> FintypeCat.{u})
  证明: by
  rw [← productEquiv_apply]; rw [Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, apply_symm_apply, productEquiv_apply
-/
lemma productEquiv_symm_comp_π_apply {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u})
    (x : forall i, X i) (i : ι) : Pi.π X i ((productEquiv X).symm x) = x i := by
  rw [← productEquiv_apply]; rw [Equiv.apply_symm_apply]

/--
Instance `nonempty_pi_of_nonempty` / 实例 `nonempty_pi_of_nonempty`

English:
instance nonempty_pi_of_nonempty
  signature: {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u})
  body: (Equiv.nonempty_congr <| productEquiv X).mpr inferInstance

中文:
实例 nonempty_pi_of_nonempty
  签名: {ι : 类型} [有限 ι] (X : ι -> FintypeCat.{u})
  定义体: (Equiv.nonempty_congr <| productEquiv X).mpr inferInstance

Depends on / 依赖: Equiv.nonempty_congr, nonempty_congr, productEquiv
-/
instance nonempty_pi_of_nonempty {ι : Type*} [Finite ι] (X : ι -> FintypeCat.{u})
    [forall i, Nonempty (X i)] : Nonempty (∏ᶜ X : FintypeCat.{u}) :=
  (Equiv.nonempty_congr <| productEquiv X).mpr inferInstance

/--
Instance `finite_colimitType` / 实例 `finite_colimitType`

English:
instance finite_colimitType
  signature: {J : Type*} [SmallCategory J] [FinCategory J]
  body: Quot.finite _

中文:
实例 finite_colimitType
  签名: {J : 类型} [小范畴 J] [有限范畴 J]
  定义体: Quot.finite _

Depends on / 依赖: Quot.finite, finite
-/
instance finite_colimitType {J : Type*} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type u) [forall j, Finite (K.obj j)] : Finite K.ColimitType :=
  Quot.finite _

/--
lemma `finite_of_isColimit` / 引理 `finite_of_isColimit`

English:
lemma finite_of_isColimit
  statement: {J : Type*} [SmallCategory J] [FinCategory J]
  proof: Finite.of_equiv _ ((Types.isColimit_iff_coconeTypesIsColimit c).1 ⟨hc⟩).equiv

中文:
引理 finite_of_isColimit
  结论: {J : 类型} [小范畴 J] [有限范畴 J]
  证明: Finite.of_equiv _ ((Types.isColimit_iff_coconeTypesIsColimit c).1 ⟨hc⟩).equiv

Depends on / 依赖: Finite, Finite.of_equiv, Types.isColimit_iff_coconeTypesIsColimit, isColimit_iff_coconeTypesIsColimit, of_equiv
-/
lemma finite_of_isColimit {J : Type*} [SmallCategory J] [FinCategory J]
    {K : J ⥤ Type u} [forall j, Finite (K.obj j)] {c : Cocone K} (hc : IsColimit c) :
    Finite c.pt :=
  Finite.of_equiv _ ((Types.isColimit_iff_coconeTypesIsColimit c).1 ⟨hc⟩).equiv

/--
Instance `finiteColimitOfFiniteDiagram` / 实例 `finiteColimitOfFiniteDiagram`

English:
instance finiteColimitOfFiniteDiagram
  signature: {J : Type} [SmallCategory J] [FinCategory J]
  body: by
  have : Finite (colimit K) := finite_of_isColimit (colimit.isColimit K)
  apply Fintype.ofFinite

中文:
实例 finiteColimitOfFiniteDiagram
  签名: {J : 类型} [小范畴 J] [有限范畴 J]
  定义体: by
  have : Finite (colimit K) := finite_of_isColimit (colimit.isColimit K)
  apply Fintype.ofFinite

Depends on / 依赖: Finite, Fintype, Fintype.ofFinite, colimit, colimit.isColimit, finite_of_isColimit, isColimit, ofFinite
-/
noncomputable instance finiteColimitOfFiniteDiagram {J : Type} [SmallCategory J] [FinCategory J]
    (K : J ⥤ Type*) [forall j, Finite (K.obj j)] : Fintype (colimit K) := by
  have : Finite (colimit K) := finite_of_isColimit (colimit.isColimit K)
  apply Fintype.ofFinite

/--
Instance `inclusionCreatesFiniteColimits` / 实例 `inclusionCreatesFiniteColimits`

English:
instance inclusionCreatesFiniteColimits
  signature: {J : Type} [SmallCategory J] [FinCategory J]
  body: createsColimitOfFullyFaithfulOfIso
    (FintypeCat.of <| colimit <| K ⋙ FintypeCat.incl) (Iso.refl _)

中文:
实例 inclusionCreatesFiniteColimits
  签名: {J : 类型} [小范畴 J] [有限范畴 J]
  定义体: createsColimitOfFullyFaithfulOfIso
    (FintypeCat.of <| colimit <| K ⋙ FintypeCat.incl) (Iso.refl _)

Depends on / 依赖: createsColimitOfFullyFaithfulOfIso
-/
noncomputable instance inclusionCreatesFiniteColimits {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J FintypeCat.incl.{u} where
  CreatesColimit {K} := createsColimitOfFullyFaithfulOfIso
    (FintypeCat.of <| colimit <| K ⋙ FintypeCat.incl) (Iso.refl _)

/-- Help typeclass inference to infer creation of finite colimits for the forgetful functor. -/
noncomputable instance {J : Type} [SmallCategory J] [FinCategory J] :
    CreatesColimitsOfShape J (forget FintypeCat) :=
  FintypeCat.inclusionCreatesFiniteColimits

instance {J : Type} [SmallCategory J] [FinCategory J] : HasColimitsOfShape J FintypeCat.{u} where
  has_colimit F := hasColimit_of_created F FintypeCat.incl

/--
Instance `hasFiniteColimits` / 实例 `hasFiniteColimits`

English:
instance hasFiniteColimits
  signature: : HasFiniteColimits FintypeCat.{u} where
  body: inferInstance

中文:
实例 hasFiniteColimits
  签名: : 有有限余极限 FintypeCat.{u} where
  定义体: inferInstance
-/
instance hasFiniteColimits : HasFiniteColimits FintypeCat.{u} where
  out _ := inferInstance

/--
Instance `inclusion_preservesFiniteColimits` / 实例 `inclusion_preservesFiniteColimits`

English:
instance inclusion_preservesFiniteColimits
  signature: :
  body: preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape FintypeCat.incl

中文:
实例 inclusion_preservesFiniteColimits
  签名: :
  定义体: preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape FintypeCat.incl

Depends on / 依赖: FintypeCat, FintypeCat.incl, preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape
-/
noncomputable instance inclusion_preservesFiniteColimits :
    PreservesFiniteColimits FintypeCat.incl.{u} where
  preservesFiniteColimits _ :=
    preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape FintypeCat.incl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesFiniteColimits (forget FintypeCat)
  body: FintypeCat.inclusion_preservesFiniteColimits

中文:
实例 :
  签名: 保持FiniteColimits (forget FintypeCat)
  定义体: FintypeCat.inclusion_preservesFiniteColimits

Depends on / 依赖: FintypeCat, FintypeCat.inclusion_preservesFiniteColimits, inclusion_preservesFiniteColimits
-/
noncomputable instance : PreservesFiniteColimits (forget FintypeCat) :=
  FintypeCat.inclusion_preservesFiniteColimits

/--
lemma `jointly_surjective` / 引理 `jointly_surjective`

English:
lemma jointly_surjective
  statement: {J : Type*} [SmallCategory J] [FinCategory J]
  proof: let hs := isColimitOfPreserves FintypeCat.incl.{u} h
  Types.jointly_surjective (F ⋙ FintypeCat.incl) hs x

中文:
引理 jointly_surjective
  结论: {J : 类型} [小范畴 J] [有限范畴 J]
  证明: let hs := isColimitOfPreserves FintypeCat.incl.{u} h
  Types.jointly_surjective (F ⋙ FintypeCat.incl) hs x

Depends on / 依赖: FintypeCat, FintypeCat.incl, Types.jointly_surjective, isColimitOfPreserves, jointly_surjective
-/
lemma jointly_surjective {J : Type*} [SmallCategory J] [FinCategory J]
    (F : J ⥤ FintypeCat.{u}) (t : Cocone F) (h : IsColimit t) (x : t.pt) :
    exists j y, t.ι.app j y = x :=
  let hs := isColimitOfPreserves FintypeCat.incl.{u} h
  Types.jointly_surjective (F ⋙ FintypeCat.incl) hs x

end CategoryTheory.Limits.FintypeCat
