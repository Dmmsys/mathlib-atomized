/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.LocalClosure

/-!
# Local isomorphisms

A local isomorphism of schemes is a morphism that is source-locally an open immersion.
-/

public section

universe u

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A local isomorphism of schemes is a morphism that is (Zariski-)source-locally an
open immersion. -/
@[mk_iff]
/--
Definition of `IsLocalIso` / `IsLocalIso` 的定义

English:
class IsLocalIso
  parameters: (f : X ⟶ Y)
  axioms and operations (1):
    - exists_isOpenImmersion((x : X)) : exists (U : X.Opens), x in U ∧ IsOpenImmersion (U.ι ≫ f)

中文:
类 IsLocalIso
  参数: (f : X ⟶ Y)
  公理与运算 (1 个):
    - exists_isOpenImmersion((x : X)) : 存在 (U : X.Opens), x in U ∧ IsOpenImmersion (U.ι ≫ f)
-/
class IsLocalIso (f : X ⟶ Y) : Prop where
  exists_isOpenImmersion (x : X) : exists (U : X.Opens), x in U ∧ IsOpenImmersion (U.ι ≫ f)

namespace IsLocalIso

variable (f : X ⟶ Y)

/--
lemma `eq_sourceLocalClosure_isOpenImmersion` / 引理 `eq_sourceLocalClosure_isOpenImmersion`

English:
lemma eq_sourceLocalClosure_isOpenImmersion
  proof: by
  ext
  rw [isLocalIso_iff]; rw [sourceLocalClosure.iff_forall_exists]

中文:
引理 eq_sourceLocalClosure_isOpenImmersion
  证明: by
  ext
  rw [isLocalIso_iff]; rw [sourceLocalClosure.iff_forall_exists]

Depends on / 依赖: iff_forall_exists, isLocalIso_iff, sourceLocalClosure, sourceLocalClosure.iff_forall_exists
-/
lemma eq_sourceLocalClosure_isOpenImmersion :
    @IsLocalIso = sourceLocalClosure IsOpenImmersion IsOpenImmersion := by
  ext
  rw [isLocalIso_iff]; rw [sourceLocalClosure.iff_forall_exists]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsZariskiLocalAtSource @IsLocalIso
  body: by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

中文:
实例 :
  签名: IsZariskiLocalAtSource @IsLocalIso
  定义体: by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

Depends on / 依赖: eq_sourceLocalClosure_isOpenImmersion, infer_instance
-/
instance : IsZariskiLocalAtSource @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMultiplicative @IsLocalIso
  body: by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

中文:
实例 :
  签名: IsMultiplicative @IsLocalIso
  定义体: by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

Depends on / 依赖: eq_sourceLocalClosure_isOpenImmersion, infer_instance
-/
instance : IsMultiplicative @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderBaseChange @IsLocalIso
  body: by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

中文:
实例 :
  签名: IsStableUnderBaseChange @IsLocalIso
  定义体: by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

Depends on / 依赖: eq_sourceLocalClosure_isOpenImmersion, infer_instance
-/
instance : IsStableUnderBaseChange @IsLocalIso := by
  rw [eq_sourceLocalClosure_isOpenImmersion]
  infer_instance

/--
lemma `le_of_isZariskiLocalAtSource` / 引理 `le_of_isZariskiLocalAtSource`

English:
lemma le_of_isZariskiLocalAtSource
  statement: (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities]
  proof: by
  intro X Y f hf
  obtain ⟨𝒰, h⟩ := eq_sourceLocalClosure_isOpenImmersion ▸ hf
  rw [IsZariskiLocalAtSource.iff_of_openCover 𝒰 (P := P)]
  exact fun _ => IsZariskiLocalAtSource.of_isOpenImmersion _

中文:
引理 le_of_isZariskiLocalAtSource
  结论: (P : Morphism命题erty Scheme.{u}) [P.ContainsIdentities]
  证明: by
  intro X Y f hf
  obtain ⟨𝒰, h⟩ := eq_sourceLocalClosure_isOpenImmersion ▸ hf
  rw [IsZariskiLocalAtSource.iff_of_openCover 𝒰 (P := P)]
  exact fun _ => IsZariskiLocalAtSource.of_isOpenImmersion _

Depends on / 依赖: IsZariskiLocalAtSource, IsZariskiLocalAtSource.iff_of_openCover, IsZariskiLocalAtSource.of_isOpenImmersion, eq_sourceLocalClosure_isOpenImmersion, iff_of_openCover, of_isOpenImmersion
-/
lemma le_of_isZariskiLocalAtSource (P : MorphismProperty Scheme.{u}) [P.ContainsIdentities]
    [IsZariskiLocalAtSource P] : @IsLocalIso <= P := by
  intro X Y f hf
  obtain ⟨𝒰, h⟩ := eq_sourceLocalClosure_isOpenImmersion ▸ hf
  rw [IsZariskiLocalAtSource.iff_of_openCover 𝒰 (P := P)]
  exact fun _ => IsZariskiLocalAtSource.of_isOpenImmersion _

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eq_iInf` / 引理 `eq_iInf`

English:
lemma eq_iInf
  proof: by
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    apply le_of_isZariskiLocalAtSource
  · refine iInf_le_of_le @IsLocalIso (iInf_le_of_le inferInstance (iInf_le _ ?_))
    infer_instance

中文:
引理 eq_iInf
  证明: by
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    apply le_of_isZariskiLocalAtSource
  · refine iInf_le_of_le @IsLocalIso (iInf_le_of_le inferInstance (iInf_le _ ?_))
    infer_instance

Depends on / 依赖: IsLocalIso, iInf_le, iInf_le_of_le, infer_instance, le_antisymm, le_iInf_iff, le_of_isZariskiLocalAtSource
-/
lemma eq_iInf :
    @IsLocalIso = ⨅ (P : MorphismProperty Scheme.{u}) (_ : P.ContainsIdentities)
      (_ : IsZariskiLocalAtSource P), P := by
  refine le_antisymm ?_ ?_
  · simp only [le_iInf_iff]
    apply le_of_isZariskiLocalAtSource
  · refine iInf_le_of_le @IsLocalIso (iInf_le_of_le inferInstance (iInf_le _ ?_))
    infer_instance

end IsLocalIso

end AlgebraicGeometry
