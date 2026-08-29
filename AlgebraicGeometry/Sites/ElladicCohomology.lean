/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers

/-!

# `ℓ`-adic cohomology of a scheme

Let `X` be a scheme and `ℓ` be a prime number. In this file we define the sheaf
associated to the topological group `ℤ_[ℓ]` on the pro-étale site of `X`.
Its cohomology groups are the `ℓ`-adic cohomology groups of `X`.

## Main declarations

- `AlgebraicGeometry.Scheme.ellAdicSheaf`: The sheaf `U ↦ C(U, ℤ_[ℓ])`.
- `AlgebraicGeometry.Scheme.EllAdicCohomology`: The pro-étale cohomology groups `Hⁱ(X, ℤ_[ℓ])`.

## Notes

The `ℓ`-adic cohomology groups of `X : Scheme.{u}` are in `Type (u + 1)`, because
the pro-étale site of `X` has no essentially small subcategory with the same category of sheaves.
Eventually, we will be able to compare the `ℓ`-adic cohomology defined here with the classical
definition using étale cohomology. This will show that the groups defined here are indeed `u`-small.

## References

- [Bhatt, Bhargav and Scholze, Peter, The pro-étale topology for schemes][proetale2015]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsGrothendieckAbelian.{u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1})
  body: by
  -- Without this, lean starts searching for `EssentiallySmall.{max (u + 1) ?v}` and fails.
  have : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (ProEt.topology X) Ab.{u + 1}

中文:
实例 :
  签名: IsGrothendieckAbelian.{u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1})
  定义体: by
  -- Without this, lean starts searching for `EssentiallySmall.{max (u + 1) ?v}` and fails.
  have : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (ProEt.topology X) Ab.{u + 1}
-/
instance : IsGrothendieckAbelian.{u + 1} (Sheaf (ProEt.topology X) Ab.{u + 1}) := by
  -- Without this, lean starts searching for `EssentiallySmall.{max (u + 1) ?v}` and fails.
  have : EssentiallySmall.{u + 1} X.ProEt := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall (ProEt.topology X) Ab.{u + 1}

/--
Definition of `ellAdicSheaf` / `ellAdicSheaf` 的定义

English:
definition ellAdicSheaf
  signature: (ℓ : Nat) [Fact ℓ.Prime]
  body: ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
⟨continuousMapPresheafAb (Int_[ℓ]), .of_le proetaleTopology_le_fpqcTopology
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

中文:
定义 ellAdicSheaf
  签名: (ℓ : 自然数) [Fact ℓ.Prime]
  定义体: ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
⟨continuousMapPresheafAb (Int_[ℓ]), .of_le proetaleTopology_le_fpqcTopology
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

Depends on / 依赖: Int_, Over.forget, ProEt.forget, continuousMapPresheafAb, forget, isSheaf_fpqcTopology_continuousMapPresheafAb, of_le, proetaleTopology, proetaleTopology_le_fpqcTopology, sheafPushforwardContinuous
-/
noncomputable def ellAdicSheaf (ℓ : Nat) [Fact ℓ.Prime] :
    Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
⟨continuousMapPresheafAb (Int_[ℓ]), .of_le proetaleTopology_le_fpqcTopology
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

variable (ℓ : Nat) [Fact ℓ.Prime]

/--
lemma `isZero_ellAdicSheaf_of_isEmpty` / 引理 `isZero_ellAdicSheaf_of_isEmpty`

English:
lemma isZero_ellAdicSheaf_of_isEmpty
  given: [IsEmpty X]
  statement: IsZero (X.ellAdicSheaf ℓ)
  proof: (Sheaf.isTerminalOfEqTop (ProEt.topology_eq_top_of_isEmpty _) _).isZero

中文:
引理 isZero_ellAdicSheaf_of_isEmpty
  条件: [IsEmpty X]
  结论: IsZero (X.ellAdicSheaf ℓ)
  证明: (Sheaf.isTerminalOfEqTop (ProEt.topology_eq_top_of_isEmpty _) _).isZero

Depends on / 依赖: ProEt.topology_eq_top_of_isEmpty, Sheaf.isTerminalOfEqTop, isTerminalOfEqTop, isZero, topology_eq_top_of_isEmpty
-/
lemma isZero_ellAdicSheaf_of_isEmpty [IsEmpty X] : IsZero (X.ellAdicSheaf ℓ) :=
  (Sheaf.isTerminalOfEqTop (ProEt.topology_eq_top_of_isEmpty _) _).isZero

/--
Definition of `EllAdicCohomology` / `EllAdicCohomology` 的定义

English:
definition EllAdicCohomology
  signature: (ℓ : Nat) [Fact ℓ.Prime] (n : Nat)
  body: ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n

中文:
定义 EllAdicCohomology
  签名: (ℓ : 自然数) [Fact ℓ.Prime] (n : 自然数)
  定义体: ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n

Depends on / 依赖: AddCommGrpCat, AddCommGrpCat.uliftFunctor, X.ellAdicSheaf, ellAdicSheaf, sheafCompose, uliftFunctor
-/
def EllAdicCohomology (ℓ : Nat) [Fact ℓ.Prime] (n : Nat) : Type (u + 1) :=
  ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n

noncomputable instance (ℓ : Nat) [Fact ℓ.Prime] (n : Nat) : AddCommGroup (X.EllAdicCohomology ℓ n) :=
inferInstanceAs AddCommGroup
    ((sheafCompose _ AddCommGrpCat.uliftFunctor.{u + 1}).obj <| X.ellAdicSheaf ℓ).H n

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: X] (n
  body: by
  apply Sheaf.subsingleton_H_of_isZero
  exact Functor.map_isZero _ (isZero_ellAdicSheaf_of_isEmpty _ _)

中文:
实例 [IsEmpty
  签名: X] (n
  定义体: by
  apply Sheaf.subsingleton_H_of_isZero
  exact Functor.map_isZero _ (isZero_ellAdicSheaf_of_isEmpty _ _)

Depends on / 依赖: Functor, Functor.map_isZero, Sheaf.subsingleton_H_of_isZero, isZero_ellAdicSheaf_of_isEmpty, map_isZero, subsingleton_H_of_isZero
-/
instance [IsEmpty X] (n : Nat) : Subsingleton (X.EllAdicCohomology ℓ n) := by
  apply Sheaf.subsingleton_H_of_isZero
  exact Functor.map_isZero _ (isZero_ellAdicSheaf_of_isEmpty _ _)

end AlgebraicGeometry.Scheme
