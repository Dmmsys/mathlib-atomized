/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.EquivalenceAdditive
public import Mathlib.AlgebraicTopology.DoldKan.Compatibility
public import Mathlib.CategoryTheory.Idempotents.SimplicialObject
public import Mathlib.Tactic.SuppressCompilation

/-!

# The Dold-Kan correspondence for pseudoabelian categories

In this file, for any idempotent complete additive category `C`,
the Dold-Kan equivalence
`Idempotents.DoldKan.Equivalence C : SimplicialObject C ≌ ChainComplex C ℕ`
is obtained. It is deduced from the equivalence
`Preadditive.DoldKan.Equivalence` between the respective idempotent
completions of these categories using the fact that when `C` is idempotent complete,
then both `SimplicialObject C` and `ChainComplex C ℕ` are idempotent complete.

The construction of `Idempotents.DoldKan.Equivalence` uses the tools
introduced in the file `Compatibility.lean`. Doing so, the functor
`Idempotents.DoldKan.N` of the equivalence is
the composition of `N₁ : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)`
(defined in `FunctorN.lean`) and the inverse of the equivalence
`ChainComplex C ℕ ≌ Karoubi (ChainComplex C ℕ)`. The functor
`Idempotents.DoldKan.Γ` of the equivalence is by definition the functor
`Γ₀` introduced in `FunctorGamma.lean`.

(See `Equivalence.lean` for the general strategy of proof of the Dold-Kan equivalence.)

-/

@[expose] public section


suppress_compilation
noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Idempotents

variable {C : Type*} [Category* C] [Preadditive C]

namespace CategoryTheory

namespace Idempotents

namespace DoldKan

open AlgebraicTopology.DoldKan

/-- The functor `N` for the equivalence is obtained by composing
`N' : SimplicialObject C ⥤ Karoubi (ChainComplex C ℕ)` and the inverse
of the equivalence `ChainComplex C ℕ ≌ Karoubi (ChainComplex C ℕ)`. -/
@[simps!, nolint unusedArguments]
/--
Definition of `N` / `N` 的定义

English:
definition N
  signature: [IsIdempotentComplete C] [HasFiniteCoproducts C]
  body: N₁ ⋙ (toKaroubiEquivalence _).inverse

中文:
定义 N
  签名: [IsIdempotentComplete C] [HasFiniteCoproducts C]
  定义体: N₁ ⋙ (toKaroubiEquivalence _).inverse

Depends on / 依赖: inverse, toKaroubiEquivalence
-/
def N [IsIdempotentComplete C] [HasFiniteCoproducts C] : SimplicialObject C ⥤ ChainComplex C Nat :=
  N₁ ⋙ (toKaroubiEquivalence _).inverse

/-- The functor `Γ` for the equivalence is `Γ₀`. -/
@[simps!, nolint unusedArguments]
/--
Definition of `Γ` / `Γ` 的定义

English:
definition Γ
  signature: [IsIdempotentComplete C] [HasFiniteCoproducts C]
  body: Γ₀

中文:
定义 Γ
  签名: [IsIdempotentComplete C] [HasFiniteCoproducts C]
  定义体: Γ₀
-/
def Γ [IsIdempotentComplete C] [HasFiniteCoproducts C] : ChainComplex C Nat ⥤ SimplicialObject C :=
  Γ₀

variable [IsIdempotentComplete C] [HasFiniteCoproducts C]

/--
Definition of `isoN₁` / `isoN₁` 的定义

English:
definition isoN₁
  signature: :
  body: toKaroubiCompN₂IsoN₁

@[simp]

中文:
定义 isoN₁
  签名: :
  定义体: toKaroubiCompN₂IsoN₁

@[simp]
-/
def isoN₁ :
    (toKaroubiEquivalence (SimplicialObject C)).functor ⋙
      Preadditive.DoldKan.equivalence.functor ≅ N₁ := toKaroubiCompN₂IsoN₁

@[simp]
/--
lemma `isoN₁_hom_app_f` / 引理 `isoN₁_hom_app_f`

English:
lemma isoN₁_hom_app_f
  given: (X : SimplicialObject C)
  proof: rfl

中文:
引理 isoN₁_hom_app_f
  条件: (X : SimplicialObject C)
  证明: rfl
-/
lemma isoN₁_hom_app_f (X : SimplicialObject C) :
    (isoN₁.hom.app X).f = PInfty := rfl

/--
Definition of `isoΓ₀` / `isoΓ₀` 的定义

English:
definition isoΓ₀
  signature: :
  body: (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀

@[simp]

中文:
定义 isoΓ₀
  签名: :
  定义体: (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀

@[simp]
-/
def isoΓ₀ :
    (toKaroubiEquivalence (ChainComplex C Nat)).functor ⋙ Preadditive.DoldKan.equivalence.inverse ≅
      Γ ⋙ (toKaroubiEquivalence _).functor :=
  (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app Γ₀

@[simp]
/--
lemma `N₂_map_isoΓ₀_hom_app_f` / 引理 `N₂_map_isoΓ₀_hom_app_f`

English:
lemma N₂_map_isoΓ₀_hom_app_f
  given: (X : ChainComplex C Nat)
  proof: by
  ext
  apply comp_id

中文:
引理 N₂_map_isoΓ₀_hom_app_f
  条件: (X : ChainComplex C 自然数)
  证明: by
  ext
  apply comp_id

Depends on / 依赖: comp_id
-/
lemma N₂_map_isoΓ₀_hom_app_f (X : ChainComplex C Nat) :
    (N₂.map (isoΓ₀.hom.app X)).f = PInfty := by
  ext
  apply comp_id

/--
Definition of `equivalence` / `equivalence` 的定义

English:
definition equivalence
  signature: : SimplicialObject C ≌ ChainComplex C Nat
  body: Compatibility.equivalence isoN₁ isoΓ₀

中文:
定义 equivalence
  签名: : SimplicialObject C ≌ ChainComplex C 自然数
  定义体: Compatibility.equivalence isoN₁ isoΓ₀

Depends on / 依赖: Compatibility, Compatibility.equivalence, equivalence
-/
def equivalence : SimplicialObject C ≌ ChainComplex C Nat :=
  Compatibility.equivalence isoN₁ isoΓ₀

/--
theorem `equivalence_functor` / 定理 `equivalence_functor`

English:
theorem equivalence_functor
  statement: (equivalence : SimplicialObject C ≌ _).functor = N
  proof: rfl

中文:
定理 equivalence_functor
  结论: (equivalence : SimplicialObject C ≌ _).functor = N
  证明: rfl
-/
theorem equivalence_functor : (equivalence : SimplicialObject C ≌ _).functor = N :=
  rfl

/--
theorem `equivalence_inverse` / 定理 `equivalence_inverse`

English:
theorem equivalence_inverse
  statement: (equivalence : SimplicialObject C ≌ _).inverse = Γ
  proof: rfl

中文:
定理 equivalence_inverse
  结论: (equivalence : SimplicialObject C ≌ _).inverse = Γ
  证明: rfl
-/
theorem equivalence_inverse : (equivalence : SimplicialObject C ≌ _).inverse = Γ :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hη` / 定理 `hη`

English:
theorem hη
  proof: by
  ext K : 3
  simp only [Compatibility.τ₀_hom_app, Compatibility.τ₁_hom_app]
  exact (N₂Γ₂_compatible_with_N₁Γ₀ K).trans (by simp)

#adaptation_note

中文:
定理 hη
  证明: by
  ext K : 3
  simp only [Compatibility.τ₀_hom_app, Compatibility.τ₁_hom_app]
  exact (N₂Γ₂_compatible_with_N₁Γ₀ K).trans (by simp)

#adaptation_note

Depends on / 依赖: Compatibility
-/
theorem hη :
    Compatibility.τ₀ =
      Compatibility.τ₁ isoN₁ isoΓ₀
        (N₁Γ₀ : Γ ⋙ N₁ ≅ (toKaroubiEquivalence (ChainComplex C Nat)).functor) := by
  ext K : 3
  simp only [Compatibility.τ₀_hom_app, Compatibility.τ₁_hom_app]
  exact (N₂Γ₂_compatible_with_N₁Γ₀ K).trans (by simp)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The counit isomorphism induced by `N₁Γ₀` -/
@[simps!]
/--
Definition of `η` / `η` 的定义

English:
definition η
  signature: : Γ ⋙ N ≅ 𝟭 (ChainComplex C Nat)
  body: Compatibility.equivalenceCounitIso
    (N₁Γ₀ : (Γ : ChainComplex C Nat ⥤ _) ⋙ N₁ ≅ (toKaroubiEquivalence _).functor)

中文:
定义 η
  签名: : Γ ⋙ N ≅ 𝟭 (ChainComplex C 自然数)
  定义体: Compatibility.equivalenceCounitIso
    (N₁Γ₀ : (Γ : ChainComplex C Nat ⥤ _) ⋙ N₁ ≅ (toKaroubiEquivalence _).functor)

Depends on / 依赖: ChainComplex, Compatibility, Compatibility.equivalenceCounitIso, equivalenceCounitIso, functor, toKaroubiEquivalence
-/
def η : Γ ⋙ N ≅ 𝟭 (ChainComplex C Nat) :=
  Compatibility.equivalenceCounitIso
    (N₁Γ₀ : (Γ : ChainComplex C Nat ⥤ _) ⋙ N₁ ≅ (toKaroubiEquivalence _).functor)

/--
theorem `equivalence_counitIso` / 定理 `equivalence_counitIso`

English:
theorem equivalence_counitIso
  proof: Compatibility.equivalenceCounitIso_eq hη

中文:
定理 equivalence_counitIso
  证明: Compatibility.equivalenceCounitIso_eq hη

Depends on / 依赖: Compatibility, Compatibility.equivalenceCounitIso_eq, equivalenceCounitIso_eq
-/
theorem equivalence_counitIso :
    DoldKan.equivalence.counitIso = (η : Γ ⋙ N ≅ 𝟭 (ChainComplex C Nat)) :=
  Compatibility.equivalenceCounitIso_eq hη

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `hε` / 定理 `hε`

English:
theorem hε
  proof: by
  dsimp only [isoN₁]
  ext1
  rw [← cancel_epi Γ₂N₁.inv]; rw [Iso.inv_hom_id]
  ext X : 2
  rw [NatTrans.comp_app]; rw [Γ₂N₁_inv]; rw [compatibility_Γ₂N₁_Γ₂N₂_natTrans X]; rw [Compatibility.υ_hom_app]; rw [Preadditive.DoldKan.equivalence_unitIso]; rw [Iso.app_inv]; rw [assoc]
  dsimp only [Functo

中文:
定理 hε
  证明: by
  dsimp only [isoN₁]
  ext1
  rw [← cancel_epi Γ₂N₁.inv]; rw [Iso.inv_hom_id]
  ext X : 2
  rw [NatTrans.comp_app]; rw [Γ₂N₁_inv]; rw [compatibility_Γ₂N₁_Γ₂N₂_natTrans X]; rw [Compatibility.υ_hom_app]; rw [Preadditive.DoldKan.equivalence_unitIso]; rw [Iso.app_inv]; rw [assoc]
  dsimp only [Functo

Depends on / 依赖: Compatibility, DoldKan, Functor, Functor.asEquivalence_functor, Functor.comp_obj, Iso.app_inv, Iso.inv_hom_id, NatTrans, NatTrans.comp_app, NatTrans.comp_app_assoc, NatTrans.id_app, Preadditive, Preadditive.DoldKan, Preadditive.DoldKan.N.eq_1, Preadditive.DoldKan.equivalence_inverse, Preadditive.DoldKan.equivalence_unitIso, app_inv, asEquivalence_functor, cancel_epi, comp_app
-/
theorem hε :
    Compatibility.υ (isoN₁) =
      (Γ₂N₁ : (toKaroubiEquivalence _).functor ≅
          (N₁ : SimplicialObject C ⥤ _) ⋙ Preadditive.DoldKan.equivalence.inverse) := by
  dsimp only [isoN₁]
  ext1
  rw [← cancel_epi Γ₂N₁.inv]; rw [Iso.inv_hom_id]
  ext X : 2
  rw [NatTrans.comp_app]; rw [Γ₂N₁_inv]; rw [compatibility_Γ₂N₁_Γ₂N₂_natTrans X]; rw [Compatibility.υ_hom_app]; rw [Preadditive.DoldKan.equivalence_unitIso]; rw [Iso.app_inv]; rw [assoc]
  dsimp only [Functor.comp_obj, Preadditive.DoldKan.equivalence_inverse, Preadditive.DoldKan.Γ.eq_1,
    toKaroubiEquivalence, Functor.asEquivalence_functor, Preadditive.DoldKan.N.eq_1,
    NatTrans.id_app]
  rw [← NatTrans.comp_app_assoc]; rw [← Γ₂N₂_inv]; rw [Iso.inv_hom_id]; rw [NatTrans.id_app]; rw [id_comp]; rw [Γ₂N₂ToKaroubiIso_inv_app]; rw [← Γ₂.map_comp]; rw [Iso.inv_hom_id_app]; rw [Γ₂.map_id]

/--
Definition of `ε` / `ε` 的定义

English:
definition ε
  signature: : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ
  body: Compatibility.equivalenceUnitIso isoΓ₀ Γ₂N₁

中文:
定义 ε
  签名: : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ
  定义体: Compatibility.equivalenceUnitIso isoΓ₀ Γ₂N₁

Depends on / 依赖: Compatibility, Compatibility.equivalenceUnitIso, equivalenceUnitIso
-/
def ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ :=
  Compatibility.equivalenceUnitIso isoΓ₀ Γ₂N₁

/--
theorem `equivalence_unitIso` / 定理 `equivalence_unitIso`

English:
theorem equivalence_unitIso
  proof: Compatibility.equivalenceUnitIso_eq hε

中文:
定理 equivalence_unitIso
  证明: Compatibility.equivalenceUnitIso_eq hε

Depends on / 依赖: Compatibility, Compatibility.equivalenceUnitIso_eq, equivalenceUnitIso_eq
-/
theorem equivalence_unitIso :
    DoldKan.equivalence.unitIso = (ε : 𝟭 (SimplicialObject C) ≅ N ⋙ Γ) :=
  Compatibility.equivalenceUnitIso_eq hε

end DoldKan

end Idempotents

end CategoryTheory
