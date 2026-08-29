/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Nick Ward
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexColimits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Horns as colimits

In this file, we express horns as colimits:
* horns in `Δ[2]` are pushouts of two copies of `Δ[1]`;
* horns in `Δ[n]` are multicoequalizers of copies of the standard
  simplex of dimension `n-1` (a dedicated API is provided for inner
  horns in `Δ[3]`).

-/

@[expose] public section

universe u

namespace SSet

open CategoryTheory Simplicial Opposite Limits

namespace horn₂₀

/--
lemma `sq` / 引理 `sq`

English:
lemma sq
  statement: Subcomplex.BicartSq.{u} (stdSimplex.face {0}) (stdSimplex.face {0, 1})
  proof: by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 0 (by simp)
      · exact face_le_horn (1 : Fin 3) 0 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq :

中文:
引理 sq
  结论: Subcomplex.BicartSq.{u} (stdSimplex.face {0}) (stdSimplex.face {0, 1})
  证明: by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 0 (by simp)
      · exact face_le_horn (1 : Fin 3) 0 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq :

Depends on / 依赖: face_inter_face, face_le_horn, fin_cases, horn_eq_iSup, iSup_le_iff, inf_eq, le_antisymm, le_sup_left, le_sup_right, stdSimplex, stdSimplex.face_inter_face, sup_le_iff
-/
lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {0}) (stdSimplex.face {0, 1})
    (stdSimplex.face {0, 2}) Λ[2, 0] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 0 (by simp)
      · exact face_le_horn (1 : Fin 3) 0 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/--
Definition of `ι₀₁` / `ι₀₁` 的定义

English:
abbreviation ι₀₁
  signature: : Δ[1] ⟶ Λ[2, 0]
  body: horn.ι.{u} 0 2 (by simp)

中文:
缩写 ι₀₁
  签名: : Δ[1] ⟶ Λ[2, 0]
  定义体: horn.ι.{u} 0 2 (by simp)
-/
abbrev ι₀₁ : Δ[1] ⟶ Λ[2, 0] := horn.ι.{u} 0 2 (by simp)

/--
Definition of `ι₀₂` / `ι₀₂` 的定义

English:
abbreviation ι₀₂
  signature: : Δ[1] ⟶ Λ[2, 0]
  body: horn.ι.{u} 0 1 (by simp)

中文:
缩写 ι₀₂
  签名: : Δ[1] ⟶ Λ[2, 0]
  定义体: horn.ι.{u} 0 1 (by simp)
-/
abbrev ι₀₂ : Δ[1] ⟶ Λ[2, 0] := horn.ι.{u} 0 1 (by simp)

/--
lemma `isPushout` / 引理 `isPushout`

English:
lemma isPushout
  proof: by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

中文:
引理 isPushout
  证明: by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

Depends on / 依赖: Iso.refl, all_goals, facePairIso, faceSingletonIso, fapply, isPushout, isPushout.of_iso, of_iso, stdSimplex, stdSimplex.facePairIso, stdSimplex.faceSingletonIso
-/
lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (1 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₀₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₀

namespace horn₂₁

/--
lemma `sq` / 引理 `sq`

English:
lemma sq
  statement: Subcomplex.BicartSq.{u} (stdSimplex.face {1}) (stdSimplex.face {0, 1})
  proof: by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 1 (by simp)
      · exact face_le_horn (0 : Fin 3) 1 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq :

中文:
引理 sq
  结论: Subcomplex.BicartSq.{u} (stdSimplex.face {1}) (stdSimplex.face {0, 1})
  证明: by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 1 (by simp)
      · exact face_le_horn (0 : Fin 3) 1 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq :

Depends on / 依赖: face_inter_face, face_le_horn, fin_cases, horn_eq_iSup, iSup_le_iff, inf_eq, le_antisymm, le_sup_left, le_sup_right, stdSimplex, stdSimplex.face_inter_face, sup_le_iff
-/
lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {1}) (stdSimplex.face {0, 1})
    (stdSimplex.face {1, 2}) Λ[2, 1] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (2 : Fin 3) 1 (by simp)
      · exact face_le_horn (0 : Fin 3) 1 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/--
Definition of `ι₀₁` / `ι₀₁` 的定义

English:
abbreviation ι₀₁
  signature: : Δ[1] ⟶ Λ[2, 1]
  body: horn.ι.{u} 1 2 (by simp)

中文:
缩写 ι₀₁
  签名: : Δ[1] ⟶ Λ[2, 1]
  定义体: horn.ι.{u} 1 2 (by simp)
-/
abbrev ι₀₁ : Δ[1] ⟶ Λ[2, 1] := horn.ι.{u} 1 2 (by simp)

/--
Definition of `ι₁₂` / `ι₁₂` 的定义

English:
abbreviation ι₁₂
  signature: : Δ[1] ⟶ Λ[2, 1]
  body: horn.ι.{u} 1 0 (by simp)

中文:
缩写 ι₁₂
  签名: : Δ[1] ⟶ Λ[2, 1]
  定义体: horn.ι.{u} 1 0 (by simp)
-/
abbrev ι₁₂ : Δ[1] ⟶ Λ[2, 1] := horn.ι.{u} 1 0 (by simp)

/--
lemma `isPushout` / 引理 `isPushout`

English:
lemma isPushout
  proof: by
  apply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

中文:
引理 isPushout
  证明: by
  apply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

Depends on / 依赖: Iso.refl, all_goals, facePairIso, faceSingletonIso, isPushout, isPushout.of_iso, of_iso, stdSimplex, stdSimplex.facePairIso, stdSimplex.faceSingletonIso
-/
lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (1 : Fin 2)) ι₀₁ ι₁₂ := by
  apply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₁

namespace horn₂₂

/--
lemma `sq` / 引理 `sq`

English:
lemma sq
  statement: Subcomplex.BicartSq.{u} (stdSimplex.face {2}) (stdSimplex.face {0, 2})
  proof: by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (1 : Fin 3) 2 (by simp)
      · exact face_le_horn (0 : Fin 3) 2 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq :

中文:
引理 sq
  结论: Subcomplex.BicartSq.{u} (stdSimplex.face {2}) (stdSimplex.face {0, 2})
  证明: by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (1 : Fin 3) 2 (by simp)
      · exact face_le_horn (0 : Fin 3) 2 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq :

Depends on / 依赖: face_inter_face, face_le_horn, fin_cases, horn_eq_iSup, iSup_le_iff, inf_eq, le_antisymm, le_sup_left, le_sup_right, stdSimplex, stdSimplex.face_inter_face, sup_le_iff
-/
lemma sq : Subcomplex.BicartSq.{u} (stdSimplex.face {2}) (stdSimplex.face {0, 2})
    (stdSimplex.face {1, 2}) Λ[2, 2] where
  sup_eq := by
    apply le_antisymm
    · rw [sup_le_iff]
      constructor
      · exact face_le_horn (1 : Fin 3) 2 (by simp)
      · exact face_le_horn (0 : Fin 3) 2 (by simp)
    · rw [horn_eq_iSup, iSup_le_iff]
      rintro i
      fin_cases i
      · exact le_sup_right
      · exact le_sup_left
  inf_eq := by simp [stdSimplex.face_inter_face]

/--
Definition of `ι₀₂` / `ι₀₂` 的定义

English:
abbreviation ι₀₂
  signature: : Δ[1] ⟶ Λ[2, 2]
  body: horn.ι.{u} 2 1 (by simp)

中文:
缩写 ι₀₂
  签名: : Δ[1] ⟶ Λ[2, 2]
  定义体: horn.ι.{u} 2 1 (by simp)
-/
abbrev ι₀₂ : Δ[1] ⟶ Λ[2, 2] := horn.ι.{u} 2 1 (by simp)

/--
Definition of `ι₁₂` / `ι₁₂` 的定义

English:
abbreviation ι₁₂
  signature: : Δ[1] ⟶ Λ[2, 2]
  body: horn.ι.{u} 2 0 (by simp)

中文:
缩写 ι₁₂
  签名: : Δ[1] ⟶ Λ[2, 2]
  定义体: horn.ι.{u} 2 0 (by simp)
-/
abbrev ι₁₂ : Δ[1] ⟶ Λ[2, 2] := horn.ι.{u} 2 0 (by simp)

/--
lemma `isPushout` / 引理 `isPushout`

English:
lemma isPushout
  proof: by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

中文:
引理 isPushout
  证明: by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

Depends on / 依赖: Iso.refl, all_goals, facePairIso, faceSingletonIso, fapply, isPushout, isPushout.of_iso, of_iso, stdSimplex, stdSimplex.facePairIso, stdSimplex.faceSingletonIso
-/
lemma isPushout :
    IsPushout (stdSimplex.{u}.δ (0 : Fin 2))
      (stdSimplex.{u}.δ (0 : Fin 2)) ι₀₂ ι₁₂ := by
  fapply sq.{u}.isPushout.of_iso' (stdSimplex.faceSingletonIso _)
    (stdSimplex.facePairIso _ _ (by simp)) (stdSimplex.facePairIso _ _ (by simp))
    (Iso.refl _)
  all_goals decide

end horn₂₂

namespace horn

variable {n : Nat}

/--
lemma `multicoequalizerDiagram` / 引理 `multicoequalizerDiagram`

English:
lemma multicoequalizerDiagram
  given: (i : Fin (n + 1))
  proof: by rw [horn_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

中文:
引理 multicoequalizerDiagram
  条件: (i : Fin (n + 1))
  证明: by rw [horn_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

Depends on / 依赖: stdSimplex, stdSimplex.face
-/
lemma multicoequalizerDiagram (i : Fin (n + 1)) :
    Subcomplex.MulticoequalizerDiagram Λ[n, i]
      (ι := ({i}ᶜ : Set (Fin (n + 1)))) (fun j => stdSimplex.face {j.1}ᶜ)
      (fun j k => stdSimplex.face {j.1, k.1}ᶜ) where
  iSup_eq := by rw [horn_eq_iSup]
  eq_inf j k := by
    rw [stdSimplex.face_inter_face]
    congr
    aesop

/--
Definition of `isColimit` / `isColimit` 的定义

English:
definition isColimit
  signature: (i : Fin (n + 1))
  body: (multicoequalizerDiagram i).isColimit'

中文:
定义 isColimit
  签名: (i : Fin (n + 1))
  定义体: (multicoequalizerDiagram i).isColimit'

Depends on / 依赖: isColimit, multicoequalizerDiagram
-/
noncomputable def isColimit (i : Fin (n + 1)) :
    IsColimit ((multicoequalizerDiagram i).multicofork.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  (multicoequalizerDiagram i).isColimit'

variable {X : SSet.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `hom_ext'` / 引理 `hom_ext'`

English:
lemma hom_ext'
  statement: {i : Fin (n + 2)} {f g : (Λ[n + 1, i] : SSet) ⟶ X}
  proof: by
  refine Multicofork.IsColimit.hom_ext (isColimit i) (fun ⟨j, hj⟩ => ?_)
  simpa only [faceSingletonComplIso_inv_ι_assoc] using!
    (stdSimplex.faceSingletonComplIso j).inv ≫= h j hj

中文:
引理 hom_ext'
  结论: {i : Fin (n + 2)} {f g : (Λ[n + 1, i] : SSet) ⟶ X}
  证明: by
  refine Multicofork.IsColimit.hom_ext (isColimit i) (fun ⟨j, hj⟩ => ?_)
  simpa only [faceSingletonComplIso_inv_ι_assoc] using!
    (stdSimplex.faceSingletonComplIso j).inv ≫= h j hj

Depends on / 依赖: IsColimit, Multicofork, Multicofork.IsColimit.hom_ext, faceSingletonComplIso, hom_ext, isColimit, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma hom_ext' {i : Fin (n + 2)} {f g : (Λ[n + 1, i] : SSet) ⟶ X}
    (h : forall (j : Fin (n + 2)) (hj : j != i), horn.ι i j hj ≫ f = horn.ι i j hj ≫ g) :
    f = g := by
  refine Multicofork.IsColimit.hom_ext (isColimit i) (fun ⟨j, hj⟩ => ?_)
  simpa only [faceSingletonComplIso_inv_ι_assoc] using!
    (stdSimplex.faceSingletonComplIso j).inv ≫= h j hj

/--
Definition of `IsCompatible` / `IsCompatible` 的定义

English:
definition IsCompatible
  body: match n with
  | 0 => True
  | n + 1 => forall (j k : Fin (n + 3)) (hj : j != i) (hk : k != i) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk

@[simp]

中文:
定义 IsCompatible
  定义体: match n with
  | 0 => True
  | n + 1 => forall (j k : Fin (n + 3)) (hj : j != i) (hk : k != i) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk

@[simp]
-/
protected def IsCompatible
    {i : Fin (n + 2)} (f : forall (j : Fin (n + 2)) (_ : j != i), Δ[n] ⟶ X) : Prop :=
  match n with
  | 0 => True
  | n + 1 => forall (j k : Fin (n + 3)) (hj : j != i) (hk : k != i) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk

@[simp]
/--
lemma `isCompatible_zero_iff_true` / 引理 `isCompatible_zero_iff_true`

English:
lemma isCompatible_zero_iff_true
  given: {i : Fin 2} (f : forall (j : Fin 2) (_ : j != i), Δ[0] ⟶ X)
  proof: Iff.rfl

@[simp]

中文:
引理 isCompatible_zero_iff_true
  条件: {i : Fin 2} (f : 对任意 (j : Fin 2) (_ : j != i), Δ[0] ⟶ X)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
lemma isCompatible_zero_iff_true {i : Fin 2} (f : forall (j : Fin 2) (_ : j != i), Δ[0] ⟶ X) :
    horn.IsCompatible f ↔ True := Iff.rfl

@[simp]
/--
lemma `isCompatible_iff` / 引理 `isCompatible_iff`

English:
lemma isCompatible_iff
  proof: Iff.rfl

中文:
引理 isCompatible_iff
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isCompatible_iff
    {i : Fin (n + 3)} (f : forall (j : Fin (n + 3)) (_ : j != i), Δ[n + 1] ⟶ X) :
    horn.IsCompatible f ↔
    forall (j k : Fin (n + 3)) (hj : j != i) (hk : k != i) (hjk : j < k),
      stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
      stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk := Iff.rfl

namespace IsCompatible

/--
lemma `of_hom` / 引理 `of_hom`

English:
lemma of_hom
  given: {i : Fin (n + 2)} (g : (Λ[n + 1, i] : SSet) ⟶ X)
  proof: by
  obtain _ | n := n
  · simp
  · simp only [isCompatible_iff, ← Category.assoc]
    intro j k hj hk hjk
    congr 1
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    rw [← cancel_mono (Subcomplex.ι _)]; 

中文:
引理 of_hom
  条件: {i : Fin (n + 2)} (g : (Λ[n + 1, i] : SSet) ⟶ X)
  证明: by
  obtain _ | n := n
  · simp
  · simp only [isCompatible_iff, ← Category.assoc]
    intro j k hj hk hjk
    congr 1
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    rw [← cancel_mono (Subcomplex.ι _)]; 

Depends on / 依赖: Category, Category.assoc, Fin.castPred_castSucc, Fin.ne_last_of_lt, Fin.ne_zero_of_lt, Fin.pred_succ, Subcomplex, cancel_mono, castPred_castSucc, eq_castSucc_of_ne_last, eq_succ_of_ne_zero, isCompatible_iff, j.eq_castSucc_of_ne_last, k.eq_succ_of_ne_zero, ne_last_of_lt, ne_zero_of_lt, pred_succ, stdSimplex
-/
lemma of_hom {i : Fin (n + 2)} (g : (Λ[n + 1, i] : SSet) ⟶ X) :
    horn.IsCompatible (fun j hj => horn.ι i j hj ≫ g) := by
  obtain _ | n := n
  · simp
  · simp only [isCompatible_iff, ← Category.assoc]
    intro j k hj hk hjk
    congr 1
    obtain ⟨j, rfl⟩ := j.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hjk)
    obtain ⟨k, rfl⟩ := k.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hjk)
    rw [← cancel_mono (Subcomplex.ι _)]; rw [Category.assoc]; rw [Category.assoc]; rw [ι_ι]; rw [ι_ι]; rw [Fin.pred_succ]; rw [Fin.castPred_castSucc]; rw [stdSimplex.δ_comp_δ (by grind)]

@[reassoc]
/--
lemma `δ_pred_comp` / 引理 `δ_pred_comp`

English:
lemma δ_pred_comp
  statement: {i : Fin (n + 3)} {f : forall (j : Fin (n + 3)) (_ : j != i), (Δ[n + 1] : SSet) ⟶ X}
  proof: hf j k hj hk hjk

中文:
引理 δ_pred_comp
  结论: {i : Fin (n + 3)} {f : 对任意 (j : Fin (n + 3)) (_ : j != i), (Δ[n + 1] : SSet) ⟶ X}
  证明: hf j k hj hk hjk

Depends on / 依赖: Fin.ne_last_of_lt, Fin.ne_zero_of_lt, castPred, j.castPred, k.pred, ne_last_of_lt, ne_zero_of_lt, stdSimplex
-/
lemma δ_pred_comp {i : Fin (n + 3)} {f : forall (j : Fin (n + 3)) (_ : j != i), (Δ[n + 1] : SSet) ⟶ X}
    (hf : horn.IsCompatible f) (j k : Fin (n + 3))
    (hj : j != i := by grind) (hk : k != i := by grind) (hjk : j < k := by grind) :
    stdSimplex.δ (k.pred (Fin.ne_zero_of_lt hjk)) ≫ f j hj =
    stdSimplex.δ (j.castPred (Fin.ne_last_of_lt hjk)) ≫ f k hk :=
  hf j k hj hk hjk

variable {i : Fin (n + 2)} {f : forall (j : Fin (n + 2)) (_ : j != i), (Δ[n] : SSet) ⟶ X}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
open stdSimplex in
/--
Definition of `multicofork` / `multicofork` 的定义

English:
definition multicofork
  signature: (hf : horn.IsCompatible f)
  body: Multicofork.ofπ _ X (fun ⟨j, hj⟩ => (stdSimplex.faceSingletonComplIso j).inv ≫ f j hj) (by
    obtain _ | n := n
    · rintro ⟨⟨a, b⟩, hab⟩
      grind
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab : a < b⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha hb
      dsimp
      rw [homOfLE_fac

中文:
定义 multicofork
  签名: (hf : horn.IsCompatible f)
  定义体: Multicofork.ofπ _ X (fun ⟨j, hj⟩ => (stdSimplex.faceSingletonComplIso j).inv ≫ f j hj) (by
    obtain _ | n := n
    · rintro ⟨⟨a, b⟩, hab⟩
      grind
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab : a < b⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha hb
      dsimp
      rw [homOfLE_fac
-/
private def multicofork (hf : horn.IsCompatible f) :
    Multicofork ((multicoequalizerDiagram i).multispanIndex.toLinearOrder.map
      (Subcomplex.toSSetFunctor)) :=
  Multicofork.ofπ _ X (fun ⟨j, hj⟩ => (stdSimplex.faceSingletonComplIso j).inv ≫ f j hj) (by
    obtain _ | n := n
    · rintro ⟨⟨a, b⟩, hab⟩
      grind
    · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab : a < b⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ha hb
      dsimp
      rw [homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_pred_assoc _ _ hab]; rw [homOfLE_faceSingletonComplIso_inv_eq_facePairComplIso_inv_δ_castPred_assoc _ _ hab]; rw [hf.δ_pred_comp ..])

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_desc` / 引理 `exists_desc`

English:
lemma exists_desc
  given: (hf : horn.IsCompatible f)
  proof: ⟨(horn.isColimit.{u} i).desc hf.multicofork, fun j hj => by
    rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).inv]
    simpa using! (horn.isColimit.{u} i).fac hf.multicofork (.right ⟨j, hj⟩)⟩

中文:
引理 exists_desc
  条件: (hf : horn.IsCompatible f)
  证明: ⟨(horn.isColimit.{u} i).desc hf.multicofork, fun j hj => by
    rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).inv]
    simpa using! (horn.isColimit.{u} i).fac hf.multicofork (.right ⟨j, hj⟩)⟩

Depends on / 依赖: cancel_epi, faceSingletonComplIso, hf.multicofork, horn.isColimit, isColimit, multicofork, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma exists_desc (hf : horn.IsCompatible f) :
    exists (φ : (Λ[n + 1, i] : SSet) ⟶ X),
      forall (j : Fin (n + 2)) (hj : j != i), horn.ι i j hj ≫ φ = f j hj :=
  ⟨(horn.isColimit.{u} i).desc hf.multicofork, fun j hj => by
    rw [← cancel_epi (stdSimplex.faceSingletonComplIso j).inv]
    simpa using! (horn.isColimit.{u} i).fac hf.multicofork (.right ⟨j, hj⟩)⟩

/-- Let `i : Fin (n + 2)`. Given a compatible family of morphisms `Δ[n] ⟶ X` for `j ≠ i`,
this is the glued morphism `Λ[n + 1, i] ⟶ X`. -/
@[no_expose]
/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: (hf : horn.IsCompatible f)
  body: hf.exists_desc.choose

@[reassoc (attr := simp)]

中文:
定义 desc
  签名: (hf : horn.IsCompatible f)
  定义体: hf.exists_desc.choose

@[reassoc (attr := simp)]

Depends on / 依赖: exists_desc, hf.exists_desc.choose
-/
noncomputable def desc (hf : horn.IsCompatible f) : (Λ[n + 1, i] : SSet) ⟶ X :=
  hf.exists_desc.choose

@[reassoc (attr := simp)]
/--
lemma `ι_desc` / 引理 `ι_desc`

English:
lemma ι_desc
  given: (hf : horn.IsCompatible f) (j : Fin (n + 2)) (hj : j != i)
  proof: hf.exists_desc.choose_spec j hj

中文:
引理 ι_desc
  条件: (hf : horn.IsCompatible f) (j : Fin (n + 2)) (hj : j != i)
  证明: hf.exists_desc.choose_spec j hj

Depends on / 依赖: choose_spec, exists_desc, hf.exists_desc.choose_spec
-/
lemma ι_desc (hf : horn.IsCompatible f) (j : Fin (n + 2)) (hj : j != i) :
    horn.ι i j hj ≫ hf.desc = f j hj :=
  hf.exists_desc.choose_spec j hj

end IsCompatible

end horn

namespace horn₃₁

/--
Definition of `ι₀` / `ι₀` 的定义

English:
abbreviation ι₀
  signature: : Δ[2] ⟶ Λ[3, 1]
  body: horn.ι.{u} 1 0 (by simp)

中文:
缩写 ι₀
  签名: : Δ[2] ⟶ Λ[3, 1]
  定义体: horn.ι.{u} 1 0 (by simp)
-/
abbrev ι₀ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 0 (by simp)

/--
Definition of `ι₂` / `ι₂` 的定义

English:
abbreviation ι₂
  signature: : Δ[2] ⟶ Λ[3, 1]
  body: horn.ι.{u} 1 2 (by simp)

中文:
缩写 ι₂
  签名: : Δ[2] ⟶ Λ[3, 1]
  定义体: horn.ι.{u} 1 2 (by simp)
-/
abbrev ι₂ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 2 (by simp)

/--
Definition of `ι₃` / `ι₃` 的定义

English:
abbreviation ι₃
  signature: : Δ[2] ⟶ Λ[3, 1]
  body: horn.ι.{u} 1 3 (by simp)

中文:
缩写 ι₃
  签名: : Δ[2] ⟶ Λ[3, 1]
  定义体: horn.ι.{u} 1 3 (by simp)
-/
abbrev ι₃ : Δ[2] ⟶ Λ[3, 1] := horn.ι.{u} 1 3 (by simp)

variable {X : SSet.{u}} (f₀ f₂ f₃ : Δ[2] ⟶ X)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₁₃ : stdSimplex.δ 1 ≫ f₀ = stdSimplex.δ 0 ≫ f₂)
  (h₂₃ : stdSimplex.δ 2 ≫ f₂ = stdSimplex.δ 2 ≫ f₃)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `desc`. -/
@[simps! pt]
/--
Definition of `desc.multicofork` / `desc.multicofork` 的定义

English:
definition desc.multicofork
  signature: :
  body: Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ => match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => False.elim (by simp at hi)
    | 2 => (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x => by
      dsimp at x ⊢

中文:
定义 desc.multicofork
  签名: :
  定义体: Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ => match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => False.elim (by simp at hi)
    | 2 => (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x => by
      dsimp at x ⊢

Depends on / 依赖: Category, Category.assoc, False.elim, Multicofork, Multicofork.of, cancel_epi, convert, facePairIso, faceSingletonComplIso, fin_cases, stdSimplex, stdSimplex.facePairIso, stdSimplex.faceSingletonComplIso
-/
def desc.multicofork :
    Multicofork ((horn.multicoequalizerDiagram (1 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ => match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => False.elim (by simp at hi)
    | 2 => (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x => by
      dsimp at x ⊢
      fin_cases x
      · simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 3 (by simp)).hom,
          ← Category.assoc]
        convert! h₁₃ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← Category.assoc]
        convert! h₁₂ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 0 1 (by simp)).hom,
          ← Category.assoc]
        convert! h₂₃ <;> decide)

@[simp, reassoc]
/--
lemma `desc.multicofork_π_zero` / 引理 `desc.multicofork_π_zero`

English:
lemma desc.multicofork_π_zero
  proof: rfl

@[simp, reassoc]

中文:
引理 desc.multicofork_π_zero
  证明: rfl

@[simp, reassoc]
-/
lemma desc.multicofork_π_zero :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨0, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀ := rfl

@[simp, reassoc]
/--
lemma `desc.multicofork_π_two` / 引理 `desc.multicofork_π_two`

English:
lemma desc.multicofork_π_two
  proof: rfl

@[simp, reassoc]

中文:
引理 desc.multicofork_π_two
  证明: rfl

@[simp, reassoc]
-/
lemma desc.multicofork_π_two :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨2, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 2).inv ≫ f₂ := rfl

@[simp, reassoc]
/--
lemma `desc.multicofork_π_three` / 引理 `desc.multicofork_π_three`

English:
lemma desc.multicofork_π_three
  proof: rfl

中文:
引理 desc.multicofork_π_three
  证明: rfl
-/
lemma desc.multicofork_π_three :
  (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃).π ⟨3, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃ := rfl

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: : (Λ[3, 1] : SSet) ⟶ X
  body: (horn.isColimit (n := 3) 1).desc (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)

@[reassoc (attr := simp)]

中文:
定义 desc
  签名: : (Λ[3, 1] : SSet) ⟶ X
  定义体: (horn.isColimit (n := 3) 1).desc (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)

@[reassoc (attr := simp)]

Depends on / 依赖: desc.multicofork, horn.isColimit, isColimit, multicofork
-/
noncomputable def desc : (Λ[3, 1] : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 1).desc (desc.multicofork f₀ f₂ f₃ h₁₂ h₁₃ h₂₃)

@[reassoc (attr := simp)]
/--
lemma `ι₀_desc` / 引理 `ι₀_desc`

English:
lemma ι₀_desc
  statement: ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀
  proof: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]

中文:
引理 ι₀_desc
  结论: ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀
  证明: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, cancel_epi, faceSingletonComplIso, horn.faceSingletonComplIso_inv_, horn.isColimit, isColimit, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma ι₀_desc : ι₀ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
/--
lemma `ι₂_desc` / 引理 `ι₂_desc`

English:
lemma ι₂_desc
  statement: ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂
  proof: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 2).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨2, by simp⟩)

@[reassoc (attr := simp)]

中文:
引理 ι₂_desc
  结论: ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂
  证明: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 2).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨2, by simp⟩)

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, cancel_epi, faceSingletonComplIso, horn.faceSingletonComplIso_inv_, horn.isColimit, isColimit, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma ι₂_desc : ι₂ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₂ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 2).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨2, by simp⟩)

@[reassoc (attr := simp)]
/--
lemma `ι₃_desc` / 引理 `ι₃_desc`

English:
lemma ι₃_desc
  statement: ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃
  proof: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨3, by simp⟩)

include h₁₂ h₁₃ h₂₃ in

中文:
引理 ι₃_desc
  结论: ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃
  证明: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨3, by simp⟩)

include h₁₂ h₁₃ h₂₃ in

Depends on / 依赖: Category, Category.assoc, cancel_epi, faceSingletonComplIso, horn.faceSingletonComplIso_inv_, horn.isColimit, isColimit, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma ι₃_desc : ι₃ ≫ desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 1).fac _ (.right ⟨3, by simp⟩)

include h₁₂ h₁₃ h₂₃ in
/--
lemma `exists_desc` / 引理 `exists_desc`

English:
lemma exists_desc
  statement: exists (φ : (Λ[3, 1] : SSet) ⟶ X),
  proof: ⟨desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃, by simp⟩

中文:
引理 exists_desc
  结论: 存在 (φ : (Λ[3, 1] : SSet) ⟶ X),
  证明: ⟨desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃, by simp⟩
-/
lemma exists_desc : exists (φ : (Λ[3, 1] : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₂ ≫ φ = f₂ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₂ f₃ h₁₂ h₁₃ h₂₃, by simp⟩

end horn₃₁

namespace horn₃₂

/--
Definition of `ι₀` / `ι₀` 的定义

English:
abbreviation ι₀
  signature: : Δ[2] ⟶ Λ[3, 2]
  body: horn.ι.{u} 2 0 (by simp)

中文:
缩写 ι₀
  签名: : Δ[2] ⟶ Λ[3, 2]
  定义体: horn.ι.{u} 2 0 (by simp)
-/
abbrev ι₀ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 0 (by simp)

/--
Definition of `ι₁` / `ι₁` 的定义

English:
abbreviation ι₁
  signature: : Δ[2] ⟶ Λ[3, 2]
  body: horn.ι.{u} 2 1 (by simp)

中文:
缩写 ι₁
  签名: : Δ[2] ⟶ Λ[3, 2]
  定义体: horn.ι.{u} 2 1 (by simp)
-/
abbrev ι₁ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 1 (by simp)

/--
Definition of `ι₃` / `ι₃` 的定义

English:
abbreviation ι₃
  signature: : Δ[2] ⟶ Λ[3, 2]
  body: horn.ι.{u} 2 3 (by simp)

中文:
缩写 ι₃
  签名: : Δ[2] ⟶ Λ[3, 2]
  定义体: horn.ι.{u} 2 3 (by simp)
-/
abbrev ι₃ : Δ[2] ⟶ Λ[3, 2] := horn.ι.{u} 2 3 (by simp)

variable {X : SSet.{u}} (f₀ f₁ f₃ : Δ[2] ⟶ X)
  (h₀₂ : stdSimplex.δ 2 ≫ f₁ = stdSimplex.δ 1 ≫ f₃)
  (h₁₂ : stdSimplex.δ 2 ≫ f₀ = stdSimplex.δ 0 ≫ f₃)
  (h₂₃ : stdSimplex.δ 0 ≫ f₀ = stdSimplex.δ 0 ≫ f₁)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary definition for `desc`. -/
@[simps! pt]
/--
Definition of `desc.multicofork` / `desc.multicofork` 的定义

English:
definition desc.multicofork
  signature: :
  body: Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ => match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁
    | 2 => False.elim (by simp at hi)
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x => by
      dsimp at x ⊢

中文:
定义 desc.multicofork
  签名: :
  定义体: Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ => match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁
    | 2 => False.elim (by simp at hi)
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x => by
      dsimp at x ⊢
-/
def desc.multicofork :
    Multicofork ((horn.multicoequalizerDiagram (2 : Fin 4)).multispanIndex.toLinearOrder.map
      Subcomplex.toSSetFunctor) :=
  Multicofork.ofπ _ X (fun ⟨(i : Fin 4), hi⟩ => match i with
    | 0 => (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀
    | 1 => (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁
    | 2 => False.elim (by simp at hi)
    | 3 => (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃) (fun x => by
      dsimp at x ⊢
      fin_cases x
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 2 3 (by simp)).hom,
          ← Category.assoc]
        convert! h₂₃ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 1 2 (by simp)).hom,
          ← Category.assoc]
        convert! h₁₂ <;> decide
      · dsimp
        simp only [← cancel_epi (stdSimplex.facePairIso.{u} (n := 3) 0 2 (by simp)).hom,
          ← Category.assoc]
        convert! h₀₂ <;> decide)

@[simp, reassoc]
/--
lemma `desc.multicofork_π_zero` / 引理 `desc.multicofork_π_zero`

English:
lemma desc.multicofork_π_zero
  proof: rfl

@[simp, reassoc]

中文:
引理 desc.multicofork_π_zero
  证明: rfl

@[simp, reassoc]
-/
lemma desc.multicofork_π_zero :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨0, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 0).inv ≫ f₀ := rfl

@[simp, reassoc]
/--
lemma `desc.multicofork_π_one` / 引理 `desc.multicofork_π_one`

English:
lemma desc.multicofork_π_one
  proof: rfl

@[simp, reassoc]

中文:
引理 desc.multicofork_π_one
  证明: rfl

@[simp, reassoc]
-/
lemma desc.multicofork_π_one :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨1, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 1).inv ≫ f₁ := rfl

@[simp, reassoc]
/--
lemma `desc.multicofork_π_three` / 引理 `desc.multicofork_π_three`

English:
lemma desc.multicofork_π_three
  proof: rfl

中文:
引理 desc.multicofork_π_three
  证明: rfl
-/
lemma desc.multicofork_π_three :
  (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃).π ⟨3, by simp⟩ =
    (stdSimplex.faceSingletonComplIso 3).inv ≫ f₃ := rfl

/--
Definition of `desc` / `desc` 的定义

English:
definition desc
  signature: : (Λ[3, 2] : SSet) ⟶ X
  body: (horn.isColimit (n := 3) 2).desc (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)

@[reassoc (attr := simp)]

中文:
定义 desc
  签名: : (Λ[3, 2] : SSet) ⟶ X
  定义体: (horn.isColimit (n := 3) 2).desc (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)

@[reassoc (attr := simp)]

Depends on / 依赖: desc.multicofork, horn.isColimit, isColimit, multicofork
-/
noncomputable def desc : (Λ[3, 2] : SSet) ⟶ X :=
  (horn.isColimit (n := 3) 2).desc (desc.multicofork f₀ f₁ f₃ h₀₂ h₁₂ h₂₃)

@[reassoc (attr := simp)]
/--
lemma `ι₀_desc` / 引理 `ι₀_desc`

English:
lemma ι₀_desc
  statement: ι₀ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₀
  proof: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]

中文:
引理 ι₀_desc
  结论: ι₀ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₀
  证明: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, cancel_epi, faceSingletonComplIso, horn.faceSingletonComplIso_inv_, horn.isColimit, isColimit, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma ι₀_desc : ι₀ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₀ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 0).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨0, by simp⟩)

@[reassoc (attr := simp)]
/--
lemma `ι₁_desc` / 引理 `ι₁_desc`

English:
lemma ι₁_desc
  statement: ι₁ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₁
  proof: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 1).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨1, by simp⟩)

@[reassoc (attr := simp)]

中文:
引理 ι₁_desc
  结论: ι₁ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₁
  证明: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 1).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨1, by simp⟩)

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, cancel_epi, faceSingletonComplIso, horn.faceSingletonComplIso_inv_, horn.isColimit, isColimit, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma ι₁_desc : ι₁ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₁ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 1).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨1, by simp⟩)

@[reassoc (attr := simp)]
/--
lemma `ι₃_desc` / 引理 `ι₃_desc`

English:
lemma ι₃_desc
  statement: ι₃ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₃
  proof: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨3, by simp⟩)

include h₀₂ h₁₂ h₂₃ in

中文:
引理 ι₃_desc
  结论: ι₃ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₃
  证明: by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨3, by simp⟩)

include h₀₂ h₁₂ h₂₃ in

Depends on / 依赖: Category, Category.assoc, cancel_epi, faceSingletonComplIso, horn.faceSingletonComplIso_inv_, horn.isColimit, isColimit, stdSimplex, stdSimplex.faceSingletonComplIso
-/
lemma ι₃_desc : ι₃ ≫ desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃ = f₃ := by
  rw [← cancel_epi (stdSimplex.faceSingletonComplIso.{u} 3).inv]; rw [← Category.assoc]; rw [horn.faceSingletonComplIso_inv_ι]
  exact (horn.isColimit 2).fac _ (.right ⟨3, by simp⟩)

include h₀₂ h₁₂ h₂₃ in
/--
lemma `exists_desc` / 引理 `exists_desc`

English:
lemma exists_desc
  statement: exists (φ : (Λ[3, 2] : SSet) ⟶ X),
  proof: ⟨desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃, by simp⟩

中文:
引理 exists_desc
  结论: 存在 (φ : (Λ[3, 2] : SSet) ⟶ X),
  证明: ⟨desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃, by simp⟩
-/
lemma exists_desc : exists (φ : (Λ[3, 2] : SSet) ⟶ X),
    ι₀ ≫ φ = f₀ ∧ ι₁ ≫ φ = f₁ ∧ ι₃ ≫ φ = f₃ :=
  ⟨desc f₀ f₁ f₃ h₀₂ h₁₂ h₂₃, by simp⟩

end horn₃₂

end SSet
