/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# The covariant involution of the simplex category

In this file, we introduce the functor `rev : SimplexCategory ⥤ SimplexCategory`
which, via the equivalence between the simplex category and the
category of nonempty finite linearly ordered types, corresponds to
the *covariant* functor which sends a type `α` to `αᵒᵈ`.

-/

@[expose] public section

open CategoryTheory

namespace SimplexCategory

set_option backward.isDefEq.respectTransparency.types false in
/-- The covariant involution `rev : SimplexCategory ⥤ SimplexCategory` which,
via the equivalence between the simplex category and the
category of nonempty finite linearly ordered types, corresponds to
the *covariant* functor which sends a type `α` to `αᵒᵈ`.
This functor sends the object `⦋n⦌` to `⦋n⦌` and a map `f : ⦋n⦌ ⟶ ⦋m⦌`
is sent to the monotone map `(i : Fin (n + 1)) ↦ (f i.rev).rev`. -/
@[simps obj, simps -isSimp map, implicit_reducible]
/--
Definition of `rev` / `rev` 的定义

English:
definition rev
  signature: : SimplexCategory ⥤ SimplexCategory where
  body: n
  map {n m} f := Hom.mk ⟨fun i => (f i.rev).rev, fun i j hij => by
    rw [Fin.rev_le_rev]
    exact f.toOrderHom.monotone (by rwa [Fin.rev_le_rev])⟩

@[simp]

中文:
定义 rev
  签名: : SimplexCategory ⥤ SimplexCategory where
  定义体: n
  map {n m} f := Hom.mk ⟨fun i => (f i.rev).rev, fun i j hij => by
    rw [Fin.rev_le_rev]
    exact f.toOrderHom.monotone (by rwa [Fin.rev_le_rev])⟩

@[simp]
-/
def rev : SimplexCategory ⥤ SimplexCategory where
  obj n := n
  map {n m} f := Hom.mk ⟨fun i => (f i.rev).rev, fun i j hij => by
    rw [Fin.rev_le_rev]
    exact f.toOrderHom.monotone (by rwa [Fin.rev_le_rev])⟩

@[simp]
/--
lemma `rev_map_apply` / 引理 `rev_map_apply`

English:
lemma rev_map_apply
  given: {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1))
  proof: rfl

@[simp]

中文:
引理 rev_map_apply
  条件: {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1))
  证明: rfl

@[simp]

Depends on / 依赖: f.toOrderHom, i.rev, toOrderHom
-/
lemma rev_map_apply {n m : SimplexCategory} (f : n ⟶ m) (i : Fin (n.len + 1)) :
    (rev.map f).toOrderHom (a := n) (b := m) i = (f.toOrderHom i.rev).rev :=
  rfl

@[simp]
/--
lemma `rev_map_δ` / 引理 `rev_map_δ`

English:
lemma rev_map_δ
  given: {n : Nat} (i : Fin (n + 2))
  proof: by
  ext j : 3
  simp [δ, Fin.succAbove_rev_right, Fin.rev_rev, rev_map_apply]

@[simp]

中文:
引理 rev_map_δ
  条件: {n : 自然数} (i : Fin (n + 2))
  证明: by
  ext j : 3
  simp [δ, Fin.succAbove_rev_right, Fin.rev_rev, rev_map_apply]

@[simp]

Depends on / 依赖: Fin.rev_rev, Fin.succAbove_rev_right, rev_map_apply, rev_rev, succAbove_rev_right
-/
lemma rev_map_δ {n : Nat} (i : Fin (n + 2)) :
    rev.map (δ i) = δ i.rev := by
  ext j : 3
  simp [δ, Fin.succAbove_rev_right, Fin.rev_rev, rev_map_apply]

@[simp]
/--
lemma `rev_map_σ` / 引理 `rev_map_σ`

English:
lemma rev_map_σ
  given: {n : Nat} (i : Fin (n + 1))
  proof: by
  ext j : 3
  simp [σ, Fin.predAbove_rev_right, Fin.rev_rev, rev_map_apply]

中文:
引理 rev_map_σ
  条件: {n : 自然数} (i : Fin (n + 1))
  证明: by
  ext j : 3
  simp [σ, Fin.predAbove_rev_right, Fin.rev_rev, rev_map_apply]

Depends on / 依赖: Fin.predAbove_rev_right, Fin.rev_rev, predAbove_rev_right, rev_map_apply, rev_rev
-/
lemma rev_map_σ {n : Nat} (i : Fin (n + 1)) :
    rev.map (σ i) = σ i.rev := by
  ext j : 3
  simp [σ, Fin.predAbove_rev_right, Fin.rev_rev, rev_map_apply]

/-- The functor `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`
is a covariant involution. -/
@[simps! hom_app inv_app]
/--
Definition of `revCompRevIso` / `revCompRevIso` 的定义

English:
definition revCompRevIso
  signature: : rev ⋙ rev ≅ 𝟭 _
  body: NatIso.ofComponents (fun _ => Iso.refl _)

@[simp]

中文:
定义 revCompRevIso
  签名: : rev ⋙ rev ≅ 𝟭 _
  定义体: NatIso.ofComponents (fun _ => Iso.refl _)

@[simp]

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, ofComponents
-/
def revCompRevIso : rev ⋙ rev ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ => Iso.refl _)

@[simp]
/--
lemma `rev_map_rev_map` / 引理 `rev_map_rev_map`

English:
lemma rev_map_rev_map
  given: {n m : SimplexCategory} (f : n ⟶ m)
  proof: by
  aesop

中文:
引理 rev_map_rev_map
  条件: {n m : SimplexCategory} (f : n ⟶ m)
  证明: by
  aesop
-/
lemma rev_map_rev_map {n m : SimplexCategory} (f : n ⟶ m) :
    rev.map (rev.map f) = f := by
  aesop

/-- The functor `SimplexCategory.rev : SimplexCategory ⥤ SimplexCategory`
as an equivalence of category. -/
@[simps]
/--
Definition of `revEquivalence` / `revEquivalence` 的定义

English:
definition revEquivalence
  signature: : SimplexCategory ≌ SimplexCategory where
  body: rev
  inverse := rev
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso

中文:
定义 revEquivalence
  签名: : SimplexCategory ≌ SimplexCategory where
  定义体: rev
  inverse := rev
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso
-/
def revEquivalence : SimplexCategory ≌ SimplexCategory where
  functor := rev
  inverse := rev
  unitIso := revCompRevIso.symm
  counitIso := revCompRevIso

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: rev.IsEquivalence
  body: revEquivalence.isEquivalence_functor

中文:
实例 :
  签名: rev.IsEquivalence
  定义体: revEquivalence.isEquivalence_functor

Depends on / 依赖: isEquivalence_functor, revEquivalence, revEquivalence.isEquivalence_functor
-/
instance : rev.IsEquivalence := revEquivalence.isEquivalence_functor

end SimplexCategory
