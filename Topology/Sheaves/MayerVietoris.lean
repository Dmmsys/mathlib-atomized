/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.MayerVietorisSquare
public import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Mayer-Vietoris squares

Given two open subsets `U` and `V` of a topological space `T`,
we construct the associated Mayer-Vietoris square:
```
U ⊓ V ---> U
  | |
  v v
  V ---> U ⊔ V
```

-/

@[expose] public section

universe u

namespace Opens

open CategoryTheory Limits TopologicalSpace

variable {T : Type u} [TopologicalSpace T]

/-- A square consisting of opens `X₂ ⊓ X₃`, `X₂`, `X₃` and `X₂ ⊔ X₃` is
a Mayer-Vietoris square. -/
@[simps! toSquare]
/--
Definition of `mayerVietorisSquare'` / `mayerVietorisSquare'` 的定义

English:
definition mayerVietorisSquare'
  signature: (sq : Square (Opens T))
  body: GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := (Opens.grothendieckTopology T)) sq
    (Square.IsPullback.mk _ (by
      refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
      · intro s
        apply homOfLE
        rw [h₁]; rw [le_inf_iff]
        exact ⟨leOfHom s.fst, leOfHom s.snd⟩
      all_goals intros; apply Subsingleton.elim))
    (fun x hx => by
      rw [h₄] at hx
      obtain (hx | hx) := hx
      · exact ⟨_, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.left, hx⟩⟩
      · exact ⟨_, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.right, hx⟩⟩)

中文:
定义 mayerVietorisSquare'
  签名: (sq : Square (Opens T))
  定义体: GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := (Opens.grothendieckTopology T)) sq
    (Square.IsPullback.mk _ (by
      refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
      · intro s
        apply homOfLE
        rw [h₁]; rw [le_inf_iff]
        exact ⟨leOfHom s.fst, leOfHom s.snd⟩
      all_goals intros; apply Subsingleton.elim))
    (fun x hx => by
      rw [h₄] at hx
      obtain (hx | hx) := hx
      · exact ⟨_, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.left, hx⟩⟩
      · exact ⟨_, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.right, hx⟩⟩)

Depends on / 依赖: GrothendieckTopology, GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback, IsLimit, IsPullback, MayerVietorisSquare, Opens.grothendieckTopology, PullbackCone, PullbackCone.IsLimit.mk, Sieve.ofArrows_mk, Square, Square.IsPullback.mk, Subsingleton, Subsingleton.elim, WalkingPair, WalkingPair.left, WalkingPair.right, all_goals, grothendieckTopology, homOfLE, intros
-/
noncomputable def mayerVietorisSquare' (sq : Square (Opens T))
    (h₄ : sq.X₄ = sq.X₂ ⊔ sq.X₃) (h₁ : sq.X₁ = sq.X₂ ⊓ sq.X₃) :
    (Opens.grothendieckTopology T).MayerVietorisSquare :=
  GrothendieckTopology.MayerVietorisSquare.mk_of_isPullback
    (J := (Opens.grothendieckTopology T)) sq
    (Square.IsPullback.mk _ (by
      refine PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_
      · intro s
        apply homOfLE
        rw [h₁]; rw [le_inf_iff]
        exact ⟨leOfHom s.fst, leOfHom s.snd⟩
      all_goals intros; apply Subsingleton.elim))
    (fun x hx => by
      rw [h₄] at hx
      obtain (hx | hx) := hx
      · exact ⟨_, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.left, hx⟩⟩
      · exact ⟨_, _, ⟨Sieve.ofArrows_mk _ _ WalkingPair.right, hx⟩⟩)

/-- The Mayer-Vietoris square attached to two open subsets
of a topological space. -/
@[simps!]
/--
Definition of `mayerVietorisSquare` / `mayerVietorisSquare` 的定义

English:
definition mayerVietorisSquare
  signature: (U V : Opens T)
  body: mayerVietorisSquare'
    { X₁ := U ⊓ V
      X₂ := U
      X₃ := V
      X₄ := U ⊔ V
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_sup_left
      f₃₄ := homOfLE le_sup_right
      fac := Subsingleton.elim _ _ } rfl rfl

中文:
定义 mayerVietorisSquare
  签名: (U V : Opens T)
  定义体: mayerVietorisSquare'
    { X₁ := U ⊓ V
      X₂ := U
      X₃ := V
      X₄ := U ⊔ V
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_sup_left
      f₃₄ := homOfLE le_sup_right
      fac := Subsingleton.elim _ _ } rfl rfl

Depends on / 依赖: Subsingleton, Subsingleton.elim, homOfLE, inf_le_left, inf_le_right, le_sup_left, le_sup_right, mayerVietorisSquare
-/
noncomputable def mayerVietorisSquare (U V : Opens T) :
    (Opens.grothendieckTopology T).MayerVietorisSquare :=
  mayerVietorisSquare'
    { X₁ := U ⊓ V
      X₂ := U
      X₃ := V
      X₄ := U ⊔ V
      f₁₂ := homOfLE inf_le_left
      f₁₃ := homOfLE inf_le_right
      f₂₄ := homOfLE le_sup_left
      f₃₄ := homOfLE le_sup_right
      fac := Subsingleton.elim _ _ } rfl rfl

end Opens
