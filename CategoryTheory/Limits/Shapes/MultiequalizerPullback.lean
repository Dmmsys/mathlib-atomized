/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Multicoequalizers that are pushouts

In this file, we show that a multicoequalizer for
`I : MultispanIndex (.ofLinearOrder ι) C` is also
a pushout when `ι` has exactly two elements.

-/

@[expose] public section

namespace CategoryTheory.Limits.Multicofork.IsColimit

variable {C : Type*} [Category* C] {J : MultispanShape} [Unique J.L]
  {I : MultispanIndex J C} (c : Multicofork I)
  (h : {J.fst default, J.snd default} = Set.univ) (h' : J.fst default != J.snd default)

namespace isPushout

variable (s : PushoutCocone (I.fst default) (I.snd default))

open scoped Classical in
/--
Definition of `multicofork` / `multicofork` 的定义

English:
definition multicofork
  signature: : Multicofork I
  body: Multicofork.ofπ _ s.pt
    (fun k =>
      if hk : k = J.fst default then
        eqToHom (by simp [hk]) ≫ s.inl
      else
        eqToHom (by
          obtain rfl : k = J.snd default := by
            have := h.symm.le (Set.mem_univ k)
            push _ in _ at this
            tauto
          rfl) ≫ s.inr)
    (by
      rw [Unique.forall_iff]
      simpa [h'.symm] using s.condition)

@[simp]

中文:
定义 multicofork
  签名: : Multicofork I
  定义体: Multicofork.ofπ _ s.pt
    (fun k =>
      if hk : k = J.fst default then
        eqToHom (by simp [hk]) ≫ s.inl
      else
        eqToHom (by
          obtain rfl : k = J.snd default := by
            have := h.symm.le (Set.mem_univ k)
            push _ in _ at this
            tauto
          rfl) ≫ s.inr)
    (by
      rw [Unique.forall_iff]
      simpa [h'.symm] using s.condition)

@[simp]

Depends on / 依赖: J.fst, J.snd, Multicofork, Multicofork.of, Set.mem_univ, Unique, Unique.forall_iff, condition, eqToHom, forall_iff, h.symm.le, mem_univ, s.condition, s.inl, s.inr, s.pt
-/
noncomputable def multicofork : Multicofork I :=
  Multicofork.ofπ _ s.pt
    (fun k =>
      if hk : k = J.fst default then
        eqToHom (by simp [hk]) ≫ s.inl
      else
        eqToHom (by
          obtain rfl : k = J.snd default := by
            have := h.symm.le (Set.mem_univ k)
            push _ in _ at this
            tauto
          rfl) ≫ s.inr)
    (by
      rw [Unique.forall_iff]
      simpa [h'.symm] using s.condition)

@[simp]
/--
lemma `multicofork_π_eq_inl` / 引理 `multicofork_π_eq_inl`

English:
lemma multicofork_π_eq_inl
  statement: (multicofork h h' s).π (J.fst default) = s.inl
  proof: by
  dsimp only [multicofork, ofπ, π]
  rw [dif_pos rfl]; rw [eqToHom_refl]; rw [Category.id_comp]

@[simp]

中文:
引理 multicofork_π_eq_inl
  结论: (multicofork h h' s).π (J.fst default) = s.inl
  证明: by
  dsimp only [multicofork, ofπ, π]
  rw [dif_pos rfl]; rw [eqToHom_refl]; rw [Category.id_comp]

@[simp]

Depends on / 依赖: Category, Category.id_comp, dif_pos, eqToHom_refl, id_comp, multicofork
-/
lemma multicofork_π_eq_inl : (multicofork h h' s).π (J.fst default) = s.inl := by
  dsimp only [multicofork, ofπ, π]
  rw [dif_pos rfl]; rw [eqToHom_refl]; rw [Category.id_comp]

@[simp]
/--
lemma `multicofork_π_eq_inr` / 引理 `multicofork_π_eq_inr`

English:
lemma multicofork_π_eq_inr
  statement: (multicofork h h' s).π (J.snd default) = s.inr
  proof: by
  dsimp only [multicofork, ofπ, π]
  rw [dif_neg h'.symm]; rw [eqToHom_refl]; rw [Category.id_comp]

中文:
引理 multicofork_π_eq_inr
  结论: (multicofork h h' s).π (J.snd default) = s.inr
  证明: by
  dsimp only [multicofork, ofπ, π]
  rw [dif_neg h'.symm]; rw [eqToHom_refl]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, dif_neg, eqToHom_refl, id_comp, multicofork
-/
lemma multicofork_π_eq_inr : (multicofork h h' s).π (J.snd default) = s.inr := by
  dsimp only [multicofork, ofπ, π]
  rw [dif_neg h'.symm]; rw [eqToHom_refl]; rw [Category.id_comp]

end isPushout

include h h' in
/--
lemma `isPushout` / 引理 `isPushout`

English:
lemma isPushout
  given: (hc : IsColimit c)
  proof: c.condition _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s => hc.desc (isPushout.multicofork h h' s))
    (fun s => by simpa using! hc.fac (isPushout.multicofork h h' s) (.right (J.fst default)))
    (fun s => by simpa using! hc.fac (isPushout.multicofork h h' s) (.right (J.snd default)))
    (fun s m h₁ h₂ => by
      apply Multicofork.IsColimit.hom_ext hc
      intro k
      have := h.symm.le (Set.mem_univ k)
      push _ in _ at this
      obtain rfl | rfl := this
      · simpa [h₁] using! (hc.fac (isPushout.multicofork h h' s) (.right (J.fst default))).symm
      · simpa [h₂] using! (hc.fac (isPushout.multicofork h h' s) (.right (J.snd default))).symm)⟩

中文:
引理 isPushout
  条件: (hc : 是余极限 c)
  证明: c.condition _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s => hc.desc (isPushout.multicofork h h' s))
    (fun s => by simpa using! hc.fac (isPushout.multicofork h h' s) (.right (J.fst default)))
    (fun s => by simpa using! hc.fac (isPushout.multicofork h h' s) (.right (J.snd default)))
    (fun s m h₁ h₂ => by
      apply Multicofork.IsColimit.hom_ext hc
      intro k
      have := h.symm.le (Set.mem_univ k)
      push _ in _ at this
      obtain rfl | rfl := this
      · simpa [h₁] using! (hc.fac (isPushout.multicofork h h' s) (.right (J.fst default))).symm
      · simpa [h₂] using! (hc.fac (isPushout.multicofork h h' s) (.right (J.snd default))).symm)⟩

Depends on / 依赖: c.condition, condition
-/
lemma isPushout (hc : IsColimit c) :
    IsPushout (I.fst default) (I.snd default) (c.π (J.fst default)) (c.π (J.snd default)) where
  w := c.condition _
  isColimit' := ⟨PushoutCocone.IsColimit.mk _
    (fun s => hc.desc (isPushout.multicofork h h' s))
    (fun s => by simpa using! hc.fac (isPushout.multicofork h h' s) (.right (J.fst default)))
    (fun s => by simpa using! hc.fac (isPushout.multicofork h h' s) (.right (J.snd default)))
    (fun s m h₁ h₂ => by
      apply Multicofork.IsColimit.hom_ext hc
      intro k
      have := h.symm.le (Set.mem_univ k)
      push _ in _ at this
      obtain rfl | rfl := this
      · simpa [h₁] using! (hc.fac (isPushout.multicofork h h' s) (.right (J.fst default))).symm
      · simpa [h₂] using! (hc.fac (isPushout.multicofork h h' s) (.right (J.snd default))).symm)⟩

end CategoryTheory.Limits.Multicofork.IsColimit
