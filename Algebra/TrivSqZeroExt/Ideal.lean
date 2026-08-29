/-
Copyright (c) 2026 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The square zero ideal of the trivial square-zero extension

- `TrivSqZeroExt.kerIdeal`: the ideal in the trivial square-zero extension

- `TrivSqZeroExt.kerIdeal_sq `: this ideal has square zero.

-/

@[expose] public section

namespace TrivSqZeroExt

open Ideal

variable (R M : Type*)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]

/--
Definition of `kerIdeal` / `kerIdeal` 的定义

English:
definition kerIdeal
  signature: : Ideal (TrivSqZeroExt R M)
  body: RingHom.ker (fstHom R R M)

中文:
定义 kerIdeal
  签名: : Ideal (TrivSqZeroExt R M)
  定义体: RingHom.ker (fstHom R R M)

Depends on / 依赖: IsZariskiLocalAtTarget, IsZariskiLocalAtTarget.descendsAlong, MorphismProperty, MorphismProperty.of_isPullback_of_descendsAlong, QuasiCompact, RingHom, RingHom.ker, Surjective, X.Opens, continuous, descendsAlong, exists_opens_image_eq_of_prespectralSpace, f.continuous, f.isOpenMap.exists_opens_image_eq_of_prespectralSpace, fstHom, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, isCompact_univ, isOpenMap, isOpen_univ
-/
def kerIdeal : Ideal (TrivSqZeroExt R M) := RingHom.ker (fstHom R R M)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_kerIdeal_iff_inr` / 定理 `mem_kerIdeal_iff_inr`

English:
theorem mem_kerIdeal_iff_inr
  given: (x : TrivSqZeroExt R M)
  statement: x in kerIdeal R M ↔ x = inr x.snd
  proof: by
  obtain ⟨r, m⟩ := x
  simp only [kerIdeal, RingHom.mem_ker, fstHom_apply, fst_mk]
  exact ⟨fun hr => by rw [hr]; rfl, fun hrm => by rw [← fst_mk r m, hrm, fst_inr]⟩

中文:
定理 mem_kerIdeal_iff_inr
  条件: (x : TrivSqZeroExt R M)
  结论: x in kerIdeal R M ↔ x = inr x.snd
  证明: by
  obtain ⟨r, m⟩ := x
  simp only [kerIdeal, RingHom.mem_ker, fstHom_apply, fst_mk]
  exact ⟨fun hr => by rw [hr]; rfl, fun hrm => by rw [← fst_mk r m, hrm, fst_inr]⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.faithful_overPullback_of_isomorphisms_descendAlong, QuasiCompact, RingHom, RingHom.mem_ker, Surjective, faithful_overPullback_of_isomorphisms_descendAlong, fstHom_apply, fst_inr, fst_mk, kerIdeal, mem_ker
-/
theorem mem_kerIdeal_iff_inr (x : TrivSqZeroExt R M) : x in kerIdeal R M ↔ x = inr x.snd := by
  obtain ⟨r, m⟩ := x
  simp only [kerIdeal, RingHom.mem_ker, fstHom_apply, fst_mk]
  exact ⟨fun hr => by rw [hr]; rfl, fun hrm => by rw [← fst_mk r m, hrm, fst_inr]⟩

/--
theorem `kerIdeal_sq` / 定理 `kerIdeal_sq`

English:
theorem kerIdeal_sq
  statement: kerIdeal R M ^ 2 = ⊥
  proof: by
  simp only [pow_two, eq_bot_iff, mul_le, mem_kerIdeal_iff_inr]
  rintro x hx y hy
  rw [hx]; rw [hy]; rw [mem_bot]; rw [inr_mul_inr]

中文:
定理 kerIdeal_sq
  结论: kerIdeal R M ^ 2 = ⊥
  证明: by
  simp only [pow_two, eq_bot_iff, mul_le, mem_kerIdeal_iff_inr]
  rintro x hx y hy
  rw [hx]; rw [hy]; rw [mem_bot]; rw [inr_mul_inr]

Depends on / 依赖: LocallyOfFinitePresentation, MorphismProperty, MorphismProperty.faithful_overPullback_of_isomorphisms_descendAlong, Surjective, faithful_overPullback_of_isomorphisms_descendAlong
-/
@[simp] theorem kerIdeal_sq : kerIdeal R M ^ 2 = ⊥ := by
  simp only [pow_two, eq_bot_iff, mul_le, mem_kerIdeal_iff_inr]
  rintro x hx y hy
  rw [hx]; rw [hy]; rw [mem_bot]; rw [inr_mul_inr]

end TrivSqZeroExt

end
