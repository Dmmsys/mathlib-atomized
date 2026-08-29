/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes, Marc Robin
-/
module

public import Mathlib.RingTheory.Ideal.Oka
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Ideal.BigOperators

/-!
# Noetherian rings and prime ideals

## Main results

- `IsNoetherianRing.of_prime`: a ring where all prime ideals are finitely generated is a noetherian
  ring

## References

- [cohen1950]: *Commutative rings with restricted minimum condition*, I. S. Cohen, Theorem 2
-/

public section

variable {R : Type*} [CommRing R]

namespace Ideal

open Set Finset

/--
theorem `isOka_fg` / 定理 `isOka_fg`

English:
theorem isOka_fg
  statement: IsOka (FG (R := R)) where
  proof: ⟨{1}, by simp⟩
  oka {I a} hsup hcolon := by
    classical
    obtain ⟨_, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hsup
    obtain ⟨_, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hcolon
    rw [submodule_span_eq] at hf
    have H k : exists r : R, exists p in I, r * a + p = f k := by
      apply mem_span_singleton_sup.1
      rw [sup_comm]; rw [← hf]
      exact mem_span_range_self
    choose! r p p_mem_I Hf using H
    refine ⟨image p univ union image (a • i) univ, le_antisymm ?_ (fun y hy => ?_)⟩
    <;> simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, span_union]
    · simp only [sup_le_iff, span_le, range_subset_iff, smul_eq_mul]
      exact ⟨p_mem_I, fun _ => mul_comm a _ ▸ mem_colon_span_singleton.1 (hi ▸ mem_span_range_self)⟩
    · rw [Submodule.mem_sup]
      obtain ⟨s, H⟩ := mem_span_range_iff_exists_fun.1 (hf ▸ Ideal.mem_sup_left hy)
      simp_rw [← Hf] at H
      ring_nf at H
      rw [sum_add_distrib]; rw [← sum_mul]; rw [add_comm] at H
      refine ⟨(∑ k, s k * p k), sum_mem _ (fun _ _ => mul_mem_left _ _ mem_span_range_self),
        (∑ k, s k * r k) * a, ?_, H⟩
      rw [mul_comm]; rw [← smul_eq_mul]; rw [range_smul]; rw [← submodule_span_eq]; rw [Submodule.span_smul]; rw [hi]
exact smul_mem_smul_set mem_colon_span_singleton.2
        (I.add_mem_iff_right <| I.sum_mem (fun _ _ => mul_mem_left _ _ <| p_mem_I _)).1 (H ▸ hy)

中文:
定理 isOka_fg
  结论: 是Oka (FG (R := R)) where
  证明: ⟨{1}, by simp⟩
  oka {I a} hsup hcolon := by
    classical
    obtain ⟨_, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hsup
    obtain ⟨_, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hcolon
    rw [submodule_span_eq] at hf
    have H k : exists r : R, exists p in I, r * a + p = f k := by
      apply mem_span_singleton_sup.1
      rw [sup_comm]; rw [← hf]
      exact mem_span_range_self
    choose! r p p_mem_I Hf using H
    refine ⟨image p univ union image (a • i) univ, le_antisymm ?_ (fun y hy => ?_)⟩
    <;> simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, span_union]
    · simp only [sup_le_iff, span_le, range_subset_iff, smul_eq_mul]
      exact ⟨p_mem_I, fun _ => mul_comm a _ ▸ mem_colon_span_singleton.1 (hi ▸ mem_span_range_self)⟩
    · rw [Submodule.mem_sup]
      obtain ⟨s, H⟩ := mem_span_range_iff_exists_fun.1 (hf ▸ Ideal.mem_sup_left hy)
      simp_rw [← Hf] at H
      ring_nf at H
      rw [sum_add_distrib]; rw [← sum_mul]; rw [add_comm] at H
      refine ⟨(∑ k, s k * p k), sum_mem _ (fun _ _ => mul_mem_left _ _ mem_span_range_self),
        (∑ k, s k * r k) * a, ?_, H⟩
      rw [mul_comm]; rw [← smul_eq_mul]; rw [range_smul]; rw [← submodule_span_eq]; rw [Submodule.span_smul]; rw [hi]
exact smul_mem_smul_set mem_colon_span_singleton.2
        (I.add_mem_iff_right <| I.sum_mem (fun _ _ => mul_mem_left _ _ <| p_mem_I _)).1 (H ▸ hy)
-/
theorem isOka_fg : IsOka (FG (R := R)) where
  top := ⟨{1}, by simp⟩
  oka {I a} hsup hcolon := by
    classical
    obtain ⟨_, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hsup
    obtain ⟨_, i, hi⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hcolon
    rw [submodule_span_eq] at hf
    have H k : exists r : R, exists p in I, r * a + p = f k := by
      apply mem_span_singleton_sup.1
      rw [sup_comm]; rw [← hf]
      exact mem_span_range_self
    choose! r p p_mem_I Hf using H
    refine ⟨image p univ union image (a • i) univ, le_antisymm ?_ (fun y hy => ?_)⟩
    <;> simp only [coe_union, coe_image, coe_univ, image_univ, Pi.smul_apply, span_union]
    · simp only [sup_le_iff, span_le, range_subset_iff, smul_eq_mul]
      exact ⟨p_mem_I, fun _ => mul_comm a _ ▸ mem_colon_span_singleton.1 (hi ▸ mem_span_range_self)⟩
    · rw [Submodule.mem_sup]
      obtain ⟨s, H⟩ := mem_span_range_iff_exists_fun.1 (hf ▸ Ideal.mem_sup_left hy)
      simp_rw [← Hf] at H
      ring_nf at H
      rw [sum_add_distrib]; rw [← sum_mul]; rw [add_comm] at H
      refine ⟨(∑ k, s k * p k), sum_mem _ (fun _ _ => mul_mem_left _ _ mem_span_range_self),
        (∑ k, s k * r k) * a, ?_, H⟩
      rw [mul_comm]; rw [← smul_eq_mul]; rw [range_smul]; rw [← submodule_span_eq]; rw [Submodule.span_smul]; rw [hi]
exact smul_mem_smul_set mem_colon_span_singleton.2
        (I.add_mem_iff_right <| I.sum_mem (fun _ _ => mul_mem_left _ _ <| p_mem_I _)).1 (H ▸ hy)

end Ideal

open Ideal

/--
theorem `IsNoetherianRing.of_prime` / 定理 `IsNoetherianRing.of_prime`

English:
theorem IsNoetherianRing.of_prime
  given: (H : forall I : Ideal R, I.IsPrime -> I.FG)
  proof: by
  refine ⟨isOka_fg.forall_of_forall_prime' (fun C hC₁ hC₂ I hI h => ⟨sSup C, ?_, h⟩) H⟩
  obtain ⟨G, hG⟩ := h
  obtain ⟨J, J_mem_C, G_subset_J⟩ : exists J in C, (G : Set R) subseteq J := by
    refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion ⟨I, hI⟩ (fun _ hx => ?_)
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
exact (Submodule.mem_sSup_of_directed ⟨I, hI⟩ hC₂.directedOn).1 hG ▸ subset_span hx
  suffices J_eq_sSup : J = sSup C from J_eq_sSup ▸ J_mem_C
  exact le_antisymm (le_sSup J_mem_C) (hG ▸ Ideal.span_le.2 G_subset_J)

中文:
定理 是Noether环.of_prime
  条件: (H : 对任意 I : 理想 R, I.是素 -> I.FG)
  证明: by
  refine ⟨isOka_fg.forall_of_forall_prime' (fun C hC₁ hC₂ I hI h => ⟨sSup C, ?_, h⟩) H⟩
  obtain ⟨G, hG⟩ := h
  obtain ⟨J, J_mem_C, G_subset_J⟩ : exists J in C, (G : Set R) subseteq J := by
    refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion ⟨I, hI⟩ (fun _ hx => ?_)
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
exact (Submodule.mem_sSup_of_directed ⟨I, hI⟩ hC₂.directedOn).1 hG ▸ subset_span hx
  suffices J_eq_sSup : J = sSup C from J_eq_sSup ▸ J_mem_C
  exact le_antisymm (le_sSup J_mem_C) (hG ▸ Ideal.span_le.2 G_subset_J)

Depends on / 依赖: G_subset_J, J_eq_sSup, J_mem_C, Set.mem_iUnion, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_sSup_of_directed, directedOn, directedOn.exists_mem_subset_of_finset_subset_biUnion, exists_mem_subset_of_finset_subset_biUnion, exists_prop, forall_of_forall_prime, isOka_fg, isOka_fg.forall_of_forall_prime, le_antisymm, le_sSu, mem_coe, mem_iUnion, mem_sSup_of_directed
-/
theorem IsNoetherianRing.of_prime (H : forall I : Ideal R, I.IsPrime -> I.FG) :
    IsNoetherianRing R := by
  refine ⟨isOka_fg.forall_of_forall_prime' (fun C hC₁ hC₂ I hI h => ⟨sSup C, ?_, h⟩) H⟩
  obtain ⟨G, hG⟩ := h
  obtain ⟨J, J_mem_C, G_subset_J⟩ : exists J in C, (G : Set R) subseteq J := by
    refine hC₂.directedOn.exists_mem_subset_of_finset_subset_biUnion ⟨I, hI⟩ (fun _ hx => ?_)
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop]
exact (Submodule.mem_sSup_of_directed ⟨I, hI⟩ hC₂.directedOn).1 hG ▸ subset_span hx
  suffices J_eq_sSup : J = sSup C from J_eq_sSup ▸ J_mem_C
  exact le_antisymm (le_sSup J_mem_C) (hG ▸ Ideal.span_le.2 G_subset_J)

/--
theorem `IsNoetherianRing.of_prime_ne_bot` / 定理 `IsNoetherianRing.of_prime_ne_bot`

English:
theorem IsNoetherianRing.of_prime_ne_bot
  given: (H : forall I : Ideal R, I.IsPrime -> I != ⊥ -> I.FG)
  proof: .of_prime fun I hi => (eq_or_ne I ⊥).elim (· ▸ Submodule.fg_bot) H _ hi

中文:
定理 是Noether环.of_prime_ne_bot
  条件: (H : 对任意 I : 理想 R, I.是素 -> I != ⊥ -> I.FG)
  证明: .of_prime fun I hi => (eq_or_ne I ⊥).elim (· ▸ Submodule.fg_bot) H _ hi

Depends on / 依赖: Submodule, Submodule.fg_bot, eq_or_ne, fg_bot, of_prime
-/
theorem IsNoetherianRing.of_prime_ne_bot (H : forall I : Ideal R, I.IsPrime -> I != ⊥ -> I.FG) :
    IsNoetherianRing R :=
.of_prime fun I hi => (eq_or_ne I ⊥).elim (· ▸ Submodule.fg_bot) H _ hi
