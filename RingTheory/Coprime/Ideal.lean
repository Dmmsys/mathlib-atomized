/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Operations

/-!
# An additional lemma about coprime ideals

This lemma generalises `exists_sum_eq_one_iff_pairwise_coprime` to the case of non-principal ideals.
It is on a separate file due to import requirements.
-/

public section


namespace Ideal

variable {ι R : Type*} [CommSemiring R]

/--
theorem `iSup_iInf_eq_top_iff_pairwise` / 定理 `iSup_iInf_eq_top_iff_pairwise`

English:
theorem iSup_iInf_eq_top_iff_pairwise
  given: {t : Finset ι} (h : t.Nonempty) (I : ι -> Ideal R)
  proof: by
  have : DecidableEq ι := Classical.decEq ι
  rw [eq_top_iff_one]; rw [Submodule.mem_iSup_finset_iff_exists_sum]
  refine h.cons_induction ?_ ?_ <;> clear t h
  · simp only [Finset.sum_singleton, Finset.coe_singleton, Set.pairwise_singleton, iff_true]
    refine fun a => ⟨fun i => if h : i = a th

中文:
定理 iSup_iInf_eq_top_iff_pairwise
  条件: {t : 有限集 ι} (h : t.非空) (I : ι -> 理想 R)
  证明: by
  have : DecidableEq ι := Classical.decEq ι
  rw [eq_top_iff_one]; rw [Submodule.mem_iSup_finset_iff_exists_sum]
  refine h.cons_induction ?_ ?_ <;> clear t h
  · simp only [Finset.sum_singleton, Finset.coe_singleton, Set.pairwise_singleton, iff_true]
    refine fun a => ⟨fun i => if h : i = a th

Depends on / 依赖: Classical, Classical.decEq, DecidableEq, Finset, Finset.coe_cons, Finset.coe_singleton, Finset.sum_singleton, Set.pairwise_insert_o, Set.pairwise_singleton, Std.Symm, Submodule, Submodule.coe_mk, Submodule.mem_iSup_finset_iff_exists_sum, coe_cons, coe_mk, coe_singleton, cons_induction, dif_pos, eq_top_iff_one, h.cons_induction
-/
theorem iSup_iInf_eq_top_iff_pairwise {t : Finset ι} (h : t.Nonempty) (I : ι -> Ideal R) :
    (⨆ i in t, ⨅ (j) (_ : j in t) (_ : j != i), I j) = ⊤ ↔
      (t : Set ι).Pairwise fun i j => I i ⊔ I j = ⊤ := by
  have : DecidableEq ι := Classical.decEq ι
  rw [eq_top_iff_one]; rw [Submodule.mem_iSup_finset_iff_exists_sum]
  refine h.cons_induction ?_ ?_ <;> clear t h
  · simp only [Finset.sum_singleton, Finset.coe_singleton, Set.pairwise_singleton, iff_true]
    refine fun a => ⟨fun i => if h : i = a then ⟨1, ?_⟩ else 0, ?_⟩
    · simp [h]
    · simp only [dif_pos, Submodule.coe_mk]
  intro a t hat h ih
  have : Std.Symm (I · ⊔ I · = ⊤) := { symm i j := sup_comm .. |>.trans }
  rw [Finset.coe_cons]; rw [Set.pairwise_insert_of_symm]
  constructor
  · rintro ⟨μ, hμ⟩
    rw [Finset.sum_cons] at hμ
    refine ⟨ih.mp ⟨Pi.single h.choose ⟨μ a, ?a1⟩ + fun i => ⟨μ i, ?a2⟩, ?a3⟩, fun b hb ab => ?a4⟩
    case a1 =>
      have := Submodule.coe_mem (μ a)
      rw [mem_iInf] at this ⊢
      --for some reason `simp only [mem_iInf]` times out
      intro i
      specialize this i
      rw [mem_iInf]; rw [mem_iInf] at this ⊢
      intro hi _
      apply this (Finset.subset_cons _ hi)
      rintro rfl
      exact hat hi
    case a2 =>
      have := Submodule.coe_mem (μ i)
      simp only [mem_iInf] at this ⊢
      intro j hj ij
      exact this _ (Finset.subset_cons _ hj) ij
    case a3 =>
      rw [← @if_pos _ _ h.choose_spec R (μ a) 0]; rw [← Finset.sum_pi_single']; rw [← Finset.sum_add_distrib]
        at hμ
      convert! hμ
      rename_i i _
      rw [Pi.add_apply]; rw [Submodule.coe_add]; rw [Submodule.coe_mk]
      by_cases hi : i = h.choose
      · rw [hi, Pi.single_eq_same, Pi.single_eq_same, Submodule.coe_mk]
      · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi, Submodule.coe_zero]
    case a4 =>
      rw [eq_top_iff_one]; rw [Submodule.mem_sup]
      rw [add_comm] at hμ
      refine ⟨_, ?_, _, ?_, hμ⟩
      · refine sum_mem _ fun x hx => ?_
        have := Submodule.coe_mem (μ x)
        simp only [mem_iInf] at this
        apply this _ (Finset.mem_cons_self _ _)
        rintro rfl
        exact hat hx
      · have := Submodule.coe_mem (μ a)
        simp only [mem_iInf] at this
        exact this _ (Finset.subset_cons _ hb) ab.symm
  · rintro ⟨hs, Hb⟩
    obtain ⟨μ, hμ⟩ := ih.mpr hs
    have := sup_iInf_eq_top fun b hb => Hb b hb (ne_of_mem_of_not_mem hb hat).symm
    rw [eq_top_iff_one]; rw [Submodule.mem_sup] at this
    obtain ⟨u, hu, v, hv, huv⟩ := this
    refine ⟨fun i => if hi : i = a then ⟨v, ?_⟩ else ⟨u * μ i, ?_⟩, ?_⟩
    · simp only [mem_iInf] at hv ⊢
      intro j hj ij
      rw [Finset.mem_cons]; rw [← hi] at hj
      exact hv _ (hj.resolve_left ij)
    · have := Submodule.coe_mem (μ i)
      simp only [mem_iInf] at this ⊢
      intro j hj ij
      rcases Finset.mem_cons.mp hj with (rfl | hj)
      · exact mul_mem_right _ _ hu
      · exact mul_mem_left _ _ (this _ hj ij)
    · dsimp only
      rw [Finset.sum_cons]; rw [dif_pos rfl]; rw [add_comm]
      rw [← mul_one u] at huv
      rw [← huv]; rw [← hμ]; rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      rw [dif_neg]
      rintro rfl
      exact hat hj

end Ideal
