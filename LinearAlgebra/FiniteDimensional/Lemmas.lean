/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Tactic.IntervalCases

/-!
# Finite-dimensional vector spaces

This file contains some further development of finite-dimensional vector spaces, their dimensions,
and linear maps on such spaces.

Definitions are in `Mathlib/LinearAlgebra/FiniteDimensional/Defs.lean`
and results that require fewer imports are in `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`.
-/

@[expose] public section

assert_not_exists Monoid.exponent Module.IsTorsion


universe u v v'

open Cardinal Submodule Module Function

variable {K : Type u} {V : Type v}

namespace Submodule

open IsNoetherian Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `finrank_lt` / 定理 `finrank_lt`

English:
theorem finrank_lt
  given: [FiniteDimensional K V] {s : Submodule K V} (h : s != ⊤)
  proof: by
  rw [← s.finrank_quotient_add_finrank]; rw [add_comm]
  rw [← Quotient.nontrivial_iff] at h
  exact Nat.lt_add_of_pos_right finrank_pos

中文:
定理 finrank_lt
  条件: [有限维 K V] {s : 子模 K V} (h : s != ⊤)
  证明: by
  rw [← s.finrank_quotient_add_finrank]; rw [add_comm]
  rw [← Quotient.nontrivial_iff] at h
  exact Nat.lt_add_of_pos_right finrank_pos

Depends on / 依赖: Nat.lt_add_of_pos_right, Quotient, Quotient.nontrivial_iff, add_comm, finrank_pos, finrank_quotient_add_finrank, lt_add_of_pos_right, nontrivial_iff, s.finrank_quotient_add_finrank
-/
theorem finrank_lt [FiniteDimensional K V] {s : Submodule K V} (h : s != ⊤) :
    finrank K s < finrank K V := by
  rw [← s.finrank_quotient_add_finrank]; rw [add_comm]
  rw [← Quotient.nontrivial_iff] at h
  exact Nat.lt_add_of_pos_right finrank_pos

/--
theorem `finrank_sup_add_finrank_inf_eq` / 定理 `finrank_sup_add_finrank_inf_eq`

English:
theorem finrank_sup_add_finrank_inf_eq
  statement: (s t : Submodule K V) [FiniteDimensional K s]
  proof: by
  have key : Module.rank K ↑(s ⊔ t) + Module.rank K ↑(s ⊓ t) = Module.rank K s + Module.rank K t :=
    rank_sup_add_rank_inf_eq s t
  repeat rw [← finrank_eq_rank] at key
  norm_cast at key

中文:
定理 finrank_sup_add_finrank_inf_eq
  结论: (s t : 子模 K V) [有限维 K s]
  证明: by
  have key : Module.rank K ↑(s ⊔ t) + Module.rank K ↑(s ⊓ t) = Module.rank K s + Module.rank K t :=
    rank_sup_add_rank_inf_eq s t
  repeat rw [← finrank_eq_rank] at key
  norm_cast at key

Depends on / 依赖: Module, Module.rank, finrank_eq_rank, rank_sup_add_rank_inf_eq, repeat
-/
theorem finrank_sup_add_finrank_inf_eq (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] :
    finrank K ↑(s ⊔ t) + finrank K ↑(s ⊓ t) = finrank K ↑s + finrank K ↑t := by
  have key : Module.rank K ↑(s ⊔ t) + Module.rank K ↑(s ⊓ t) = Module.rank K s + Module.rank K t :=
    rank_sup_add_rank_inf_eq s t
  repeat rw [← finrank_eq_rank] at key
  norm_cast at key

/--
theorem `finrank_add_le_finrank_add_finrank` / 定理 `finrank_add_le_finrank_add_finrank`

English:
theorem finrank_add_le_finrank_add_finrank
  statement: (s t : Submodule K V) [FiniteDimensional K s]
  proof: by
  rw [← finrank_sup_add_finrank_inf_eq]
  exact self_le_add_right _ _

中文:
定理 finrank_add_le_finrank_add_finrank
  结论: (s t : 子模 K V) [有限维 K s]
  证明: by
  rw [← finrank_sup_add_finrank_inf_eq]
  exact self_le_add_right _ _

Depends on / 依赖: finrank_sup_add_finrank_inf_eq, self_le_add_right
-/
theorem finrank_add_le_finrank_add_finrank (s t : Submodule K V) [FiniteDimensional K s]
    [FiniteDimensional K t] : finrank K (s ⊔ t : Submodule K V) <= finrank K s + finrank K t := by
  rw [← finrank_sup_add_finrank_inf_eq]
  exact self_le_add_right _ _

/--
theorem `finrank_add_finrank_le_of_disjoint` / 定理 `finrank_add_finrank_le_of_disjoint`

English:
theorem finrank_add_finrank_le_of_disjoint
  statement: [FiniteDimensional K V]
  proof: by
  rw [← Submodule.finrank_sup_add_finrank_inf_eq s t]; rw [hdisjoint.eq_bot]; rw [finrank_bot]; rw [add_zero]
  exact Submodule.finrank_le _

中文:
定理 finrank_add_finrank_le_of_disjoint
  结论: [有限维 K V]
  证明: by
  rw [← Submodule.finrank_sup_add_finrank_inf_eq s t]; rw [hdisjoint.eq_bot]; rw [finrank_bot]; rw [add_zero]
  exact Submodule.finrank_le _

Depends on / 依赖: Submodule, Submodule.finrank_le, Submodule.finrank_sup_add_finrank_inf_eq, add_zero, eq_bot, finrank_bot, finrank_le, finrank_sup_add_finrank_inf_eq, hdisjoint, hdisjoint.eq_bot
-/
theorem finrank_add_finrank_le_of_disjoint [FiniteDimensional K V]
    {s t : Submodule K V} (hdisjoint : Disjoint s t) :
    finrank K s + finrank K t <= finrank K V := by
  rw [← Submodule.finrank_sup_add_finrank_inf_eq s t]; rw [hdisjoint.eq_bot]; rw [finrank_bot]; rw [add_zero]
  exact Submodule.finrank_le _

/--
theorem `eq_top_of_disjoint` / 定理 `eq_top_of_disjoint`

English:
theorem eq_top_of_disjoint
  statement: [FiniteDimensional K V] (s t : Submodule K V)
  proof: by
  have h_finrank_inf : finrank K ↑(s ⊓ t) = 0 := by
    rw [disjoint_iff_inf_le]; rw [le_bot_iff] at hdisjoint
    rw [hdisjoint]; rw [finrank_bot]
  apply eq_top_of_finrank_eq
  replace hdim : finrank K V = finrank K s + finrank K t :=
    le_antisymm hdim (finrank_add_finrank_le_of_disjoint hdi

中文:
定理 eq_top_of_disjoint
  结论: [有限维 K V] (s t : 子模 K V)
  证明: by
  have h_finrank_inf : finrank K ↑(s ⊓ t) = 0 := by
    rw [disjoint_iff_inf_le]; rw [le_bot_iff] at hdisjoint
    rw [hdisjoint]; rw [finrank_bot]
  apply eq_top_of_finrank_eq
  replace hdim : finrank K V = finrank K s + finrank K t :=
    le_antisymm hdim (finrank_add_finrank_le_of_disjoint hdi

Depends on / 依赖: add_zero, convert, disjoint_iff_inf_le, eq_top_of_finrank_eq, finrank, finrank_add_finrank_le_of_disjoint, finrank_bot, finrank_sup_add_finrank_inf_eq, h_finrank_inf, hdisjoint, le_antisymm, le_bot_iff, replace, s.finrank_sup_add_finrank_inf_eq
-/
theorem eq_top_of_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K V <= finrank K s + finrank K t) (hdisjoint : Disjoint s t) : s ⊔ t = ⊤ := by
  have h_finrank_inf : finrank K ↑(s ⊓ t) = 0 := by
    rw [disjoint_iff_inf_le]; rw [le_bot_iff] at hdisjoint
    rw [hdisjoint]; rw [finrank_bot]
  apply eq_top_of_finrank_eq
  replace hdim : finrank K V = finrank K s + finrank K t :=
    le_antisymm hdim (finrank_add_finrank_le_of_disjoint hdisjoint)
  rw [hdim]
  convert! s.finrank_sup_add_finrank_inf_eq t
  rw [h_finrank_inf]; rw [add_zero]

/--
theorem `isCompl_iff_disjoint` / 定理 `isCompl_iff_disjoint`

English:
theorem isCompl_iff_disjoint
  statement: [FiniteDimensional K V] (s t : Submodule K V)
  proof: ⟨fun h => h.1, fun h => ⟨h, codisjoint_iff.mpr eq_top_of_disjoint s t hdim h⟩⟩

中文:
定理 isCompl_iff_disjoint
  结论: [有限维 K V] (s t : 子模 K V)
  证明: ⟨fun h => h.1, fun h => ⟨h, codisjoint_iff.mpr eq_top_of_disjoint s t hdim h⟩⟩

Depends on / 依赖: codisjoint_iff, codisjoint_iff.mpr, eq_top_of_disjoint
-/
theorem isCompl_iff_disjoint [FiniteDimensional K V] (s t : Submodule K V)
    (hdim : finrank K V <= finrank K s + finrank K t) :
    IsCompl s t ↔ Disjoint s t :=
⟨fun h => h.1, fun h => ⟨h, codisjoint_iff.mpr eq_top_of_disjoint s t hdim h⟩⟩

/--
theorem `sup_span_singleton_eq_top_iff` / 定理 `sup_span_singleton_eq_top_iff`

English:
theorem sup_span_singleton_eq_top_iff
  given: [Module.Finite K V] {W : Submodule K V} {v : V} (hv : v ∉ W)
  proof: by
  refine ⟨fun hW => ?_, fun hW => ?_⟩
  · suffices W ⊓ span K {v} = ⊥ by
      have hv₀ : v != 0 := by aesop
      have aux := finrank_sup_add_finrank_inf_eq W (span K {v})
      rw [hW]; rw [finrank_span_singleton hv₀]; rw [this]; rw [finrank_bot]; rw [finrank_top]; rw [← finrank_quotient_add_fi

中文:
定理 sup_span_singleton_eq_top_iff
  条件: [模.有限 K V] {W : 子模 K V} {v : V} (hv : v ∉ W)
  证明: by
  refine ⟨fun hW => ?_, fun hW => ?_⟩
  · suffices W ⊓ span K {v} = ⊥ by
      have hv₀ : v != 0 := by aesop
      have aux := finrank_sup_add_finrank_inf_eq W (span K {v})
      rw [hW]; rw [finrank_span_singleton hv₀]; rw [this]; rw [finrank_bot]; rw [finrank_top]; rw [← finrank_quotient_add_fi

Depends on / 依赖: Submodu, Submodule, Submodule.eq_bot_iff, eq_bot_iff, eq_or_ne, finrank_bot, finrank_quotient_add_finrank, finrank_span_singleton, finrank_sup_add_finrank_inf_eq, finrank_top, mem_span_singleton
-/
theorem sup_span_singleton_eq_top_iff [Module.Finite K V] {W : Submodule K V} {v : V} (hv : v ∉ W) :
    W ⊔ span K {v} = ⊤ ↔ finrank K (V ⧸ W) = 1 := by
  refine ⟨fun hW => ?_, fun hW => ?_⟩
  · suffices W ⊓ span K {v} = ⊥ by
      have hv₀ : v != 0 := by aesop
      have aux := finrank_sup_add_finrank_inf_eq W (span K {v})
      rw [hW]; rw [finrank_span_singleton hv₀]; rw [this]; rw [finrank_bot]; rw [finrank_top]; rw [← finrank_quotient_add_finrank W] at aux
      lia
    refine (Submodule.eq_bot_iff _).mpr fun w hw => ?_
    obtain ⟨ht, t, rfl⟩ : w in W ∧ exists t : K, t • v = w := by simpa [mem_span_singleton] using hw
    rcases eq_or_ne t 0 with rfl | ht₀; · simp
    rw [Submodule.smul_mem_iff _ ht₀] at ht
    contradiction
  · apply Submodule.eq_top_of_disjoint
    · rw [← W.finrank_quotient_add_finrank, add_comm, add_le_add_iff_left, hW]
      aesop
    · exact Submodule.disjoint_span_singleton_of_notMem hv

/--
theorem `finrank_sup_span_singleton` / 定理 `finrank_sup_span_singleton`

English:
theorem finrank_sup_span_singleton
  given: [Module.Finite K V] {p : Submodule K V} {v : V} (hv : v ∉ p)
  proof: by
  rw [← Nat.add_left_inj]; rw [finrank_sup_add_finrank_inf_eq]; rw [add_assoc]; rw [Nat.add_left_cancel_iff]; rw [finrank_span_singleton (by aesop)]; rw [Nat.left_eq_add]; rw [Submodule.finrank_eq_zero]; rw [eq_bot_iff]
  intro x
  simp only [mem_inf, mem_span_singleton]
  rintro ⟨hx, ⟨a, hx'⟩⟩
 

中文:
定理 finrank_sup_span_singleton
  条件: [模.有限 K V] {p : 子模 K V} {v : V} (hv : v ∉ p)
  证明: by
  rw [← Nat.add_left_inj]; rw [finrank_sup_add_finrank_inf_eq]; rw [add_assoc]; rw [Nat.add_left_cancel_iff]; rw [finrank_span_singleton (by aesop)]; rw [Nat.left_eq_add]; rw [Submodule.finrank_eq_zero]; rw [eq_bot_iff]
  intro x
  simp only [mem_inf, mem_span_singleton]
  rintro ⟨hx, ⟨a, hx'⟩⟩
 

Depends on / 依赖: Nat.add_left_cancel_iff, Nat.add_left_inj, Nat.left_eq_add, Submodule, Submodule.finrank_eq_zero, add_assoc, add_left_cancel_iff, add_left_inj, contrapose, eq_bot_iff, finrank_eq_zero, finrank_span_singleton, finrank_sup_add_finrank_inf_eq, left_eq_add, mem_inf, mem_span_singleton, smul_mem_iff
-/
theorem finrank_sup_span_singleton [Module.Finite K V] {p : Submodule K V} {v : V} (hv : v ∉ p) :
    finrank K (p ⊔ Submodule.span K {v} : Submodule K V) = finrank K p + 1 := by
  rw [← Nat.add_left_inj]; rw [finrank_sup_add_finrank_inf_eq]; rw [add_assoc]; rw [Nat.add_left_cancel_iff]; rw [finrank_span_singleton (by aesop)]; rw [Nat.left_eq_add]; rw [Submodule.finrank_eq_zero]; rw [eq_bot_iff]
  intro x
  simp only [mem_inf, mem_span_singleton]
  rintro ⟨hx, ⟨a, hx'⟩⟩
  rw [← hx'] at hx
  suffices a = 0 by simp [← hx', this]
  contrapose hv
  simpa [smul_mem_iff p hv] using hx

/--
theorem `eq_top_iff_finrank_eq` / 定理 `eq_top_iff_finrank_eq`

English:
theorem eq_top_iff_finrank_eq
  given: [Module.Finite K V] {W : Submodule K V}
  proof: by
  refine ⟨fun h => by rw [h, finrank_top], fun h => ?_⟩
  apply eq_of_le_of_finrank_eq le_top
  rw [finrank_top]; rw [h]

中文:
定理 eq_top_iff_finrank_eq
  条件: [模.有限 K V] {W : 子模 K V}
  证明: by
  refine ⟨fun h => by rw [h, finrank_top], fun h => ?_⟩
  apply eq_of_le_of_finrank_eq le_top
  rw [finrank_top]; rw [h]

Depends on / 依赖: eq_of_le_of_finrank_eq, finrank_top, le_top
-/
theorem eq_top_iff_finrank_eq [Module.Finite K V] {W : Submodule K V} :
    W = ⊤ ↔ finrank K W = finrank K V := by
  refine ⟨fun h => by rw [h, finrank_top], fun h => ?_⟩
  apply eq_of_le_of_finrank_eq le_top
  rw [finrank_top]; rw [h]

end DivisionRing

end Submodule

namespace FiniteDimensional

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

variable [FiniteDimensional K V] [FiniteDimensional K V₂]

/--
Definition of `LinearEquiv.quotEquivOfEquiv` / `LinearEquiv.quotEquivOfEquiv` 的定义

English:
definition LinearEquiv.quotEquivOfEquiv
  signature: {p : Subspace K V} {q : Subspace K V₂}
  body: LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ _ (finrank K p)]; rw [Submodule.finrank_quotient_add_finrank]; rw [LinearEquiv.finrank_eq f₁]; rw [Submodule.finrank_quotient_add_finrank]; rw [LinearEquiv.finrank_eq f₂])

中文:
定义 线性等价.quotEquivOfEquiv
  签名: {p : 子空间 K V} {q : 子空间 K V₂}
  定义体: LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ _ (finrank K p)]; rw [Submodule.finrank_quotient_add_finrank]; rw [LinearEquiv.finrank_eq f₁]; rw [Submodule.finrank_quotient_add_finrank]; rw [LinearEquiv.finrank_eq f₂])

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_eq, LinearEquiv.ofFinrankEq, Submodule, Submodule.finrank_quotient_add_finrank, add_right_cancel_iff, finrank, finrank_eq, finrank_quotient_add_finrank, ofFinrankEq
-/
noncomputable def LinearEquiv.quotEquivOfEquiv {p : Subspace K V} {q : Subspace K V₂}
    (f₁ : p ≃ₗ[K] q) (f₂ : V ≃ₗ[K] V₂) : (V ⧸ p) ≃ₗ[K] V₂ ⧸ q :=
  LinearEquiv.ofFinrankEq _ _
    (by
      rw [← @add_right_cancel_iff _ _ _ (finrank K p)]; rw [Submodule.finrank_quotient_add_finrank]; rw [LinearEquiv.finrank_eq f₁]; rw [Submodule.finrank_quotient_add_finrank]; rw [LinearEquiv.finrank_eq f₂])

-- TODO: generalize to the case where one of `p` and `q` is finite-dimensional.
/--
Definition of `LinearEquiv.quotEquivOfQuotEquiv` / `LinearEquiv.quotEquivOfQuotEquiv` 的定义

English:
definition LinearEquiv.quotEquivOfQuotEquiv
  signature: {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q)
  body: LinearEquiv.ofFinrankEq _ _ by
    rw [← add_right_cancel_iff]; rw [Submodule.finrank_quotient_add_finrank]; rw [← LinearEquiv.finrank_eq f]; rw [add_comm]; rw [Submodule.finrank_quotient_add_finrank]

中文:
定义 线性等价.quotEquivOfQuotEquiv
  签名: {p q : 子空间 K V} (f : (V ⧸ p) ≃ₗ[K] q)
  定义体: LinearEquiv.ofFinrankEq _ _ by
    rw [← add_right_cancel_iff]; rw [Submodule.finrank_quotient_add_finrank]; rw [← LinearEquiv.finrank_eq f]; rw [add_comm]; rw [Submodule.finrank_quotient_add_finrank]

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_eq, LinearEquiv.ofFinrankEq, Submodule, Submodule.finrank_quotient_add_finrank, add_comm, add_right_cancel_iff, finrank_eq, finrank_quotient_add_finrank, ofFinrankEq
-/
noncomputable def LinearEquiv.quotEquivOfQuotEquiv {p q : Subspace K V} (f : (V ⧸ p) ≃ₗ[K] q) :
    (V ⧸ q) ≃ₗ[K] p :=
LinearEquiv.ofFinrankEq _ _ by
    rw [← add_right_cancel_iff]; rw [Submodule.finrank_quotient_add_finrank]; rw [← LinearEquiv.finrank_eq f]; rw [add_comm]; rw [Submodule.finrank_quotient_add_finrank]

end DivisionRing

end FiniteDimensional

namespace LinearMap

open Module

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/--
theorem `finrank_range_add_finrank_ker` / 定理 `finrank_range_add_finrank_ker`

English:
theorem finrank_range_add_finrank_ker
  given: [FiniteDimensional K V] (f : V ->ₗ[K] V₂)
  proof: by
  rw [← f.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

中文:
定理 finrank_range_add_finrank_ker
  条件: [有限维 K V] (f : V ->ₗ[K] V₂)
  证明: by
  rw [← f.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

Depends on / 依赖: Submodule, Submodule.finrank_quotient_add_finrank, f.quotKerEquivRange.finrank_eq, finrank_eq, finrank_quotient_add_finrank, quotKerEquivRange
-/
theorem finrank_range_add_finrank_ker [FiniteDimensional K V] (f : V ->ₗ[K] V₂) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V := by
  rw [← f.quotKerEquivRange.finrank_eq]
  exact Submodule.finrank_quotient_add_finrank _

/--
lemma `ker_ne_bot_of_finrank_lt` / 引理 `ker_ne_bot_of_finrank_lt`

English:
lemma ker_ne_bot_of_finrank_lt
  statement: [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V ->ₗ[K] V₂}
  proof: by
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ : finrank K (LinearMap.range f) <= finrank K V₂ := (LinearMap.range f).finrank_le
  suffices 0 < finrank K (LinearMap.ker f) from Submodule.one_le_finrank_iff.mp this
  lia

中文:
引理 ker_ne_bot_of_finrank_lt
  结论: [有限维 K V] [有限维 K V₂] {f : V ->ₗ[K] V₂}
  证明: by
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ : finrank K (LinearMap.range f) <= finrank K V₂ := (LinearMap.range f).finrank_le
  suffices 0 < finrank K (LinearMap.ker f) from Submodule.one_le_finrank_iff.mp this
  lia

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.range, Submodule, Submodule.one_le_finrank_iff.mp, f.finrank_range_add_finrank_ker, finrank, finrank_le, finrank_range_add_finrank_ker, one_le_finrank_iff
-/
lemma ker_ne_bot_of_finrank_lt [FiniteDimensional K V] [FiniteDimensional K V₂] {f : V ->ₗ[K] V₂}
    (h : finrank K V₂ < finrank K V) :
    LinearMap.ker f != ⊥ := by
  have h₁ := f.finrank_range_add_finrank_ker
  have h₂ : finrank K (LinearMap.range f) <= finrank K V₂ := (LinearMap.range f).finrank_le
  suffices 0 < finrank K (LinearMap.ker f) from Submodule.one_le_finrank_iff.mp this
  lia

end DivisionRing

end LinearMap

open Module

namespace LinearMap

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/--
theorem `injective_iff_surjective_of_finrank_eq_finrank` / 定理 `injective_iff_surjective_of_finrank_eq_finrank`

English:
theorem injective_iff_surjective_of_finrank_eq_finrank
  statement: [FiniteDimensional K V]
  proof: by
  have := finrank_range_add_finrank_ker f
  rw [← ker_eq_bot]; rw [← range_eq_top]; refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, finrank_bot, add_zero, H] at this
    exact eq_top_of_finrank_eq this
  · rw [h, finrank_top, H] at this
    exact Submodule.finrank_eq_zero.1 (add_right_injective _ th

中文:
定理 injective_iff_surjective_of_finrank_eq_finrank
  结论: [有限维 K V]
  证明: by
  have := finrank_range_add_finrank_ker f
  rw [← ker_eq_bot]; rw [← range_eq_top]; refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, finrank_bot, add_zero, H] at this
    exact eq_top_of_finrank_eq this
  · rw [h, finrank_top, H] at this
    exact Submodule.finrank_eq_zero.1 (add_right_injective _ th

Depends on / 依赖: Submodule, Submodule.finrank_eq_zero, add_right_injective, add_zero, eq_top_of_finrank_eq, finrank_bot, finrank_eq_zero, finrank_range_add_finrank_ker, finrank_top, ker_eq_bot, range_eq_top
-/
theorem injective_iff_surjective_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V ->ₗ[K] V₂} :
    Function.Injective f ↔ Function.Surjective f := by
  have := finrank_range_add_finrank_ker f
  rw [← ker_eq_bot]; rw [← range_eq_top]; refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, finrank_bot, add_zero, H] at this
    exact eq_top_of_finrank_eq this
  · rw [h, finrank_top, H] at this
    exact Submodule.finrank_eq_zero.1 (add_right_injective _ this)

/--
theorem `ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank` / 定理 `ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank`

English:
theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
  statement: [FiniteDimensional K V]
  proof: by
  rw [range_eq_top]; rw [ker_eq_bot]; rw [injective_iff_surjective_of_finrank_eq_finrank H]

中文:
定理 ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
  结论: [有限维 K V]
  证明: by
  rw [range_eq_top]; rw [ker_eq_bot]; rw [injective_iff_surjective_of_finrank_eq_finrank H]

Depends on / 依赖: injective_iff_surjective_of_finrank_eq_finrank, ker_eq_bot, range_eq_top
-/
theorem ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank [FiniteDimensional K V]
    [FiniteDimensional K V₂] (H : finrank K V = finrank K V₂) {f : V ->ₗ[K] V₂} :
    LinearMap.ker f = ⊥ ↔ LinearMap.range f = ⊤ := by
  rw [range_eq_top]; rw [ker_eq_bot]; rw [injective_iff_surjective_of_finrank_eq_finrank H]

/--
Definition of `linearEquivOfInjective` / `linearEquivOfInjective` 的定义

English:
definition linearEquivOfInjective
  signature: [FiniteDimensional K V] [FiniteDimensional K V₂]
  body: LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩

@[simp]

中文:
定义 linearEquivOfInjective
  签名: [有限维 K V] [有限维 K V₂]
  定义体: LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, LinearMap, LinearMap.injective_iff_surjective_of_finrank_eq_finrank, injective_iff_surjective_of_finrank_eq_finrank, ofBijective
-/
noncomputable def linearEquivOfInjective [FiniteDimensional K V] [FiniteDimensional K V₂]
    (f : V ->ₗ[K] V₂) (hf : Injective f) (hdim : finrank K V = finrank K V₂) : V ≃ₗ[K] V₂ :=
  LinearEquiv.ofBijective f
    ⟨hf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf⟩

@[simp]
/--
theorem `linearEquivOfInjective_apply` / 定理 `linearEquivOfInjective_apply`

English:
theorem linearEquivOfInjective_apply
  statement: [FiniteDimensional K V] [FiniteDimensional K V₂]
  proof: rfl

中文:
定理 linearEquivOfInjective_apply
  结论: [有限维 K V] [有限维 K V₂]
  证明: rfl
-/
theorem linearEquivOfInjective_apply [FiniteDimensional K V] [FiniteDimensional K V₂]
    {f : V ->ₗ[K] V₂} (hf : Injective f) (hdim : finrank K V = finrank K V₂) (x : V) :
    f.linearEquivOfInjective hf hdim x = f x :=
  rfl

end LinearMap

namespace Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] {V₂ : Type v'} [AddCommGroup V₂]
  [Module K V₂]

/--
theorem `finrank_lt_finrank_of_lt` / 定理 `finrank_lt_finrank_of_lt`

English:
theorem finrank_lt_finrank_of_lt
  given: {s t : Submodule K V} [FiniteDimensional K t] (hst : s < t)
  proof: (comapSubtypeEquivOfLe hst.le).finrank_eq.symm.trans_lt
finrank_lt by simp [not_le_of_gt hst]

中文:
定理 finrank_lt_finrank_of_lt
  条件: {s t : 子模 K V} [有限维 K t] (hst : s < t)
  证明: (comapSubtypeEquivOfLe hst.le).finrank_eq.symm.trans_lt
finrank_lt by simp [not_le_of_gt hst]

Depends on / 依赖: comapSubtypeEquivOfLe, finrank_eq, finrank_eq.symm.trans_lt, finrank_lt, hst.le, not_le_of_gt, trans_lt
-/
theorem finrank_lt_finrank_of_lt {s t : Submodule K V} [FiniteDimensional K t] (hst : s < t) :
    finrank K s < finrank K t :=
(comapSubtypeEquivOfLe hst.le).finrank_eq.symm.trans_lt
finrank_lt by simp [not_le_of_gt hst]

/--
theorem `finrank_strictMono` / 定理 `finrank_strictMono`

English:
theorem finrank_strictMono
  given: [FiniteDimensional K V]
  proof: fun _ _ => finrank_lt_finrank_of_lt

中文:
定理 finrank_strictMono
  条件: [有限维 K V]
  证明: fun _ _ => finrank_lt_finrank_of_lt

Depends on / 依赖: finrank_lt_finrank_of_lt
-/
theorem finrank_strictMono [FiniteDimensional K V] :
    StrictMono fun s : Submodule K V => finrank K s := fun _ _ => finrank_lt_finrank_of_lt

/--
theorem `finrank_add_eq_of_isCompl` / 定理 `finrank_add_eq_of_isCompl`

English:
theorem finrank_add_eq_of_isCompl
  given: [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W)
  proof: by
  rw [← finrank_sup_add_finrank_inf_eq]; rw [h.codisjoint.eq_top]; rw [h.disjoint.eq_bot]; rw [finrank_bot]; rw [add_zero]
  exact finrank_top _ _

中文:
定理 finrank_add_eq_of_isCompl
  条件: [有限维 K V] {U W : 子模 K V} (h : 是补集 U W)
  证明: by
  rw [← finrank_sup_add_finrank_inf_eq]; rw [h.codisjoint.eq_top]; rw [h.disjoint.eq_bot]; rw [finrank_bot]; rw [add_zero]
  exact finrank_top _ _

Depends on / 依赖: add_zero, codisjoint, disjoint, eq_bot, eq_top, finrank_bot, finrank_sup_add_finrank_inf_eq, finrank_top, h.codisjoint.eq_top, h.disjoint.eq_bot
-/
theorem finrank_add_eq_of_isCompl [FiniteDimensional K V] {U W : Submodule K V} (h : IsCompl U W) :
    finrank K U + finrank K W = finrank K V := by
  rw [← finrank_sup_add_finrank_inf_eq]; rw [h.codisjoint.eq_top]; rw [h.disjoint.eq_bot]; rw [finrank_bot]; rw [add_zero]
  exact finrank_top _ _

end DivisionRing

end Submodule

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V]

section Basis
variable {ι : Type*} [Fintype ι]

/--
theorem `LinearIndependent.span_eq_top_of_card_eq_finrank'` / 定理 `LinearIndependent.span_eq_top_of_card_eq_finrank'`

English:
theorem LinearIndependent.span_eq_top_of_card_eq_finrank'
  statement: [FiniteDimensional K V] {b : ι -> V}
  proof: by
  by_contra ne_top
  rw [← finrank_span_eq_card lin_ind] at card_eq
  exact ne_of_lt (Submodule.finrank_lt ne_top) card_eq

中文:
定理 LinearIndependent.span_eq_top_of_card_eq_finrank'
  结论: [有限维 K V] {b : ι -> V}
  证明: by
  by_contra ne_top
  rw [← finrank_span_eq_card lin_ind] at card_eq
  exact ne_of_lt (Submodule.finrank_lt ne_top) card_eq

Depends on / 依赖: Submodule, Submodule.finrank_lt, card_eq, finrank_lt, finrank_span_eq_card, lin_ind, ne_of_lt, ne_top
-/
theorem LinearIndependent.span_eq_top_of_card_eq_finrank' [FiniteDimensional K V] {b : ι -> V}
    (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    span K (Set.range b) = ⊤ := by
  by_contra ne_top
  rw [← finrank_span_eq_card lin_ind] at card_eq
  exact ne_of_lt (Submodule.finrank_lt ne_top) card_eq

/--
theorem `LinearIndependent.span_eq_top_of_card_eq_finrank` / 定理 `LinearIndependent.span_eq_top_of_card_eq_finrank`

English:
theorem LinearIndependent.span_eq_top_of_card_eq_finrank
  statement: [Nonempty ι]
  proof: have : FiniteDimensional K V := .of_finrank_pos card_eq ▸ Fintype.card_pos
  lin_ind.span_eq_top_of_card_eq_finrank' card_eq

中文:
定理 LinearIndependent.span_eq_top_of_card_eq_finrank
  结论: [非空 ι]
  证明: have : FiniteDimensional K V := .of_finrank_pos card_eq ▸ Fintype.card_pos
  lin_ind.span_eq_top_of_card_eq_finrank' card_eq

Depends on / 依赖: FiniteDimensional, Fintype, Fintype.card_pos, card_eq, card_pos, lin_ind, lin_ind.span_eq_top_of_card_eq_finrank, of_finrank_pos, span_eq_top_of_card_eq_finrank
-/
theorem LinearIndependent.span_eq_top_of_card_eq_finrank [Nonempty ι]
    {b : ι -> V} (lin_ind : LinearIndependent K b)
    (card_eq : Fintype.card ι = finrank K V) : span K (Set.range b) = ⊤ :=
have : FiniteDimensional K V := .of_finrank_pos card_eq ▸ Fintype.card_pos
  lin_ind.span_eq_top_of_card_eq_finrank' card_eq

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
/--
Definition of `basisOfLinearIndependentOfCardEqFinrank'` / `basisOfLinearIndependentOfCardEqFinrank'` 的定义

English:
definition basisOfLinearIndependentOfCardEqFinrank'
  body: .mk hb (hb.span_eq_top_of_card_eq_finrank' hι).ge

@[simp]

中文:
定义 basisOfLinearIndependentOfCardEqFinrank'
  定义体: .mk hb (hb.span_eq_top_of_card_eq_finrank' hι).ge

@[simp]

Depends on / 依赖: hb.span_eq_top_of_card_eq_finrank, span_eq_top_of_card_eq_finrank
-/
noncomputable def basisOfLinearIndependentOfCardEqFinrank'
    [FiniteDimensional K V] (b : ι -> V) (hb : LinearIndependent K b)
    (hι : Fintype.card ι = finrank K V) : Basis ι K V :=
  .mk hb (hb.span_eq_top_of_card_eq_finrank' hι).ge

@[simp]
/--
lemma `coe_basisOfLinearIndependentOfCardEqFinrank'` / 引理 `coe_basisOfLinearIndependentOfCardEqFinrank'`

English:
lemma coe_basisOfLinearIndependentOfCardEqFinrank'
  given: [FiniteDimensional K V] (b : ι -> V) (hb hι)
  proof: Basis.coe_mk ..

中文:
引理 coe_basisOfLinearIndependentOfCardEqFinrank'
  条件: [有限维 K V] (b : ι -> V) (hb hι)
  证明: Basis.coe_mk ..

Depends on / 依赖: Basis.coe_mk, coe_mk
-/
lemma coe_basisOfLinearIndependentOfCardEqFinrank' [FiniteDimensional K V] (b : ι -> V) (hb hι) :
    ⇑(basisOfLinearIndependentOfCardEqFinrank' (K := K) b hb hι) = b := Basis.coe_mk ..

/-- A linear independent family of `finrank K V` vectors forms a basis. -/
@[simps! repr_apply]
/--
Definition of `basisOfLinearIndependentOfCardEqFinrank` / `basisOfLinearIndependentOfCardEqFinrank` 的定义

English:
definition basisOfLinearIndependentOfCardEqFinrank
  signature: [Nonempty ι]
  body: Basis.mk lin_ind (lin_ind.span_eq_top_of_card_eq_finrank card_eq).ge

@[simp]

中文:
定义 basisOfLinearIndependentOfCardEqFinrank
  签名: [非空 ι]
  定义体: Basis.mk lin_ind (lin_ind.span_eq_top_of_card_eq_finrank card_eq).ge

@[simp]

Depends on / 依赖: Basis.mk, card_eq, lin_ind, lin_ind.span_eq_top_of_card_eq_finrank, span_eq_top_of_card_eq_finrank
-/
noncomputable def basisOfLinearIndependentOfCardEqFinrank [Nonempty ι]
    {b : ι -> V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    Basis ι K V :=
Basis.mk lin_ind (lin_ind.span_eq_top_of_card_eq_finrank card_eq).ge

@[simp]
/--
theorem `coe_basisOfLinearIndependentOfCardEqFinrank` / 定理 `coe_basisOfLinearIndependentOfCardEqFinrank`

English:
theorem coe_basisOfLinearIndependentOfCardEqFinrank
  statement: [Nonempty ι]
  proof: Basis.coe_mk ..

中文:
定理 coe_basisOfLinearIndependentOfCardEqFinrank
  结论: [非空 ι]
  证明: Basis.coe_mk ..

Depends on / 依赖: Basis.coe_mk, coe_mk
-/
theorem coe_basisOfLinearIndependentOfCardEqFinrank [Nonempty ι]
    {b : ι -> V} (lin_ind : LinearIndependent K b) (card_eq : Fintype.card ι = finrank K V) :
    ⇑(basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = b := Basis.coe_mk ..

/--
Definition of `basisOfPiSpaceOfLinearIndependent` / `basisOfPiSpaceOfLinearIndependent` 的定义

English:
definition basisOfPiSpaceOfLinearIndependent
  body: if hι : Nonempty ι then
    basisOfLinearIndependentOfCardEqFinrank hb (Module.finrank_fintype_fun_eq_card K).symm
  else
    have : IsEmpty ι := not_nonempty_iff.mp hι
    Basis.empty _

中文:
定义 basisOfPiSpaceOfLinearIndependent
  定义体: if hι : Nonempty ι then
    basisOfLinearIndependentOfCardEqFinrank hb (Module.finrank_fintype_fun_eq_card K).symm
  else
    have : IsEmpty ι := not_nonempty_iff.mp hι
    Basis.empty _

Depends on / 依赖: Basis.empty, IsEmpty, Module, Module.finrank_fintype_fun_eq_card, Nonempty, basisOfLinearIndependentOfCardEqFinrank, finrank_fintype_fun_eq_card, not_nonempty_iff, not_nonempty_iff.mp
-/
noncomputable def basisOfPiSpaceOfLinearIndependent
    [Decidable (Nonempty ι)] {b : ι -> (ι -> K)} (hb : LinearIndependent K b) : Basis ι K (ι -> K) :=
  if hι : Nonempty ι then
    basisOfLinearIndependentOfCardEqFinrank hb (Module.finrank_fintype_fun_eq_card K).symm
  else
    have : IsEmpty ι := not_nonempty_iff.mp hι
    Basis.empty _

open scoped Classical in
@[simp]
/--
theorem `coe_basisOfPiSpaceOfLinearIndependent` / 定理 `coe_basisOfPiSpaceOfLinearIndependent`

English:
theorem coe_basisOfPiSpaceOfLinearIndependent
  proof: by
  by_cases hι : Nonempty ι
  · simp [hι, basisOfPiSpaceOfLinearIndependent]
  · rw [basisOfPiSpaceOfLinearIndependent, dif_neg hι]
    ext i
    exact ((not_nonempty_iff.mp hι).false i).elim

中文:
定理 coe_basisOfPiSpaceOfLinearIndependent
  证明: by
  by_cases hι : Nonempty ι
  · simp [hι, basisOfPiSpaceOfLinearIndependent]
  · rw [basisOfPiSpaceOfLinearIndependent, dif_neg hι]
    ext i
    exact ((not_nonempty_iff.mp hι).false i).elim

Depends on / 依赖: Nonempty, basisOfPiSpaceOfLinearIndependent, dif_neg, not_nonempty_iff, not_nonempty_iff.mp
-/
theorem coe_basisOfPiSpaceOfLinearIndependent
    {b : ι -> (ι -> K)} (hb : LinearIndependent K b) :
    ⇑(basisOfPiSpaceOfLinearIndependent hb) = b := by
  by_cases hι : Nonempty ι
  · simp [hι, basisOfPiSpaceOfLinearIndependent]
  · rw [basisOfPiSpaceOfLinearIndependent, dif_neg hι]
    ext i
    exact ((not_nonempty_iff.mp hι).false i).elim

/-- A linear independent finset of `finrank K V`-many vectors forms a basis. -/
@[simps! repr_apply]
/--
Definition of `finsetBasisOfLinearIndependentOfCardEqFinrank` / `finsetBasisOfLinearIndependentOfCardEqFinrank` 的定义

English:
definition finsetBasisOfLinearIndependentOfCardEqFinrank
  signature: {s : Finset V} (hs : s.Nonempty)
  body: haveI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans (Fintype.card_coe _) card_eq)

@[simp]

中文:
定义 finsetBasisOfLinearIndependentOfCardEqFinrank
  签名: {s : 有限集 V} (hs : s.非空)
  定义体: haveI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans (Fintype.card_coe _) card_eq)

@[simp]

Depends on / 依赖: Fintype, Fintype.card_coe, Nonempty, _root_, _root_.trans, basisOfLinearIndependentOfCardEqFinrank, card_coe, card_eq, choose_spec, hs.choose, hs.choose_spec, lin_ind
-/
noncomputable def finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s -> V)) (card_eq : s.card = finrank K V) : Basis s K V :=
  haveI : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans (Fintype.card_coe _) card_eq)

@[simp]
/--
theorem `coe_finsetBasisOfLinearIndependentOfCardEqFinrank` / 定理 `coe_finsetBasisOfLinearIndependentOfCardEqFinrank`

English:
theorem coe_finsetBasisOfLinearIndependentOfCardEqFinrank
  statement: {s : Finset V} (hs : s.Nonempty)
  proof: by
  have : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  simp [finsetBasisOfLinearIndependentOfCardEqFinrank]

中文:
定理 coe_finsetBasisOfLinearIndependentOfCardEqFinrank
  结论: {s : 有限集 V} (hs : s.非空)
  证明: by
  have : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  simp [finsetBasisOfLinearIndependentOfCardEqFinrank]

Depends on / 依赖: Nonempty, choose_spec, finsetBasisOfLinearIndependentOfCardEqFinrank, hs.choose, hs.choose_spec
-/
theorem coe_finsetBasisOfLinearIndependentOfCardEqFinrank {s : Finset V} (hs : s.Nonempty)
    (lin_ind : LinearIndependent K ((↑) : s -> V)) (card_eq : s.card = finrank K V) :
    ⇑(finsetBasisOfLinearIndependentOfCardEqFinrank hs lin_ind card_eq) = ((↑) : s -> V) := by
  have : Nonempty s := ⟨⟨hs.choose, hs.choose_spec⟩⟩
  simp [finsetBasisOfLinearIndependentOfCardEqFinrank]

/-- A linear independent set of `finrank K V`-many vectors forms a basis. -/
@[simps! repr_apply]
/--
Definition of `setBasisOfLinearIndependentOfCardEqFinrank` / `setBasisOfLinearIndependentOfCardEqFinrank` 的定义

English:
definition setBasisOfLinearIndependentOfCardEqFinrank
  signature: {s : Set V} [Nonempty s] [Fintype s]
  body: basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans s.toFinset_card.symm card_eq)

@[simp]

中文:
定义 setBasisOfLinearIndependentOfCardEqFinrank
  签名: {s : 集合 V} [非空 s] [有限类型 s]
  定义体: basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans s.toFinset_card.symm card_eq)

@[simp]

Depends on / 依赖: _root_, _root_.trans, basisOfLinearIndependentOfCardEqFinrank, card_eq, lin_ind, s.toFinset_card.symm, toFinset_card
-/
noncomputable def setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s -> V)) (card_eq : s.toFinset.card = finrank K V) :
    Basis s K V :=
  basisOfLinearIndependentOfCardEqFinrank lin_ind (_root_.trans s.toFinset_card.symm card_eq)

@[simp]
/--
theorem `coe_setBasisOfLinearIndependentOfCardEqFinrank` / 定理 `coe_setBasisOfLinearIndependentOfCardEqFinrank`

English:
theorem coe_setBasisOfLinearIndependentOfCardEqFinrank
  statement: {s : Set V} [Nonempty s] [Fintype s]
  proof: by
  simp [setBasisOfLinearIndependentOfCardEqFinrank]

中文:
定理 coe_setBasisOfLinearIndependentOfCardEqFinrank
  结论: {s : 集合 V} [非空 s] [有限类型 s]
  证明: by
  simp [setBasisOfLinearIndependentOfCardEqFinrank]

Depends on / 依赖: setBasisOfLinearIndependentOfCardEqFinrank
-/
theorem coe_setBasisOfLinearIndependentOfCardEqFinrank {s : Set V} [Nonempty s] [Fintype s]
    (lin_ind : LinearIndependent K ((↑) : s -> V)) (card_eq : s.toFinset.card = finrank K V) :
    ⇑(setBasisOfLinearIndependentOfCardEqFinrank lin_ind card_eq) = ((↑) : s -> V) := by
  simp [setBasisOfLinearIndependentOfCardEqFinrank]

end Basis

/-!
We now give characterisations of `finrank K V = 1` and `finrank K V ≤ 1`.
-/

section finrank_eq_one

/--
theorem `is_simple_module_of_finrank_eq_one` / 定理 `is_simple_module_of_finrank_eq_one`

English:
theorem is_simple_module_of_finrank_eq_one
  statement: {A} [Semiring A] [Module A V] [SMul K A]
  proof: by
  have := nontrivial_of_finrank_eq_succ h
  refine ⟨fun S => or_iff_not_imp_left.2 fun hn => ?_⟩
  rw [← restrictScalars_inj K] at hn ⊢
  have : FiniteDimensional _ _ := .of_finrank_eq_succ h
  refine eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm ?_)
  simpa only [h, finrank_bot] using!

中文:
定理 is_simple_module_of_finrank_eq_one
  结论: {A} [半环 A] [模 A V] [标量乘法 K A]
  证明: by
  have := nontrivial_of_finrank_eq_succ h
  refine ⟨fun S => or_iff_not_imp_left.2 fun hn => ?_⟩
  rw [← restrictScalars_inj K] at hn ⊢
  have : FiniteDimensional _ _ := .of_finrank_eq_succ h
  refine eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm ?_)
  simpa only [h, finrank_bot] using!

Depends on / 依赖: FiniteDimensional, Ne.bot_lt, Submodule, Submodule.finrank_le, Submodule.finrank_strictMono, antisymm, bot_lt, eq_top_of_finrank_eq, finrank_bot, finrank_le, finrank_strictMono, nontrivial_of_finrank_eq_succ, of_finrank_eq_succ, or_iff_not_imp_left, restrictScalars_inj
-/
theorem is_simple_module_of_finrank_eq_one {A} [Semiring A] [Module A V] [SMul K A]
    [IsScalarTower K A V] (h : finrank K V = 1) : IsSimpleOrder (Submodule A V) := by
  have := nontrivial_of_finrank_eq_succ h
  refine ⟨fun S => or_iff_not_imp_left.2 fun hn => ?_⟩
  rw [← restrictScalars_inj K] at hn ⊢
  have : FiniteDimensional _ _ := .of_finrank_eq_succ h
  refine eq_top_of_finrank_eq ((Submodule.finrank_le _).antisymm ?_)
  simpa only [h, finrank_bot] using! Submodule.finrank_strictMono (Ne.bot_lt hn)

end finrank_eq_one

end DivisionRing

section SubalgebraRank

open Module

variable {F E : Type*} [Field F] [Ring E] [Algebra F E]

/--
theorem `Subalgebra.isSimpleOrder_of_finrank` / 定理 `Subalgebra.isSimpleOrder_of_finrank`

English:
theorem Subalgebra.isSimpleOrder_of_finrank
  given: (hr : finrank F E = 2)
  proof: let i := nontrivial_of_finrank_pos (zero_lt_two.trans_eq hr.symm)
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun h => by cases hr.symm.trans (Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h)⟩⟩
    eq_bot_or_eq_top := by
      intro S
      have : FiniteDimensional F E := .of_finrank_eq_succ hr
      have : Fini

中文:
定理 子代数.isSimpleOrder_of_finrank
  条件: (hr : finrank F E = 2)
  证明: let i := nontrivial_of_finrank_pos (zero_lt_two.trans_eq hr.symm)
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun h => by cases hr.symm.trans (Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h)⟩⟩
    eq_bot_or_eq_top := by
      intro S
      have : FiniteDimensional F E := .of_finrank_eq_succ hr
      have : Fini

Depends on / 依赖: FiniteDimensional, FiniteDimensional.finiteDimensional_submodule, S.toSubmodule.finrank_le, Subalgebra, Subalgebra.bot_eq_top_iff_finrank_eq_one, Subalgebra.toSubmodule, bot_eq_top_iff_finrank_eq_one, eq_bot_or_eq_top, finiteDimensional_submodule, finrank, finrank_le, finrank_pos_iff, finrank_pos_iff.mpr, hr.symm, hr.symm.trans, interval_cases, nontrivial_of_finrank_pos, of_finrank_eq_succ, toNontrivial, toSubmodule
-/
theorem Subalgebra.isSimpleOrder_of_finrank (hr : finrank F E = 2) :
    IsSimpleOrder (Subalgebra F E) :=
  let i := nontrivial_of_finrank_pos (zero_lt_two.trans_eq hr.symm)
  { toNontrivial :=
      ⟨⟨⊥, ⊤, fun h => by cases hr.symm.trans (Subalgebra.bot_eq_top_iff_finrank_eq_one.1 h)⟩⟩
    eq_bot_or_eq_top := by
      intro S
      have : FiniteDimensional F E := .of_finrank_eq_succ hr
      have : FiniteDimensional F S :=
        FiniteDimensional.finiteDimensional_submodule (Subalgebra.toSubmodule S)
      have : finrank F S <= 2 := hr ▸ S.toSubmodule.finrank_le
      have : 0 < finrank F S := finrank_pos_iff.mpr inferInstance
      interval_cases h : finrank F { x // x in S }
      · left
        exact Subalgebra.eq_bot_of_finrank_one h
      · right
        rw [← hr] at h
        rw [← Algebra.toSubmodule_eq_top]
        exact eq_top_of_finrank_eq h }

end SubalgebraRank

namespace Module

namespace End

variable [DivisionRing K] [AddCommGroup V] [Module K V]

/--
theorem `exists_ker_pow_eq_ker_pow_succ` / 定理 `exists_ker_pow_eq_ker_pow_succ`

English:
theorem exists_ker_pow_eq_ker_pow_succ
  given: [FiniteDimensional K V] (f : End K V)
  proof: by
  by_contra h_contra
  simp_rw [not_exists, not_and] at h_contra
  have h_le_ker_pow : forall n : Nat, n <= (finrank K V).succ ->
      n <= finrank K (LinearMap.ker (f ^ n)) := by
    intro n hn
    induction n with
    | zero => exact zero_le
    | succ n ih =>
      have h_ker_lt_ker : LinearM

中文:
定理 存在_ker_pow_eq_ker_pow_succ
  条件: [有限维 K V] (f : End K V)
  证明: by
  by_contra h_contra
  simp_rw [not_exists, not_and] at h_contra
  have h_le_ker_pow : forall n : Nat, n <= (finrank K V).succ ->
      n <= finrank K (LinearMap.ker (f ^ n)) := by
    intro n hn
    induction n with
    | zero => exact zero_le
    | succ n ih =>
      have h_ker_lt_ker : LinearM

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.ker_le_ker_comp, Nat.le_of_succ_le_succ, finrank, h_contra, h_finrank_lt_finrank, h_ker_lt_ker, h_le_ker_pow, ker_le_ker_comp, le_of_succ_le_succ, lt_of_le_of_ne, n.succ, not_and, not_exists, pow_succ, simp_rw, zero_le
-/
theorem exists_ker_pow_eq_ker_pow_succ [FiniteDimensional K V] (f : End K V) :
    exists k : Nat, k <= finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) := by
  by_contra h_contra
  simp_rw [not_exists, not_and] at h_contra
  have h_le_ker_pow : forall n : Nat, n <= (finrank K V).succ ->
      n <= finrank K (LinearMap.ker (f ^ n)) := by
    intro n hn
    induction n with
    | zero => exact zero_le
    | succ n ih =>
      have h_ker_lt_ker : LinearMap.ker (f ^ n) < LinearMap.ker (f ^ n.succ) := by
        refine lt_of_le_of_ne ?_ (h_contra n (Nat.le_of_succ_le_succ hn))
        rw [pow_succ']
        apply LinearMap.ker_le_ker_comp
      have h_finrank_lt_finrank :
          finrank K (LinearMap.ker (f ^ n)) < finrank K (LinearMap.ker (f ^ n.succ)) := by
        apply Submodule.finrank_lt_finrank_of_lt h_ker_lt_ker
      calc
        n.succ <= (finrank K ↑(LinearMap.ker (f ^ n))).succ :=
          Nat.succ_le_succ (ih (Nat.le_of_succ_le hn))
        _ <= finrank K ↑(LinearMap.ker (f ^ n.succ)) := Nat.succ_le_of_lt h_finrank_lt_finrank
  have h_any_n_lt : forall n, n <= (finrank K V).succ -> n <= finrank K V := fun n hn =>
    (h_le_ker_pow n hn).trans (Submodule.finrank_le _)
  exact Nat.not_succ_le_self _ (h_any_n_lt (finrank K V).succ (finrank K V).succ.le_refl)

/--
theorem `ker_pow_eq_ker_pow_finrank_of_le` / 定理 `ker_pow_eq_ker_pow_finrank_of_le`

English:
theorem ker_pow_eq_ker_pow_finrank_of_le
  statement: [FiniteDimensional K V] {f : End K V} {m : Nat}
  proof: by
  obtain ⟨k, h_k_le, hk⟩ :
    exists k, k <= finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f
  calc
    LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (k + (m - k))) := by
      rw [add_tsub_cancel_of_le (h_k_le.trans hm)]
    _ = LinearMap.ke

中文:
定理 ker_pow_eq_ker_pow_finrank_of_le
  结论: [有限维 K V] {f : End K V} {m : 自然数}
  证明: by
  obtain ⟨k, h_k_le, hk⟩ :
    exists k, k <= finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f
  calc
    LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (k + (m - k))) := by
      rw [add_tsub_cancel_of_le (h_k_le.trans hm)]
    _ = LinearMap.ke

Depends on / 依赖: LinearMap, LinearMap.ker, add_tsub_cancel_of_le, exists_ker_pow_eq_ker_pow_succ, finrank, h_k_le, h_k_le.trans, k.succ, ker_pow_constant
-/
theorem ker_pow_eq_ker_pow_finrank_of_le [FiniteDimensional K V] {f : End K V} {m : Nat}
    (hm : finrank K V <= m) : LinearMap.ker (f ^ m) = LinearMap.ker (f ^ finrank K V) := by
  obtain ⟨k, h_k_le, hk⟩ :
    exists k, k <= finrank K V ∧ LinearMap.ker (f ^ k) = LinearMap.ker (f ^ k.succ) :=
    exists_ker_pow_eq_ker_pow_succ f
  calc
    LinearMap.ker (f ^ m) = LinearMap.ker (f ^ (k + (m - k))) := by
      rw [add_tsub_cancel_of_le (h_k_le.trans hm)]
    _ = LinearMap.ker (f ^ k) := by rw [ker_pow_constant hk _]
    _ = LinearMap.ker (f ^ (k + (finrank K V - k))) := ker_pow_constant hk (finrank K V - k)
    _ = LinearMap.ker (f ^ finrank K V) := by rw [add_tsub_cancel_of_le h_k_le]

/--
theorem `ker_pow_le_ker_pow_finrank` / 定理 `ker_pow_le_ker_pow_finrank`

English:
theorem ker_pow_le_ker_pow_finrank
  given: [FiniteDimensional K V] (f : End K V) (m : Nat)
  proof: by
  by_cases! h_cases : m < finrank K V
  · rw [← add_tsub_cancel_of_le h_cases.le, add_comm, pow_add]
    apply LinearMap.ker_le_ker_comp
  · rw [ker_pow_eq_ker_pow_finrank_of_le h_cases]

中文:
定理 ker_pow_le_ker_pow_finrank
  条件: [有限维 K V] (f : End K V) (m : 自然数)
  证明: by
  by_cases! h_cases : m < finrank K V
  · rw [← add_tsub_cancel_of_le h_cases.le, add_comm, pow_add]
    apply LinearMap.ker_le_ker_comp
  · rw [ker_pow_eq_ker_pow_finrank_of_le h_cases]

Depends on / 依赖: LinearMap, LinearMap.ker_le_ker_comp, add_comm, add_tsub_cancel_of_le, finrank, h_cases, h_cases.le, ker_le_ker_comp, ker_pow_eq_ker_pow_finrank_of_le, pow_add
-/
theorem ker_pow_le_ker_pow_finrank [FiniteDimensional K V] (f : End K V) (m : Nat) :
    LinearMap.ker (f ^ m) <= LinearMap.ker (f ^ finrank K V) := by
  by_cases! h_cases : m < finrank K V
  · rw [← add_tsub_cancel_of_le h_cases.le, add_comm, pow_add]
    apply LinearMap.ker_le_ker_comp
  · rw [ker_pow_eq_ker_pow_finrank_of_le h_cases]

end End

end Module

namespace Submodule

section DivisionRing

variable {W : Type v'} [DivisionRing K] [AddCommGroup W] [AddCommGroup V] [Module K V] [Module K W]
  {f : V ->ₗ[K] W}

instance (p : Submodule K W) [FiniteDimensional K p] [FiniteDimensional K f.ker] :
    FiniteDimensional K (comap f p) := by
  grw [FiniteDimensional, ← rank_lt_aleph0_iff, ← lift_lt, f.lift_rank_comap_le p, lift_aleph0]
  apply add_lt_aleph0 <;> rwa [lift_lt_aleph0, rank_lt_aleph0_iff]

instance (p : Submodule K V) [FiniteDimensional K (V ⧸ p)] [FiniteDimensional K (W ⧸ f.range)] :
    FiniteDimensional K (W ⧸ map f p) := by
  grw [FiniteDimensional, ← rank_lt_aleph0_iff, ← lift_lt, f.lift_rank_quot_map_le p, lift_aleph0]
  apply add_lt_aleph0 <;> rwa [lift_lt_aleph0, rank_lt_aleph0_iff]

end DivisionRing

end Submodule
