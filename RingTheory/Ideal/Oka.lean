/-
Copyright (c) 2025 Anthony Fernandes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Fernandes, Marc Robin
-/
module

public import Mathlib.RingTheory.Ideal.Colon

/-!
# Oka predicates

This file introduces the notion of Oka predicates and standard results about them.

## Main results

- `Ideal.IsOka.isPrime_of_maximal_not`: if an ideal is maximal for not satisfying an Oka predicate,
  then it is prime.
- `Ideal.IsOka.forall_of_forall_prime`: if all prime ideals of a ring satisfy an Oka predicate,
  then all its ideals also satisfy the predicate.

## References

- [stacks-project]: The Stacks project, [tag 05K7](https://stacks.math.columbia.edu/tag/05K7)
- [lam_reyes_2009]: *Oka and Ako ideal families in commutative rings*, 2009
-/

public section

namespace Ideal

variable {R : Type*} [CommSemiring R]

/-- A predicate `P : Ideal R → Prop` over the ideals of a ring `R` is said to be Oka if R satisfies
it (`P ⊤`) and whenever we have `I : Ideal R`, `P (I.colon (span {a})` and `P (I ⊔ span {a})` for
some `a : R` then `P I`. -/
@[stacks 05K9]
/--
Definition of `IsOka` / `IsOka` 的定义

English:
structure IsOka
  parameters: (P : Ideal R -> Prop)
  axioms and operations (2):
    - top : P ⊤
    - oka({I : Ideal R} {a : R}) : P (I ⊔ span {a}) -> P (I.colon (span {a})) -> P I

中文:
结构 是Oka
  参数: (P : 理想 R -> 命题)
  公理与运算 (2 个):
    - top : P ⊤
    - oka({I : 理想 R} {a : R}) : P (I ⊔ span {a}) -> P (I.colon (span {a})) -> P I
-/
structure IsOka (P : Ideal R -> Prop) : Prop where
  top : P ⊤
  oka {I : Ideal R} {a : R} : P (I ⊔ span {a}) -> P (I.colon (span {a})) -> P I

namespace IsOka

variable {P : Ideal R -> Prop} (hP : IsOka P)
include hP

/-- If an ideal is maximal for not satisfying an Oka predicate then it is prime. -/
@[stacks 05KE]
/--
theorem `isPrime_of_maximal_not` / 定理 `isPrime_of_maximal_not`

English:
theorem isPrime_of_maximal_not
  given: {I : Ideal R} (hI : Maximal (¬P ·) I)
  statement: I.IsPrime where
  proof: hI.prop (hI' ▸ hP.top)
  mem_or_mem' := by
    by_contra! ⟨a, b, hab, ha, hb⟩
have h₁ : P (I ⊔ span {a}) := of_not_not hI.not_prop_of_gt (Submodule.lt_sup_iff_notMem.2 ha)
have h₂ : P (I.colon (span {a})) := of_not_not hI.not_prop_of_gt lt_of_le_of_ne le_colon
      (fun H => hb <| H ▸ mem_colon_span_singleton.2 (mul_comm a b ▸ hab))
    exact hI.prop (hP.oka h₁ h₂)

中文:
定理 isPrime_of_maximal_not
  条件: {I : 理想 R} (hI : 极大 (¬P ·) I)
  结论: I.是素 where
  证明: hI.prop (hI' ▸ hP.top)
  mem_or_mem' := by
    by_contra! ⟨a, b, hab, ha, hb⟩
have h₁ : P (I ⊔ span {a}) := of_not_not hI.not_prop_of_gt (Submodule.lt_sup_iff_notMem.2 ha)
have h₂ : P (I.colon (span {a})) := of_not_not hI.not_prop_of_gt lt_of_le_of_ne le_colon
      (fun H => hb <| H ▸ mem_colon_span_singleton.2 (mul_comm a b ▸ hab))
    exact hI.prop (hP.oka h₁ h₂)

Depends on / 依赖: hI.prop, hP.top
-/
theorem isPrime_of_maximal_not {I : Ideal R} (hI : Maximal (¬P ·) I) : I.IsPrime where
  ne_top' hI' := hI.prop (hI' ▸ hP.top)
  mem_or_mem' := by
    by_contra! ⟨a, b, hab, ha, hb⟩
have h₁ : P (I ⊔ span {a}) := of_not_not hI.not_prop_of_gt (Submodule.lt_sup_iff_notMem.2 ha)
have h₂ : P (I.colon (span {a})) := of_not_not hI.not_prop_of_gt lt_of_le_of_ne le_colon
      (fun H => hb <| H ▸ mem_colon_span_singleton.2 (mul_comm a b ▸ hab))
    exact hI.prop (hP.oka h₁ h₂)

/--
theorem `forall_of_forall_prime` / 定理 `forall_of_forall_prime`

English:
theorem forall_of_forall_prime
  statement: (hmax : forall I, ¬P I -> exists I, Maximal (¬P ·) I)
  proof: by
  by_contra hI
  obtain ⟨I, hI⟩ := hmax I hI
exact hI.prop hprime I (hP.isPrime_of_maximal_not hI)

中文:
定理 对任意_of_对任意_prime
  结论: (hmax : 对任意 I, ¬P I -> 存在 I, 极大 (¬P ·) I)
  证明: by
  by_contra hI
  obtain ⟨I, hI⟩ := hmax I hI
exact hI.prop hprime I (hP.isPrime_of_maximal_not hI)

Depends on / 依赖: hI.prop, hP.isPrime_of_maximal_not, hprime, isPrime_of_maximal_not
-/
theorem forall_of_forall_prime (hmax : forall I, ¬P I -> exists I, Maximal (¬P ·) I)
    (hprime : forall I, I.IsPrime -> P I) (I : Ideal R) : P I := by
  by_contra hI
  obtain ⟨I, hI⟩ := hmax I hI
exact hI.prop hprime I (hP.isPrime_of_maximal_not hI)

/--
theorem `forall_of_forall_prime'` / 定理 `forall_of_forall_prime'`

English:
theorem forall_of_forall_prime'
  proof: by
  refine forall_of_forall_prime hP (fun I hI => ?_) hprime
  obtain ⟨M, _, hM⟩ : exists M, I <= M ∧ Maximal (¬P ·) M := by
    refine zorn_le_nonempty₀ {I | ¬P I} (fun C hC₁ hC₂ J hJ => ⟨sSup C, ?_, fun _ => le_sSup⟩) I hI
    intro H
    obtain ⟨_, h₁, h₂⟩ := hchain C hC₁ hC₂ J hJ H
    exact hC₁ h₁ h₂
  exact ⟨M, hM⟩

中文:
定理 对任意_of_对任意_prime'
  证明: by
  refine forall_of_forall_prime hP (fun I hI => ?_) hprime
  obtain ⟨M, _, hM⟩ : exists M, I <= M ∧ Maximal (¬P ·) M := by
    refine zorn_le_nonempty₀ {I | ¬P I} (fun C hC₁ hC₂ J hJ => ⟨sSup C, ?_, fun _ => le_sSup⟩) I hI
    intro H
    obtain ⟨_, h₁, h₂⟩ := hchain C hC₁ hC₂ J hJ H
    exact hC₁ h₁ h₂
  exact ⟨M, hM⟩

Depends on / 依赖: Maximal, forall_of_forall_prime, hchain, hprime, le_sSup
-/
theorem forall_of_forall_prime'
    (hchain : forall C subseteq {I | ¬P I}, IsChain (· <= ·) C -> forall _ in C, P (sSup C) -> exists I in C, P I)
    (hprime : forall I, I.IsPrime -> P I) : forall I, P I := by
  refine forall_of_forall_prime hP (fun I hI => ?_) hprime
  obtain ⟨M, _, hM⟩ : exists M, I <= M ∧ Maximal (¬P ·) M := by
    refine zorn_le_nonempty₀ {I | ¬P I} (fun C hC₁ hC₂ J hJ => ⟨sSup C, ?_, fun _ => le_sSup⟩) I hI
    intro H
    obtain ⟨_, h₁, h₂⟩ := hchain C hC₁ hC₂ J hJ H
    exact hC₁ h₁ h₂
  exact ⟨M, hM⟩

end IsOka

end Ideal
