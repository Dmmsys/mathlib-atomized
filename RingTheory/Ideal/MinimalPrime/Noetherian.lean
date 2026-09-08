/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!

# Finiteness of minimal primes

We prove finiteness of minimal primes above an ideal.

This is proved without reference to `PrimeSpectrum` to avoid heavy imports.

-/

public section

variable (R : Type*) [CommSemiring R] [hR : IsNoetherianRing R]

/-
**Ideal.finite_minimalPrimes_of_isNoetherianRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.finite_minimalPrimes_of_isNoetherianRing (I : Ideal R) : I.minimalPr
imes.Finite
参数：I : Ideal R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_has_maximal_iff_noetherian`：set_has_maximal_iff_noetherian : (forall
 a : Set <| Submodule R M, a.Nonempty -> exists M' in a, forall I in a, ¬M' < I)
 ↔ IsNoetherian R M
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.minimalPrimes_eq_subsingleton_self`：Ideal.minimalPrimes_eq_subsing
leton_self [I.IsPrime] : I.minimalPrimes = {I}
· 使用定理 `Ideal.minimalPrimes_top`：Ideal.minimalPrimes_top : (⊤ : Ideal R).minimal
Primes = ∅
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.not_isPrime_iff`：not_isPrime_iff {I : Ideal α} : ¬I.IsPrime ↔ I = 
⊤ ∨ exists (x : α) (_hx : x ∉ I) (y : α) (_hy : y ∉ I), x * y in I
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.union`：∀ {α : Type u} {s t : Set α}, s.Finite → t.Finite → (s
 ∪ t).Finite
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `left_lt_sup`：left_lt_sup : a < a ⊔ b ↔ ¬b <= a
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Ideal.IsPrime.mem_or_mem'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal
 α} [self : I.IsPrime] {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma Ideal.finite_minimalPrimes_of_isNoetherianRing (I : Ideal R) :
    I.minimalPrimes.Finite := by
  by_contra hI
  obtain ⟨I : Ideal R, hI : ¬ I.minimalPrimes.Finite, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr hR {I : Ideal R | ¬ I.minimalPrimes.Finite} ⟨I, hI⟩
  simp only [Set.mem_ofPred_eq, not_imp_not] at hmax
  have h1 : ¬ I.IsPrime := by contrapose hI; simp [minimalPrimes_eq_subsingleton_self]
  have h2 : I ≠ ⊤ := by contrapose hI; simp [hI, minimalPrimes_top]
  obtain ⟨x, hx, y, hy, h⟩ := (not_isPrime_iff.mp h1).resolve_left h2
  rw [← Ideal.span_singleton_le_iff_mem, ← left_lt_sup] at hx hy
  refine hI (((hmax _ hx).union (hmax _ hy)).subset fun p ⟨⟨hp, hI⟩, hmin⟩ ↦ ?_)
  rcases hp.2 (hI h) with hxp | hyp
  · exact Or.inl ⟨⟨hp, sup_le hI (p.span_singleton_le_iff_mem.mpr hxp)⟩,
      fun q hq hqp ↦ hmin ⟨hq.1, hx.le.trans hq.2⟩ hqp⟩
  · exact Or.inr ⟨⟨hp, sup_le hI (p.span_singleton_le_iff_mem.mpr hyp)⟩,
      fun q hq hqp ↦ hmin ⟨hq.1, hy.le.trans hq.2⟩ hqp⟩
/-
**minimalPrimes.finite_of_isNoetherianRing** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：minimalPrimes.finite_of_isNoetherianRing : (minimalPrimes R).Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.finite_minimalPrimes_of_isNoetherianRing`：Ideal.finite_minimalPrim
es_of_isNoetherianRing (I : Ideal R) : I.minimalPrimes.Finite
-/
lemma minimalPrimes.finite_of_isNoetherianRing : (minimalPrimes R).Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥
