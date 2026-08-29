/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
module

public import Mathlib.Algebra.CharP.Quotient
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.Determinant
public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Basis
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicative

/-!

# Ideal norms

This file defines the absolute ideal norm `Ideal.absNorm (I : Ideal R) : ℕ` as the cardinality of
the quotient `R ⧸ I` (setting it to 0 if the cardinality is infinite).

## Main definitions

* `Submodule.cardQuot (S : Submodule R M)`: the cardinality of the quotient `M ⧸ S`, in `ℕ`.
  This maps `⊥` to `0` and `⊤` to `1`.
* `Ideal.absNorm (I : Ideal R)`: the absolute ideal norm, defined as
  the cardinality of the quotient `R ⧸ I`, as a bundled monoid-with-zero homomorphism.

## Main results

* `map_mul Ideal.absNorm`: multiplicativity of the ideal norm is bundled in
  the definition of `Ideal.absNorm`
* `Ideal.natAbs_det_basis_change`: the ideal norm is given by the determinant
  of the basis change matrix
* `Ideal.absNorm_span_singleton`: the ideal norm of a principal ideal is the
  norm of its generator
-/

@[expose] public section

open Module
open scoped nonZeroDivisors

section abs_norm

namespace Submodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

section

/--
Definition of `cardQuot` / `cardQuot` 的定义

English:
definition cardQuot
  signature: (S : Submodule R M)
  body: AddSubgroup.index S.toAddSubgroup

中文:
定义 cardQuot
  签名: (S : 子模 R M)
  定义体: AddSubgroup.index S.toAddSubgroup

Depends on / 依赖: AddSubgroup, AddSubgroup.index, S.toAddSubgroup, toAddSubgroup
-/
noncomputable def cardQuot (S : Submodule R M) : Nat :=
  AddSubgroup.index S.toAddSubgroup

/--
theorem `cardQuot_apply` / 定理 `cardQuot_apply`

English:
theorem cardQuot_apply
  given: (S : Submodule R M)
  statement: cardQuot S = Nat.card (M ⧸ S)
  proof: by
  rfl

中文:
定理 cardQuot_apply
  条件: (S : 子模 R M)
  结论: cardQuot S = 自然数.card (M ⧸ S)
  证明: by
  rfl
-/
theorem cardQuot_apply (S : Submodule R M) : cardQuot S = Nat.card (M ⧸ S) := by
  rfl

variable (R M)

@[simp]
/--
theorem `cardQuot_bot` / 定理 `cardQuot_bot`

English:
theorem cardQuot_bot
  given: [Infinite M]
  statement: cardQuot (⊥ : Submodule R M) = 0
  proof: AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite

@[simp]

中文:
定理 cardQuot_bot
  条件: [无限 M]
  结论: cardQuot (⊥ : 子模 R M) = 0
  证明: AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite

@[simp]

Depends on / 依赖: AddSubgroup, AddSubgroup.index_bot.trans, Nat.card_eq_zero_of_infinite, card_eq_zero_of_infinite, index_bot
-/
theorem cardQuot_bot [Infinite M] : cardQuot (⊥ : Submodule R M) = 0 :=
  AddSubgroup.index_bot.trans Nat.card_eq_zero_of_infinite

@[simp]
/--
theorem `cardQuot_top` / 定理 `cardQuot_top`

English:
theorem cardQuot_top
  statement: cardQuot (⊤ : Submodule R M) = 1
  proof: AddSubgroup.index_top

中文:
定理 cardQuot_top
  结论: cardQuot (⊤ : 子模 R M) = 1
  证明: AddSubgroup.index_top

Depends on / 依赖: AddSubgroup, AddSubgroup.index_top, index_top
-/
theorem cardQuot_top : cardQuot (⊤ : Submodule R M) = 1 :=
  AddSubgroup.index_top

variable {R M}

@[simp]
/--
theorem `cardQuot_eq_one_iff` / 定理 `cardQuot_eq_one_iff`

English:
theorem cardQuot_eq_one_iff
  given: {P : Submodule R M}
  statement: cardQuot P = 1 ↔ P = ⊤
  proof: AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])

中文:
定理 cardQuot_eq_one_iff
  条件: {P : 子模 R M}
  结论: cardQuot P = 1 ↔ P = ⊤
  证明: AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])

Depends on / 依赖: AddSubgroup, AddSubgroup.index_eq_one.trans, SetLike, SetLike.ext_iff, ext_iff, index_eq_one
-/
theorem cardQuot_eq_one_iff {P : Submodule R M} : cardQuot P = 1 ↔ P = ⊤ :=
  AddSubgroup.index_eq_one.trans (by simp [SetLike.ext_iff])

end

end Submodule

section RingOfIntegers

variable {S : Type*} [CommRing S]

open Submodule

/--
theorem `cardQuot_mul_of_coprime` / 定理 `cardQuot_mul_of_coprime`

English:
theorem cardQuot_mul_of_coprime
  proof: by
  rw [cardQuot_apply]; rw [cardQuot_apply]; rw [cardQuot_apply]; rw [Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv]; rw [Nat.card_prod]

中文:
定理 cardQuot_mul_of_coprime
  证明: by
  rw [cardQuot_apply]; rw [cardQuot_apply]; rw [cardQuot_apply]; rw [Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv]; rw [Nat.card_prod]

Depends on / 依赖: Ideal.quotientMulEquivQuotientProd, Nat.card_congr, Nat.card_prod, cardQuot_apply, card_congr, card_prod, coprime, quotientMulEquivQuotientProd, toEquiv
-/
theorem cardQuot_mul_of_coprime
    {I J : Ideal S} (coprime : IsCoprime I J) : cardQuot (I * J) = cardQuot I * cardQuot J := by
  rw [cardQuot_apply]; rw [cardQuot_apply]; rw [cardQuot_apply]; rw [Nat.card_congr (Ideal.quotientMulEquivQuotientProd I J coprime).toEquiv]; rw [Nat.card_prod]

/--
theorem `Ideal.mul_add_mem_pow_succ_inj` / 定理 `Ideal.mul_add_mem_pow_succ_inj`

English:
theorem Ideal.mul_add_mem_pow_succ_inj
  statement: (P : Ideal S) {i : Nat} (a d d' e e' : S) (a_mem : a in P ^ i)
  proof: by
  have : a * d - a * d' in P ^ (i + 1) := by
    simp only [← mul_sub]
    exact Ideal.mul_mem_mul a_mem h
  convert! Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem) using 1
  ring

中文:
定理 理想.mul_add_mem_pow_succ_inj
  结论: (P : 理想 S) {i : 自然数} (a d d' e e' : S) (a_mem : a in P ^ i)
  证明: by
  have : a * d - a * d' in P ^ (i + 1) := by
    simp only [← mul_sub]
    exact Ideal.mul_mem_mul a_mem h
  convert! Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem) using 1
  ring

Depends on / 依赖: Ideal.add_mem, Ideal.mul_mem_mul, Ideal.sub_mem, _mem, a_mem, add_mem, convert, e_mem, mul_mem_mul, mul_sub, sub_mem
-/
theorem Ideal.mul_add_mem_pow_succ_inj (P : Ideal S) {i : Nat} (a d d' e e' : S) (a_mem : a in P ^ i)
    (e_mem : e in P ^ (i + 1)) (e'_mem : e' in P ^ (i + 1)) (h : d - d' in P) :
    a * d + e - (a * d' + e') in P ^ (i + 1) := by
  have : a * d - a * d' in P ^ (i + 1) := by
    simp only [← mul_sub]
    exact Ideal.mul_mem_mul a_mem h
  convert! Ideal.add_mem _ this (Ideal.sub_mem _ e_mem e'_mem) using 1
  ring

section PPrime

variable {P : Ideal S} [P_prime : P.IsPrime]

/--
theorem `Ideal.exists_mul_add_mem_pow_succ` / 定理 `Ideal.exists_mul_add_mem_pow_succ`

English:
theorem Ideal.exists_mul_add_mem_pow_succ
  statement: [IsDedekindDomain S] (hP : P != ⊥)
  proof: by
  suffices eq_b : P ^ i = Ideal.span {a} ⊔ P ^ (i + 1) by
    rw [eq_b] at c_mem
    simp only [mul_comm a]
    exact Ideal.mem_span_singleton_sup.mp c_mem
  refine (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right ?_)
    (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mp

中文:
定理 理想.存在_mul_add_mem_pow_succ
  结论: [是Dedekind整环 S] (hP : P != ⊥)
  证明: by
  suffices eq_b : P ^ i = Ideal.span {a} ⊔ P ^ (i + 1) by
    rw [eq_b] at c_mem
    simp only [mul_comm a]
    exact Ideal.mem_span_singleton_sup.mp c_mem
  refine (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right ?_)
    (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mp

Depends on / 依赖: Ideal.eq_prime_pow_of_succ_lt_of_le, Ideal.mem_span_singleton_sup.mp, Ideal.pow_succ_lt_pow, Ideal.span, Ideal.span_le.mpr, Set.singleton_subset_iff.mpr, a_mem, a_notMem, c_mem, contrapose, eq_b, eq_prime_pow_of_succ_lt_of_le, le_sup_right, lt_of_le_of_ne, mem_span_singleton_self, mem_span_singleton_sup, mem_sup, mem_sup.mpr, mul_comm, pow_succ_lt_pow
-/
theorem Ideal.exists_mul_add_mem_pow_succ [IsDedekindDomain S] (hP : P != ⊥)
    {i : Nat} (a c : S) (a_mem : a in P ^ i)
    (a_notMem : a ∉ P ^ (i + 1)) (c_mem : c in P ^ i) :
    exists d : S, exists e in P ^ (i + 1), a * d + e = c := by
  suffices eq_b : P ^ i = Ideal.span {a} ⊔ P ^ (i + 1) by
    rw [eq_b] at c_mem
    simp only [mul_comm a]
    exact Ideal.mem_span_singleton_sup.mp c_mem
  refine (Ideal.eq_prime_pow_of_succ_lt_of_le hP (lt_of_le_of_ne le_sup_right ?_)
    (sup_le (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr a_mem))
      (Ideal.pow_succ_lt_pow hP i).le)).symm
  contrapose a_notMem with this
  rw [this]
  exact mem_sup.mpr ⟨a, mem_span_singleton_self a, 0, by simp, by simp⟩

/--
theorem `Ideal.mem_prime_of_mul_mem_pow` / 定理 `Ideal.mem_prime_of_mul_mem_pow`

English:
theorem Ideal.mem_prime_of_mul_mem_pow
  statement: [IsDedekindDomain S] {P : Ideal S} [P_prime : P.IsPrime]
  proof: by
  simp only [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, pow_succ, ←
    Ideal.span_singleton_mul_span_singleton] at a_notMem ab_mem ⊢
  exact (prime_pow_succ_dvd_mul (Ideal.prime_of_isPrime hP P_prime) ab_mem).resolve_left a_notMem

中文:
定理 理想.mem_prime_of_mul_mem_pow
  结论: [是Dedekind整环 S] {P : 理想 S} [P_prime : P.是素]
  证明: by
  simp only [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, pow_succ, ←
    Ideal.span_singleton_mul_span_singleton] at a_notMem ab_mem ⊢
  exact (prime_pow_succ_dvd_mul (Ideal.prime_of_isPrime hP P_prime) ab_mem).resolve_left a_notMem

Depends on / 依赖: Ideal.dvd_iff_le, Ideal.prime_of_isPrime, Ideal.span_singleton_le_iff_mem, Ideal.span_singleton_mul_span_singleton, P_prime, a_notMem, ab_mem, dvd_iff_le, pow_succ, prime_of_isPrime, prime_pow_succ_dvd_mul, resolve_left, span_singleton_le_iff_mem, span_singleton_mul_span_singleton
-/
theorem Ideal.mem_prime_of_mul_mem_pow [IsDedekindDomain S] {P : Ideal S} [P_prime : P.IsPrime]
    (hP : P != ⊥) {i : Nat} {a b : S} (a_notMem : a ∉ P ^ (i + 1)) (ab_mem : a * b in P ^ (i + 1)) :
    b in P := by
  simp only [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, pow_succ, ←
    Ideal.span_singleton_mul_span_singleton] at a_notMem ab_mem ⊢
  exact (prime_pow_succ_dvd_mul (Ideal.prime_of_isPrime hP P_prime) ab_mem).resolve_left a_notMem

/--
theorem `Ideal.mul_add_mem_pow_succ_unique` / 定理 `Ideal.mul_add_mem_pow_succ_unique`

English:
theorem Ideal.mul_add_mem_pow_succ_unique
  statement: [IsDedekindDomain S] (hP : P != ⊥)
  proof: by
  have h' : a * (d - d') in P ^ (i + 1) := by
    convert! Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem) using 1
    ring
  exact Ideal.mem_prime_of_mul_mem_pow hP a_notMem h'

中文:
定理 理想.mul_add_mem_pow_succ_unique
  结论: [是Dedekind整环 S] (hP : P != ⊥)
  证明: by
  have h' : a * (d - d') in P ^ (i + 1) := by
    convert! Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem) using 1
    ring
  exact Ideal.mem_prime_of_mul_mem_pow hP a_notMem h'

Depends on / 依赖: Ideal.add_mem, Ideal.mem_prime_of_mul_mem_pow, Ideal.sub_mem, _mem, a_notMem, add_mem, convert, e_mem, mem_prime_of_mul_mem_pow, sub_mem
-/
theorem Ideal.mul_add_mem_pow_succ_unique [IsDedekindDomain S] (hP : P != ⊥)
    {i : Nat} (a d d' e e' : S)
    (a_notMem : a ∉ P ^ (i + 1)) (e_mem : e in P ^ (i + 1)) (e'_mem : e' in P ^ (i + 1))
    (h : a * d + e - (a * d' + e') in P ^ (i + 1)) : d - d' in P := by
  have h' : a * (d - d') in P ^ (i + 1) := by
    convert! Ideal.add_mem _ h (Ideal.sub_mem _ e'_mem e_mem) using 1
    ring
  exact Ideal.mem_prime_of_mul_mem_pow hP a_notMem h'

/--
theorem `cardQuot_pow_of_prime` / 定理 `cardQuot_pow_of_prime`

English:
theorem cardQuot_pow_of_prime
  given: [IsDedekindDomain S] (hP : P != ⊥) {i : Nat}
  proof: by
  induction i with
  | zero => simp
  | succ i ih => ?_
  have : P ^ (i + 1) < P ^ i := Ideal.pow_succ_lt_pow hP i
  suffices hquot : map (P ^ i.succ).mkQ (P ^ i) ≃ S ⧸ P by
    rw [pow_succ' (cardQuot P)]; rw [← ih]; rw [cardQuot_apply (P ^ i.succ)]; rw [←
      card_quotient_mul_card_quotient (

中文:
定理 cardQuot_pow_of_prime
  条件: [是Dedekind整环 S] (hP : P != ⊥) {i : 自然数}
  证明: by
  induction i with
  | zero => simp
  | succ i ih => ?_
  have : P ^ (i + 1) < P ^ i := Ideal.pow_succ_lt_pow hP i
  suffices hquot : map (P ^ i.succ).mkQ (P ^ i) ≃ S ⧸ P by
    rw [pow_succ' (cardQuot P)]; rw [← ih]; rw [cardQuot_apply (P ^ i.succ)]; rw [←
      card_quotient_mul_card_quotient (

Depends on / 依赖: Ideal.pow_succ_lt_pow, Nat.card_congr, SetLike, SetLike.exists_of_lt, a_mem, a_notMem, cardQuot, cardQuot_apply, card_congr, card_quotient_mul_card_quotient, exists_of_lt, i.succ, pow_succ, pow_succ_lt_pow, this.le
-/
theorem cardQuot_pow_of_prime [IsDedekindDomain S] (hP : P != ⊥) {i : Nat} :
    cardQuot (P ^ i) = cardQuot P ^ i := by
  induction i with
  | zero => simp
  | succ i ih => ?_
  have : P ^ (i + 1) < P ^ i := Ideal.pow_succ_lt_pow hP i
  suffices hquot : map (P ^ i.succ).mkQ (P ^ i) ≃ S ⧸ P by
    rw [pow_succ' (cardQuot P)]; rw [← ih]; rw [cardQuot_apply (P ^ i.succ)]; rw [←
      card_quotient_mul_card_quotient (P ^ i) (P ^ i.succ) this.le]; rw [cardQuot_apply (P ^ i)]; rw [cardQuot_apply P]; rw [Nat.card_congr hquot]
  choose a a_mem a_notMem using SetLike.exists_of_lt this
  choose f g hg hf using fun c (hc : c in P ^ i) =>
    Ideal.exists_mul_add_mem_pow_succ hP a c a_mem a_notMem hc
  choose k hk_mem hk_eq using fun c' (hc' : c' in map (mkQ (P ^ i.succ)) (P ^ i)) =>
    Submodule.mem_map.mp hc'
  refine Equiv.ofBijective (fun c' => Quotient.mk'' (f (k c' c'.prop) (hk_mem c' c'.prop))) ⟨?_, ?_⟩
  · rintro ⟨c₁', hc₁'⟩ ⟨c₂', hc₂'⟩ h
    rw [Subtype.mk_eq_mk]; rw [← hk_eq _ hc₁']; rw [← hk_eq _ hc₂']; rw [mkQ_apply]; rw [mkQ_apply]; rw [Submodule.Quotient.eq]; rw [← hf _ (hk_mem _ hc₁')]; rw [← hf _ (hk_mem _ hc₂')]
    refine Ideal.mul_add_mem_pow_succ_inj _ _ _ _ _ _ a_mem (hg _ _) (hg _ _) ?_
    simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.Quotient.mk''_eq_mk,
      Submodule.Quotient.eq] using h
  · intro d'
    induction d' using Quotient.inductionOn with | _ d
    have hd' := (mem_map (f := mkQ (P ^ i.succ))).mpr ⟨a * d, Ideal.mul_mem_right d _ a_mem, rfl⟩
    refine ⟨⟨_, hd'⟩, ?_⟩
    simp only [Submodule.Quotient.mk''_eq_mk, Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq]
    refine
      Ideal.mul_add_mem_pow_succ_unique hP a _ _ _ _ a_notMem (hg _ (hk_mem _ hd')) (zero_mem _) ?_
    rw [hf]; rw [add_zero]
    exact (Submodule.Quotient.eq _).mp (hk_eq _ hd')

end PPrime

/--
theorem `cardQuot_mul` / 定理 `cardQuot_mul`

English:
theorem cardQuot_mul
  given: [IsDedekindDomain S] [Module.Free Int S] (I J : Ideal S)
  proof: by
  let b := Module.Free.chooseBasis Int S
  have : Infinite S := Infinite.of_surjective _ b.repr.toEquiv.surjective
  exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
      (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
      (fun {I} i h

中文:
定理 cardQuot_mul
  条件: [是Dedekind整环 S] [模.自由 整数 S] (I J : 理想 S)
  证明: by
  let b := Module.Free.chooseBasis Int S
  have : Infinite S := Infinite.of_surjective _ b.repr.toEquiv.surjective
  exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
      (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
      (fun {I} i h

Depends on / 依赖: Ideal.IsPrime, Ideal.dvd_iff_le.mpr, Ideal.isCoprime_iff_sup_eq.mpr, Ideal.isPrime_of_prime, Ideal.isUnit_iff.mp, Ideal.mul_top, Infinite, Infinite.of_surjective, IsPrime, Module, Module.Free.chooseBasis, UniqueFactorizationMonoid, UniqueFactorizationMonoid.multiplicative_of_coprime, b.repr.toEquiv.surjective, cardQuot, cardQuot_bot, cardQuot_mul_of_coprime, cardQuot_pow_of_prime, chooseBasis, dvd_iff_le
-/
theorem cardQuot_mul [IsDedekindDomain S] [Module.Free Int S] (I J : Ideal S) :
    cardQuot (I * J) = cardQuot I * cardQuot J := by
  let b := Module.Free.chooseBasis Int S
  have : Infinite S := Infinite.of_surjective _ b.repr.toEquiv.surjective
  exact UniqueFactorizationMonoid.multiplicative_of_coprime cardQuot I J (cardQuot_bot _ _)
      (fun {I J} hI => by simp [Ideal.isUnit_iff.mp hI, Ideal.mul_top])
      (fun {I} i hI =>
        have : Ideal.IsPrime I := Ideal.isPrime_of_prime hI
        cardQuot_pow_of_prime hI.ne_zero)
fun {I J} hIJ => cardQuot_mul_of_coprime Ideal.isCoprime_iff_sup_eq.mpr
        (Ideal.isUnit_iff.mp
          (hIJ (Ideal.dvd_iff_le.mpr le_sup_left) (Ideal.dvd_iff_le.mpr le_sup_right)))

/--
Definition of `Ideal.absNorm` / `Ideal.absNorm` 的定义

English:
definition Ideal.absNorm
  signature: [IsDedekindDomain S] [Module.Free Int S]
  body: Submodule.cardQuot
  map_mul' I J := by rw [cardQuot_mul]
  map_one' := by rw [Ideal.one_eq_top, cardQuot_top]
  map_zero' := by
    have : Infinite S := Module.Free.infinite Int S
    rw [Ideal.zero_eq_bot]; rw [cardQuot_bot]

中文:
定义 理想.absNorm
  签名: [是Dedekind整环 S] [模.自由 整数 S]
  定义体: Submodule.cardQuot
  map_mul' I J := by rw [cardQuot_mul]
  map_one' := by rw [Ideal.one_eq_top, cardQuot_top]
  map_zero' := by
    have : Infinite S := Module.Free.infinite Int S
    rw [Ideal.zero_eq_bot]; rw [cardQuot_bot]

Depends on / 依赖: Submodule, Submodule.cardQuot, cardQuot
-/
noncomputable def Ideal.absNorm [IsDedekindDomain S] [Module.Free Int S] :
    Ideal S ->*₀ Nat where
  toFun := Submodule.cardQuot
  map_mul' I J := by rw [cardQuot_mul]
  map_one' := by rw [Ideal.one_eq_top, cardQuot_top]
  map_zero' := by
    have : Infinite S := Module.Free.infinite Int S
    rw [Ideal.zero_eq_bot]; rw [cardQuot_bot]

namespace Ideal

variable [IsDedekindDomain S] [Module.Free Int S]

/--
theorem `absNorm_apply` / 定理 `absNorm_apply`

English:
theorem absNorm_apply
  given: (I : Ideal S)
  statement: absNorm I = cardQuot I
  proof: rfl

中文:
定理 absNorm_apply
  条件: (I : 理想 S)
  结论: absNorm I = cardQuot I
  证明: rfl
-/
theorem absNorm_apply (I : Ideal S) : absNorm I = cardQuot I := rfl

/--
lemma `absNorm_eq_index` / 引理 `absNorm_eq_index`

English:
lemma absNorm_eq_index
  given: (I : Ideal S)
  statement: absNorm I = I.toAddSubgroup.index
  proof: rfl

@[simp]

中文:
引理 absNorm_eq_index
  条件: (I : 理想 S)
  结论: absNorm I = I.toAddSubgroup.index
  证明: rfl

@[simp]
-/
lemma absNorm_eq_index (I : Ideal S) : absNorm I = I.toAddSubgroup.index := rfl

@[simp]
/--
theorem `absNorm_bot` / 定理 `absNorm_bot`

English:
theorem absNorm_bot
  statement: absNorm (⊥ : Ideal S) = 0
  proof: by rw [← Ideal.zero_eq_bot, map_zero]

@[simp]

中文:
定理 absNorm_bot
  结论: absNorm (⊥ : 理想 S) = 0
  证明: by rw [← Ideal.zero_eq_bot, map_zero]

@[simp]

Depends on / 依赖: Ideal.zero_eq_bot, map_zero, zero_eq_bot
-/
theorem absNorm_bot : absNorm (⊥ : Ideal S) = 0 := by rw [← Ideal.zero_eq_bot, map_zero]

@[simp]
/--
theorem `absNorm_top` / 定理 `absNorm_top`

English:
theorem absNorm_top
  statement: absNorm (⊤ : Ideal S) = 1
  proof: by rw [← Ideal.one_eq_top, map_one]

@[simp]

中文:
定理 absNorm_top
  结论: absNorm (⊤ : 理想 S) = 1
  证明: by rw [← Ideal.one_eq_top, map_one]

@[simp]

Depends on / 依赖: Ideal.one_eq_top, map_one, one_eq_top
-/
theorem absNorm_top : absNorm (⊤ : Ideal S) = 1 := by rw [← Ideal.one_eq_top, map_one]

@[simp]
/--
theorem `absNorm_eq_one_iff` / 定理 `absNorm_eq_one_iff`

English:
theorem absNorm_eq_one_iff
  given: {I : Ideal S}
  statement: absNorm I = 1 ↔ I = ⊤
  proof: by
  rw [absNorm_apply]; rw [cardQuot_eq_one_iff]

中文:
定理 absNorm_eq_one_iff
  条件: {I : 理想 S}
  结论: absNorm I = 1 ↔ I = ⊤
  证明: by
  rw [absNorm_apply]; rw [cardQuot_eq_one_iff]

Depends on / 依赖: absNorm_apply, cardQuot_eq_one_iff
-/
theorem absNorm_eq_one_iff {I : Ideal S} : absNorm I = 1 ↔ I = ⊤ := by
  rw [absNorm_apply]; rw [cardQuot_eq_one_iff]

/--
theorem `absNorm_ne_zero_iff` / 定理 `absNorm_ne_zero_iff`

English:
theorem absNorm_ne_zero_iff
  given: (I : Ideal S)
  statement: Ideal.absNorm I != 0 ↔ Finite (S ⧸ I)
  proof: ⟨fun h => Nat.finite_of_card_ne_zero h, fun h =>
    (@AddSubgroup.finiteIndex_of_finite_quotient _ _ _ h).index_ne_zero⟩

中文:
定理 absNorm_ne_zero_iff
  条件: (I : 理想 S)
  结论: 理想.absNorm I != 0 ↔ 有限 (S ⧸ I)
  证明: ⟨fun h => Nat.finite_of_card_ne_zero h, fun h =>
    (@AddSubgroup.finiteIndex_of_finite_quotient _ _ _ h).index_ne_zero⟩

Depends on / 依赖: AddSubgroup, AddSubgroup.finiteIndex_of_finite_quotient, Nat.finite_of_card_ne_zero, finiteIndex_of_finite_quotient, finite_of_card_ne_zero, index_ne_zero
-/
theorem absNorm_ne_zero_iff (I : Ideal S) : Ideal.absNorm I != 0 ↔ Finite (S ⧸ I) :=
  ⟨fun h => Nat.finite_of_card_ne_zero h, fun h =>
    (@AddSubgroup.finiteIndex_of_finite_quotient _ _ _ h).index_ne_zero⟩

/--
theorem `absNorm_dvd_absNorm_of_le` / 定理 `absNorm_dvd_absNorm_of_le`

English:
theorem absNorm_dvd_absNorm_of_le
  given: {I J : Ideal S} (h : J <= I)
  statement: Ideal.absNorm I ∣ Ideal.absNorm J
  proof: map_dvd absNorm (dvd_iff_le.mpr h)

中文:
定理 absNorm_dvd_absNorm_of_le
  条件: {I J : 理想 S} (h : J <= I)
  结论: 理想.absNorm I ∣ 理想.absNorm J
  证明: map_dvd absNorm (dvd_iff_le.mpr h)

Depends on / 依赖: absNorm, dvd_iff_le, dvd_iff_le.mpr, map_dvd
-/
theorem absNorm_dvd_absNorm_of_le {I J : Ideal S} (h : J <= I) : Ideal.absNorm I ∣ Ideal.absNorm J :=
  map_dvd absNorm (dvd_iff_le.mpr h)

/--
theorem `irreducible_of_irreducible_absNorm` / 定理 `irreducible_of_irreducible_absNorm`

English:
theorem irreducible_of_irreducible_absNorm
  given: {I : Ideal S} (hI : Irreducible (Ideal.absNorm I))
  proof: irreducible_iff.mpr
    ⟨fun h =>
      hI.not_isUnit (by simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using h),
      by
      rintro a b rfl
      simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using
        hI.isUnit_or_isUnit (map_mul absNorm a b)⟩

中文:
定理 irreducible_of_irreducible_absNorm
  条件: {I : 理想 S} (hI : 不可约 (理想.absNorm I))
  证明: irreducible_iff.mpr
    ⟨fun h =>
      hI.not_isUnit (by simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using h),
      by
      rintro a b rfl
      simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using
        hI.isUnit_or_isUnit (map_mul absNorm a b)⟩

Depends on / 依赖: Ideal.isUnit_iff, Nat.isUnit_iff, absNorm, absNorm_eq_one_iff, hI.isUnit_or_isUnit, hI.not_isUnit, irreducible_iff, irreducible_iff.mpr, isUnit_iff, isUnit_or_isUnit, map_mul, not_isUnit
-/
theorem irreducible_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) :
    Irreducible I :=
  irreducible_iff.mpr
    ⟨fun h =>
      hI.not_isUnit (by simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using h),
      by
      rintro a b rfl
      simpa only [Ideal.isUnit_iff, Nat.isUnit_iff, absNorm_eq_one_iff] using
        hI.isUnit_or_isUnit (map_mul absNorm a b)⟩

/--
theorem `isPrime_of_irreducible_absNorm` / 定理 `isPrime_of_irreducible_absNorm`

English:
theorem isPrime_of_irreducible_absNorm
  given: {I : Ideal S} (hI : Irreducible (Ideal.absNorm I))
  proof: isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_irreducible_absNorm hI))

中文:
定理 isPrime_of_irreducible_absNorm
  条件: {I : 理想 S} (hI : 不可约 (理想.absNorm I))
  证明: isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_irreducible_absNorm hI))

Depends on / 依赖: UniqueFactorizationMonoid, UniqueFactorizationMonoid.irreducible_iff_prime.mp, irreducible_iff_prime, irreducible_of_irreducible_absNorm, isPrime_of_prime
-/
theorem isPrime_of_irreducible_absNorm {I : Ideal S} (hI : Irreducible (Ideal.absNorm I)) :
    I.IsPrime :=
  isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp (irreducible_of_irreducible_absNorm hI))

/--
theorem `prime_of_irreducible_absNorm_span` / 定理 `prime_of_irreducible_absNorm_span`

English:
theorem prime_of_irreducible_absNorm_span
  statement: {a : S} (ha : a != 0)
  proof: (Ideal.span_singleton_prime ha).mp (isPrime_of_irreducible_absNorm hI)

中文:
定理 prime_of_irreducible_absNorm_span
  结论: {a : S} (ha : a != 0)
  证明: (Ideal.span_singleton_prime ha).mp (isPrime_of_irreducible_absNorm hI)

Depends on / 依赖: Ideal.span_singleton_prime, isPrime_of_irreducible_absNorm, span_singleton_prime
-/
theorem prime_of_irreducible_absNorm_span {a : S} (ha : a != 0)
    (hI : Irreducible (Ideal.absNorm (Ideal.span ({a} : Set S)))) : Prime a :=
  (Ideal.span_singleton_prime ha).mp (isPrime_of_irreducible_absNorm hI)

/--
theorem `absNorm_mem` / 定理 `absNorm_mem`

English:
theorem absNorm_mem
  given: (I : Ideal S)
  statement: ↑(Ideal.absNorm I) in I
  proof: by
  rw [absNorm_apply]; rw [cardQuot]; rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [map_natCast]; rw [Quotient.index_eq_zero]

中文:
定理 absNorm_mem
  条件: (I : 理想 S)
  结论: ↑(理想.absNorm I) in I
  证明: by
  rw [absNorm_apply]; rw [cardQuot]; rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [map_natCast]; rw [Quotient.index_eq_zero]

Depends on / 依赖: Ideal.Quotient.eq_zero_iff_mem, Quotient, Quotient.index_eq_zero, absNorm_apply, cardQuot, eq_zero_iff_mem, index_eq_zero, map_natCast
-/
theorem absNorm_mem (I : Ideal S) : ↑(Ideal.absNorm I) in I := by
  rw [absNorm_apply]; rw [cardQuot]; rw [← Ideal.Quotient.eq_zero_iff_mem]; rw [map_natCast]; rw [Quotient.index_eq_zero]

/--
theorem `span_singleton_absNorm_le` / 定理 `span_singleton_absNorm_le`

English:
theorem span_singleton_absNorm_le
  given: (I : Ideal S)
  statement: Ideal.span {(Ideal.absNorm I : S)} <= I
  proof: by
  simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.absNorm_mem I]

中文:
定理 span_singleton_absNorm_le
  条件: (I : 理想 S)
  结论: 理想.span {(理想.absNorm I : S)} <= I
  证明: by
  simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.absNorm_mem I]

Depends on / 依赖: Ideal.absNorm_mem, Ideal.span_le, Set.singleton_subset_iff, SetLike, SetLike.mem_coe, absNorm_mem, mem_coe, singleton_subset_iff, span_le
-/
theorem span_singleton_absNorm_le (I : Ideal S) : Ideal.span {(Ideal.absNorm I : S)} <= I := by
  simp only [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.absNorm_mem I]

/--
theorem `span_singleton_absNorm` / 定理 `span_singleton_absNorm`

English:
theorem span_singleton_absNorm
  given: {I : Ideal S} (hI : (Ideal.absNorm I).Prime)
  proof: by
  have : Ideal.IsPrime (Ideal.span (singleton (Ideal.absNorm I : Int))) := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hI.ne_zero), ← Nat.prime_iff_prime_int]
  apply (this.isMaximal _).eq_of_le
  · exact ((isPrime_of_irreducible_absNorm
      ((Nat.irreducible_iff_nat_prime _).

中文:
定理 span_singleton_absNorm
  条件: {I : 理想 S} (hI : (理想.absNorm I).素)
  证明: by
  have : Ideal.IsPrime (Ideal.span (singleton (Ideal.absNorm I : Int))) := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hI.ne_zero), ← Nat.prime_iff_prime_int]
  apply (this.isMaximal _).eq_of_le
  · exact ((isPrime_of_irreducible_absNorm
      ((Nat.irreducible_iff_nat_prime _).

Depends on / 依赖: Ideal.IsPrime, Ideal.absNorm, Ideal.span, Ideal.span_singleton_prime, Int.ofNat_ne_zero.mpr, IsPrime, Nat.irreducible_iff_nat_prime, Nat.prime_iff_prime_int, absNorm, absNorm_mem, algebraMap, algebraMap_int_eq, eq_of_le, hI.ne_zero, irreducible_iff_nat_prime, isMaximal, isPrime_of_irreducible_absNorm, map_natCast, mem_comap, ne_top
-/
theorem span_singleton_absNorm {I : Ideal S} (hI : (Ideal.absNorm I).Prime) :
    Ideal.span (singleton (Ideal.absNorm I : Int)) = I.comap (algebraMap Int S) := by
  have : Ideal.IsPrime (Ideal.span (singleton (Ideal.absNorm I : Int))) := by
    rwa [Ideal.span_singleton_prime (Int.ofNat_ne_zero.mpr hI.ne_zero), ← Nat.prime_iff_prime_int]
  apply (this.isMaximal _).eq_of_le
  · exact ((isPrime_of_irreducible_absNorm
      ((Nat.irreducible_iff_nat_prime _).mpr hI)).comap (algebraMap Int S)).ne_top
  · rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
    exact absNorm_mem I
  · rw [Ne, span_singleton_eq_bot]
    exact Int.ofNat_ne_zero.mpr hI.ne_zero

variable [Module.Finite Int S]

/--
theorem `natAbs_det_equiv` / 定理 `natAbs_det_equiv`

English:
theorem natAbs_det_equiv
  given: (I : Ideal S) {E : Type*} [EquivLike E S I] [AddEquivClass E S I] (e : E)
  proof: by
  -- `S ⧸ I` might be infinite if `I = ⊥`, but then `e` can't be an equiv.
  by_cases hI : I = ⊥
  · subst hI
    have : (1 : S) != 0 := one_ne_zero
    have : (1 : S) = 0 := EquivLike.injective e (Subsingleton.elim _ _)
    contradiction
  exact Submodule.natAbs_det_equiv (I.restrictScalars Int)

中文:
定理 natAbs_det_equiv
  条件: (I : 理想 S) {E : 类型} [等价状 E S I] [加法等价类 E S I] (e : E)
  证明: by
  -- `S ⧸ I` might be infinite if `I = ⊥`, but then `e` can't be an equiv.
  by_cases hI : I = ⊥
  · subst hI
    have : (1 : S) != 0 := one_ne_zero
    have : (1 : S) = 0 := EquivLike.injective e (Subsingleton.elim _ _)
    contradiction
  exact Submodule.natAbs_det_equiv (I.restrictScalars Int)
-/
theorem natAbs_det_equiv (I : Ideal S) {E : Type*} [EquivLike E S I] [AddEquivClass E S I] (e : E) :
    Int.natAbs
        (LinearMap.det
          ((Submodule.subtype I).restrictScalars Int ∘ₗ AddMonoidHom.toIntLinearMap (e : S ->+ I))) =
      Ideal.absNorm I := by
  -- `S ⧸ I` might be infinite if `I = ⊥`, but then `e` can't be an equiv.
  by_cases hI : I = ⊥
  · subst hI
    have : (1 : S) != 0 := one_ne_zero
    have : (1 : S) = 0 := EquivLike.injective e (Subsingleton.elim _ _)
    contradiction
  exact Submodule.natAbs_det_equiv (I.restrictScalars Int) e

/--
theorem `natAbs_det_basis_change` / 定理 `natAbs_det_basis_change`

English:
theorem natAbs_det_basis_change
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int S)
  proof: Submodule.natAbs_det_basis_change b (I.restrictScalars Int) bI

@[simp]

中文:
定理 natAbs_det_basis_change
  结论: {ι : 类型} [有限类型 ι] [DecidableEq ι] (b : 基 ι 整数 S)
  证明: Submodule.natAbs_det_basis_change b (I.restrictScalars Int) bI

@[simp]

Depends on / 依赖: I.restrictScalars, Submodule, Submodule.natAbs_det_basis_change, natAbs_det_basis_change, restrictScalars
-/
theorem natAbs_det_basis_change {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι Int S)
    (I : Ideal S) (bI : Basis ι Int I) : (b.det ((↑) ∘ bI)).natAbs = Ideal.absNorm I :=
  Submodule.natAbs_det_basis_change b (I.restrictScalars Int) bI

@[simp]
/--
theorem `absNorm_span_singleton` / 定理 `absNorm_span_singleton`

English:
theorem absNorm_span_singleton
  given: (r : S)
  proof: by
  rw [Algebra.norm_apply]
  by_cases hr : r = 0
  · simp only [hr, Ideal.span_zero, Ideal.absNorm_bot,
      LinearMap.det_zero'', Set.singleton_zero, map_zero, Int.natAbs_zero]
  let b := Module.Free.chooseBasis Int S
  rw [← natAbs_det_equiv _ (b.equiv (basisSpanSingleton b hr) (Equiv.refl _))]

中文:
定理 absNorm_span_singleton
  条件: (r : S)
  证明: by
  rw [Algebra.norm_apply]
  by_cases hr : r = 0
  · simp only [hr, Ideal.span_zero, Ideal.absNorm_bot,
      LinearMap.det_zero'', Set.singleton_zero, map_zero, Int.natAbs_zero]
  let b := Module.Free.chooseBasis Int S
  rw [← natAbs_det_equiv _ (b.equiv (basisSpanSingleton b hr) (Equiv.refl _))]

Depends on / 依赖: Algebra, Algebra.norm_apply, Equiv.refl, Ideal.absNorm_bot, Ideal.span_zero, Int.natAbs_zero, LinearMap, LinearMap.det_zero, Module, Module.Free.chooseBasis, Set.singleton_zero, absNorm_bot, b.equiv, b.ext, basisSpanSingleton, chooseBasis, det_zero, map_zero, natAbs_det_equiv, natAbs_zero
-/
theorem absNorm_span_singleton (r : S) :
    absNorm (span ({r} : Set S)) = (Algebra.norm Int r).natAbs := by
  rw [Algebra.norm_apply]
  by_cases hr : r = 0
  · simp only [hr, Ideal.span_zero, Ideal.absNorm_bot,
      LinearMap.det_zero'', Set.singleton_zero, map_zero, Int.natAbs_zero]
  let b := Module.Free.chooseBasis Int S
  rw [← natAbs_det_equiv _ (b.equiv (basisSpanSingleton b hr) (Equiv.refl _))]
  congr
  refine b.ext fun i => ?_
  simp

/--
lemma `absNorm_span_natCast` / 引理 `absNorm_span_natCast`

English:
lemma absNorm_span_natCast
  given: (n : Nat)
  statement: (span {(n : S)}).absNorm = n ^ Module.finrank Int S
  proof: by
  simp [absNorm_span_singleton, Algebra.norm_natCast]

中文:
引理 absNorm_span_natCast
  条件: (n : 自然数)
  结论: (span {(n : S)}).absNorm = n ^ 模.finrank 整数 S
  证明: by
  simp [absNorm_span_singleton, Algebra.norm_natCast]

Depends on / 依赖: Algebra, Algebra.norm_natCast, absNorm_span_singleton, norm_natCast
-/
lemma absNorm_span_natCast (n : Nat) : (span {(n : S)}).absNorm = n ^ Module.finrank Int S := by
  simp [absNorm_span_singleton, Algebra.norm_natCast]

/--
theorem `absNorm_dvd_norm_of_mem` / 定理 `absNorm_dvd_norm_of_mem`

English:
theorem absNorm_dvd_norm_of_mem
  given: {I : Ideal S} {x : S} (h : x in I)
  proof: by
  rw [← Int.dvd_natAbs]; rw [← absNorm_span_singleton x]; rw [Int.natCast_dvd_natCast]
  exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr h)

@[simp]

中文:
定理 absNorm_dvd_norm_of_mem
  条件: {I : 理想 S} {x : S} (h : x in I)
  证明: by
  rw [← Int.dvd_natAbs]; rw [← absNorm_span_singleton x]; rw [Int.natCast_dvd_natCast]
  exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr h)

@[simp]

Depends on / 依赖: Int.dvd_natAbs, Int.natCast_dvd_natCast, absNorm_dvd_absNorm_of_le, absNorm_span_singleton, dvd_natAbs, natCast_dvd_natCast, span_singleton_le_iff_mem
-/
theorem absNorm_dvd_norm_of_mem {I : Ideal S} {x : S} (h : x in I) :
    ↑(Ideal.absNorm I) ∣ Algebra.norm Int x := by
  rw [← Int.dvd_natAbs]; rw [← absNorm_span_singleton x]; rw [Int.natCast_dvd_natCast]
  exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem _).mpr h)

@[simp]
/--
theorem `absNorm_span_insert` / 定理 `absNorm_span_insert`

English:
theorem absNorm_span_insert
  given: (r : S) (s : Set S)
  proof: (dvd_gcd_iff _ _ _).mpr
    ⟨absNorm_dvd_absNorm_of_le (span_mono (Set.subset_insert _ _)),
      _root_.trans
        (absNorm_dvd_absNorm_of_le (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))))
        (by rw [absNorm_span_singleton])⟩

中文:
定理 absNorm_span_insert
  条件: (r : S) (s : 集合 S)
  证明: (dvd_gcd_iff _ _ _).mpr
    ⟨absNorm_dvd_absNorm_of_le (span_mono (Set.subset_insert _ _)),
      _root_.trans
        (absNorm_dvd_absNorm_of_le (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))))
        (by rw [absNorm_span_singleton])⟩

Depends on / 依赖: Set.mem_insert, Set.singleton_subset_iff.mpr, Set.subset_insert, _root_, _root_.trans, absNorm_dvd_absNorm_of_le, absNorm_span_singleton, dvd_gcd_iff, mem_insert, singleton_subset_iff, span_mono, subset_insert
-/
theorem absNorm_span_insert (r : S) (s : Set S) :
    absNorm (span (insert r s)) ∣ gcd (absNorm (span s)) (Algebra.norm Int r).natAbs :=
  (dvd_gcd_iff _ _ _).mpr
    ⟨absNorm_dvd_absNorm_of_le (span_mono (Set.subset_insert _ _)),
      _root_.trans
        (absNorm_dvd_absNorm_of_le (span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))))
        (by rw [absNorm_span_singleton])⟩

/--
theorem `absNorm_eq_zero_iff` / 定理 `absNorm_eq_zero_iff`

English:
theorem absNorm_eq_zero_iff
  given: {I : Ideal S}
  statement: Ideal.absNorm I = 0 ↔ I = ⊥
  proof: by
  constructor
  · intro hI
    rw [← le_bot_iff]
    intro x hx
    rw [mem_bot]; rw [← Algebra.norm_eq_zero_iff (R := Int)]; rw [← Int.natAbs_eq_zero]; rw [← Ideal.absNorm_span_singleton]; rw [← zero_dvd_iff]; rw [← hI]
    apply Ideal.absNorm_dvd_absNorm_of_le
    rwa [Ideal.span_singleton_le_i

中文:
定理 absNorm_eq_zero_iff
  条件: {I : 理想 S}
  结论: 理想.absNorm I = 0 ↔ I = ⊥
  证明: by
  constructor
  · intro hI
    rw [← le_bot_iff]
    intro x hx
    rw [mem_bot]; rw [← Algebra.norm_eq_zero_iff (R := Int)]; rw [← Int.natAbs_eq_zero]; rw [← Ideal.absNorm_span_singleton]; rw [← zero_dvd_iff]; rw [← hI]
    apply Ideal.absNorm_dvd_absNorm_of_le
    rwa [Ideal.span_singleton_le_i

Depends on / 依赖: Algebra, Algebra.norm_eq_zero_iff, Ideal.absNorm_dvd_absNorm_of_le, Ideal.absNorm_span_singleton, Ideal.span_singleton_le_iff_mem, Int.natAbs_eq_zero, absNorm_bot, absNorm_dvd_absNorm_of_le, absNorm_span_singleton, le_bot_iff, mem_bot, natAbs_eq_zero, norm_eq_zero_iff, span_singleton_le_iff_mem, zero_dvd_iff
-/
theorem absNorm_eq_zero_iff {I : Ideal S} : Ideal.absNorm I = 0 ↔ I = ⊥ := by
  constructor
  · intro hI
    rw [← le_bot_iff]
    intro x hx
    rw [mem_bot]; rw [← Algebra.norm_eq_zero_iff (R := Int)]; rw [← Int.natAbs_eq_zero]; rw [← Ideal.absNorm_span_singleton]; rw [← zero_dvd_iff]; rw [← hI]
    apply Ideal.absNorm_dvd_absNorm_of_le
    rwa [Ideal.span_singleton_le_iff_mem]
  · rintro rfl
    exact absNorm_bot

/--
theorem `absNorm_ne_zero_iff_mem_nonZeroDivisors` / 定理 `absNorm_ne_zero_iff_mem_nonZeroDivisors`

English:
theorem absNorm_ne_zero_iff_mem_nonZeroDivisors
  given: {I : Ideal S}
  proof: by
  simp_rw [ne_eq, Ideal.absNorm_eq_zero_iff, mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot]

中文:
定理 absNorm_ne_zero_iff_mem_nonZeroDivisors
  条件: {I : 理想 S}
  证明: by
  simp_rw [ne_eq, Ideal.absNorm_eq_zero_iff, mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot]

Depends on / 依赖: Ideal.absNorm_eq_zero_iff, Submodule, Submodule.zero_eq_bot, absNorm_eq_zero_iff, mem_nonZeroDivisors_iff_ne_zero, ne_eq, simp_rw, zero_eq_bot
-/
theorem absNorm_ne_zero_iff_mem_nonZeroDivisors {I : Ideal S} :
    absNorm I != 0 ↔ I in (Ideal S)⁰ := by
  simp_rw [ne_eq, Ideal.absNorm_eq_zero_iff, mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot]

/--
theorem `absNorm_pos_iff_mem_nonZeroDivisors` / 定理 `absNorm_pos_iff_mem_nonZeroDivisors`

English:
theorem absNorm_pos_iff_mem_nonZeroDivisors
  given: {I : Ideal S}
  proof: by
  rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors]; rw [Nat.pos_iff_ne_zero]

中文:
定理 absNorm_pos_iff_mem_nonZeroDivisors
  条件: {I : 理想 S}
  证明: by
  rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors]; rw [Nat.pos_iff_ne_zero]

Depends on / 依赖: Nat.pos_iff_ne_zero, absNorm_ne_zero_iff_mem_nonZeroDivisors, pos_iff_ne_zero
-/
theorem absNorm_pos_iff_mem_nonZeroDivisors {I : Ideal S} :
    0 < absNorm I ↔ I in (Ideal S)⁰ := by
  rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors]; rw [Nat.pos_iff_ne_zero]

/--
theorem `absNorm_ne_zero_of_nonZeroDivisors` / 定理 `absNorm_ne_zero_of_nonZeroDivisors`

English:
theorem absNorm_ne_zero_of_nonZeroDivisors
  given: (I : (Ideal S)⁰)
  statement: absNorm (I : Ideal S) != 0
  proof: absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)

中文:
定理 absNorm_ne_zero_of_nonZeroDivisors
  条件: (I : (理想 S)⁰)
  结论: absNorm (I : 理想 S) != 0
  证明: absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)

Depends on / 依赖: SetLike, SetLike.coe_mem, absNorm_ne_zero_iff_mem_nonZeroDivisors, absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr, coe_mem
-/
theorem absNorm_ne_zero_of_nonZeroDivisors (I : (Ideal S)⁰) : absNorm (I : Ideal S) != 0 :=
  absNorm_ne_zero_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)

/--
theorem `absNorm_pos_of_nonZeroDivisors` / 定理 `absNorm_pos_of_nonZeroDivisors`

English:
theorem absNorm_pos_of_nonZeroDivisors
  given: (I : (Ideal S)⁰)
  statement: 0 < absNorm (I : Ideal S)
  proof: absNorm_pos_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)

中文:
定理 absNorm_pos_of_nonZeroDivisors
  条件: (I : (理想 S)⁰)
  结论: 0 < absNorm (I : 理想 S)
  证明: absNorm_pos_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)

Depends on / 依赖: SetLike, SetLike.coe_mem, absNorm_pos_iff_mem_nonZeroDivisors, absNorm_pos_iff_mem_nonZeroDivisors.mpr, coe_mem
-/
theorem absNorm_pos_of_nonZeroDivisors (I : (Ideal S)⁰) : 0 < absNorm (I : Ideal S) :=
  absNorm_pos_iff_mem_nonZeroDivisors.mpr (SetLike.coe_mem I)

/--
lemma `finiteIndex` / 引理 `finiteIndex`

English:
lemma finiteIndex
  given: {I : Ideal S} (hI : I != ⊥)
  statement: I.toAddSubgroup.FiniteIndex
  proof: by
  rwa [AddSubgroup.finiteIndex_iff, ← absNorm_eq_index, Ne, absNorm_eq_zero_iff]

中文:
引理 finiteIndex
  条件: {I : 理想 S} (hI : I != ⊥)
  结论: I.toAddSubgroup.FiniteIndex
  证明: by
  rwa [AddSubgroup.finiteIndex_iff, ← absNorm_eq_index, Ne, absNorm_eq_zero_iff]

Depends on / 依赖: AddSubgroup, AddSubgroup.finiteIndex_iff, absNorm_eq_index, absNorm_eq_zero_iff, finiteIndex_iff
-/
lemma finiteIndex {I : Ideal S} (hI : I != ⊥) : I.toAddSubgroup.FiniteIndex := by
  rwa [AddSubgroup.finiteIndex_iff, ← absNorm_eq_index, Ne, absNorm_eq_zero_iff]

open AddSubgroup in
/--
lemma `isFiniteRelIndex` / 引理 `isFiniteRelIndex`

English:
lemma isFiniteRelIndex
  given: {I : Ideal S} (hI : I != ⊥) (J : Ideal S)
  proof: by
  have := finiteIndex hI
  exact isFiniteRelIndex_of_finiteIndex

中文:
引理 isFiniteRelIndex
  条件: {I : 理想 S} (hI : I != ⊥) (J : 理想 S)
  证明: by
  have := finiteIndex hI
  exact isFiniteRelIndex_of_finiteIndex

Depends on / 依赖: finiteIndex, isFiniteRelIndex_of_finiteIndex
-/
lemma isFiniteRelIndex {I : Ideal S} (hI : I != ⊥) (J : Ideal S) :
    I.toAddSubgroup.IsFiniteRelIndex J.toAddSubgroup := by
  have := finiteIndex hI
  exact isFiniteRelIndex_of_finiteIndex

/--
lemma `exists_prime_and_absNorm_eq_pow` / 引理 `exists_prime_and_absNorm_eq_pow`

English:
lemma exists_prime_and_absNorm_eq_pow
  given: (P : Ideal S) [P.IsMaximal]
  proof: by
  have : IsAddTorsionFree S := .of_isTorsionFree Int _
  have := CharZero.of_isAddTorsionFree S S
  have : Finite (S ⧸ P) := Submodule.finiteQuotientOfFreeOfRankEq (P.restrictScalars Int)
    (Ideal.finrank_eq_finrank (Module.Free.chooseBasis _ _) _
      (Ideal.IsMaximal.ne_bot_of_isIntegral_int

中文:
引理 存在_prime_and_absNorm_eq_pow
  条件: (P : 理想 S) [P.是极大]
  证明: by
  have : IsAddTorsionFree S := .of_isTorsionFree Int _
  have := CharZero.of_isAddTorsionFree S S
  have : Finite (S ⧸ P) := Submodule.finiteQuotientOfFreeOfRankEq (P.restrictScalars Int)
    (Ideal.finrank_eq_finrank (Module.Free.chooseBasis _ _) _
      (Ideal.IsMaximal.ne_bot_of_isIntegral_int

Depends on / 依赖: CharP.exists, CharZero, CharZero.of_isAddTorsionFree, Finite, FiniteField, FiniteField.card, Ideal.IsMaximal.ne_bot_of_isIntegral_int, Ideal.Quotient.field, Ideal.finrank_eq_finrank, IsAddTorsionFree, IsMaximal, Module, Module.Free.chooseBasis, Nat.card_eq_fintype_ca, P.absNorm, P.restrictScalars, Quotient, Submodule, Submodule.finiteQuotientOfFreeOfRankEq, absNorm
-/
lemma exists_prime_and_absNorm_eq_pow (P : Ideal S) [P.IsMaximal] :
    exists p n, 0 < n ∧ ↑p in P ∧ p.Prime ∧ P.absNorm = p ^ n := by
  have : IsAddTorsionFree S := .of_isTorsionFree Int _
  have := CharZero.of_isAddTorsionFree S S
  have : Finite (S ⧸ P) := Submodule.finiteQuotientOfFreeOfRankEq (P.restrictScalars Int)
    (Ideal.finrank_eq_finrank (Module.Free.chooseBasis _ _) _
      (Ideal.IsMaximal.ne_bot_of_isIntegral_int P))
  cases nonempty_fintype (S ⧸ P)
  let := Ideal.Quotient.field P
  obtain ⟨p, hpR⟩ := CharP.exists (S ⧸ P)
  obtain ⟨n, hp, e⟩ := FiniteField.card (S ⧸ P) p
  have hP : P.absNorm = p ^ (n : Nat) := (Nat.card_eq_fintype_card.trans e:)
  refine ⟨p, n, n.2, ?_, hp, hP⟩
  rw [← Ideal.IsPrime.pow_mem_iff_mem (I := P) inferInstance _ n.pos]; rw [← Nat.cast_pow]; rw [← hP]
  exact P.absNorm_mem

/--
lemma `exists_isMaximal_dvd_of_dvd_absNorm` / 引理 `exists_isMaximal_dvd_of_dvd_absNorm`

English:
lemma exists_isMaximal_dvd_of_dvd_absNorm
  proof: by
  have : IsAddTorsionFree S := .of_isTorsionFree Int _
  have := CharZero.of_isAddTorsionFree S S
  have hpMax : (Ideal.span {p}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  induction I using UniqueFactorizationMonoid.induction_on_prim

中文:
引理 存在_isMaximal_dvd_of_dvd_absNorm
  证明: by
  have : IsAddTorsionFree S := .of_isTorsionFree Int _
  have := CharZero.of_isAddTorsionFree S S
  have hpMax : (Ideal.span {p}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  induction I using UniqueFactorizationMonoid.induction_on_prim

Depends on / 依赖: CharZero, CharZero.of_isAddTorsionFree, Ideal.exists_ideal_over_maximal_of_isIntegral, Ideal.span, Ideal.span_singleton_prime, IsAddTorsionFree, IsMaximal, UniqueFactorizationMonoid, UniqueFactorizationMonoid.induction_on_prime, contextual, dvd_zero, exists_ideal_over_maximal_of_isIntegral, hp.ne_zero, induction_on_prime, isMaximal, ne_zero, of_isAddTorsionFree, of_isTorsionFree, span_singleton_prime
-/
lemma exists_isMaximal_dvd_of_dvd_absNorm
    {p : Int} (hp : Prime p) (I : Ideal S) (hI : p ∣ I.absNorm) :
    exists P : Ideal S, P.IsMaximal ∧ P.under Int = .span {p} ∧ P ∣ I := by
  have : IsAddTorsionFree S := .of_isTorsionFree Int _
  have := CharZero.of_isAddTorsionFree S S
  have hpMax : (Ideal.span {p}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).mpr hp).isMaximal (by simpa using hp.ne_zero)
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    obtain ⟨Q, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S) (Ideal.span {p})
      (fun x => by simp +contextual)
    exact ⟨Q, hQ, e, dvd_zero _⟩
  | h₂ I hI' =>
    obtain rfl : I = ⊤ := by simpa using hI'
    cases hp.not_dvd_one (by simpa using hI)
  | h₃ I P hI' hP IH =>
    simp only [_root_.map_mul, Nat.cast_mul, hp.dvd_mul] at hI
    cases hI with
    | inr h =>
      obtain ⟨Q, h₁, h₂, h₃⟩ := IH h
      exact ⟨Q, h₁, h₂, dvd_mul_of_dvd_right h₃ _⟩
    | inl hI =>
      have := (Ideal.isPrime_of_prime hP).isMaximal hP.ne_zero
      refine ⟨P, this, (hpMax.eq_of_le (by simpa using this.ne_top) ?_).symm, dvd_mul_right _ _⟩
      obtain ⟨q, n, hn, hqP, hq, H⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
      rw [H]; rw [Nat.cast_pow]; rw [dvd_prime_pow (Nat.prime_iff_prime_int.mp hq)] at hI
      obtain ⟨m, hmn, hp⟩ := hI
      rw [Ideal.span_singleton_le_iff_mem]
      have : m != 0 := fun h => hpMax.ne_top (Ideal.span_singleton_eq_top.mpr (by simpa [h] using hp))
      exact Ideal.mem_of_dvd _ hp.symm.dvd (Ideal.pow_mem_of_mem _ (by simpa) _ this.bot_lt)

/--
lemma `exists_isMaximal_dvd_of_dvd_absNorm'` / 引理 `exists_isMaximal_dvd_of_dvd_absNorm'`

English:
lemma exists_isMaximal_dvd_of_dvd_absNorm'
  proof: exists_isMaximal_dvd_of_dvd_absNorm (Int.prime_iff_natAbs_prime.mpr (by simpa)) _
    (by exact_mod_cast hI)

中文:
引理 存在_isMaximal_dvd_of_dvd_absNorm'
  证明: exists_isMaximal_dvd_of_dvd_absNorm (Int.prime_iff_natAbs_prime.mpr (by simpa)) _
    (by exact_mod_cast hI)

Depends on / 依赖: Int.prime_iff_natAbs_prime.mpr, exists_isMaximal_dvd_of_dvd_absNorm, prime_iff_natAbs_prime
-/
lemma exists_isMaximal_dvd_of_dvd_absNorm'
    {p : Nat} (hp : p.Prime) (I : Ideal S) (hI : p ∣ I.absNorm) :
    exists P : Ideal S, P.IsMaximal ∧ P.under Int = .span {(p : Int)} ∧ P ∣ I :=
  exists_isMaximal_dvd_of_dvd_absNorm (Int.prime_iff_natAbs_prime.mpr (by simpa)) _
    (by exact_mod_cast hI)

/--
theorem `finite_setOfPred_absNorm_eq` / 定理 `finite_setOfPred_absNorm_eq`

English:
theorem finite_setOfPred_absNorm_eq
  given: [CharZero S] (n : Nat)
  proof: by
  obtain hn | hn := Nat.eq_zero_or_pos n
  · simp only [hn, absNorm_eq_zero_iff, Set.ofPred_eq_eq_singleton, Set.finite_singleton]
  · let f := fun I : Ideal S => Ideal.map (Ideal.Quotient.mk (@Ideal.span S _ {↑n})) I
    refine Set.Finite.of_finite_image (f := f) ?_ ?_
    · suffices Finite (S ⧸

中文:
定理 finite_setOfPred_absNorm_eq
  条件: [特征零 S] (n : 自然数)
  证明: by
  obtain hn | hn := Nat.eq_zero_or_pos n
  · simp only [hn, absNorm_eq_zero_iff, Set.ofPred_eq_eq_singleton, Set.finite_singleton]
  · let f := fun I : Ideal S => Ideal.map (Ideal.Quotient.mk (@Ideal.span S _ {↑n})) I
    refine Set.Finite.of_finite_image (f := f) ?_ ?_
    · suffices Finite (S ⧸

Depends on / 依赖: Finite, Ideal.Quotient.mk, Ideal.map, Ideal.span, Nat.eq_zero_or_pos, Quotient, Set.Finite.of_finite_image, Set.Finite.subset, Set.fi, Set.finite_singleton, Set.ofPred_eq_eq_singleton, SetLike, SetLike.coe_injective.injOn, absNorm_eq_zero_iff, coe_injective, eq_zero_or_pos, finite_singleton, ofPred_eq_eq_singleton, of_finite_image, subset
-/
theorem finite_setOfPred_absNorm_eq [CharZero S] (n : Nat) :
    {I : Ideal S | Ideal.absNorm I = n}.Finite := by
  obtain hn | hn := Nat.eq_zero_or_pos n
  · simp only [hn, absNorm_eq_zero_iff, Set.ofPred_eq_eq_singleton, Set.finite_singleton]
  · let f := fun I : Ideal S => Ideal.map (Ideal.Quotient.mk (@Ideal.span S _ {↑n})) I
    refine Set.Finite.of_finite_image (f := f) ?_ ?_
    · suffices Finite (S ⧸ @Ideal.span S _ {↑n}) by
        let g := ((↑) : Ideal (S ⧸ @Ideal.span S _ {↑n}) -> Set (S ⧸ @Ideal.span S _ {↑n}))
        refine Set.Finite.of_finite_image (f := g) ?_ SetLike.coe_injective.injOn
        exact Set.Finite.subset Set.finite_univ (Set.subset_univ _)
      rw [← absNorm_ne_zero_iff]; rw [absNorm_span_singleton]
      simpa only [Ne, Int.natAbs_eq_zero, Algebra.norm_eq_zero_iff, Nat.cast_eq_zero] using
        ne_of_gt hn
    · intro I hI J hJ h
      rw [← comap_map_mk (span_singleton_absNorm_le I)]; rw [← hI.symm]; rw [←
        comap_map_mk (span_singleton_absNorm_le J)]; rw [← hJ.symm]
      congr

@[deprecated (since := "2026-07-09")] alias finite_setOf_absNorm_eq := finite_setOfPred_absNorm_eq

/--
theorem `finite_setOfPred_absNorm_le` / 定理 `finite_setOfPred_absNorm_le`

English:
theorem finite_setOfPred_absNorm_le
  given: [CharZero S] (n : Nat)
  proof: by
  rw [show {I : Ideal S | Ideal.absNorm I <= n} =
    (⋃ i in Set.Icc 0 n]; rw [{I : Ideal S | Ideal.absNorm I = i}) by ext; simp]
  refine Set.Finite.biUnion (Set.finite_Icc 0 n) (fun i _ => Ideal.finite_setOfPred_absNorm_eq i)

@[deprecated (since := "2026-07-09")] alias finite_setOf_absNorm_le

中文:
定理 finite_setOfPred_absNorm_le
  条件: [特征零 S] (n : 自然数)
  证明: by
  rw [show {I : Ideal S | Ideal.absNorm I <= n} =
    (⋃ i in Set.Icc 0 n]; rw [{I : Ideal S | Ideal.absNorm I = i}) by ext; simp]
  refine Set.Finite.biUnion (Set.finite_Icc 0 n) (fun i _ => Ideal.finite_setOfPred_absNorm_eq i)

@[deprecated (since := "2026-07-09")] alias finite_setOf_absNorm_le

Depends on / 依赖: Finite, Ideal.absNorm, Ideal.finite_setOfPred_absNorm_eq, Set.Finite.biUnion, Set.Icc, Set.finite_Icc, absNorm, biUnion, finite_Icc, finite_setOfPred_absNorm_eq
-/
theorem finite_setOfPred_absNorm_le [CharZero S] (n : Nat) :
    {I : Ideal S | Ideal.absNorm I <= n}.Finite := by
  rw [show {I : Ideal S | Ideal.absNorm I <= n} =
    (⋃ i in Set.Icc 0 n]; rw [{I : Ideal S | Ideal.absNorm I = i}) by ext; simp]
  refine Set.Finite.biUnion (Set.finite_Icc 0 n) (fun i _ => Ideal.finite_setOfPred_absNorm_eq i)

@[deprecated (since := "2026-07-09")] alias finite_setOf_absNorm_le := finite_setOfPred_absNorm_le

/--
theorem `finite_setOfPred_absNorm_le₀` / 定理 `finite_setOfPred_absNorm_le₀`

English:
theorem finite_setOfPred_absNorm_le₀
  given: [CharZero S] (n : Nat)
  proof: by
  have : Finite {I : Ideal S // I in (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  exact Finite.of_equiv _ (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun I => absNorm I <= n)).symm

@[deprecated (since := "2026-07-09")]
alias finite_setOf_absNorm_le

中文:
定理 finite_setOfPred_absNorm_le₀
  条件: [特征零 S] (n : 自然数)
  证明: by
  have : Finite {I : Ideal S // I in (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  exact Finite.of_equiv _ (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun I => absNorm I <= n)).symm

@[deprecated (since := "2026-07-09")]
alias finite_setOf_absNorm_le

Depends on / 依赖: Equiv.subtypeSubtypeEquivSubtypeInter, Finite, Finite.of_equiv, absNorm, finite_setOfPred_absNorm_le, of_equiv, subset, subtypeSubtypeEquivSubtypeInter
-/
theorem finite_setOfPred_absNorm_le₀ [CharZero S] (n : Nat) :
    {I : (Ideal S)⁰ | Ideal.absNorm (I : Ideal S) <= n}.Finite := by
  have : Finite {I : Ideal S // I in (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  exact Finite.of_equiv _ (Equiv.subtypeSubtypeEquivSubtypeInter _ (fun I => absNorm I <= n)).symm

@[deprecated (since := "2026-07-09")]
alias finite_setOf_absNorm_le₀ := finite_setOfPred_absNorm_le₀

/--
theorem `card_norm_le_eq_card_norm_le_add_one` / 定理 `card_norm_le_eq_card_norm_le_add_one`

English:
theorem card_norm_le_eq_card_norm_le_add_one
  given: (n : Nat) [CharZero S]
  proof: by
  classical
  have : Finite {I : Ideal S // I in (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  have : Finite {I : Ideal S // I ∉ (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  rw [Nat.card_congr (Equi

中文:
定理 card_norm_le_eq_card_norm_le_add_one
  条件: (n : 自然数) [特征零 S]
  证明: by
  classical
  have : Finite {I : Ideal S // I in (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  have : Finite {I : Ideal S // I ∉ (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  rw [Nat.card_congr (Equi

Depends on / 依赖: Equiv.subtypeSubtypeEquivSubtypeInter, Finite, Nat.card_congr, absNorm, card_congr, classical, finite_setOfPred_absNorm_le, subset, subtypeSubtypeEquivSubtypeInter
-/
theorem card_norm_le_eq_card_norm_le_add_one (n : Nat) [CharZero S] :
    Nat.card {I : Ideal S // absNorm I <= n} =
      Nat.card {I : (Ideal S)⁰ // absNorm (I : Ideal S) <= n} + 1 := by
  classical
  have : Finite {I : Ideal S // I in (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  have : Finite {I : Ideal S // I ∉ (Ideal S)⁰ ∧ absNorm I <= n} :=
    (finite_setOfPred_absNorm_le n).subset fun _ ⟨_, h⟩ => h
  rw [Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter (fun I => I in (Ideal S)⁰)
    (fun I => absNorm I <= n))]
  let e : {I : Ideal S // absNorm I <= n} ≃ {I : Ideal S // I in (Ideal S)⁰ ∧ absNorm I <= n} oplus
      {I : Ideal S // I ∉ (Ideal S)⁰ ∧ absNorm I <= n} := by
    refine (Equiv.subtypeEquivRight ?_).trans (subtypeOrEquiv _ _ ?_)
    · intro _
      simp_rw [← or_and_right, em, true_and]
    · exact Pi.disjoint_iff.mpr fun I => Prop.disjoint_iff.mpr (by tauto)
  simp_rw [Nat.card_congr e, Nat.card_sum, add_right_inj]
  conv_lhs =>
    enter [1, 1, I]
    rw [← absNorm_ne_zero_iff_mem_nonZeroDivisors]; rw [ne_eq]; rw [not_not]; rw [and_iff_left_iff_imp.mpr
      (fun h => by rw [h]; exact Nat.zero_le n), absNorm_eq_zero_iff]
  rw [Nat.card_unique]

/--
theorem `norm_dvd_iff` / 定理 `norm_dvd_iff`

English:
theorem norm_dvd_iff
  given: {x : S} (hx : Prime (Algebra.norm Int x)) {y : Int}
  proof: by
  rw [← Ideal.mem_span_singleton (y := x)]; rw [← eq_intCast (algebraMap Int S)]; rw [← Ideal.mem_comap]; rw [← Ideal.span_singleton_absNorm]; rw [Ideal.mem_span_singleton]; rw [Ideal.absNorm_span_singleton]; rw [Int.natAbs_dvd]
  rwa [Ideal.absNorm_span_singleton, ← Int.prime_iff_natAbs_prime]

中文:
定理 norm_dvd_iff
  条件: {x : S} (hx : 素 (代数.norm 整数 x)) {y : 整数}
  证明: by
  rw [← Ideal.mem_span_singleton (y := x)]; rw [← eq_intCast (algebraMap Int S)]; rw [← Ideal.mem_comap]; rw [← Ideal.span_singleton_absNorm]; rw [Ideal.mem_span_singleton]; rw [Ideal.absNorm_span_singleton]; rw [Int.natAbs_dvd]
  rwa [Ideal.absNorm_span_singleton, ← Int.prime_iff_natAbs_prime]

Depends on / 依赖: Ideal.absNorm_span_singleton, Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.span_singleton_absNorm, Int.natAbs_dvd, Int.prime_iff_natAbs_prime, absNorm_span_singleton, algebraMap, eq_intCast, mem_comap, mem_span_singleton, natAbs_dvd, prime_iff_natAbs_prime, span_singleton_absNorm
-/
theorem norm_dvd_iff {x : S} (hx : Prime (Algebra.norm Int x)) {y : Int} :
    Algebra.norm Int x ∣ y ↔ x ∣ y := by
  rw [← Ideal.mem_span_singleton (y := x)]; rw [← eq_intCast (algebraMap Int S)]; rw [← Ideal.mem_comap]; rw [← Ideal.span_singleton_absNorm]; rw [Ideal.mem_span_singleton]; rw [Ideal.absNorm_span_singleton]; rw [Int.natAbs_dvd]
  rwa [Ideal.absNorm_span_singleton, ← Int.prime_iff_natAbs_prime]

end Ideal

end RingOfIntegers

section Int

open Ideal

@[simp]
/--
theorem `Int.ideal_span_absNorm_eq_self` / 定理 `Int.ideal_span_absNorm_eq_self`

English:
theorem Int.ideal_span_absNorm_eq_self
  given: (J : Ideal Int)
  proof: by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp

@[simp]

中文:
定理 整数.ideal_span_absNorm_eq_self
  条件: (J : 理想 整数)
  证明: by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp

@[simp]

Depends on / 依赖: IsPrincipalIdealRing, IsPrincipalIdealRing.principal, principal
-/
theorem Int.ideal_span_absNorm_eq_self (J : Ideal Int) :
    span {(absNorm J : Int)} = J := by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp

@[simp]
/--
theorem `Int.prime_absNorm` / 定理 `Int.prime_absNorm`

English:
theorem Int.prime_absNorm
  given: (J : Ideal Int)
  proof: by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp [prime_span_singleton_iff, prime_iff_natAbs_prime]

中文:
定理 整数.prime_absNorm
  条件: (J : 理想 整数)
  证明: by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp [prime_span_singleton_iff, prime_iff_natAbs_prime]

Depends on / 依赖: IsPrincipalIdealRing, IsPrincipalIdealRing.principal, prime_iff_natAbs_prime, prime_span_singleton_iff, principal
-/
theorem Int.prime_absNorm (J : Ideal Int) :
    (absNorm J).Prime ↔ Prime J := by
  obtain ⟨g, rfl⟩ := IsPrincipalIdealRing.principal J
  simp [prime_span_singleton_iff, prime_iff_natAbs_prime]

end Int

end abs_norm
