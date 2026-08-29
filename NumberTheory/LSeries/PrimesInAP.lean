/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Coprime
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.Linearity
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Dirichlet's Theorem on primes in arithmetic progression

The goal of this file is to prove **Dirichlet's Theorem**: If `q` is a positive natural number
and `a : ZMod q` is invertible, then there are infinitely many prime numbers `p` such that
`(p : ZMod q) = a`.

The main steps of the proof are as follows.
1. Define `ArithmeticFunction.vonMangoldt.residueClass a` for `a : ZMod q`, which is
   a function `ℕ → ℝ` taking the value zero when `(n : ZMod q) ≠ a` and `Λ n` else
   (where `Λ` is the von Mangoldt function `ArithmeticFunction.vonMangoldt`; we have
   `Λ (p^k) = log p` for prime powers and `Λ n = 0` otherwise.)
2. Show that this function can be written as a linear combination of functions
   of the form `χ * Λ` (pointwise product) with Dirichlet characters `χ` mod `q`.
   See `ArithmeticFunction.vonMangoldt.residueClass_eq`.
3. This implies that the L-series of `ArithmeticFunction.vonMangoldt.residueClass a`
   agrees (on `re s > 1`) with the corresponding linear combination of negative logarithmic
   derivatives of Dirichlet L-functions.
   See `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq`.
4. Define an auxiliary function `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux a` that is
   this linear combination of negative logarithmic derivatives of L-functions minus
   `(q.totient)⁻¹/(s-1)`, which cancels the pole at `s = 1`.
   See `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux` for the statement
   that the auxiliary function agrees with the L-series of
   `ArithmeticFunction.vonMangoldt.residueClass` up to the term `(q.totient)⁻¹/(s-1)`.
5. Show that the auxiliary function is continuous on `re s ≥ 1`;
   see `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux`.
   This relies heavily on the non-vanishing of Dirichlet L-functions on the *closed*
   half-plane `re s ≥ 1` (`DirichletCharacter.LFunction_ne_zero_of_one_le_re`), which
   in turn can only be stated since we know that the L-series of a Dirichlet character
   extends to an entire function (unless the character is trivial; then there is a
   simple pole at `s = 1`); see `DirichletCharacter.LFunction_eq_LSeries`
   (contributed by David Loeffler).
6. Show that the sum of `Λ n / n` over any residue class, but *excluding* the primes, converges.
   See `ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`.
7. Combining these ingredients, we can deduce that the sum of `Λ n / n` over
   the *primes* in a residue class must diverge.
   See `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`.
8. This finally easily implies that there must be infinitely many primes in the residue class.

## Definitions

* `ArithmeticFunction.vonMangoldt.residueClass a` (see above).
* `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux` (see above).

## Main Result

We give two versions of **Dirichlet's Theorem**:
* `Nat.infinite_setOfPred_prime_and_eq_mod` states that the set of primes `p`
  such that `(p : ZMod q) = a` is infinite (when `a` is invertible in `ZMod q`).
* `Nat.forall_exists_prime_gt_and_eq_mod` states that for any natural number `n`
  there is a prime `p > n` such that `(p : ZMod q) = a`.

## Tags

prime number, arithmetic progression, residue class, Dirichlet's Theorem
-/

@[expose] public section

/-!
### The L-series of the von Mangoldt function restricted to a residue class
-/

section arith_prog

namespace ArithmeticFunction.vonMangoldt

open Complex LSeries DirichletCharacter

open scoped LSeries.notation

variable {q : Nat} (a : ZMod q)

/--
Definition of `residueClass` / `residueClass` 的定义

English:
abbreviation residueClass
  signature: : Nat -> Real
  body: {n : Nat | (n : ZMod q) = a}.indicator (vonMangoldt ·)

中文:
缩写 residueClass
  签名: : 自然数 -> 实数
  定义体: {n : Nat | (n : ZMod q) = a}.indicator (vonMangoldt ·)

Depends on / 依赖: indicator, vonMangoldt
-/
noncomputable abbrev residueClass : Nat -> Real :=
  {n : Nat | (n : ZMod q) = a}.indicator (vonMangoldt ·)

/--
lemma `residueClass_nonneg` / 引理 `residueClass_nonneg`

English:
lemma residueClass_nonneg
  given: (n : Nat)
  statement: 0 <= residueClass a n
  proof: Set.indicator_apply_nonneg fun _ => vonMangoldt_nonneg

中文:
引理 residueClass_nonneg
  条件: (n : 自然数)
  结论: 0 <= residueClass a n
  证明: Set.indicator_apply_nonneg fun _ => vonMangoldt_nonneg

Depends on / 依赖: Set.indicator_apply_nonneg, indicator_apply_nonneg, vonMangoldt_nonneg
-/
lemma residueClass_nonneg (n : Nat) : 0 <= residueClass a n :=
  Set.indicator_apply_nonneg fun _ => vonMangoldt_nonneg

/--
lemma `residueClass_le` / 引理 `residueClass_le`

English:
lemma residueClass_le
  given: (n : Nat)
  statement: residueClass a n <= vonMangoldt n
  proof: Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => vonMangoldt_nonneg)

@[simp]

中文:
引理 residueClass_le
  条件: (n : 自然数)
  结论: residueClass a n <= vonMangoldt n
  证明: Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => vonMangoldt_nonneg)

@[simp]

Depends on / 依赖: Set.indicator_apply_le, indicator_apply_le, le_rfl, vonMangoldt_nonneg
-/
lemma residueClass_le (n : Nat) : residueClass a n <= vonMangoldt n :=
  Set.indicator_apply_le' (fun _ => le_rfl) (fun _ => vonMangoldt_nonneg)

@[simp]
/--
lemma `residueClass_apply_zero` / 引理 `residueClass_apply_zero`

English:
lemma residueClass_apply_zero
  statement: residueClass a 0 = 0
  proof: by
  simp only [Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_zero, map_zero,
    implies_true]

中文:
引理 residueClass_apply_zero
  结论: residueClass a 0 = 0
  证明: by
  simp only [Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_zero, map_zero,
    implies_true]

Depends on / 依赖: Nat.cast_zero, Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, cast_zero, implies_true, indicator_apply_eq_zero, map_zero, mem_ofPred_eq
-/
lemma residueClass_apply_zero : residueClass a 0 = 0 := by
  simp only [Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_zero, map_zero,
    implies_true]

/--
lemma `abscissaOfAbsConv_residueClass_le_one` / 引理 `abscissaOfAbsConv_residueClass_le_one`

English:
lemma abscissaOfAbsConv_residueClass_le_one
  proof: by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  unfold LSeriesSummable
have := LSeriesSummable_vonMangoldt show 1 < (y : Complex).re by simp only [ofReal_re, hy]
  convert! this.indicator {n : Nat | (n : ZMod q) = a}
  ext1 n
  by_cases hn : (n : ZMod q) = a
  · simp +

中文:
引理 abscissaOfAbsConv_residueClass_le_one
  证明: by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  unfold LSeriesSummable
have := LSeriesSummable_vonMangoldt show 1 < (y : Complex).re by simp only [ofReal_re, hy]
  convert! this.indicator {n : Nat | (n : ZMod q) = a}
  ext1 n
  by_cases hn : (n : ZMod q) = a
  · simp +

Depends on / 依赖: LSeriesSummable, LSeriesSummable_vonMangoldt, Set.indicator, Set.indicator_of_notMem, Set.mem_ofPred_eq, abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable, apply_ite, contextual, convert, indicator, indicator_of_notMem, ite_self, mem_ofPred_eq, not_false_eq_true, ofReal_re, ofReal_zero, reduceIte, this.indicator, zero_di
-/
lemma abscissaOfAbsConv_residueClass_le_one :
    abscissaOfAbsConv ↗(residueClass a) <= 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
  unfold LSeriesSummable
have := LSeriesSummable_vonMangoldt show 1 < (y : Complex).re by simp only [ofReal_re, hy]
  convert! this.indicator {n : Nat | (n : ZMod q) = a}
  ext1 n
  by_cases hn : (n : ZMod q) = a
  · simp +contextual only [term, Set.indicator, Set.mem_ofPred_eq, hn, ↓reduceIte, apply_ite,
      ite_self]
  · simp +contextual only [term, Set.mem_ofPred_eq, hn, not_false_eq_true, Set.indicator_of_notMem,
      ofReal_zero, zero_div, ite_self]

/--
lemma `support_residueClass_prime_div` / 引理 `support_residueClass_prime_div`

English:
lemma support_residueClass_prime_div
  proof: by
  simp only [Function.support, ne_eq, div_eq_zero_iff, ite_eq_right_iff,
    Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_eq_zero, not_or, Classical.not_imp]
  ext1 p
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun H => ⟨H.1.1, H.1.2.1⟩,
    fun H => ⟨⟨H.1, H.2, vonMangoldt_ne_zero_iff.m

中文:
引理 support_residueClass_prime_div
  证明: by
  simp only [Function.support, ne_eq, div_eq_zero_iff, ite_eq_right_iff,
    Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_eq_zero, not_or, Classical.not_imp]
  ext1 p
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun H => ⟨H.1.1, H.1.2.1⟩,
    fun H => ⟨⟨H.1, H.2, vonMangoldt_ne_zero_iff.m

Depends on / 依赖: Classical, Classical.not_imp, Function, Function.support, Nat.cast_eq_zero, Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, cast_eq_zero, div_eq_zero_iff, indicator_apply_eq_zero, isPrimePow, ite_eq_right_iff, mem_ofPred_eq, ne_eq, ne_zero, not_imp, not_or, support, vonMangoldt_ne_zero_iff, vonMangoldt_ne_zero_iff.mpr
-/
lemma support_residueClass_prime_div :
    Function.support (fun n : Nat => (if n.Prime then residueClass a n else 0) / n) =
      {p : Nat | p.Prime ∧ (p : ZMod q) = a} := by
  simp only [Function.support, ne_eq, div_eq_zero_iff, ite_eq_right_iff,
    Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_eq_zero, not_or, Classical.not_imp]
  ext1 p
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun H => ⟨H.1.1, H.1.2.1⟩,
    fun H => ⟨⟨H.1, H.2, vonMangoldt_ne_zero_iff.mpr H.1.isPrimePow⟩, H.1.ne_zero⟩⟩

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def F₀ (n : Nat)
  body: (if n.Prime then 0 else vonMangoldt n) / n

中文:
定义 noncomputable
  签名: def F₀ (n : 自然数)
  定义体: (if n.Prime then 0 else vonMangoldt n) / n
-/
private noncomputable def F₀ (n : Nat) : Real := (if n.Prime then 0 else vonMangoldt n) / n

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def F' (pk : Nat.Primes × Nat)
  body: F₀ (pk.1 ^ (pk.2 + 1))

中文:
定义 noncomputable
  签名: def F' (pk : 自然数.Primes × 自然数)
  定义体: F₀ (pk.1 ^ (pk.2 + 1))
-/
private noncomputable def F' (pk : Nat.Primes × Nat) : Real := F₀ (pk.1 ^ (pk.2 + 1))

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def F''
  body: F' ∘ (Prod.map _root_.id (· + 1))

中文:
定义 noncomputable
  签名: def F''
  定义体: F' ∘ (Prod.map _root_.id (· + 1))
-/
private noncomputable def F'' : Nat.Primes × Nat -> Real := F' ∘ (Prod.map _root_.id (· + 1))

/--
lemma `F''_le` / 引理 `F''_le`

English:
lemma F''_le
  given: (p : Nat.Primes) (k : Nat)
  statement: F'' (p, k) <= 2 * (p : Real)⁻¹ ^ (k + 3 / 2 : Real)
  proof: calc _
    _ = Real.log p * (p : Real)⁻¹ ^ (k + 2) := by
      simp only [F'', Function.comp_apply, F', F₀, Prod.map_apply, id_eq, le_add_iff_nonneg_left,
        zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, vonMangoldt_apply_prime p.prop,
        vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm,

中文:
引理 F''_le
  条件: (p : 自然数.Primes) (k : 自然数)
  结论: F'' (p, k) <= 2 * (p : 实数)⁻¹ ^ (k + 3 / 2 : 实数)
  证明: calc _
    _ = Real.log p * (p : Real)⁻¹ ^ (k + 2) := by
      simp only [F'', Function.comp_apply, F', F₀, Prod.map_apply, id_eq, le_add_iff_nonneg_left,
        zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, vonMangoldt_apply_prime p.prop,
        vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm,
-/
private lemma F''_le (p : Nat.Primes) (k : Nat) : F'' (p, k) <= 2 * (p : Real)⁻¹ ^ (k + 3 / 2 : Real) :=
  calc _
    _ = Real.log p * (p : Real)⁻¹ ^ (k + 2) := by
      simp only [F'', Function.comp_apply, F', F₀, Prod.map_apply, id_eq, le_add_iff_nonneg_left,
        zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, vonMangoldt_apply_prime p.prop,
        vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm, Nat.cast_pow, div_eq_mul_inv,
        inv_pow (p : Real) (k + 2)]
    _ <= (p : Real) ^ (1 / 2 : Real) / (1 / 2) * (p : Real)⁻¹ ^ (k + 2) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div p.val.cast_nonneg one_half_pos)
          (pow_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg ↑p)) (k + 2))
    _ = 2 * (p : Real)⁻¹ ^ (-1 / 2 : Real) * (p : Real)⁻¹ ^ (k + 2) := by
      simp only [← div_mul, div_one, mul_comm, neg_div, Real.inv_rpow p.val.cast_nonneg,
        ← Real.rpow_neg p.val.cast_nonneg, neg_neg]
    _ = _ := by
      rw [mul_assoc]; rw [← Real.rpow_natCast]; rw [← Real.rpow_add by have := p.prop.pos; positivity]; rw [Nat.cast_add]; rw [Nat.cast_two]; rw [add_comm]; rw [add_assoc]
      norm_num

open Nat.Primes

/--
lemma `summable_F''` / 引理 `summable_F''`

English:
lemma summable_F''
  statement: Summable F''
  proof: by
  have hp₀ (p : Nat.Primes) : 0 < (p : Real)⁻¹ := inv_pos_of_pos (Nat.cast_pos.mpr p.prop.pos)
  have hp₁ (p : Nat.Primes) : (p : Real)⁻¹ < 1 :=
(inv_lt_one₀ <| mod_cast p.prop.pos).mpr Nat.one_lt_cast.mpr p.prop.one_lt
  suffices Summable fun (pk : Nat.Primes × Nat) => (pk.1 : Real)⁻¹ ^ (pk.2 + 

中文:
引理 summable_F''
  结论: Summable F''
  证明: by
  have hp₀ (p : Nat.Primes) : 0 < (p : Real)⁻¹ := inv_pos_of_pos (Nat.cast_pos.mpr p.prop.pos)
  have hp₁ (p : Nat.Primes) : (p : Real)⁻¹ < 1 :=
(inv_lt_one₀ <| mod_cast p.prop.pos).mpr Nat.one_lt_cast.mpr p.prop.one_lt
  suffices Summable fun (pk : Nat.Primes × Nat) => (pk.1 : Real)⁻¹ ^ (pk.2 + 
-/
private lemma summable_F'' : Summable F'' := by
  have hp₀ (p : Nat.Primes) : 0 < (p : Real)⁻¹ := inv_pos_of_pos (Nat.cast_pos.mpr p.prop.pos)
  have hp₁ (p : Nat.Primes) : (p : Real)⁻¹ < 1 :=
(inv_lt_one₀ <| mod_cast p.prop.pos).mpr Nat.one_lt_cast.mpr p.prop.one_lt
  suffices Summable fun (pk : Nat.Primes × Nat) => (pk.1 : Real)⁻¹ ^ (pk.2 + 3 / 2 : Real) by
    refine (Summable.mul_left 2 this).of_nonneg_of_le (fun pk => ?_) (fun pk => F''_le pk.1 pk.2)
    simp only [F'', Function.comp_apply, F', F₀, Prod.map_fst, id_eq, Prod.map_snd, Nat.cast_pow]
    positivity [vonMangoldt_nonneg (n := (pk.1 : Nat) ^ (pk.2 + 2))]
  conv => enter [1, pk]; rw [Real.rpow_add <| hp₀ pk.1, Real.rpow_natCast]
  refine (summable_prod_of_nonneg (fun _ => by positivity)).mpr ⟨(fun p => ?_), ?_⟩
  · dsimp only -- otherwise the `exact` below times out
exact Summable.mul_right _ summable_geometric_of_lt_one (hp₀ p).le (hp₁ p)
  · dsimp only
    conv => enter [1, p]; rw [tsum_mul_right, tsum_geometric_of_lt_one (hp₀ p).le (hp₁ p)]
    refine (summable_rpow.mpr (by norm_num : -(3 / 2 : Real) < -1)).mul_left 2
.of_nonneg_of_le (fun p => ?_) (fun p => ?_)
    · positivity [sub_pos.mpr (hp₁ p)]
    · rw [Real.inv_rpow p.val.cast_nonneg, Real.rpow_neg p.val.cast_nonneg]
      gcongr
      rw [inv_le_comm₀ (sub_pos.mpr (hp₁ p)) zero_lt_two]; rw [le_sub_comm]; rw [show (1 : Real) - 2⁻¹ = 2⁻¹ by norm_num]; rw [inv_le_inv₀ (mod_cast p.prop.pos) zero_lt_two]
      exact Nat.ofNat_le_cast.mpr p.prop.two_le

/--
lemma `summable_residueClass_non_primes_div` / 引理 `summable_residueClass_non_primes_div`

English:
lemma summable_residueClass_non_primes_div
  proof: by
  have h₀ (n : Nat) : 0 <= (if n.Prime then 0 else residueClass a n) / n := by
    positivity [residueClass_nonneg a n]
  have hleF₀ (n : Nat) : (if n.Prime then 0 else residueClass a n) / n <= F₀ n := by
    refine div_le_div_of_nonneg_right ?_ n.cast_nonneg
    split_ifs; exacts [le_rfl, residu

中文:
引理 summable_residueClass_non_primes_div
  证明: by
  have h₀ (n : Nat) : 0 <= (if n.Prime then 0 else residueClass a n) / n := by
    positivity [residueClass_nonneg a n]
  have hleF₀ (n : Nat) : (if n.Prime then 0 else residueClass a n) / n <= F₀ n := by
    refine div_le_div_of_nonneg_right ?_ n.cast_nonneg
    split_ifs; exacts [le_rfl, residu

Depends on / 依赖: IsPrimePow, Nat.Primes, Primes, Summable, Summable.of_nonneg_of_le, cast_nonneg, div_le_div_of_nonneg_right, exacts, le_rfl, n.Prime, n.cast_nonneg, of_nonneg_of_le, p.prop, p.val, reduceIte, residueClass, residueClass_le, residueClass_nonneg, split_ifs, summable_subtype_iff_indicator
-/
lemma summable_residueClass_non_primes_div :
    Summable fun n : Nat => (if n.Prime then 0 else residueClass a n) / n := by
  have h₀ (n : Nat) : 0 <= (if n.Prime then 0 else residueClass a n) / n := by
    positivity [residueClass_nonneg a n]
  have hleF₀ (n : Nat) : (if n.Prime then 0 else residueClass a n) / n <= F₀ n := by
    refine div_le_div_of_nonneg_right ?_ n.cast_nonneg
    split_ifs; exacts [le_rfl, residueClass_le a n]
  refine Summable.of_nonneg_of_le h₀ hleF₀ ?_
  have hF₀ (p : Nat.Primes) : F₀ p.val = 0 := by
    simp only [p.prop, ↓reduceIte, zero_div, F₀]
  refine (summable_subtype_iff_indicator (s := {n | IsPrimePow n}).mp ?_).congr
      fun n => Set.indicator_apply_eq_self.mpr fun (hn : ¬ IsPrimePow n) => ?_
  swap
  · simp +contextual only [div_eq_zero_iff, ite_eq_left_iff, vonMangoldt_eq_zero_iff, hn,
      not_false_eq_true, implies_true, Nat.cast_eq_zero, true_or, F₀]
  have hFF' :
      F₀ ∘ Subtype.val (p := fun n => n in {n | IsPrimePow n}) = F' ∘ ⇑prodNatEquiv.symm := by
    refine (Equiv.eq_comp_symm prodNatEquiv (F₀ ∘ Subtype.val) F').mpr ?_
    ext1 n
    simp only [Function.comp_apply, F']
    congr
  rw [hFF']
  refine (Nat.Primes.prodNatEquiv.symm.summable_iff (f := F')).mpr ?_
  have hF'₀ (p : Nat.Primes) : F' (p, 0) = 0 := by simp only [zero_add, pow_one, hF₀, F']
  have hF'₁ : F'' = F' ∘ (Prod.map _root_.id (· + 1)) := by
    ext1
    simp only [Function.comp_apply, Prod.map_fst, id_eq, Prod.map_snd, F'', F']
refine (Function.Injective.summable_iff ?_ fun u hu => ?_).mp hF'₁ ▸ summable_F''
· exact Function.Injective.prodMap (fun ⦃a₁ a₂⦄ a => a) add_left_injective 1
  · simp only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range,
      Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu
    rw [← hF'₀ u.1]; rw [← hu]

variable [NeZero q] {a}

/--
lemma `residueClass_apply` / 引理 `residueClass_apply`

English:
lemma residueClass_apply
  given: (ha : IsUnit a) (n : Nat)
  proof: by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq Complex ha n, eq_comm (a := a),
    ite_mul, zero_mul

中文:
引理 residueClass_apply
  条件: (ha : IsUnit a) (n : 自然数)
  证明: by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq Complex ha n, eq_comm (a := a),
    ite_mul, zero_mul

Depends on / 依赖: Finset, Finset.sum_mul, Nat.totient_pos.mpr, Set.indicator_apply, Set.mem_ofPred_eq, apply_ite, contextual, eq_comm, indicator_apply, ite_mul, ite_self, mem_ofPred_eq, mod_cast, mul_zero, ofReal_zero, pos_of_neZero, q.pos_of_neZero, reduceIte, residueClass, sum_char_inv_mul_char_eq
-/
lemma residueClass_apply (ha : IsUnit a) (n : Nat) :
    residueClass a n =
      (q.totient : Complex)⁻¹ * ∑ χ : DirichletCharacter Complex q, χ a⁻¹ * χ n * vonMangoldt n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq Complex ha n, eq_comm (a := a),
    ite_mul, zero_mul, ↓reduceIte, ite_self]

/--
lemma `residueClass_eq` / 引理 `residueClass_eq`

English:
lemma residueClass_eq
  given: (ha : IsUnit a)
  proof: by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residueClass_apply ha n

中文:
引理 residueClass_eq
  条件: (ha : IsUnit a)
  证明: by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residueClass_apply ha n

Depends on / 依赖: Finset, Finset.sum_apply, Pi.smul_apply, mul_assoc, residueClass_apply, smul_apply, smul_eq_mul, sum_apply
-/
lemma residueClass_eq (ha : IsUnit a) :
    ↗(residueClass a) = (q.totient : Complex)⁻¹ •
      ∑ χ : DirichletCharacter Complex q, χ a⁻¹ • (fun n : Nat => χ n * vonMangoldt n) := by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residueClass_apply ha n

/--
lemma `LSeries_residueClass_eq` / 引理 `LSeries_residueClass_eq`

English:
lemma LSeries_residueClass_eq
  given: (ha : IsUnit a) {s : Complex} (hs : 1 < s.re)
  proof: by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp_rw [← LSeries_smul,
← LSeries

中文:
引理 LSeries_residueClass_eq
  条件: (ha : IsUnit a) {s : Complex} (hs : 1 < s.re)
  证明: by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp_rw [← LSeries_smul,
← LSeries

Depends on / 依赖: Finset, Finset.sum_neg_distrib, LFunction_eq_LSeries, LSeriesSummable_twist_vonMangoldt, LSeries_congr, LSeries_smul, LSeries_sum, LSeries_twist_vonMangoldt_eq, Nat.totient_pos.mpr, Pi.smul_apply, deriv_LFunction_eq_deriv_LSeries, mod_cast, mul_assoc, mul_inv_cancel_of_invertible, mul_neg, neg_div, neg_mul, pos_of_neZero, q.pos_of_neZero, residueClass_apply
-/
lemma LSeries_residueClass_eq (ha : IsUnit a) {s : Complex} (hs : 1 < s.re) :
    LSeries ↗(residueClass a) s =
      -(q.totient : Complex)⁻¹ * ∑ χ : DirichletCharacter Complex q, χ a⁻¹ *
        (deriv (LFunction χ) s / LFunction χ s) := by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp_rw [← LSeries_smul,
← LSeries_sum fun χ _ => (LSeriesSummable_twist_vonMangoldt χ hs).smul _]
  refine LSeries_congr (fun {n} _ => ?_) s
  simp only [Pi.smul_apply, residueClass_apply ha, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel_of_invertible, one_mul, Finset.sum_apply, Pi.mul_apply]

variable (a)

open scoped Classical in
/-- The auxiliary function used, e.g., with the Wiener-Ikehara Theorem to prove
Dirichlet's Theorem. On `re s > 1`, it agrees with the L-series of the von Mangoldt
function restricted to the residue class `a : ZMod q` minus the principal part
`(q.totient)⁻¹/(s-1)` of the pole at `s = 1`;
see `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux`. -/
noncomputable
/--
Definition of `LFunctionResidueClassAux` / `LFunctionResidueClassAux` 的定义

English:
abbreviation LFunctionResidueClassAux
  signature: (s : Complex)
  body: (q.totient : Complex)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ in ({1}ᶜ : Finset (DirichletCharacter Complex q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

中文:
缩写 LFunctionResidueClassAux
  签名: (s : Complex)
  定义体: (q.totient : Complex)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ in ({1}ᶜ : Finset (DirichletCharacter Complex q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

Depends on / 依赖: DirichletCharacter, Finset, LFunction, q.totient, totient
-/
abbrev LFunctionResidueClassAux (s : Complex) : Complex :=
  (q.totient : Complex)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ in ({1}ᶜ : Finset (DirichletCharacter Complex q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

/--
lemma `continuousOn_LFunctionResidueClassAux'` / 引理 `continuousOn_LFunctionResidueClassAux'`

English:
lemma continuousOn_LFunctionResidueClassAux'
  proof: by
  rw [show LFunctionResidueClassAux a = fun s => _ from rfl]
  simp only [LFunctionResidueClassAux, sub_eq_add_neg]
refine continuousOn_const.mul ContinuousOn.add ?_ ?_
  · refine (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).mono fun s hs => ?_
    simp only [ne_eq, Set.mem_ofPred_eq] at hs
 

中文:
引理 continuousOn_LFunctionResidueClassAux'
  证明: by
  rw [show LFunctionResidueClassAux a = fun s => _ from rfl]
  simp only [LFunctionResidueClassAux, sub_eq_add_neg]
refine continuousOn_const.mul ContinuousOn.add ?_ ?_
  · refine (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).mono fun s hs => ?_
    simp only [ne_eq, Set.mem_ofPred_eq] at hs
 

Depends on / 依赖: ContinuousOn, ContinuousOn.add, Finset, Finset.mem_com, Finset.sum_neg_distrib, LFunctionResidueClassAux, Set.mem_ofPred_eq, continuousOn_const, continuousOn_const.mul, continuousOn_finsetSum, mem_com, mem_ofPred_eq, mul_div_assoc, mul_neg, ne_eq, neg_div, replace, sub_eq_add_neg, sum_neg_distrib
-/
lemma continuousOn_LFunctionResidueClassAux' :
    ContinuousOn (LFunctionResidueClassAux a)
      {s | s = 1 ∨ forall χ : DirichletCharacter Complex q, LFunction χ s != 0} := by
  rw [show LFunctionResidueClassAux a = fun s => _ from rfl]
  simp only [LFunctionResidueClassAux, sub_eq_add_neg]
refine continuousOn_const.mul ContinuousOn.add ?_ ?_
  · refine (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).mono fun s hs => ?_
    simp only [ne_eq, Set.mem_ofPred_eq] at hs
    tauto
  · simp only [← Finset.sum_neg_distrib, mul_div_assoc, ← mul_neg, ← neg_div]
    refine continuousOn_finsetSum _ fun χ hχ => continuousOn_const.mul ?_
    replace hχ : χ != 1 := by simpa only [ne_eq, Finset.mem_compl, Finset.mem_singleton] using hχ
    refine (continuousOn_neg_logDeriv_LFunction_of_nontriv hχ).mono fun s hs => ?_
    simp only [ne_eq, Set.mem_ofPred_eq] at hs
    rcases hs with rfl | hs
    · simp only [ne_eq, Set.mem_ofPred_eq, one_re, le_refl,
        LFunction_ne_zero_of_one_le_re χ (.inl hχ), not_false_eq_true]
    · exact hs χ

/--
lemma `continuousOn_LFunctionResidueClassAux` / 引理 `continuousOn_LFunctionResidueClassAux`

English:
lemma continuousOn_LFunctionResidueClassAux
  proof: by
  refine (continuousOn_LFunctionResidueClassAux' a).mono fun s hs => ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_ofPred_eq, true_or]
  · simp only [ne_eq, Set.mem_ofPred_eq, hs₁, false_or]
exact fun χ => LFunction_ne_zero_of_one_le_re χ (.inr hs₁) Set.mem_ofPred.mp hs

中文:
引理 continuousOn_LFunctionResidueClassAux
  证明: by
  refine (continuousOn_LFunctionResidueClassAux' a).mono fun s hs => ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_ofPred_eq, true_or]
  · simp only [ne_eq, Set.mem_ofPred_eq, hs₁, false_or]
exact fun χ => LFunction_ne_zero_of_one_le_re χ (.inr hs₁) Set.mem_ofPred.mp hs

Depends on / 依赖: LFunction_ne_zero_of_one_le_re, Set.mem_ofPred.mp, Set.mem_ofPred_eq, continuousOn_LFunctionResidueClassAux, eq_or_ne, false_or, mem_ofPred, mem_ofPred_eq, ne_eq, true_or
-/
lemma continuousOn_LFunctionResidueClassAux :
    ContinuousOn (LFunctionResidueClassAux a) {s | 1 <= s.re} := by
  refine (continuousOn_LFunctionResidueClassAux' a).mono fun s hs => ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_ofPred_eq, true_or]
  · simp only [ne_eq, Set.mem_ofPred_eq, hs₁, false_or]
exact fun χ => LFunction_ne_zero_of_one_le_re χ (.inr hs₁) Set.mem_ofPred.mp hs

variable {a}

open scoped LSeries.notation

/--
lemma `eqOn_LFunctionResidueClassAux` / 引理 `eqOn_LFunctionResidueClassAux`

English:
lemma eqOn_LFunctionResidueClassAux
  given: (ha : IsUnit a)
  proof: by
  intro s hs
  replace hs := Set.mem_ofPred.mp hs
  simp only [LSeries_residueClass_eq ha hs, LFunctionResidueClassAux]
  rw [neg_div]; rw [← neg_add']; rw [mul_neg]; rw [← neg_mul]; rw [div_eq_mul_one_div (q.totient : Complex)⁻¹]; rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← mul_add]
  congrm (_ *

中文:
引理 eqOn_LFunctionResidueClassAux
  条件: (ha : IsUnit a)
  证明: by
  intro s hs
  replace hs := Set.mem_ofPred.mp hs
  simp only [LSeries_residueClass_eq ha hs, LFunctionResidueClassAux]
  rw [neg_div]; rw [← neg_add']; rw [mul_neg]; rw [← neg_mul]; rw [div_eq_mul_one_div (q.totient : Complex)⁻¹]; rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← mul_add]
  congrm (_ *

Depends on / 依赖: LFunctionResidueClassAux, LSeries_residueClass_eq, Set.mem_ofPred.mp, congrm, div_eq_mul_one_div, mem_ofPred, mul_add, mul_neg, neg_add, neg_div, neg_mul, q.totient, replace, sub_eq_add_neg, totient
-/
lemma eqOn_LFunctionResidueClassAux (ha : IsUnit a) :
    Set.EqOn (LFunctionResidueClassAux a)
      (fun s => L ↗(residueClass a) s - (q.totient : Complex)⁻¹ / (s - 1))
      {s | 1 < s.re} := by
  intro s hs
  replace hs := Set.mem_ofPred.mp hs
  simp only [LSeries_residueClass_eq ha hs, LFunctionResidueClassAux]
  rw [neg_div]; rw [← neg_add']; rw [mul_neg]; rw [← neg_mul]; rw [div_eq_mul_one_div (q.totient : Complex)⁻¹]; rw [sub_eq_add_neg]; rw [← neg_mul]; rw [← mul_add]
  congrm (_ * ?_)
  -- this should be easier, but `IsUnit.inv ha` does not work here
  have ha' : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a, (ZMod.inv_mul_of_unit a ha).symm⟩
  classical -- for `Fintype.sum_eq_add_sum_compl`
  rw [Fintype.sum_eq_add_sum_compl 1]; rw [MulChar.one_apply ha']; rw [one_mul]; rw [add_right_comm]
  simp only [mul_div_assoc]
  congrm (?_ + _)
  have hs₁ : s != 1 := fun h => ((h ▸ hs).trans_eq one_re).false
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁]; rw [LFunctionTrivChar₁]; rw [Function.update_of_ne hs₁]; rw [LFunctionTrivChar]; rw [add_div]; rw [mul_div_mul_left _ _ (sub_ne_zero_of_ne hs₁)]
  conv_lhs => enter [2, 1]; rw [← mul_one (LFunction ..)]
  rw [mul_comm _ 1]; rw [mul_div_mul_right _ _ <| LFunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le]

/--
lemma `LFunctionResidueClassAux_real` / 引理 `LFunctionResidueClassAux_real`

English:
lemma LFunctionResidueClassAux_real
  given: (ha : IsUnit a) {x : Real} (hx : 1 < x)
  proof: by
  rw [eqOn_LFunctionResidueClassAux ha hx]
  simp only [sub_re, ofReal_sub]
  congr 1
  · rw [LSeries, re_tsum <| LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
(abscissaOfAbsConv_residueClass_le_one a).trans_lt by norm_cast]
    push_cast
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 

中文:
引理 LFunctionResidueClassAux_real
  条件: (ha : IsUnit a) {x : 实数} (hx : 1 < x)
  证明: by
  rw [eqOn_LFunctionResidueClassAux ha hx]
  simp only [sub_re, ofReal_sub]
  congr 1
  · rw [LSeries, re_tsum <| LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
(abscissaOfAbsConv_residueClass_le_one a).trans_lt by norm_cast]
    push_cast
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 

Depends on / 依赖: LSeries, LSeriesSummable_of_abscissaOfAbsConv_lt_re, abscissaOfAbsConv_residueClass_le_one, cast_nonneg, eqOn_LFunctionResidueClassAux, eq_or_ne, n.cast_nonneg, ofReal_cpow, ofReal_div, ofReal_natCast, ofReal_one, ofReal_re, ofReal_sub, ofReal_zero, re_tsum, sub_re, term_of_ne_zero, term_zero, trans_lt, tsum_congr
-/
lemma LFunctionResidueClassAux_real (ha : IsUnit a) {x : Real} (hx : 1 < x) :
    LFunctionResidueClassAux a x = (LFunctionResidueClassAux a x).re := by
  rw [eqOn_LFunctionResidueClassAux ha hx]
  simp only [sub_re, ofReal_sub]
  congr 1
  · rw [LSeries, re_tsum <| LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
(abscissaOfAbsConv_residueClass_le_one a).trans_lt by norm_cast]
    push_cast
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, zero_re, ofReal_zero]
    · simp only [term_of_ne_zero hn, ← ofReal_natCast n, ← ofReal_cpow n.cast_nonneg, ← ofReal_div,
        ofReal_re]
  · rw [← ofReal_natCast, ← ofReal_one, ← ofReal_sub, ← ofReal_inv,
      ← ofReal_div, ofReal_re]

variable {q : Nat} [NeZero q] {a : ZMod q}

/--
lemma `LSeries_residueClass_lower_bound` / 引理 `LSeries_residueClass_lower_bound`

English:
lemma LSeries_residueClass_lower_bound
  given: (ha : IsUnit a)
  proof: by
  have H {x : Real} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : Real) ^ x =
        (LFunctionResidueClassAux a x).re + (q.totient : Real)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_

中文:
引理 LSeries_residueClass_lower_bound
  条件: (ha : IsUnit a)
  证明: by
  have H {x : Real} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : Real) ^ x =
        (LFunctionResidueClassAux a x).re + (q.totient : Real)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_

Depends on / 依赖: LFunctionResidueClassAux, LFunctionResidueClassAux_real, LSeries, Nat.cast_nonneg, Set.mem_ofPred.mpr, cast_nonneg, eqOn_LFunctionResidueClassAux, mem_ofPred, ofReal_add, ofReal_cpow, ofReal_div, ofReal_injective, ofReal_inv, ofReal_natCast, ofReal_one, ofReal_re, ofReal_sub, ofReal_tsum, q.totient, residueClass
-/
lemma LSeries_residueClass_lower_bound (ha : IsUnit a) :
    exists C : Real, forall {x : Real} (_ : x in Set.Ioc 1 2),
      (q.totient : Real)⁻¹ / (x - 1) - C <= ∑' n, residueClass a n / (n : Real) ^ x := by
  have H {x : Real} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : Real) ^ x =
        (LFunctionResidueClassAux a x).re + (q.totient : Real)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hx,
eqOn_LFunctionResidueClassAux ha Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, term]
    refine tsum_congr fun n => ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have : ContinuousOn (fun x : Real => (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux a)
.comp continuous_ofReal.continuousOn fun x hx => by (fun ⦃x⦄ a => trivial)
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
obtain ⟨C, hC⟩ := bddBelow_def.mp IsCompact.bddBelow_image isCompact_Icc this
  replace hC {x : Real} (hx : x in Set.Icc 1 2) : C <= (LFunctionResidueClassAux a x).re :=
hC (LFunctionResidueClassAux a x).re
      Set.mem_image_of_mem (fun x : Real => (LFunctionResidueClassAux a x).re) hx
  refine ⟨-C, fun {x} hx => ?_⟩
  rw [H hx.1]; rw [add_comm]; rw [sub_neg_eq_add]; rw [add_le_add_iff_left]
exact hC Set.mem_Icc_of_Ioc hx

open vonMangoldt Filter Topology in
/--
lemma `not_summable_residueClass_prime_div` / 引理 `not_summable_residueClass_prime_div`

English:
lemma not_summable_residueClass_prime_div
  given: (ha : IsUnit a)
  proof: by
  intro H
  have key : Summable fun n : Nat => residueClass a n / n := by
    convert! (summable_residueClass_non_primes_div a).add H using 2 with n
    simp only [← add_div, ite_add_ite, zero_add, add_zero, ite_self]
  let C := ∑' n, residueClass a n / n
  have H₁ {x : Real} (hx : 1 < x) : ∑' n,

中文:
引理 not_summable_residueClass_prime_div
  条件: (ha : IsUnit a)
  证明: by
  intro H
  have key : Summable fun n : Nat => residueClass a n / n := by
    convert! (summable_residueClass_non_primes_div a).add H using 2 with n
    simp only [← add_div, ite_add_ite, zero_add, add_zero, ite_self]
  let C := ∑' n, residueClass a n / n
  have H₁ {x : Real} (hx : 1 < x) : ∑' n,

Depends on / 依赖: Summable, Summable.tsum_le_tsum, add_div, add_zero, convert, div_le_div_of_nonneg_left, eq_zero_or_pos, ite_add_ite, ite_self, mod_cast, n.eq_zero_or_pos, residueClass, residueClass_nonneg, summable_residueClass_non_primes_div, tsum_le_tsum, zero_add
-/
lemma not_summable_residueClass_prime_div (ha : IsUnit a) :
    ¬ Summable fun n : Nat => (if n.Prime then residueClass a n else 0) / n := by
  intro H
  have key : Summable fun n : Nat => residueClass a n / n := by
    convert! (summable_residueClass_non_primes_div a).add H using 2 with n
    simp only [← add_div, ite_add_ite, zero_add, add_zero, ite_self]
  let C := ∑' n, residueClass a n / n
  have H₁ {x : Real} (hx : 1 < x) : ∑' n, residueClass a n / (n : Real) ^ x <= C := by
    refine Summable.tsum_le_tsum (fun n => ?_) ?_ key
    · rcases n.eq_zero_or_pos with rfl | hn
      · simp
      · refine div_le_div_of_nonneg_left (residueClass_nonneg a _) (mod_cast hn) ?_
        conv_lhs => rw [← Real.rpow_one n]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_cast) hx.le
· exact summable_real_of_abscissaOfAbsConv_lt
(abscissaOfAbsConv_residueClass_le_one a).trans_lt mod_cast hx
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound ha
  have H₁ {x} (hx : x in Set.Ioc 1 2) : (q.totient : Real)⁻¹ <= (C + C') * (x - 1) :=
(div_le_iff₀ <| sub_pos.mpr hx.1).mp
sub_le_iff_le_add.mp (hC' hx).trans (H₁ hx.1)
  have hq : 0 < (q.totient : Real)⁻¹ := inv_pos.mpr (mod_cast q.totient.pos_of_neZero)
  rcases le_or_gt (C + C') 0 with h₀ | h₀
  · have := hq.trans_le (H₁ (Set.right_mem_Ioc.mpr one_lt_two))
    rw [show (2 : Real) - 1 = 1 by norm_num]; rw [mul_one] at this
    exact (this.trans_le h₀).false
  · obtain ⟨ξ, hξ₁, hξ₂⟩ : exists ξ in Set.Ioc 1 2, (C + C') * (ξ - 1) < (q.totient : Real)⁻¹ := by
      refine ⟨min (1 + (q.totient : Real)⁻¹ / (C + C') / 2) 2, ⟨?_, min_le_right ..⟩, ?_⟩
      · simpa only [lt_inf_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right,
          Nat.one_lt_ofNat, and_true] using div_pos hq h₀
      · rw [← min_sub_sub_right, add_sub_cancel_left, ← lt_div_iff₀' h₀]
exact (min_le_left ..).trans_lt div_lt_self (div_pos hq h₀) one_lt_two
    exact ((H₁ hξ₁).trans_lt hξ₂).false

end ArithmeticFunction.vonMangoldt

end arith_prog

/-!
### Dirichlet's Theorem
-/

section DirichletsTheorem

namespace Nat

open ArithmeticFunction vonMangoldt

variable {q : Nat} [NeZero q] {a : ZMod q}

/--
theorem `infinite_setOfPred_prime_and_eq_mod` / 定理 `infinite_setOfPred_prime_and_eq_mod`

English:
theorem infinite_setOfPred_prime_and_eq_mod
  given: (ha : IsUnit a)
  proof: by
  by_contra! H
exact not_summable_residueClass_prime_div ha
summable_of_hasFiniteSupport show Set.Finite _ from support_residueClass_prime_div a ▸ H

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_eq_mod := infinite_setOfPred_prime_and_eq_mod

中文:
定理 infinite_setOfPred_prime_and_eq_mod
  条件: (ha : IsUnit a)
  证明: by
  by_contra! H
exact not_summable_residueClass_prime_div ha
summable_of_hasFiniteSupport show Set.Finite _ from support_residueClass_prime_div a ▸ H

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_eq_mod := infinite_setOfPred_prime_and_eq_mod

Depends on / 依赖: Finite, Set.Finite, not_summable_residueClass_prime_div, summable_of_hasFiniteSupport, support_residueClass_prime_div
-/
theorem infinite_setOfPred_prime_and_eq_mod (ha : IsUnit a) :
    {p : Nat | p.Prime ∧ (p : ZMod q) = a}.Infinite := by
  by_contra! H
exact not_summable_residueClass_prime_div ha
summable_of_hasFiniteSupport show Set.Finite _ from support_residueClass_prime_div a ▸ H

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_eq_mod := infinite_setOfPred_prime_and_eq_mod

/--
theorem `forall_exists_prime_gt_and_eq_mod` / 定理 `forall_exists_prime_gt_and_eq_mod`

English:
theorem forall_exists_prime_gt_and_eq_mod
  given: (ha : IsUnit a) (n : Nat)
  proof: by
  obtain ⟨p, hp₁, hp₂⟩ := Set.infinite_iff_exists_gt.mp (infinite_setOfPred_prime_and_eq_mod ha) n
  exact ⟨p, hp₂.gt, Set.mem_ofPred.mp hp₁⟩

中文:
定理 forall_exists_prime_gt_and_eq_mod
  条件: (ha : IsUnit a) (n : 自然数)
  证明: by
  obtain ⟨p, hp₁, hp₂⟩ := Set.infinite_iff_exists_gt.mp (infinite_setOfPred_prime_and_eq_mod ha) n
  exact ⟨p, hp₂.gt, Set.mem_ofPred.mp hp₁⟩

Depends on / 依赖: Set.infinite_iff_exists_gt.mp, Set.mem_ofPred.mp, infinite_iff_exists_gt, infinite_setOfPred_prime_and_eq_mod, mem_ofPred
-/
theorem forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : Nat) :
    exists p > n, p.Prime ∧ (p : ZMod q) = a := by
  obtain ⟨p, hp₁, hp₂⟩ := Set.infinite_iff_exists_gt.mp (infinite_setOfPred_prime_and_eq_mod ha) n
  exact ⟨p, hp₂.gt, Set.mem_ofPred.mp hp₁⟩

/--
theorem `forall_exists_prime_gt_and_zmodEq` / 定理 `forall_exists_prime_gt_and_zmodEq`

English:
theorem forall_exists_prime_gt_and_zmodEq
  given: (n : Nat) {q : Nat} {a : Int} (hq : q != 0) (h : IsCoprime a q)
  proof: by
  have : NeZero q := ⟨hq⟩
  have : IsUnit (a : ZMod q) := by
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]
  obtain ⟨p, hpn, hpp, heq⟩ := forall_exists_prime_gt_and_eq_mod this n
  refine ⟨p, hpn, hpp, ?_⟩
  simpa [← ZMod.intCast_eq_intCast_iff] using heq

中文:
定理 forall_exists_prime_gt_and_zmodEq
  条件: (n : 自然数) {q : 自然数} {a : 整数} (hq : q != 0) (h : IsCoprime a q)
  证明: by
  have : NeZero q := ⟨hq⟩
  have : IsUnit (a : ZMod q) := by
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]
  obtain ⟨p, hpn, hpp, heq⟩ := forall_exists_prime_gt_and_eq_mod this n
  refine ⟨p, hpn, hpp, ?_⟩
  simpa [← ZMod.intCast_eq_intCast_iff] using heq

Depends on / 依赖: IsUnit, NeZero, ZMod.coe_int_isUnit_iff_isCoprime, ZMod.intCast_eq_intCast_iff, coe_int_isUnit_iff_isCoprime, forall_exists_prime_gt_and_eq_mod, intCast_eq_intCast_iff, isCoprime_comm
-/
theorem forall_exists_prime_gt_and_zmodEq (n : Nat) {q : Nat} {a : Int} (hq : q != 0) (h : IsCoprime a q) :
    exists p > n, p.Prime ∧ p ≡ a [ZMOD q] := by
  have : NeZero q := ⟨hq⟩
  have : IsUnit (a : ZMod q) := by
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]
  obtain ⟨p, hpn, hpp, heq⟩ := forall_exists_prime_gt_and_eq_mod this n
  refine ⟨p, hpn, hpp, ?_⟩
  simpa [← ZMod.intCast_eq_intCast_iff] using heq

/--
theorem `forall_exists_prime_gt_and_modEq` / 定理 `forall_exists_prime_gt_and_modEq`

English:
theorem forall_exists_prime_gt_and_modEq
  given: (n : Nat) {q a : Nat} (hq : q != 0) (h : a.Coprime q)
  proof: by
  simpa using forall_exists_prime_gt_and_zmodEq n (q := q) (a := a) hq (by simpa)

中文:
定理 forall_exists_prime_gt_and_modEq
  条件: (n : 自然数) {q a : 自然数} (hq : q != 0) (h : a.Coprime q)
  证明: by
  simpa using forall_exists_prime_gt_and_zmodEq n (q := q) (a := a) hq (by simpa)

Depends on / 依赖: forall_exists_prime_gt_and_zmodEq
-/
theorem forall_exists_prime_gt_and_modEq (n : Nat) {q a : Nat} (hq : q != 0) (h : a.Coprime q) :
    exists p > n, p.Prime ∧ p ≡ a [MOD q] := by
  simpa using forall_exists_prime_gt_and_zmodEq n (q := q) (a := a) hq (by simpa)

open Filter in
/--
lemma `frequently_atTop_prime_and_modEq` / 引理 `frequently_atTop_prime_and_modEq`

English:
lemma frequently_atTop_prime_and_modEq
  given: {q a : Nat} (hq : q != 0) (h : a.Coprime q)
  proof: by
  rw [frequently_atTop]
  intro n
  obtain ⟨p, hn, hp, ha⟩ := forall_exists_prime_gt_and_modEq n hq h
  exact ⟨p, hn.le, hp, ha⟩

中文:
引理 frequently_atTop_prime_and_modEq
  条件: {q a : 自然数} (hq : q != 0) (h : a.Coprime q)
  证明: by
  rw [frequently_atTop]
  intro n
  obtain ⟨p, hn, hp, ha⟩ := forall_exists_prime_gt_and_modEq n hq h
  exact ⟨p, hn.le, hp, ha⟩

Depends on / 依赖: forall_exists_prime_gt_and_modEq, frequently_atTop, hn.le
-/
lemma frequently_atTop_prime_and_modEq {q a : Nat} (hq : q != 0) (h : a.Coprime q) :
    existsᶠ p in atTop, p.Prime ∧ p ≡ a [MOD q] := by
  rw [frequently_atTop]
  intro n
  obtain ⟨p, hn, hp, ha⟩ := forall_exists_prime_gt_and_modEq n hq h
  exact ⟨p, hn.le, hp, ha⟩

/--
lemma `infinite_setOfPred_prime_and_modEq` / 引理 `infinite_setOfPred_prime_and_modEq`

English:
lemma infinite_setOfPred_prime_and_modEq
  given: {q a : Nat} (hq : q != 0) (h : a.Coprime q)
  proof: frequently_atTop_iff_infinite.1 (frequently_atTop_prime_and_modEq hq h)

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_modEq := infinite_setOfPred_prime_and_modEq

中文:
引理 infinite_setOfPred_prime_and_modEq
  条件: {q a : 自然数} (hq : q != 0) (h : a.Coprime q)
  证明: frequently_atTop_iff_infinite.1 (frequently_atTop_prime_and_modEq hq h)

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_modEq := infinite_setOfPred_prime_and_modEq

Depends on / 依赖: frequently_atTop_iff_infinite, frequently_atTop_prime_and_modEq
-/
lemma infinite_setOfPred_prime_and_modEq {q a : Nat} (hq : q != 0) (h : a.Coprime q) :
    Set.Infinite {p : Nat | p.Prime ∧ p ≡ a [MOD q]} :=
  frequently_atTop_iff_infinite.1 (frequently_atTop_prime_and_modEq hq h)

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_modEq := infinite_setOfPred_prime_and_modEq

end Nat

end DirichletsTheorem
