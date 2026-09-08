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

variable {q : ℕ} (a : ZMod q)

/-- The von Mangoldt function restricted to the residue class `a` mod `q`. -/
/-
**ArithmeticFunction.vonMangoldt.residueClass** 是 Mathlib 中的一个缩写定义，位于命名空间 `Arith
meticFunction.vonMangoldt`。
形式化陈述：residueClass : Nat -> Real
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The von Mangoldt function restricted to the residue class `a` mod `q`.
-/
noncomputable abbrev residueClass : ℕ → ℝ :=
  {n : ℕ | (n : ZMod q) = a}.indicator (vonMangoldt ·)
/-
**ArithmeticFunction.vonMangoldt.residueClass_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `
ArithmeticFunction.vonMangoldt`。
形式化陈述：residueClass_nonneg (n : Nat) : 0 <= residueClass a n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_apply_nonneg`：∀ {α : Type u_2} {M : Type u_3} [inst : Preo
rder M] [inst_1 : Zero M] {s : Set α} {f : α → M} {a : α},   (a ∈ s → 0 ≤ f a) →
 0 ≤ s.indicator…
· 使用定理 `ArithmeticFunction.vonMangoldt_nonneg`：∀ {n : ℕ}, 0 ≤ ArithmeticFunction
.vonMangoldt n
-/
lemma residueClass_nonneg (n : ℕ) : 0 ≤ residueClass a n :=
  Set.indicator_apply_nonneg fun _ ↦ vonMangoldt_nonneg
/-
**ArithmeticFunction.vonMangoldt.residueClass_le** 是 Mathlib 中的一个引理，位于命名空间 `Arit
hmeticFunction.vonMangoldt`。
形式化陈述：residueClass_le (n : Nat) : residueClass a n <= vonMangoldt n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.indicator_apply_le'`：∀ {α : Type u_2} {M : Type u_3} [inst : LE M] [
inst_1 : Zero M] {s : Set α} {f : α → M} {a : α} {y : M},   (a ∈ s → f a ≤ y) → 
(a ∉ s → 0 ≤ …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ArithmeticFunction.vonMangoldt_nonneg`：∀ {n : ℕ}, 0 ≤ ArithmeticFunction
.vonMangoldt n
-/
lemma residueClass_le (n : ℕ) : residueClass a n ≤ vonMangoldt n :=
  Set.indicator_apply_le' (fun _ ↦ le_rfl) (fun _ ↦ vonMangoldt_nonneg)

@[simp]
/-
**ArithmeticFunction.vonMangoldt.residueClass_apply_zero** 是 Mathlib 中的一个引理，位于命名
空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：residueClass_apply_zero : residueClass a 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `ArithmeticFunction.map_zero`：map_zero {f : ArithmeticFunction R} : f 0 =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma residueClass_apply_zero : residueClass a 0 = 0 := by
  simp only [Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_zero, map_zero,
    implies_true]
/-
**ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one** 是 Mathl
ib 中的一个引理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：abscissaOfAbsConv_residueClass_le_one : abscissaOfAbsConv ↗(residueClass a
) <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable`：LSeries.absci
ssaOfAbsConv_le_of_forall_lt_LSeriesSummable {f : Nat -> Complex} {x : Real} (h 
: forall y : Real, x < y -> LSeriesSummable f y…
· 使用引理 `ArithmeticFunction.LSeriesSummable_vonMangoldt`：LSeriesSummable_vonMango
ldt {s : Complex} (hs : 1 < s.re) : LSeriesSummable ↗Λ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator.eq_1`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s :
 Set α) (f : α → M) (x : α),   s.indicator f x = if x ∈ s then f x else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Summable.indicator`：∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace
 α] [inst_1 : AddCommGroup α] [IsUniformAddGroup α] {f : β → α}   [CompleteSpace
 α], Sum…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
-/
lemma abscissaOfAbsConv_residueClass_le_one :
    abscissaOfAbsConv ↗(residueClass a) ≤ 1 := by
  refine abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy ↦ ?_
  unfold LSeriesSummable
  have := LSeriesSummable_vonMangoldt <| show 1 < (y : ℂ).re by simp only [ofReal_re, hy]
  convert! this.indicator {n : ℕ | (n : ZMod q) = a}
  ext1 n
  by_cases hn : (n : ZMod q) = a
  · simp +contextual only [term, Set.indicator, Set.mem_ofPred_eq, hn, ↓reduceIte, apply_ite,
      ite_self]
  · simp +contextual only [term, Set.mem_ofPred_eq, hn, not_false_eq_true, Set.indicator_of_notMem,
      ofReal_zero, zero_div, ite_self]

/-- The set we are interested in (prime numbers in the residue class `a`) is the same as the support
of `ArithmeticFunction.vonMangoldt.residueClass` restricted to primes (and divided by `n`;
this is how this result is used later). -/
/-
**ArithmeticFunction.vonMangoldt.support_residueClass_prime_div** 是 Mathlib 中的一个
引理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：support_residueClass_prime_div : Function.support (fun n : Nat => (if n.Pr
ime then residueClass a n else 0) / n) = {p : Nat | p.Prime ∧ (p : ZMod q) = a}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ArithmeticFunction.vonMangoldt_ne_zero_iff`：∀ {n : ℕ}, ArithmeticFunctio
n.vonMangoldt n ≠ 0 ↔ IsPrimePow n
· 使用定理 `Nat.Prime.isPrimePow`：Nat.Prime.isPrimePow {p : Nat} (hp : p.Prime) : Is
PrimePow p
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0

--- 原说明 ---
The set we are interested in (prime numbers in the residue class `a`) is the sam
e as the support
of `ArithmeticFunction.vonMangoldt.residueClass` restricted to primes (and divid
ed by `n`;
this is how this result is used later).
-/
lemma support_residueClass_prime_div :
    Function.support (fun n : ℕ ↦ (if n.Prime then residueClass a n else 0) / n) =
      {p : ℕ | p.Prime ∧ (p : ZMod q) = a} := by
  simp only [Function.support, ne_eq, div_eq_zero_iff, ite_eq_right_iff,
    Set.indicator_apply_eq_zero, Set.mem_ofPred_eq, Nat.cast_eq_zero, not_or, Classical.not_imp]
  ext1 p
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun H ↦ ⟨H.1.1, H.1.2.1⟩,
    fun H ↦ ⟨⟨H.1, H.2, vonMangoldt_ne_zero_iff.mpr H.1.isPrimePow⟩, H.1.ne_zero⟩⟩
/-
**ArithmeticFunction.vonMangoldt.F** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunction
.vonMangoldt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def F₀ (n : ℕ) : ℝ := (if n.Prime then 0 else vonMangoldt n) / n
/-
**ArithmeticFunction.vonMangoldt.F'** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFunctio
n.vonMangoldt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def F' (pk : Nat.Primes × ℕ) : ℝ := F₀ (pk.1 ^ (pk.2 + 1))
/-
**ArithmeticFunction.vonMangoldt.F''** 是 Mathlib 中的一个定义，位于命名空间 `ArithmeticFuncti
on.vonMangoldt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private noncomputable def F'' : Nat.Primes × ℕ → ℝ := F' ∘ (Prod.map _root_.id (· + 1))
/-
**ArithmeticFunction.vonMangoldt.F''_le** 是 Mathlib 中的一个引理，位于命名空间 `ArithmeticFun
ction.vonMangoldt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma F''_le (p : Nat.Primes) (k : ℕ) : F'' (p, k) ≤ 2 * (p : ℝ)⁻¹ ^ (k + 3 / 2 : ℝ) :=
  calc _
    _ = Real.log p * (p : ℝ)⁻¹ ^ (k + 2) := by
      simp only [F'', Function.comp_apply, F', F₀, Prod.map_apply, id_eq, le_add_iff_nonneg_left,
        zero_le, Nat.Prime.not_prime_pow, ↓reduceIte, vonMangoldt_apply_prime p.prop,
        vonMangoldt_apply_pow (Nat.zero_ne_add_one _).symm, Nat.cast_pow, div_eq_mul_inv,
        inv_pow (p : ℝ) (k + 2)]
    _ ≤ (p : ℝ) ^ (1 / 2 : ℝ) / (1 / 2) * (p : ℝ)⁻¹ ^ (k + 2) :=
        mul_le_mul_of_nonneg_right (Real.log_le_rpow_div p.val.cast_nonneg one_half_pos)
          (pow_nonneg (inv_nonneg_of_nonneg (Nat.cast_nonneg ↑p)) (k + 2))
    _ = 2 * (p : ℝ)⁻¹ ^ (-1 / 2 : ℝ) * (p : ℝ)⁻¹ ^ (k + 2) := by
      simp only [← div_mul, div_one, mul_comm, neg_div, Real.inv_rpow p.val.cast_nonneg,
        ← Real.rpow_neg p.val.cast_nonneg, neg_neg]
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_natCast,
        ← Real.rpow_add <| by have := p.prop.pos; positivity, Nat.cast_add, Nat.cast_two,
        add_comm, add_assoc]
      norm_num

open Nat.Primes
/-
**ArithmeticFunction.vonMangoldt.summable_F''** 是 Mathlib 中的一个引理，位于命名空间 `Arithme
ticFunction.vonMangoldt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma summable_F'' : Summable F'' := by
  have hp₀ (p : Nat.Primes) : 0 < (p : ℝ)⁻¹ := inv_pos_of_pos (Nat.cast_pos.mpr p.prop.pos)
  have hp₁ (p : Nat.Primes) : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ <| mod_cast p.prop.pos).mpr <| Nat.one_lt_cast.mpr <| p.prop.one_lt
  suffices Summable fun (pk : Nat.Primes × ℕ) ↦ (pk.1 : ℝ)⁻¹ ^ (pk.2 + 3 / 2 : ℝ) by
    refine (Summable.mul_left 2 this).of_nonneg_of_le (fun pk ↦ ?_) (fun pk ↦ F''_le pk.1 pk.2)
    simp only [F'', Function.comp_apply, F', F₀, Prod.map_fst, id_eq, Prod.map_snd, Nat.cast_pow]
    positivity [vonMangoldt_nonneg (n := (pk.1 : ℕ) ^ (pk.2 + 2))]
  conv => enter [1, pk]; rw [Real.rpow_add <| hp₀ pk.1, Real.rpow_natCast]
  refine (summable_prod_of_nonneg (fun _ ↦ by positivity)).mpr ⟨(fun p ↦ ?_), ?_⟩
  · dsimp only -- otherwise the `exact` below times out
    exact Summable.mul_right _ <| summable_geometric_of_lt_one (hp₀ p).le (hp₁ p)
  · dsimp only
    conv => enter [1, p]; rw [tsum_mul_right, tsum_geometric_of_lt_one (hp₀ p).le (hp₁ p)]
    refine (summable_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).mul_left 2
      |>.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    · positivity [sub_pos.mpr (hp₁ p)]
    · rw [Real.inv_rpow p.val.cast_nonneg, Real.rpow_neg p.val.cast_nonneg]
      gcongr
      rw [inv_le_comm₀ (sub_pos.mpr (hp₁ p)) zero_lt_two, le_sub_comm,
        show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, inv_le_inv₀ (mod_cast p.prop.pos) zero_lt_two]
      exact Nat.ofNat_le_cast.mpr p.prop.two_le

/-- The function `n ↦ Λ n / n`, restricted to non-primes in a residue class, is summable.
This is used to convert results on `ArithmeticFunction.vonMangoldt.residueClass` to results
on primes in an arithmetic progression. -/
/-
**ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div** 是 Mathli
b 中的一个引理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：summable_residueClass_non_primes_div : Summable fun n : Nat => (if n.Prime
 then 0 else residueClass a n) / n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ArithmeticFunction.vonMangoldt.residueClass_nonneg`：residueClass_nonneg 
(n : Nat) : 0 <= residueClass a n
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.ite_nonneg`：ite_nonneg [LE α] (ha : 0 <= a) (hb 
: 0 <= b) : 0 <= ite p a b
· 使用引理 `Mathlib.Meta.Positivity.nonneg_of_isNat`：nonneg_of_isNat {n : Nat} [Semi
ring A] [PartialOrder A] [IsOrderedRing A] (h : NormNum.IsNat e n) : 0 <= (e : A
)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `ArithmeticFunction.vonMangoldt.residueClass_le`：residueClass_le (n : Nat
) : residueClass a n <= vonMangoldt n
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Summable.of_nonneg_of_le`：Summable.of_nonneg_of_le {f g : β -> Real} (hg
 : forall b, 0 <= g b) (hgf : forall b, g b <= f b) (hf : Summable f) : Summable
 g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
The function `n ↦ Λ n / n`, restricted to non-primes in a residue class, is summ
able.
This is used to convert results on `ArithmeticFunction.vonMangoldt.residueClass`
 to results
on primes in an arithmetic progression.
-/
lemma summable_residueClass_non_primes_div :
    Summable fun n : ℕ ↦ (if n.Prime then 0 else residueClass a n) / n := by
  have h₀ (n : ℕ) : 0 ≤ (if n.Prime then 0 else residueClass a n) / n := by
    positivity [residueClass_nonneg a n]
  have hleF₀ (n : ℕ) : (if n.Prime then 0 else residueClass a n) / n ≤ F₀ n := by
    refine div_le_div_of_nonneg_right ?_ n.cast_nonneg
    split_ifs; exacts [le_rfl, residueClass_le a n]
  refine Summable.of_nonneg_of_le h₀ hleF₀ ?_
  have hF₀ (p : Nat.Primes) : F₀ p.val = 0 := by
    simp only [p.prop, ↓reduceIte, zero_div, F₀]
  refine (summable_subtype_iff_indicator (s := {n | IsPrimePow n}).mp ?_).congr
      fun n ↦ Set.indicator_apply_eq_self.mpr fun (hn : ¬ IsPrimePow n) ↦ ?_
  swap
  · simp +contextual only [div_eq_zero_iff, ite_eq_left_iff, vonMangoldt_eq_zero_iff, hn,
      not_false_eq_true, implies_true, Nat.cast_eq_zero, true_or, F₀]
  have hFF' :
      F₀ ∘ Subtype.val (p := fun n ↦ n ∈ {n | IsPrimePow n}) = F' ∘ ⇑prodNatEquiv.symm := by
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
  refine (Function.Injective.summable_iff ?_ fun u hu ↦ ?_).mp <| hF'₁ ▸ summable_F''
  · exact Function.Injective.prodMap (fun ⦃a₁ a₂⦄ a ↦ a) <| add_left_injective 1
  · simp only [Set.range_prodMap, Set.range_id, Set.mem_prod, Set.mem_univ, Set.mem_range,
      Nat.exists_add_one_eq, true_and, not_lt, nonpos_iff_eq_zero] at hu
    rw [← hF'₀ u.1, ← hu]

variable [NeZero q] {a}

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function by Dirichlet characters. -/
/-
**ArithmeticFunction.vonMangoldt.residueClass_apply** 是 Mathlib 中的一个引理，位于命名空间 `A
rithmeticFunction.vonMangoldt`。
形式化陈述：residueClass_apply (ha : IsUnit a) (n : Nat) : residueClass a n = (q.totie
nt : Complex)⁻¹ * ∑ χ : DirichletCharacter Complex q, χ a⁻¹ * χ n * vonMangoldt 
n
参数：ha : IsUnit a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_inv_mul_iff_mul_eq₀`：eq_inv_mul_iff_mul_eq₀ (hb : b != 0) : a = b⁻¹ *
 c ↔ b * a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirichletCharacter.sum_char_inv_mul_char_eq`：sum_char_inv_mul_char_eq {a
 : ZMod n} (ha : IsUnit a) (b : ZMod n) : ∑ χ : DirichletCharacter R n, χ a⁻¹ * 
χ b = if a = b then (n.totient : …
· 使用定理 `ZMod.instFiniteZModUnits`：∀ (n : ℕ), Finite (ZMod n)ˣ
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a

--- 原说明 ---
We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combina
tion
of twists of the von Mangoldt function by Dirichlet characters.
-/
lemma residueClass_apply (ha : IsUnit a) (n : ℕ) :
    residueClass a n =
      (q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ n * vonMangoldt n := by
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp +contextual only [residueClass, Set.indicator_apply, Set.mem_ofPred_eq, apply_ite,
    ofReal_zero, mul_zero, ← Finset.sum_mul, sum_char_inv_mul_char_eq ℂ ha n, eq_comm (a := a),
    ite_mul, zero_mul, ↓reduceIte, ite_self]

/-- We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combination
of twists of the von Mangoldt function by Dirichlet characters. -/
/-
**ArithmeticFunction.vonMangoldt.residueClass_eq** 是 Mathlib 中的一个引理，位于命名空间 `Arit
hmeticFunction.vonMangoldt`。
形式化陈述：residueClass_eq (ha : IsUnit a) : ↗(residueClass a) = (q.totient : Complex
)⁻¹ • ∑ χ : DirichletCharacter Complex q, χ a⁻¹ • (fun n : Nat => χ n * vonMango
ldt n)
参数：ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ArithmeticFunction.vonMangoldt.residueClass_apply`：residueClass_apply (h
a : IsUnit a) (n : Nat) : residueClass a n = (q.totient : Complex)⁻¹ * ∑ χ : Dir
ichletCharacter Complex q, χ a⁻¹ * χ n …

--- 原说明 ---
We can express `ArithmeticFunction.vonMangoldt.residueClass` as a linear combina
tion
of twists of the von Mangoldt function by Dirichlet characters.
-/
lemma residueClass_eq (ha : IsUnit a) :
    ↗(residueClass a) = (q.totient : ℂ)⁻¹ •
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ • (fun n : ℕ ↦ χ n * vonMangoldt n) := by
  ext1 n
  simpa only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, ← mul_assoc]
    using residueClass_apply ha n

/-- The L-series of the von Mangoldt function restricted to the residue class `a` mod `q`
with `a` invertible in `ZMod q` is a linear combination of logarithmic derivatives of
L-functions of the Dirichlet characters mod `q` (on `re s > 1`). -/
/-
**ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq** 是 Mathlib 中的一个引理，位于命名
空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：LSeries_residueClass_eq (ha : IsUnit a) {s : Complex} (hs : 1 < s.re) : LS
eries ↗(residueClass a) s = -(q.totient : Complex)⁻¹ * ∑ χ : DirichletCharacter 
Complex q, χ a⁻¹ * (deriv (LFunction χ) s / LFunction χ s)
参数：ha : IsUnit a；hs : 1 < s.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `DirichletCharacter.deriv_LFunction_eq_deriv_LSeries`：deriv_LFunction_eq_
deriv_LSeries (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re) :
 deriv (LFunction χ) s = deriv (LSeries (…
· 使用引理 `DirichletCharacter.LFunction_eq_LSeries`：LFunction_eq_LSeries (χ : Diric
hletCharacter Complex N) {s : Complex} (hs : 1 < re s) : LFunction χ s = LSeries
 (χ ·) s
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirichletCharacter.LSeries_twist_vonMangoldt_eq`：LSeries_twist_vonMangol
dt_eq {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs : 1 < s.re)
 : L (↗χ * ↗Λ) s = -deriv (L ↗χ) s / …
· 使用引理 `eq_inv_mul_iff_mul_eq₀`：eq_inv_mul_iff_mul_eq₀ (hb : b != 0) : a = b⁻¹ *
 c ↔ b * a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.totient_pos`：∀ {n : ℕ}, 0 < n.totient ↔ 0 < n
· 使用定理 `Nat.pos_of_neZero`：∀ (n : ℕ) [NeZero n], 0 < n
· 使用引理 `LSeries_sum`：LSeries_sum (hf : forall i in S, LSeriesSummable (f i) s) :
 LSeries (∑ i in S, f i) s = ∑ i in S, LSeries (f i) s
· 使用引理 `LSeriesSummable.smul`：LSeriesSummable.smul {f : Nat -> Complex} (c : Com
plex) {s : Complex} (hf : LSeriesSummable f s) : LSeriesSummable (c • f) s
· 使用引理 `DirichletCharacter.LSeriesSummable_twist_vonMangoldt`：LSeriesSummable_tw
ist_vonMangoldt {N : Nat} (χ : DirichletCharacter Complex N) {s : Complex} (hs :
 1 < s.re) : LSeriesSummable (↗χ * ↗Λ) s
· 使用引理 `LSeries_congr`：LSeries_congr {f g : Nat -> Complex} (h : forall {n}, n !
= 0 -> f n = g n) (s : Complex) : LSeries f s = LSeries g s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ArithmeticFunction.vonMangoldt.residueClass_apply`：residueClass_apply (h
a : IsUnit a) (n : Nat) : residueClass a n = (q.totient : Complex)⁻¹ * ∑ χ : Dir
ichletCharacter Complex q, χ a⁻¹ * χ n …
· 使用定理 `mul_inv_cancel_of_invertible`：mul_inv_cancel_of_invertible (a : α) [Inve
rtible a] : a * a⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The L-series of the von Mangoldt function restricted to the residue class `a` mo
d `q`
with `a` invertible in `ZMod q` is a linear combination of logarithmic derivativ
es of
L-functions of the Dirichlet characters mod `q` (on `re s > 1`).
-/
lemma LSeries_residueClass_eq (ha : IsUnit a) {s : ℂ} (hs : 1 < s.re) :
    LSeries ↗(residueClass a) s =
      -(q.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ *
        (deriv (LFunction χ) s / LFunction χ s) := by
  simp only [deriv_LFunction_eq_deriv_LSeries _ hs, LFunction_eq_LSeries _ hs, neg_mul, ← mul_neg,
    ← Finset.sum_neg_distrib, ← neg_div, ← LSeries_twist_vonMangoldt_eq _ hs]
  rw [eq_inv_mul_iff_mul_eq₀ <| mod_cast (Nat.totient_pos.mpr q.pos_of_neZero).ne']
  simp_rw [← LSeries_smul,
    ← LSeries_sum <| fun χ _ ↦ (LSeriesSummable_twist_vonMangoldt χ hs).smul _]
  refine LSeries_congr (fun {n} _ ↦ ?_) s
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
/-
**ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux** 是 Mathlib 中的一个缩写定义，位
于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：LFunctionResidueClassAux (s : Complex) : Complex
参数：s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev LFunctionResidueClassAux (s : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ * (-deriv (LFunctionTrivChar₁ q) s / LFunctionTrivChar₁ q s -
    ∑ χ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), χ a⁻¹ * deriv (LFunction χ) s / LFunction χ s)

/-- The auxiliary function is continuous away from the zeros of the L-functions of the Dirichlet
characters mod `q` (including at `s = 1`). -/
/-
**ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux'** 是 Math
lib 中的一个引理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：continuousOn_LFunctionResidueClassAux' : ContinuousOn (LFunctionResidueCla
ssAux a) {s | s = 1 ∨ forall χ : DirichletCharacter Complex q, LFunction χ s != 
0}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ContinuousOn.mul`：ContinuousOn.mul (hf : ContinuousOn f s) (hg : Continu
ousOn g s) : ContinuousOn (f * g) s
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1 :
 Add M] [ContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f g : 
X → M}…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁`：continu
ousOn_neg_logDeriv_LFunctionTrivChar₁ : ContinuousOn (fun s => -deriv (LFunction
TrivChar₁ n) s / LFunctionTrivChar₁ n s) {s | s = 1 ∨…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `continuousOn_finsetSum`：∀ {ι : Type u_1} {M : Type u_3} {X : Type u_5} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace M]   [inst_2 : AddCommMono
id M] [Conti…
· 使用引理 `DirichletCharacter.continuousOn_neg_logDeriv_LFunction_of_nontriv`：conti
nuousOn_neg_logDeriv_LFunction_of_nontriv (hχ : χ != 1) : ContinuousOn (fun s =>
 -deriv (LFunction χ) s / LFunction χ s) {s | LFunction…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `DirichletCharacter.LFunction_ne_zero_of_one_le_re`：LFunction_ne_zero_of_
one_le_re ⦃s : Complex⦄ (hχs : χ != 1 ∨ s != 1) (hs : 1 <= s.re) : LFunction χ s
 != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The auxiliary function is continuous away from the zeros of the L-functions of t
he Dirichlet
characters mod `q` (including at `s = 1`).
-/
lemma continuousOn_LFunctionResidueClassAux' :
    ContinuousOn (LFunctionResidueClassAux a)
      {s | s = 1 ∨ ∀ χ : DirichletCharacter ℂ q, LFunction χ s ≠ 0} := by
  rw [show LFunctionResidueClassAux a = fun s ↦ _ from rfl]
  simp only [LFunctionResidueClassAux, sub_eq_add_neg]
  refine continuousOn_const.mul <| ContinuousOn.add ?_ ?_
  · refine (continuousOn_neg_logDeriv_LFunctionTrivChar₁ q).mono fun s hs ↦ ?_
    simp only [ne_eq, Set.mem_ofPred_eq] at hs
    tauto
  · simp only [← Finset.sum_neg_distrib, mul_div_assoc, ← mul_neg, ← neg_div]
    refine continuousOn_finsetSum _ fun χ hχ ↦ continuousOn_const.mul ?_
    replace hχ : χ ≠ 1 := by simpa only [ne_eq, Finset.mem_compl, Finset.mem_singleton] using hχ
    refine (continuousOn_neg_logDeriv_LFunction_of_nontriv hχ).mono fun s hs ↦ ?_
    simp only [ne_eq, Set.mem_ofPred_eq] at hs
    rcases hs with rfl | hs
    · simp only [ne_eq, Set.mem_ofPred_eq, one_re, le_refl,
        LFunction_ne_zero_of_one_le_re χ (.inl hχ), not_false_eq_true]
    · exact hs χ

/-- The L-series of the von Mangoldt function restricted to the prime residue class `a` mod `q`
is continuous on `re s ≥ 1` except for a simple pole at `s = 1` with residue `(q.totient)⁻¹`.
The statement as given here in terms of `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux`
is equivalent. -/
/-
**ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux** 是 Mathl
ib 中的一个引理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：continuousOn_LFunctionResidueClassAux : ContinuousOn (LFunctionResidueClas
sAux a) {s | 1 <= s.re}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用引理 `ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux'`：c
ontinuousOn_LFunctionResidueClassAux' : ContinuousOn (LFunctionResidueClassAux a
) {s | s = 1 ∨ forall χ : DirichletCharacter Complex q, LFu…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `DirichletCharacter.LFunction_ne_zero_of_one_le_re`：LFunction_ne_zero_of_
one_le_re ⦃s : Complex⦄ (hχs : χ != 1 ∨ s != 1) (hs : 1 <= s.re) : LFunction χ s
 != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a

--- 原说明 ---
The L-series of the von Mangoldt function restricted to the prime residue class 
`a` mod `q`
is continuous on `re s ≥ 1` except for a simple pole at `s = 1` with residue `(q
.totient)⁻¹`.
The statement as given here in terms of `ArithmeticFunction.vonMangoldt.LFunctio
nResidueClassAux`
is equivalent.
-/
lemma continuousOn_LFunctionResidueClassAux :
    ContinuousOn (LFunctionResidueClassAux a) {s | 1 ≤ s.re} := by
  refine (continuousOn_LFunctionResidueClassAux' a).mono fun s hs ↦ ?_
  rcases eq_or_ne s 1 with rfl | hs₁
  · simp only [ne_eq, Set.mem_ofPred_eq, true_or]
  · simp only [ne_eq, Set.mem_ofPred_eq, hs₁, false_or]
    exact fun χ ↦ LFunction_ne_zero_of_one_le_re χ (.inr hs₁) <| Set.mem_ofPred.mp hs

variable {a}

open scoped LSeries.notation

/-- The auxiliary function agrees on `re s > 1` with the L-series of the von Mangoldt function
restricted to the residue class `a : ZMod q` minus the principal part `(q.totient)⁻¹/(s-1)`
of its pole at `s = 1`. -/
/-
**ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux** 是 Mathlib 中的一个引
理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：eqOn_LFunctionResidueClassAux (ha : IsUnit a) : Set.EqOn (LFunctionResidue
ClassAux a) (fun s => L ↗(residueClass a) s - (q.totient : Complex)⁻¹ / (s - 1))
 {s | 1 < s.re}
参数：ha : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq`：LSeries_residueC
lass_eq (ha : IsUnit a) {s : Complex} (hs : 1 < s.re) : LSeries ↗(residueClass a
) s = -(q.totient : Complex)⁻¹ * ∑ χ : Diric…
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `div_eq_mul_one_div`：div_eq_mul_one_div (a b : G) : a / b = a * (1 / b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `ZMod.inv_mul_of_unit`：inv_mul_of_unit {n : Nat} (a : ZMod n) (h : IsUnit
 a) : a⁻¹ * a = 1
· 使用定理 `Fintype.sum_eq_add_sum_compl`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ad
dCommMonoid M] [inst_1 : DecidableEq ι] [inst_2 : Fintype ι] (a : ι)   (f : ι → 
M), ∑ i, f i = f a…
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Complex.one_re`：one_re : (1 : Complex).re = 1
· 使用引理 `DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one`：deriv_LFunc
tionTrivChar₁_apply_of_ne_one {s : Complex} (hs : s != 1) : deriv (LFunctionTriv
Char₁ n) s = (s - 1) * deriv (LFunctionTrivChar n…
· 使用定理 `DirichletCharacter.LFunctionTrivChar₁.eq_1`：∀ (n : ℕ) [inst : NeZero n],
   DirichletCharacter.LFunctionTrivChar₁ n =     Function.update (fun s => (s - 
1) * DirichletCharacter.LFunctio…
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `DirichletCharacter.LFunctionTrivChar.eq_1`：∀ (N : ℕ) [inst : NeZero N], 
DirichletCharacter.LFunctionTrivChar N = DirichletCharacter.LFunction 1
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The auxiliary function agrees on `re s > 1` with the L-series of the von Mangold
t function
restricted to the residue class `a : ZMod q` minus the principal part `(q.totien
t)⁻¹/(s-1)`
of its pole at `s = 1`.
-/
lemma eqOn_LFunctionResidueClassAux (ha : IsUnit a) :
    Set.EqOn (LFunctionResidueClassAux a)
      (fun s ↦ L ↗(residueClass a) s - (q.totient : ℂ)⁻¹ / (s - 1))
      {s | 1 < s.re} := by
  intro s hs
  replace hs := Set.mem_ofPred.mp hs
  simp only [LSeries_residueClass_eq ha hs, LFunctionResidueClassAux]
  rw [neg_div, ← neg_add', mul_neg, ← neg_mul, div_eq_mul_one_div (q.totient : ℂ)⁻¹,
    sub_eq_add_neg, ← neg_mul, ← mul_add]
  congrm (_ * ?_)
  -- this should be easier, but `IsUnit.inv ha` does not work here
  have ha' : IsUnit a⁻¹ := isUnit_of_dvd_one ⟨a, (ZMod.inv_mul_of_unit a ha).symm⟩
  classical -- for `Fintype.sum_eq_add_sum_compl`
  rw [Fintype.sum_eq_add_sum_compl 1, MulChar.one_apply ha', one_mul, add_right_comm]
  simp only [mul_div_assoc]
  congrm (?_ + _)
  have hs₁ : s ≠ 1 := fun h ↦ ((h ▸ hs).trans_eq one_re).false
  rw [deriv_LFunctionTrivChar₁_apply_of_ne_one _ hs₁, LFunctionTrivChar₁,
    Function.update_of_ne hs₁, LFunctionTrivChar, add_div,
    mul_div_mul_left _ _ (sub_ne_zero_of_ne hs₁)]
  conv_lhs => enter [2, 1]; rw [← mul_one (LFunction ..)]
  rw [mul_comm _ 1, mul_div_mul_right _ _ <| LFunction_ne_zero_of_one_le_re 1 (.inr hs₁) hs.le]

/-- The auxiliary function takes real values for real arguments `x > 1`. -/
/-
**ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux_real** 是 Mathlib 中的一个引
理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：LFunctionResidueClassAux_real (ha : IsUnit a) {x : Real} (hx : 1 < x) : LF
unctionResidueClassAux a x = (LFunctionResidueClassAux a x).re
参数：ha : IsUnit a；hx : 1 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux`：eqOn_LFunc
tionResidueClassAux (ha : IsUnit a) : Set.EqOn (LFunctionResidueClassAux a) (fun
 s => L ↗(residueClass a) s - (q.totient : Complex…
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `LSeries.eq_1`：∀ (f : ℕ → ℂ) (s : ℂ), LSeries f s = ∑' (n : ℕ), LSeries.t
erm f s n
· 使用定理 `Complex.re_tsum`：∀ {α : Type u_1} {L : SummationFilter α} [L.NeBot] {f :
 α → ℂ},   Summable f L → (∑'[L] (a : α), f a).re = ∑'[L] (a : α), (f a).re
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `LSeriesSummable_of_abscissaOfAbsConv_lt_re`：LSeriesSummable_of_abscissaO
fAbsConv_lt_re {f : Nat -> Complex} {s : Complex} (hs : abscissaOfAbsConv f < s.
re) : LSeriesSummable f s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one`：ab
scissaOfAbsConv_residueClass_le_one : abscissaOfAbsConv ↗(residueClass a) <= 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `LSeries.term_of_ne_zero`：term_of_ne_zero {n : Nat} (hn : n != 0) (f : Na
t -> Complex) (s : Complex) : term f s n = f n / n ^ s
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Complex.ofReal_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r

--- 原说明 ---
The auxiliary function takes real values for real arguments `x > 1`.
-/
lemma LFunctionResidueClassAux_real (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    LFunctionResidueClassAux a x = (LFunctionResidueClassAux a x).re := by
  rw [eqOn_LFunctionResidueClassAux ha hx]
  simp only [sub_re, ofReal_sub]
  congr 1
  · rw [LSeries, re_tsum <| LSeriesSummable_of_abscissaOfAbsConv_lt_re <|
      (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| by norm_cast]
    push_cast
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero, zero_re, ofReal_zero]
    · simp only [term_of_ne_zero hn, ← ofReal_natCast n, ← ofReal_cpow n.cast_nonneg, ← ofReal_div,
        ofReal_re]
  · rw [← ofReal_natCast, ← ofReal_one, ← ofReal_sub, ← ofReal_inv,
      ← ofReal_div, ofReal_re]

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- As `x` approaches `1` from the right along the real axis, the L-series of
`ArithmeticFunction.vonMangoldt.residueClass` is bounded below by `(q.totient)⁻¹/(x-1) - C`. -/
/-
**ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound** 是 Mathlib 中的
一个引理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：LSeries_residueClass_lower_bound (ha : IsUnit a) : exists C : Real, forall
 {x : Real} (_ : x in Set.Ioc 1 2), (q.totient : Real)⁻¹ / (x - 1) - C <= ∑' n, 
residueClass a n / (n : Real) ^ x
参数：ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ofReal_injective`：ofReal_injective : Function.Injective ((↑) : R
eal -> Complex)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_tsum`：∀ {α : Type u_1} {L : SummationFilter α} (f : α → ℝ
), ↑(∑'[L] (a : α), f a) = ∑'[L] (a : α), ↑(f a)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux_real`：LFunctionR
esidueClassAux_real (ha : IsUnit a) {x : Real} (hx : 1 < x) : LFunctionResidueCl
assAux a x = (LFunctionResidueClassAux a x).re
· 使用引理 `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux`：eqOn_LFunc
tionResidueClassAux (ha : IsUnit a) : Set.EqOn (LFunctionResidueClassAux a) (fun
 s => L ↗(residueClass a) s - (q.totient : Complex…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `tsum_congr`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [in
st_1 : TopologicalSpace α] {L : SummationFilter β}   {f g : β → α}, (∀ (b : β), 
…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `ArithmeticFunction.vonMangoldt.residueClass_apply_zero`：residueClass_app
ly_zero : residueClass a 0 = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
As `x` approaches `1` from the right along the real axis, the L-series of
`ArithmeticFunction.vonMangoldt.residueClass` is bounded below by `(q.totient)⁻¹
/(x-1) - C`.
-/
lemma LSeries_residueClass_lower_bound (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
      (q.totient : ℝ)⁻¹ / (x - 1) - C ≤ ∑' n, residueClass a n / (n : ℝ) ^ x := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : ℝ) ^ x =
        (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hx,
      eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux a)
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨C, hC⟩ := bddBelow_def.mp <| IsCompact.bddBelow_image isCompact_Icc this
  replace hC {x : ℝ} (hx : x ∈ Set.Icc 1 2) : C ≤ (LFunctionResidueClassAux a x).re :=
    hC (LFunctionResidueClassAux a x).re <|
      Set.mem_image_of_mem (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) hx
  refine ⟨-C, fun {x} hx ↦ ?_⟩
  rw [H hx.1, add_comm, sub_neg_eq_add, add_le_add_iff_left]
  exact hC <| Set.mem_Icc_of_Ioc hx

open vonMangoldt Filter Topology in
/-- The function `n ↦ Λ n / n` restricted to primes in an invertible residue class
is not summable. This then implies that there must be infinitely many such primes. -/
/-
**ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div** 是 Mathlib
 中的一个引理，位于命名空间 `ArithmeticFunction.vonMangoldt`。
形式化陈述：not_summable_residueClass_prime_div (ha : IsUnit a) : ¬ Summable fun n : N
at => (if n.Prime then residueClass a n else 0) / n
参数：ha : IsUnit a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_add_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : 
Add α] (a b c d : α),   ((if P then a else b) + if P then c else d) = if P then 
a…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Summable.add`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [
inst_1 : TopologicalSpace α] {f g : β → α}   {L : SummationFilter β} [Continuous
Ad…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用引理 `ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div`：sum
mable_residueClass_non_primes_div : Summable fun n : Nat => (if n.Prime then 0 e
lse residueClass a n) / n
· 使用定理 `Summable.tsum_le_tsum`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFil
ter ι} [inst : AddCommMonoid α] [inst_1 : Preorder α]   [IsOrderedAddMonoid α] [
inst_3 : To…
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ArithmeticFunction.vonMangoldt.residueClass_apply_zero`：residueClass_app
ly_zero : residueClass a 0 = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `EuclideanDomain.div_zero`：div_zero (a : R) : a / 0 = 0
（共 88 条，此处仅展示前 30 条）

--- 原说明 ---
The function `n ↦ Λ n / n` restricted to primes in an invertible residue class
is not summable. This then implies that there must be infinitely many such prime
s.
-/
lemma not_summable_residueClass_prime_div (ha : IsUnit a) :
    ¬ Summable fun n : ℕ ↦ (if n.Prime then residueClass a n else 0) / n := by
  intro H
  have key : Summable fun n : ℕ ↦ residueClass a n / n := by
    convert! (summable_residueClass_non_primes_div a).add H using 2 with n
    simp only [← add_div, ite_add_ite, zero_add, add_zero, ite_self]
  let C := ∑' n, residueClass a n / n
  have H₁ {x : ℝ} (hx : 1 < x) : ∑' n, residueClass a n / (n : ℝ) ^ x ≤ C := by
    refine Summable.tsum_le_tsum (fun n ↦ ?_) ?_ key
    · rcases n.eq_zero_or_pos with rfl | hn
      · simp
      · refine div_le_div_of_nonneg_left (residueClass_nonneg a _) (mod_cast hn) ?_
        conv_lhs => rw [← Real.rpow_one n]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_cast) hx.le
    · exact summable_real_of_abscissaOfAbsConv_lt <|
        (abscissaOfAbsConv_residueClass_le_one a).trans_lt <| mod_cast hx
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound ha
  have H₁ {x} (hx : x ∈ Set.Ioc 1 2) : (q.totient : ℝ)⁻¹ ≤ (C + C') * (x - 1) :=
    (div_le_iff₀ <| sub_pos.mpr hx.1).mp <|
      sub_le_iff_le_add.mp <| (hC' hx).trans (H₁ hx.1)
  have hq : 0 < (q.totient : ℝ)⁻¹ := inv_pos.mpr (mod_cast q.totient.pos_of_neZero)
  rcases le_or_gt (C + C') 0 with h₀ | h₀
  · have := hq.trans_le (H₁ (Set.right_mem_Ioc.mpr one_lt_two))
    rw [show (2 : ℝ) - 1 = 1 by norm_num, mul_one] at this
    exact (this.trans_le h₀).false
  · obtain ⟨ξ, hξ₁, hξ₂⟩ : ∃ ξ ∈ Set.Ioc 1 2, (C + C') * (ξ - 1) < (q.totient : ℝ)⁻¹ := by
      refine ⟨min (1 + (q.totient : ℝ)⁻¹ / (C + C') / 2) 2, ⟨?_, min_le_right ..⟩, ?_⟩
      · simpa only [lt_inf_iff, lt_add_iff_pos_right, Nat.ofNat_pos, div_pos_iff_of_pos_right,
          Nat.one_lt_ofNat, and_true] using div_pos hq h₀
      · rw [← min_sub_sub_right, add_sub_cancel_left, ← lt_div_iff₀' h₀]
        exact (min_le_left ..).trans_lt <| div_lt_self (div_pos hq h₀) one_lt_two
    exact ((H₁ hξ₁).trans_lt hξ₂).false

end ArithmeticFunction.vonMangoldt

end arith_prog

/-!
### Dirichlet's Theorem
-/

section DirichletsTheorem

namespace Nat

open ArithmeticFunction vonMangoldt

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
/-
**Nat.infinite_setOfPred_prime_and_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：infinite_setOfPred_prime_and_eq_mod (ha : IsUnit a) : {p : Nat | p.Prime ∧
 (p : ZMod q) = a}.Infinite
参数：ha : IsUnit a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div`：not_
summable_residueClass_prime_div (ha : IsUnit a) : ¬ Summable fun n : Nat => (if 
n.Prime then residueClass a n else 0) / n
· 使用定理 `summable_of_hasFiniteSupport`：∀ {α : Type u_1} {β : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : TopologicalSpace α] {f : β → α}   {L : SummationFilter 
β} [L.HasSupport],…
· 使用定理 `SummationFilter.instHasSupportOfLeAtTop`：∀ {β : Type u_2} (L : Summation
Filter β) [L.LeAtTop], L.HasSupport
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ArithmeticFunction.vonMangoldt.support_residueClass_prime_div`：support_r
esidueClass_prime_div : Function.support (fun n : Nat => (if n.Prime then residu
eClass a n else 0) / n) = {p : Nat | p.Prime ∧ (p :…

--- 原说明 ---
**Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positiv
e
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers
 `p`
such that `(p : ZMod q) = a`.
-/
theorem infinite_setOfPred_prime_and_eq_mod (ha : IsUnit a) :
    {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite := by
  by_contra! H
  exact not_summable_residueClass_prime_div ha <|
    summable_of_hasFiniteSupport <| show Set.Finite _ from support_residueClass_prime_div a ▸ H

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_eq_mod := infinite_setOfPred_prime_and_eq_mod

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers `p`
such that `(p : ZMod q) = a`. -/
/-
**Nat.forall_exists_prime_gt_and_eq_mod** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : Nat) : exists p > n
, p.Prime ∧ (p : ZMod q) = a
参数：ha : IsUnit a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_iff_exists_gt`：∀ {α : Type u_2} [inst : LinearOrder α] [Loc
allyFiniteOrderBot α] {s : Set α} [Nonempty α],   s.Infinite ↔ ∀ (a : α), ∃ b ∈ 
s, a < b
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.infinite_setOfPred_prime_and_eq_mod`：infinite_setOfPred_prime_and_eq
_mod (ha : IsUnit a) : {p : Nat | p.Prime ∧ (p : ZMod q) = a}.Infinite
· 使用定理 `LT.lt.gt`：∀ {α : Type u_2} [inst : LT α] {a b : α}, a < b → b > a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a

--- 原说明 ---
**Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positiv
e
integer and `a : ZMod q` is a unit, then there are infinitely many prime numbers
 `p`
such that `(p : ZMod q) = a`.
-/
theorem forall_exists_prime_gt_and_eq_mod (ha : IsUnit a) (n : ℕ) :
    ∃ p > n, p.Prime ∧ (p : ZMod q) = a := by
  obtain ⟨p, hp₁, hp₂⟩ := Set.infinite_iff_exists_gt.mp (infinite_setOfPred_prime_and_eq_mod ha) n
  exact ⟨p, hp₂.gt, Set.mem_ofPred.mp hp₁⟩

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ℤ` is coprime to `q`, then there are infinitely many prime numbers `p`
such that `p ≡ a mod q`. -/
/-
**Nat.forall_exists_prime_gt_and_zmodEq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：forall_exists_prime_gt_and_zmodEq (n : Nat) {q : Nat} {a : Int} (hq : q !=
 0) (h : IsCoprime a q) : exists p > n, p.Prime ∧ p ≡ a [ZMOD q]
参数：n : Nat；hq : q != 0；h : IsCoprime a q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.coe_int_isUnit_iff_isCoprime`：coe_int_isUnit_iff_isCoprime (n : Int
) (m : Nat) : IsUnit (n : ZMod m) ↔ IsCoprime (m : Int) n
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `Nat.forall_exists_prime_gt_and_eq_mod`：forall_exists_prime_gt_and_eq_mod
 (ha : IsUnit a) (n : Nat) : exists p > n, p.Prime ∧ (p : ZMod q) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n

--- 原说明 ---
**Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positiv
e
integer and `a : ℤ` is coprime to `q`, then there are infinitely many prime numb
ers `p`
such that `p ≡ a mod q`.
-/
theorem forall_exists_prime_gt_and_zmodEq (n : ℕ) {q : ℕ} {a : ℤ} (hq : q ≠ 0) (h : IsCoprime a q) :
    ∃ p > n, p.Prime ∧ p ≡ a [ZMOD q] := by
  have : NeZero q := ⟨hq⟩
  have : IsUnit (a : ZMod q) := by
    rwa [ZMod.coe_int_isUnit_iff_isCoprime, isCoprime_comm]
  obtain ⟨p, hpn, hpp, heq⟩ := forall_exists_prime_gt_and_eq_mod this n
  refine ⟨p, hpn, hpp, ?_⟩
  simpa [← ZMod.intCast_eq_intCast_iff] using heq

/-- **Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positive
integer and `a : ℕ` is coprime to `q`, then there are infinitely many prime numbers `p`
such that `p ≡ a mod q`. -/
/-
**Nat.forall_exists_prime_gt_and_modEq** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：forall_exists_prime_gt_and_modEq (n : Nat) {q a : Nat} (hq : q != 0) (h : 
a.Coprime q) : exists p > n, p.Prime ∧ p ≡ a [MOD q]
参数：n : Nat；hq : q != 0；h : a.Coprime q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.forall_exists_prime_gt_and_zmodEq`：forall_exists_prime_gt_and_zmodEq
 (n : Nat) {q : Nat} {a : Int} (hq : q != 0) (h : IsCoprime a q) : exists p > n,
 p.Prime ∧ p ≡ a [ZMOD q]

--- 原说明 ---
**Dirichlet's Theorem** on primes in arithmetic progression: if `q` is a positiv
e
integer and `a : ℕ` is coprime to `q`, then there are infinitely many prime numb
ers `p`
such that `p ≡ a mod q`.
-/
theorem forall_exists_prime_gt_and_modEq (n : ℕ) {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ p > n, p.Prime ∧ p ≡ a [MOD q] := by
  simpa using forall_exists_prime_gt_and_zmodEq n (q := q) (a := a) hq (by simpa)

open Filter in
/-
**Nat.frequently_atTop_prime_and_modEq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：frequently_atTop_prime_and_modEq {q a : Nat} (hq : q != 0) (h : a.Coprime 
q) : existsᶠ p in atTop, p.Prime ∧ p ≡ a [MOD q]
参数：hq : q != 0；h : a.Coprime q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.forall_exists_prime_gt_and_modEq`：forall_exists_prime_gt_and_modEq (
n : Nat) {q a : Nat} (hq : q != 0) (h : a.Coprime q) : exists p > n, p.Prime ∧ p
 ≡ a [MOD q]
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma frequently_atTop_prime_and_modEq {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    ∃ᶠ p in atTop, p.Prime ∧ p ≡ a [MOD q] := by
  rw [frequently_atTop]
  intro n
  obtain ⟨p, hn, hp, ha⟩ := forall_exists_prime_gt_and_modEq n hq h
  exact ⟨p, hn.le, hp, ha⟩
/-
**Nat.infinite_setOfPred_prime_and_modEq** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：infinite_setOfPred_prime_and_modEq {q a : Nat} (hq : q != 0) (h : a.Coprim
e q) : Set.Infinite {p : Nat | p.Prime ∧ p ≡ a [MOD q]}
参数：hq : q != 0；h : a.Coprime q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.frequently_atTop_iff_infinite`：Nat.frequently_atTop_iff_infinite {p 
: Nat -> Prop} : (existsᶠ n in atTop, p n) ↔ Set.Infinite { n | p n }
· 使用引理 `Nat.frequently_atTop_prime_and_modEq`：frequently_atTop_prime_and_modEq {
q a : Nat} (hq : q != 0) (h : a.Coprime q) : existsᶠ p in atTop, p.Prime ∧ p ≡ a
 [MOD q]
-/
lemma infinite_setOfPred_prime_and_modEq {q a : ℕ} (hq : q ≠ 0) (h : a.Coprime q) :
    Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
  frequently_atTop_iff_infinite.1 (frequently_atTop_prime_and_modEq hq h)

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_and_modEq := infinite_setOfPred_prime_and_modEq

end Nat

end DirichletsTheorem

