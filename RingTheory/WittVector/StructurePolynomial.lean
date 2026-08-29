/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Robert Y. Lewis
-/
module

public import Mathlib.FieldTheory.Finite.Polynomial
public import Mathlib.NumberTheory.Basic
public import Mathlib.RingTheory.WittVector.WittPolynomial

/-!
# Witt structure polynomials

In this file we prove the main theorem that makes the whole theory of Witt vectors work.
Briefly, consider a polynomial `Φ : MvPolynomial idx ℤ` over the integers,
with polynomials variables indexed by an arbitrary type `idx`.

Then there exists a unique family of polynomials `φ : ℕ → MvPolynomial (idx × ℕ) Φ`
such that for all `n : ℕ` we have (`wittStructureInt_existsUnique`)
```
bind₁ φ (wittPolynomial p ℤ n) = bind₁ (fun i ↦ (rename (prod.mk i) (wittPolynomial p ℤ n))) Φ
```
In other words: evaluating the `n`-th Witt polynomial on the family `φ`
is the same as evaluating `Φ` on the (appropriately renamed) `n`-th Witt polynomials.

N.b.: As far as we know, these polynomials do not have a name in the literature,
so we have decided to call them the “Witt structure polynomials”. See `wittStructureInt`.

## Special cases

With the main result of this file in place, we apply it to certain special polynomials.
For example, by taking `Φ = X tt + X ff` resp. `Φ = X tt * X ff`
we obtain families of polynomials `witt_add` resp. `witt_mul`
(with type `ℕ → MvPolynomial (Bool × ℕ) ℤ`) that will be used in later files to define the
addition and multiplication on the ring of Witt vectors.

## Outline of the proof

The proof of `wittStructureInt_existsUnique` is rather technical, and takes up most of this file.

We start by proving the analogous version for polynomials with rational coefficients,
instead of integer coefficients.
In this case, the solution is rather easy,
since the Witt polynomials form a faithful change of coordinates
in the polynomial ring `MvPolynomial ℕ ℚ`.
We therefore obtain a family of polynomials `wittStructureRat Φ`
for every `Φ : MvPolynomial idx ℚ`.

If `Φ` has integer coefficients, then the polynomials `wittStructureRat Φ n` do so as well.
Proving this claim is the essential core of this file, and culminates in
`map_wittStructureInt`, which proves that upon mapping the coefficients
of `wittStructureInt Φ n` from the integers to the rationals,
one obtains `wittStructureRat Φ n`.
Ultimately, the proof of `map_wittStructureInt` relies on
```
dvd_sub_pow_of_dvd_sub {R : Type*} [CommRing R] {p : ℕ} {a b : R} :
    (p : R) ∣ a - b → ∀ (k : ℕ), (p : R) ^ (k + 1) ∣ a ^ p ^ k - b ^ p ^ k
```

## Main results

* `wittStructureRat Φ`: the family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℚ`
  associated with `Φ : MvPolynomial idx ℚ` and satisfying the property explained above.
* `wittStructureRat_prop`: the proof that `wittStructureRat` indeed satisfies the property.
* `wittStructureInt Φ`: the family of polynomials `ℕ → MvPolynomial (idx × ℕ) ℤ`
  associated with `Φ : MvPolynomial idx ℤ` and satisfying the property explained above.
* `map_wittStructureInt`: the proof that the integral polynomials `with_structure_int Φ`
  are equal to `wittStructureRat Φ` when mapped to polynomials with rational coefficients.
* `wittStructureInt_prop`: the proof that `wittStructureInt` indeed satisfies the property.
* Five families of polynomials that will be used to define the ring structure
  on the ring of Witt vectors:
  - `WittVector.wittZero`
  - `WittVector.wittOne`
  - `WittVector.wittAdd`
  - `WittVector.wittMul`
  - `WittVector.wittNeg`

  (We also define `WittVector.wittSub`, and later we will prove that it describes subtraction,
  which is defined as `fun a b ↦ a + -b`. See `WittVector.sub_coeff` for this proof.)

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

@[expose] public section


open MvPolynomial Set

open Finset (range)

open Finsupp (single)

-- This lemma reduces a bundled morphism to a "mere" function,
-- and consequently the simplifier cannot use a lot of powerful simp-lemmas.
-- We disable this locally, and probably it should be disabled globally in mathlib.
attribute [-simp] coe_eval₂Hom

variable {p : Nat} {R : Type*} {idx : Type*} [CommRing R]

open scoped Witt

section PPrime

variable (p)
variable [hp : Fact p.Prime]

-- Notation with ring of coefficients explicit
set_option quotPrecheck false in
@[inherit_doc]
scoped[Witt] notation "W_" => wittPolynomial p

-- Notation with ring of coefficients implicit
set_option quotPrecheck false in
@[inherit_doc]
scoped[Witt] notation "W" => wittPolynomial p _

/--
Definition of `wittStructureRat` / `wittStructureRat` 的定义

English:
definition wittStructureRat
  signature: (Φ : MvPolynomial idx Rat) (n : Nat)
  body: bind₁ (fun k => bind₁ (fun i => rename (Prod.mk i) (W_ Rat k)) Φ) (xInTermsOfW p Rat n)

中文:
定义 wittStructureRat
  签名: (Φ : 多元多项式 idx 有理数) (n : 自然数)
  定义体: bind₁ (fun k => bind₁ (fun i => rename (Prod.mk i) (W_ Rat k)) Φ) (xInTermsOfW p Rat n)

Depends on / 依赖: Prod.mk, xInTermsOfW
-/
noncomputable def wittStructureRat (Φ : MvPolynomial idx Rat) (n : Nat) : MvPolynomial (idx × Nat) Rat :=
  bind₁ (fun k => bind₁ (fun i => rename (Prod.mk i) (W_ Rat k)) Φ) (xInTermsOfW p Rat n)

/--
theorem `wittStructureRat_prop` / 定理 `wittStructureRat_prop`

English:
theorem wittStructureRat_prop
  given: (Φ : MvPolynomial idx Rat) (n : Nat)
  proof: calc
    bind₁ (wittStructureRat p Φ) (W_ Rat n) =
        bind₁ (fun k => bind₁ (fun i => (rename (Prod.mk i)) (W_ Rat k)) Φ)
          (bind₁ (xInTermsOfW p Rat) (W_ Rat n)) := by
      rw [bind₁_bind₁]; exact eval₂Hom_congr (RingHom.ext_rat _ _) rfl rfl
    _ = bind₁ (fun i => rename (Prod.mk i) 

中文:
定理 wittStructureRat_prop
  条件: (Φ : 多元多项式 idx 有理数) (n : 自然数)
  证明: calc
    bind₁ (wittStructureRat p Φ) (W_ Rat n) =
        bind₁ (fun k => bind₁ (fun i => (rename (Prod.mk i)) (W_ Rat k)) Φ)
          (bind₁ (xInTermsOfW p Rat) (W_ Rat n)) := by
      rw [bind₁_bind₁]; exact eval₂Hom_congr (RingHom.ext_rat _ _) rfl rfl
    _ = bind₁ (fun i => rename (Prod.mk i) 

Depends on / 依赖: Prod.mk, RingHom, RingHom.ext_rat, ext_rat, wittStructureRat, xInTermsOfW
-/
theorem wittStructureRat_prop (Φ : MvPolynomial idx Rat) (n : Nat) :
    bind₁ (wittStructureRat p Φ) (W_ Rat n) = bind₁ (fun i => rename (Prod.mk i) (W_ Rat n)) Φ :=
  calc
    bind₁ (wittStructureRat p Φ) (W_ Rat n) =
        bind₁ (fun k => bind₁ (fun i => (rename (Prod.mk i)) (W_ Rat k)) Φ)
          (bind₁ (xInTermsOfW p Rat) (W_ Rat n)) := by
      rw [bind₁_bind₁]; exact eval₂Hom_congr (RingHom.ext_rat _ _) rfl rfl
    _ = bind₁ (fun i => rename (Prod.mk i) (W_ Rat n)) Φ := by
      rw [bind₁_xInTermsOfW_wittPolynomial p _ n]; rw [bind₁_X_right]

/--
theorem `wittStructureRat_existsUnique` / 定理 `wittStructureRat_existsUnique`

English:
theorem wittStructureRat_existsUnique
  given: (Φ : MvPolynomial idx Rat)
  proof: by
  refine ⟨wittStructureRat p Φ, ?_, ?_⟩
  · intro n; apply wittStructureRat_prop
  · intro φ H
    funext n
    rw [show φ n = bind₁ φ (bind₁ (W_ Rat) (xInTermsOfW p Rat n)) by
        rw [bind₁_wittPolynomial_xInTermsOfW p]; rw [bind₁_X_right]]
    rw [bind₁_bind₁]
    exact eval₂Hom_congr (Ring

中文:
定理 wittStructureRat_存在Unique
  条件: (Φ : 多元多项式 idx 有理数)
  证明: by
  refine ⟨wittStructureRat p Φ, ?_, ?_⟩
  · intro n; apply wittStructureRat_prop
  · intro φ H
    funext n
    rw [show φ n = bind₁ φ (bind₁ (W_ Rat) (xInTermsOfW p Rat n)) by
        rw [bind₁_wittPolynomial_xInTermsOfW p]; rw [bind₁_X_right]]
    rw [bind₁_bind₁]
    exact eval₂Hom_congr (Ring

Depends on / 依赖: RingHom, RingHom.ext_rat, ext_rat, wittStructureRat, wittStructureRat_prop, xInTermsOfW
-/
theorem wittStructureRat_existsUnique (Φ : MvPolynomial idx Rat) :
    exists! φ : Nat -> MvPolynomial (idx × Nat) Rat,
      forall n : Nat, bind₁ φ (W_ Rat n) = bind₁ (fun i => rename (Prod.mk i) (W_ Rat n)) Φ := by
  refine ⟨wittStructureRat p Φ, ?_, ?_⟩
  · intro n; apply wittStructureRat_prop
  · intro φ H
    funext n
    rw [show φ n = bind₁ φ (bind₁ (W_ Rat) (xInTermsOfW p Rat n)) by
        rw [bind₁_wittPolynomial_xInTermsOfW p]; rw [bind₁_X_right]]
    rw [bind₁_bind₁]
    exact eval₂Hom_congr (RingHom.ext_rat _ _) (funext H) rfl

/--
theorem `wittStructureRat_rec_aux` / 定理 `wittStructureRat_rec_aux`

English:
theorem wittStructureRat_rec_aux
  given: (Φ : MvPolynomial idx Rat) (n : Nat)
  proof: by
  have := xInTermsOfW_aux p Rat n
  replace := congr_arg (bind₁ fun k : Nat => bind₁ (fun i => rename (Prod.mk i) (W_ Rat k)) Φ) this
  rw [map_mul]; rw [bind₁_C_right] at this
  rw [wittStructureRat]; rw [this]; clear this
  conv_lhs => simp only [map_sub, bind₁_X_right]
  rw [sub_right_inj]
  s

中文:
定理 wittStructureRat_rec_aux
  条件: (Φ : 多元多项式 idx 有理数) (n : 自然数)
  证明: by
  have := xInTermsOfW_aux p Rat n
  replace := congr_arg (bind₁ fun k : Nat => bind₁ (fun i => rename (Prod.mk i) (W_ Rat k)) Φ) this
  rw [map_mul]; rw [bind₁_C_right] at this
  rw [wittStructureRat]; rw [this]; clear this
  conv_lhs => simp only [map_sub, bind₁_X_right]
  rw [sub_right_inj]
  s

Depends on / 依赖: Prod.mk, congr_arg, conv_lhs, map_mul, map_pow, map_sub, map_sum, replace, sub_right_inj, wittStructureRat, xInTermsOfW_aux
-/
theorem wittStructureRat_rec_aux (Φ : MvPolynomial idx Rat) (n : Nat) :
    wittStructureRat p Φ n * C ((p : Rat) ^ n) =
      bind₁ (fun b => rename (fun i => (b, i)) (W_ Rat n)) Φ -
        ∑ i in range n, C ((p : Rat) ^ i) * wittStructureRat p Φ i ^ p ^ (n - i) := by
  have := xInTermsOfW_aux p Rat n
  replace := congr_arg (bind₁ fun k : Nat => bind₁ (fun i => rename (Prod.mk i) (W_ Rat k)) Φ) this
  rw [map_mul]; rw [bind₁_C_right] at this
  rw [wittStructureRat]; rw [this]; clear this
  conv_lhs => simp only [map_sub, bind₁_X_right]
  rw [sub_right_inj]
  simp only [map_sum, map_mul, bind₁_C_right, map_pow]
  rfl

/--
theorem `wittStructureRat_rec` / 定理 `wittStructureRat_rec`

English:
theorem wittStructureRat_rec
  given: (Φ : MvPolynomial idx Rat) (n : Nat)
  proof: by
  calc
    wittStructureRat p Φ n = C (1 / (p : Rat) ^ n) * (wittStructureRat p Φ n * C ((p : Rat) ^ n)) := ?_
    _ = _ := by rw [wittStructureRat_rec_aux]
  rw [mul_left_comm]; rw [← C_mul]; rw [div_mul_cancel₀]; rw [C_1]; rw [mul_one]
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)

中文:
定理 wittStructureRat_rec
  条件: (Φ : 多元多项式 idx 有理数) (n : 自然数)
  证明: by
  calc
    wittStructureRat p Φ n = C (1 / (p : Rat) ^ n) * (wittStructureRat p Φ n * C ((p : Rat) ^ n)) := ?_
    _ = _ := by rw [wittStructureRat_rec_aux]
  rw [mul_left_comm]; rw [← C_mul]; rw [div_mul_cancel₀]; rw [C_1]; rw [mul_one]
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)

Depends on / 依赖: C_mul, Nat.cast_ne_zero, cast_ne_zero, mul_left_comm, mul_one, ne_zero, pow_ne_zero, wittStructureRat, wittStructureRat_rec_aux
-/
theorem wittStructureRat_rec (Φ : MvPolynomial idx Rat) (n : Nat) :
    wittStructureRat p Φ n =
      C (1 / (p : Rat) ^ n) *
        (bind₁ (fun b => rename (fun i => (b, i)) (W_ Rat n)) Φ -
          ∑ i in range n, C ((p : Rat) ^ i) * wittStructureRat p Φ i ^ p ^ (n - i)) := by
  calc
    wittStructureRat p Φ n = C (1 / (p : Rat) ^ n) * (wittStructureRat p Φ n * C ((p : Rat) ^ n)) := ?_
    _ = _ := by rw [wittStructureRat_rec_aux]
  rw [mul_left_comm]; rw [← C_mul]; rw [div_mul_cancel₀]; rw [C_1]; rw [mul_one]
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hp.1.ne_zero)

/--
Definition of `wittStructureInt` / `wittStructureInt` 的定义

English:
definition wittStructureInt
  signature: (Φ : MvPolynomial idx Int) (n : Nat)
  body: .ofCoeff .mapRange Rat.num (Rat.num_intCast 0) AddMonoidAlgebra.coeff
    wittStructureRat p (map (Int.castRingHom Rat) Φ) n

中文:
定义 wittStructure整数
  签名: (Φ : 多元多项式 idx 整数) (n : 自然数)
  定义体: .ofCoeff .mapRange Rat.num (Rat.num_intCast 0) AddMonoidAlgebra.coeff
    wittStructureRat p (map (Int.castRingHom Rat) Φ) n

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.coeff, Int.castRingHom, Rat.num, Rat.num_intCast, castRingHom, mapRange, num_intCast, ofCoeff, wittStructureRat
-/
noncomputable def wittStructureInt (Φ : MvPolynomial idx Int) (n : Nat) : MvPolynomial (idx × Nat) Int :=
.ofCoeff .mapRange Rat.num (Rat.num_intCast 0) AddMonoidAlgebra.coeff
    wittStructureRat p (map (Int.castRingHom Rat) Φ) n

variable {p}

/--
theorem `bind₁_rename_expand_wittPolynomial` / 定理 `bind₁_rename_expand_wittPolynomial`

English:
theorem bind₁_rename_expand_wittPolynomial
  statement: (Φ : MvPolynomial idx Int) (n : Nat)
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_bind₁, map_rename, map_expand, rename_expand, map_wittPolynomial]
  have key := (wittStructureRat_prop p (map (Int.castRingHom Rat) Φ) n).symm
  apply_fun expand p at key
  simp only [expand_bind₁] at key

中文:
定理 bind₁_rename_expand_wittPolynomial
  结论: (Φ : 多元多项式 idx 整数) (n : 自然数)
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_bind₁, map_rename, map_expand, rename_expand, map_wittPolynomial]
  have key := (wittStructureRat_prop p (map (Int.castRingHom Rat) Φ) n).symm
  apply_fun expand p at key
  simp only [expand_bind₁] at key

Depends on / 依赖: Finset, Finset.mem_range, Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, apply_fun, castRingHom, cast_injective, expand, map_expand, map_injective, map_rename, map_wittPolynomial, mem_range, rename_expand, wittPolynomial_vars, wittStructureRat_prop
-/
theorem bind₁_rename_expand_wittPolynomial (Φ : MvPolynomial idx Int) (n : Nat)
    (IH :
      forall m : Nat,
        m < n + 1 ->
          map (Int.castRingHom Rat) (wittStructureInt p Φ m) =
            wittStructureRat p (map (Int.castRingHom Rat) Φ) m) :
    bind₁ (fun b => rename (fun i => (b, i)) (expand p (W_ Int n))) Φ =
      bind₁ (fun i => expand p (wittStructureInt p Φ i)) (W_ Int n) := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_bind₁, map_rename, map_expand, rename_expand, map_wittPolynomial]
  have key := (wittStructureRat_prop p (map (Int.castRingHom Rat) Φ) n).symm
  apply_fun expand p at key
  simp only [expand_bind₁] at key
  rw [key]; clear key
  apply eval₂Hom_congr' rfl _ rfl
  rintro i hi -
  rw [wittPolynomial_vars]; rw [Finset.mem_range] at hi
  simp only [IH i hi]

/--
theorem `C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum` / 定理 `C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum`

English:
theorem C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum
  statement: (Φ : MvPolynomial idx Int) (n : Nat)
  proof: by
  rcases n with - | n
  · simp
  -- prepare a useful equation for rewriting
  have key := bind₁_rename_expand_wittPolynomial Φ n IH
  apply_fun map (Int.castRingHom (ZMod (p ^ (n + 1)))) at key
  conv_lhs at key => simp only [map_bind₁, map_rename, map_expand, map_wittPolynomial]
  -- clean up an

中文:
定理 C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum
  结论: (Φ : 多元多项式 idx 整数) (n : 自然数)
  证明: by
  rcases n with - | n
  · simp
  -- prepare a useful equation for rewriting
  have key := bind₁_rename_expand_wittPolynomial Φ n IH
  apply_fun map (Int.castRingHom (ZMod (p ^ (n + 1)))) at key
  conv_lhs at key => simp only [map_bind₁, map_rename, map_expand, map_wittPolynomial]
  -- clean up an
-/
theorem C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum (Φ : MvPolynomial idx Int) (n : Nat)
    (IH :
      forall m : Nat,
        m < n ->
          map (Int.castRingHom Rat) (wittStructureInt p Φ m) =
            wittStructureRat p (map (Int.castRingHom Rat) Φ) m) :
    (C ((p ^ n :) : Int) : MvPolynomial (idx × Nat) Int) ∣
      bind₁ (fun b : idx => rename (fun i => (b, i)) (wittPolynomial p Int n)) Φ -
        ∑ i in range n, C ((p : Int) ^ i) * wittStructureInt p Φ i ^ p ^ (n - i) := by
  rcases n with - | n
  · simp
  -- prepare a useful equation for rewriting
  have key := bind₁_rename_expand_wittPolynomial Φ n IH
  apply_fun map (Int.castRingHom (ZMod (p ^ (n + 1)))) at key
  conv_lhs at key => simp only [map_bind₁, map_rename, map_expand, map_wittPolynomial]
  -- clean up and massage
  rw [C_dvd_iff_zmod]; rw [map_sub]; rw [sub_eq_zero]; rw [map_bind₁]
  simp only [map_rename, map_wittPolynomial, wittPolynomial_zmod_self]
  rw [key]; clear key IH
  rw [bind₁]; rw [aeval_wittPolynomial]; rw [map_sum]; rw [map_sum]; rw [Finset.sum_congr rfl]
  intro k hk
  rw [Finset.mem_range]; rw [Nat.lt_succ_iff] at hk
  rw [← sub_eq_zero]; rw [← map_sub]; rw [← C_dvd_iff_zmod]; rw [C_eq_coe_nat]; rw [← Nat.cast_pow]; rw [← Nat.cast_pow]; rw [C_eq_coe_nat]; rw [← mul_sub]
  have : p ^ (n + 1) = p ^ k * p ^ (n - k + 1) := by
    rw [← pow_add]; rw [← add_assoc]; congr 2; rw [add_comm, ← tsub_eq_iff_eq_add_of_le hk]
  rw [this]
  rw [Nat.cast_mul]; rw [Nat.cast_pow]; rw [Nat.cast_pow]
  apply mul_dvd_mul_left ((p : MvPolynomial (idx × Nat) Int) ^ k)
  rw [show p ^ (n + 1 - k) = p * p ^ (n - k) by rw [← pow_succ']; rw [← tsub_add_eq_add_tsub hk]]
  rw [pow_mul]
  -- the machine!
  apply dvd_sub_pow_of_dvd_sub
  rw [← C_eq_coe_nat]; rw [C_dvd_iff_zmod]; rw [map_sub]; rw [sub_eq_zero]; rw [map_expand]; rw [map_pow]; rw [MvPolynomial.expand_zmod]

variable (p)

@[simp]
/--
theorem `map_wittStructureInt` / 定理 `map_wittStructureInt`

English:
theorem map_wittStructureInt
  given: (Φ : MvPolynomial idx Int) (n : Nat)
  proof: by
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [wittStructureInt]; rw [map_mapRange_eq_iff]; rw [Int.coe_castRingHom]
  intro c
  rw [wittStructureRat_rec]; rw [coeff_C_mul]; rw [mul_comm]; rw [mul_div_assoc']; rw [mul_one]
  have sum_induction_steps :
      map (Int.castRin

中文:
定理 map_wittStructure整数
  条件: (Φ : 多元多项式 idx 整数) (n : 自然数)
  证明: by
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [wittStructureInt]; rw [map_mapRange_eq_iff]; rw [Int.coe_castRingHom]
  intro c
  rw [wittStructureRat_rec]; rw [coeff_C_mul]; rw [mul_comm]; rw [mul_div_assoc']; rw [mul_one]
  have sum_induction_steps :
      map (Int.castRin

Depends on / 依赖: Int.castRingHom, Int.coe_castRingHom, Nat.strong_induction_on, castRingHom, coe_castRingHom, coeff_C_mul, map_mapRange_eq_iff, map_sum, mul_comm, mul_div_assoc, mul_one, strong_induction_on, sum_induction_steps, wittStructureInt, wittStructureRat, wittStructureRat_rec
-/
theorem map_wittStructureInt (Φ : MvPolynomial idx Int) (n : Nat) :
    map (Int.castRingHom Rat) (wittStructureInt p Φ n) =
      wittStructureRat p (map (Int.castRingHom Rat) Φ) n := by
  induction n using Nat.strong_induction_on with | h n IH => ?_
  rw [wittStructureInt]; rw [map_mapRange_eq_iff]; rw [Int.coe_castRingHom]
  intro c
  rw [wittStructureRat_rec]; rw [coeff_C_mul]; rw [mul_comm]; rw [mul_div_assoc']; rw [mul_one]
  have sum_induction_steps :
      map (Int.castRingHom Rat)
        (∑ i in range n, C ((p : Int) ^ i) * wittStructureInt p Φ i ^ p ^ (n - i)) =
      ∑ i in range n,
        C ((p : Rat) ^ i) * wittStructureRat p (map (Int.castRingHom Rat) Φ) i ^ p ^ (n - i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [IH i hi, map_mul, map_pow, map_C]
    rfl
  simp only [← sum_induction_steps, ← map_wittPolynomial p (Int.castRingHom Rat), ← map_rename, ←
    map_bind₁, ← map_sub, coeff_map]
  rw [show (p : Rat) ^ n = ((↑(p ^ n) : Int) : Rat) by norm_cast]
  rw [← Rat.den_eq_one_iff]; rw [eq_intCast]; rw [Rat.den_div_intCast_eq_one_iff]
  swap; · exact mod_cast pow_ne_zero n hp.1.ne_zero
  revert c; rw [← C_dvd_iff_dvd_coeff]
  exact C_p_pow_dvd_bind₁_rename_wittPolynomial_sub_sum Φ n IH

/--
theorem `wittStructureInt_prop` / 定理 `wittStructureInt_prop`

English:
theorem wittStructureInt_prop
  given: (Φ : MvPolynomial idx Int) (n)
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  have := wittStructureRat_prop p (map (Int.castRingHom Rat) Φ) n
  simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
    AlgHom.coe_toRingHom, map_wittStructureInt]

中文:
定理 wittStructure整数_prop
  条件: (Φ : 多元多项式 idx 整数) (n)
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  have := wittStructureRat_prop p (map (Int.castRingHom Rat) Φ) n
  simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
    AlgHom.coe_toRingHom, map_wittStructureInt]

Depends on / 依赖: AlgHom, AlgHom.coe_toRingHom, Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, coe_toRingHom, map_injective, map_rename, map_wittPolynomial, map_wittStructureInt, wittStructureRat_prop
-/
theorem wittStructureInt_prop (Φ : MvPolynomial idx Int) (n) :
    bind₁ (wittStructureInt p Φ) (wittPolynomial p Int n) =
      bind₁ (fun i => rename (Prod.mk i) (W_ Int n)) Φ := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  have := wittStructureRat_prop p (map (Int.castRingHom Rat) Φ) n
  simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
    AlgHom.coe_toRingHom, map_wittStructureInt]

/--
theorem `eq_wittStructureInt` / 定理 `eq_wittStructureInt`

English:
theorem eq_wittStructureInt
  statement: (Φ : MvPolynomial idx Int) (φ : Nat -> MvPolynomial (idx × Nat) Int)
  proof: by
  funext k
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [map_wittStructureInt]
  -- Porting note: was `refine' congr_fun _ k`
  revert k
  refine congr_fun ?_
  apply ExistsUnique.unique (wittStructureRat_existsUnique p (map (Int.castRingHom Rat) Φ))
  · intro 

中文:
定理 eq_wittStructure整数
  结论: (Φ : 多元多项式 idx 整数) (φ : 自然数 -> 多元多项式 (idx × 自然数) 整数)
  证明: by
  funext k
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [map_wittStructureInt]
  -- Porting note: was `refine' congr_fun _ k`
  revert k
  refine congr_fun ?_
  apply ExistsUnique.unique (wittStructureRat_existsUnique p (map (Int.castRingHom Rat) Φ))
  · intro 

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, map_injective, map_wittStructureInt
-/
theorem eq_wittStructureInt (Φ : MvPolynomial idx Int) (φ : Nat -> MvPolynomial (idx × Nat) Int)
    (h : forall n, bind₁ φ (wittPolynomial p Int n) = bind₁ (fun i => rename (Prod.mk i) (W_ Int n)) Φ) :
    φ = wittStructureInt p Φ := by
  funext k
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  rw [map_wittStructureInt]
  -- Porting note: was `refine' congr_fun _ k`
  revert k
  refine congr_fun ?_
  apply ExistsUnique.unique (wittStructureRat_existsUnique p (map (Int.castRingHom Rat) Φ))
  · intro n
    specialize h n
    apply_fun map (Int.castRingHom Rat) at h
    simpa only [map_bind₁, ← eval₂Hom_map_hom, eval₂Hom_C_left, map_rename, map_wittPolynomial,
      AlgHom.coe_toRingHom] using h
  · intro n; apply wittStructureRat_prop

/--
theorem `wittStructureInt_existsUnique` / 定理 `wittStructureInt_existsUnique`

English:
theorem wittStructureInt_existsUnique
  given: (Φ : MvPolynomial idx Int)
  proof: ⟨wittStructureInt p Φ, wittStructureInt_prop _ _, eq_wittStructureInt _ _⟩

中文:
定理 wittStructure整数_存在Unique
  条件: (Φ : 多元多项式 idx 整数)
  证明: ⟨wittStructureInt p Φ, wittStructureInt_prop _ _, eq_wittStructureInt _ _⟩

Depends on / 依赖: eq_wittStructureInt, wittStructureInt, wittStructureInt_prop
-/
theorem wittStructureInt_existsUnique (Φ : MvPolynomial idx Int) :
    exists! φ : Nat -> MvPolynomial (idx × Nat) Int,
      forall n : Nat,
        bind₁ φ (wittPolynomial p Int n) = bind₁ (fun i : idx => rename (Prod.mk i) (W_ Int n)) Φ :=
  ⟨wittStructureInt p Φ, wittStructureInt_prop _ _, eq_wittStructureInt _ _⟩

/--
theorem `witt_structure_prop` / 定理 `witt_structure_prop`

English:
theorem witt_structure_prop
  given: (Φ : MvPolynomial idx Int) (n)
  proof: by
  convert! congr_arg (map (Int.castRingHom R)) (wittStructureInt_prop p Φ n) using 1 <;>
      rw [hom_bind₁] <;>
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  · rfl
  · simp only [map_rename, map_wittPolynomial]

中文:
定理 witt_structure_prop
  条件: (Φ : 多元多项式 idx 整数) (n)
  证明: by
  convert! congr_arg (map (Int.castRingHom R)) (wittStructureInt_prop p Φ n) using 1 <;>
      rw [hom_bind₁] <;>
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  · rfl
  · simp only [map_rename, map_wittPolynomial]

Depends on / 依赖: Int.castRingHom, RingHom, RingHom.ext_int, castRingHom, congr_arg, convert, ext_int, map_rename, map_wittPolynomial, wittStructureInt_prop
-/
theorem witt_structure_prop (Φ : MvPolynomial idx Int) (n) :
    aeval (fun i => map (Int.castRingHom R) (wittStructureInt p Φ i)) (wittPolynomial p Int n) =
      aeval (fun i => rename (Prod.mk i) (W n)) Φ := by
  convert! congr_arg (map (Int.castRingHom R)) (wittStructureInt_prop p Φ n) using 1 <;>
      rw [hom_bind₁] <;>
    apply eval₂Hom_congr (RingHom.ext_int _ _) _ rfl
  · rfl
  · simp only [map_rename, map_wittPolynomial]

/--
theorem `wittStructureInt_rename` / 定理 `wittStructureInt_rename`

English:
theorem wittStructureInt_rename
  given: {σ : Type*} (Φ : MvPolynomial idx Int) (f : idx -> σ) (n : Nat)
  proof: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_rename, map_wittStructureInt, wittStructureRat, rename_bind₁, rename_rename,
    bind₁_rename]
  rfl

@[simp]

中文:
定理 wittStructure整数_rename
  条件: {σ : 类型} (Φ : 多元多项式 idx 整数) (f : idx -> σ) (n : 自然数)
  证明: by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_rename, map_wittStructureInt, wittStructureRat, rename_bind₁, rename_rename,
    bind₁_rename]
  rfl

@[simp]

Depends on / 依赖: Int.castRingHom, Int.cast_injective, MvPolynomial, MvPolynomial.map_injective, castRingHom, cast_injective, map_injective, map_rename, map_wittStructureInt, rename_rename, wittStructureRat
-/
theorem wittStructureInt_rename {σ : Type*} (Φ : MvPolynomial idx Int) (f : idx -> σ) (n : Nat) :
    wittStructureInt p (rename f Φ) n = rename (Prod.map f id) (wittStructureInt p Φ n) := by
  apply MvPolynomial.map_injective (Int.castRingHom Rat) Int.cast_injective
  simp only [map_rename, map_wittStructureInt, wittStructureRat, rename_bind₁, rename_rename,
    bind₁_rename]
  rfl

@[simp]
/--
theorem `constantCoeff_wittStructureRat_zero` / 定理 `constantCoeff_wittStructureRat_zero`

English:
theorem constantCoeff_wittStructureRat_zero
  given: (Φ : MvPolynomial idx Rat)
  proof: by
  simp only [wittStructureRat, bind₁, map_aeval, xInTermsOfW_zero, constantCoeff_rename,
    constantCoeff_wittPolynomial, aeval_X, constantCoeff_comp_algebraMap, eval₂Hom_zero'_apply,
    RingHom.id_apply]

中文:
定理 constantCoeff_wittStructureRat_zero
  条件: (Φ : 多元多项式 idx 有理数)
  证明: by
  simp only [wittStructureRat, bind₁, map_aeval, xInTermsOfW_zero, constantCoeff_rename,
    constantCoeff_wittPolynomial, aeval_X, constantCoeff_comp_algebraMap, eval₂Hom_zero'_apply,
    RingHom.id_apply]

Depends on / 依赖: RingHom, RingHom.id_apply, _apply, aeval_X, constantCoeff_comp_algebraMap, constantCoeff_rename, constantCoeff_wittPolynomial, id_apply, map_aeval, wittStructureRat, xInTermsOfW_zero
-/
theorem constantCoeff_wittStructureRat_zero (Φ : MvPolynomial idx Rat) :
    constantCoeff (wittStructureRat p Φ 0) = constantCoeff Φ := by
  simp only [wittStructureRat, bind₁, map_aeval, xInTermsOfW_zero, constantCoeff_rename,
    constantCoeff_wittPolynomial, aeval_X, constantCoeff_comp_algebraMap, eval₂Hom_zero'_apply,
    RingHom.id_apply]

/--
theorem `constantCoeff_wittStructureRat` / 定理 `constantCoeff_wittStructureRat`

English:
theorem constantCoeff_wittStructureRat
  given: (Φ : MvPolynomial idx Rat) (h : constantCoeff Φ = 0) (n : Nat)
  proof: by
  simp only [wittStructureRat, eval₂Hom_zero'_apply, h, bind₁, map_aeval, constantCoeff_rename,
    constantCoeff_wittPolynomial, constantCoeff_comp_algebraMap, RingHom.id_apply,
    constantCoeff_xInTermsOfW]

@[simp]

中文:
定理 constantCoeff_wittStructureRat
  条件: (Φ : 多元多项式 idx 有理数) (h : constantCoeff Φ = 0) (n : 自然数)
  证明: by
  simp only [wittStructureRat, eval₂Hom_zero'_apply, h, bind₁, map_aeval, constantCoeff_rename,
    constantCoeff_wittPolynomial, constantCoeff_comp_algebraMap, RingHom.id_apply,
    constantCoeff_xInTermsOfW]

@[simp]

Depends on / 依赖: RingHom, RingHom.id_apply, _apply, constantCoeff_comp_algebraMap, constantCoeff_rename, constantCoeff_wittPolynomial, constantCoeff_xInTermsOfW, id_apply, map_aeval, wittStructureRat
-/
theorem constantCoeff_wittStructureRat (Φ : MvPolynomial idx Rat) (h : constantCoeff Φ = 0) (n : Nat) :
    constantCoeff (wittStructureRat p Φ n) = 0 := by
  simp only [wittStructureRat, eval₂Hom_zero'_apply, h, bind₁, map_aeval, constantCoeff_rename,
    constantCoeff_wittPolynomial, constantCoeff_comp_algebraMap, RingHom.id_apply,
    constantCoeff_xInTermsOfW]

@[simp]
/--
theorem `constantCoeff_wittStructureInt_zero` / 定理 `constantCoeff_wittStructureInt_zero`

English:
theorem constantCoeff_wittStructureInt_zero
  given: (Φ : MvPolynomial idx Int)
  proof: by
  have inj : Function.Injective (Int.castRingHom Rat) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map]; rw [map_wittStructureInt]; rw [constantCoeff_wittStructureRat_zero]; rw [constantCoeff_map]

中文:
定理 constantCoeff_wittStructure整数_zero
  条件: (Φ : 多元多项式 idx 整数)
  证明: by
  have inj : Function.Injective (Int.castRingHom Rat) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map]; rw [map_wittStructureInt]; rw [constantCoeff_wittStructureRat_zero]; rw [constantCoeff_map]

Depends on / 依赖: Function, Function.Injective, Injective, Int.castRingHom, Int.cast_inj.mp, castRingHom, cast_inj, constantCoeff_map, constantCoeff_wittStructureRat_zero, map_wittStructureInt
-/
theorem constantCoeff_wittStructureInt_zero (Φ : MvPolynomial idx Int) :
    constantCoeff (wittStructureInt p Φ 0) = constantCoeff Φ := by
  have inj : Function.Injective (Int.castRingHom Rat) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map]; rw [map_wittStructureInt]; rw [constantCoeff_wittStructureRat_zero]; rw [constantCoeff_map]

/--
theorem `constantCoeff_wittStructureInt` / 定理 `constantCoeff_wittStructureInt`

English:
theorem constantCoeff_wittStructureInt
  given: (Φ : MvPolynomial idx Int) (h : constantCoeff Φ = 0) (n : Nat)
  proof: by
  have inj : Function.Injective (Int.castRingHom Rat) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map]; rw [map_wittStructureInt]; rw [constantCoeff_wittStructureRat]; rw [map_zero]
  rw [constantCoeff_map]; rw [h]; rw [map_zero]

中文:
定理 constantCoeff_wittStructure整数
  条件: (Φ : 多元多项式 idx 整数) (h : constantCoeff Φ = 0) (n : 自然数)
  证明: by
  have inj : Function.Injective (Int.castRingHom Rat) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map]; rw [map_wittStructureInt]; rw [constantCoeff_wittStructureRat]; rw [map_zero]
  rw [constantCoeff_map]; rw [h]; rw [map_zero]

Depends on / 依赖: Function, Function.Injective, Injective, Int.castRingHom, Int.cast_inj.mp, castRingHom, cast_inj, constantCoeff_map, constantCoeff_wittStructureRat, map_wittStructureInt, map_zero
-/
theorem constantCoeff_wittStructureInt (Φ : MvPolynomial idx Int) (h : constantCoeff Φ = 0) (n : Nat) :
    constantCoeff (wittStructureInt p Φ n) = 0 := by
  have inj : Function.Injective (Int.castRingHom Rat) := by intro m n; exact Int.cast_inj.mp
  apply inj
  rw [← constantCoeff_map]; rw [map_wittStructureInt]; rw [constantCoeff_wittStructureRat]; rw [map_zero]
  rw [constantCoeff_map]; rw [h]; rw [map_zero]

variable (R)

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
/--
theorem `wittStructureRat_vars` / 定理 `wittStructureRat_vars`

English:
theorem wittStructureRat_vars
  given: [Fintype idx] (Φ : MvPolynomial idx Rat) (n : Nat)
  proof: by
  rw [wittStructureRat]
  intro x hx
  simp only [Finset.mem_product, true_and, Finset.mem_univ, Finset.mem_range]
  obtain ⟨k, hk, hx'⟩ := mem_vars_bind₁ _ _ hx
  obtain ⟨i, -, hx''⟩ := mem_vars_bind₁ _ _ hx'
  obtain ⟨j, hj, rfl⟩ := mem_vars_rename _ _ hx''
  rw [wittPolynomial_vars]; rw [Finse

中文:
定理 wittStructureRat_vars
  条件: [有限类型 idx] (Φ : 多元多项式 idx 有理数) (n : 自然数)
  证明: by
  rw [wittStructureRat]
  intro x hx
  simp only [Finset.mem_product, true_and, Finset.mem_univ, Finset.mem_range]
  obtain ⟨k, hk, hx'⟩ := mem_vars_bind₁ _ _ hx
  obtain ⟨i, -, hx''⟩ := mem_vars_bind₁ _ _ hx'
  obtain ⟨j, hj, rfl⟩ := mem_vars_rename _ _ hx''
  rw [wittPolynomial_vars]; rw [Finse

Depends on / 依赖: Finset, Finset.mem_product, Finset.mem_range, Finset.mem_univ, mem_product, mem_range, mem_univ, mem_vars_rename, replace, true_and, wittPolynomial_vars, wittStructureRat, xInTermsOfW_vars_subset
-/
theorem wittStructureRat_vars [Fintype idx] (Φ : MvPolynomial idx Rat) (n : Nat) :
    (wittStructureRat p Φ n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) := by
  rw [wittStructureRat]
  intro x hx
  simp only [Finset.mem_product, true_and, Finset.mem_univ, Finset.mem_range]
  obtain ⟨k, hk, hx'⟩ := mem_vars_bind₁ _ _ hx
  obtain ⟨i, -, hx''⟩ := mem_vars_bind₁ _ _ hx'
  obtain ⟨j, hj, rfl⟩ := mem_vars_rename _ _ hx''
  rw [wittPolynomial_vars]; rw [Finset.mem_range] at hj
  replace hk := xInTermsOfW_vars_subset p _ hk
  grind

-- we could relax the fintype on `idx`, but then we need to cast from finset to set.
-- for our applications `idx` is always finite.
/--
theorem `wittStructureInt_vars` / 定理 `wittStructureInt_vars`

English:
theorem wittStructureInt_vars
  given: [Fintype idx] (Φ : MvPolynomial idx Int) (n : Nat)
  proof: by
  have : Function.Injective (Int.castRingHom Rat) := Int.cast_injective
  rw [← vars_map_of_injective _ this]; rw [map_wittStructureInt]
  apply wittStructureRat_vars

中文:
定理 wittStructure整数_vars
  条件: [有限类型 idx] (Φ : 多元多项式 idx 整数) (n : 自然数)
  证明: by
  have : Function.Injective (Int.castRingHom Rat) := Int.cast_injective
  rw [← vars_map_of_injective _ this]; rw [map_wittStructureInt]
  apply wittStructureRat_vars

Depends on / 依赖: Function, Function.Injective, Injective, Int.castRingHom, Int.cast_injective, castRingHom, cast_injective, map_wittStructureInt, vars_map_of_injective, wittStructureRat_vars
-/
theorem wittStructureInt_vars [Fintype idx] (Φ : MvPolynomial idx Int) (n : Nat) :
    (wittStructureInt p Φ n).vars subseteq Finset.univ ×ˢ Finset.range (n + 1) := by
  have : Function.Injective (Int.castRingHom Rat) := Int.cast_injective
  rw [← vars_map_of_injective _ this]; rw [map_wittStructureInt]
  apply wittStructureRat_vars

end PPrime
