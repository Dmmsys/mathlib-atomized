/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.WittVector.Frobenius
public import Mathlib.RingTheory.WittVector.Verschiebung
public import Mathlib.RingTheory.WittVector.MulP

/-!
## Identities between operations on the ring of Witt vectors

In this file we derive common identities between the Frobenius and Verschiebung operators.

## Main declarations

* `frobenius_verschiebung`: the composition of Frobenius and Verschiebung is multiplication by `p`
* `verschiebung_mul_frobenius`: the “projection formula”: `V(x * F y) = V x * y`
* `iterate_verschiebung_mul_coeff`: an identity from [Haze09] 6.2

## References

* [Hazewinkel, *Witt Vectors*][Haze09]

* [Commelin and Lewis, *Formalizing the Ring of Witt Vectors*][CL21]
-/

public section


namespace WittVector

variable {p : Nat} {R : Type*} [hp : Fact p.Prime] [CommRing R]

-- type as `\bbW`
local notation "𝕎" => WittVector p

noncomputable section

-- Porting note: `ghost_calc` failure: the manual instances had to be added.
/--
theorem `frobenius_verschiebung` / 定理 `frobenius_verschiebung`

English:
theorem frobenius_verschiebung
  given: (x : 𝕎 R)
  statement: frobenius (verschiebung x) = x * p
  proof: by
  have : IsPoly p fun {R} [CommRing R] x => frobenius (verschiebung x) :=
    IsPoly.comp (hg := frobenius_isPoly p) (hf := verschiebung_isPoly)
  have : IsPoly p fun {R} [CommRing R] x => x * p := mulN_isPoly p p
  ghost_calc x
  ghost_simp [mul_comm]

中文:
定理 frobenius_verschiebung
  条件: (x : 𝕎 R)
  结论: frobenius (verschiebung x) = x * p
  证明: by
  have : IsPoly p fun {R} [CommRing R] x => frobenius (verschiebung x) :=
    IsPoly.comp (hg := frobenius_isPoly p) (hf := verschiebung_isPoly)
  have : IsPoly p fun {R} [CommRing R] x => x * p := mulN_isPoly p p
  ghost_calc x
  ghost_simp [mul_comm]

Depends on / 依赖: CommRing, IsPoly, IsPoly.comp, frobenius, frobenius_isPoly, ghost_calc, ghost_simp, mulN_isPoly, mul_comm, verschiebung, verschiebung_isPoly
-/
theorem frobenius_verschiebung (x : 𝕎 R) : frobenius (verschiebung x) = x * p := by
  have : IsPoly p fun {R} [CommRing R] x => frobenius (verschiebung x) :=
    IsPoly.comp (hg := frobenius_isPoly p) (hf := verschiebung_isPoly)
  have : IsPoly p fun {R} [CommRing R] x => x * p := mulN_isPoly p p
  ghost_calc x
  ghost_simp [mul_comm]

/--
theorem `verschiebung_zmod` / 定理 `verschiebung_zmod`

English:
theorem verschiebung_zmod
  given: (x : 𝕎 (ZMod p))
  statement: verschiebung x = x * p
  proof: by
  rw [← frobenius_verschiebung]; rw [frobenius_zmodp]

中文:
定理 verschiebung_zmod
  条件: (x : 𝕎 (ZMod p))
  结论: verschiebung x = x * p
  证明: by
  rw [← frobenius_verschiebung]; rw [frobenius_zmodp]

Depends on / 依赖: frobenius_verschiebung, frobenius_zmodp
-/
theorem verschiebung_zmod (x : 𝕎 (ZMod p)) : verschiebung x = x * p := by
  rw [← frobenius_verschiebung]; rw [frobenius_zmodp]

variable (p R)

/--
theorem `coeff_p_pow` / 定理 `coeff_p_pow`

English:
theorem coeff_p_pow
  given: [CharP R p] (i : Nat)
  statement: ((p : 𝕎 R) ^ i).coeff i = 1
  proof: by
  induction i with
  | zero => simp only [one_coeff_zero, pow_zero]
  | succ i h =>
    rw [pow_succ]; rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_succ]; rw [h]; rw [one_pow]

中文:
定理 coeff_p_pow
  条件: [特征p R p] (i : 自然数)
  结论: ((p : 𝕎 R) ^ i).coeff i = 1
  证明: by
  induction i with
  | zero => simp only [one_coeff_zero, pow_zero]
  | succ i h =>
    rw [pow_succ]; rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_succ]; rw [h]; rw [one_pow]

Depends on / 依赖: coeff_frobenius_charP, frobenius_verschiebung, one_coeff_zero, one_pow, pow_succ, pow_zero, verschiebung_coeff_succ
-/
theorem coeff_p_pow [CharP R p] (i : Nat) : ((p : 𝕎 R) ^ i).coeff i = 1 := by
  induction i with
  | zero => simp only [one_coeff_zero, pow_zero]
  | succ i h =>
    rw [pow_succ]; rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_succ]; rw [h]; rw [one_pow]

/--
theorem `coeff_p_pow_eq_zero` / 定理 `coeff_p_pow_eq_zero`

English:
theorem coeff_p_pow_eq_zero
  given: [CharP R p] {i j : Nat} (hj : j != i)
  statement: ((p : 𝕎 R) ^ i).coeff j = 0
  proof: by
  induction i generalizing j with
  | zero =>
    rw [pow_zero]; rw [one_coeff_eq_of_pos]
    exact Nat.pos_of_ne_zero hj
  | succ i hi =>
    rw [pow_succ]; rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]
    cases j
    · rw [verschiebung_coeff_zero, zero_pow hp.out.ne_zero]
    · rw 

中文:
定理 coeff_p_pow_eq_zero
  条件: [特征p R p] {i j : 自然数} (hj : j != i)
  结论: ((p : 𝕎 R) ^ i).coeff j = 0
  证明: by
  induction i generalizing j with
  | zero =>
    rw [pow_zero]; rw [one_coeff_eq_of_pos]
    exact Nat.pos_of_ne_zero hj
  | succ i hi =>
    rw [pow_succ]; rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]
    cases j
    · rw [verschiebung_coeff_zero, zero_pow hp.out.ne_zero]
    · rw 

Depends on / 依赖: Nat.pos_of_ne_zero, coeff_frobenius_charP, frobenius_verschiebung, generalizing, hp.out.ne_zero, ne_of_apply_ne, ne_zero, one_coeff_eq_of_pos, pos_of_ne_zero, pow_succ, pow_zero, verschiebung_coeff_succ, verschiebung_coeff_zero, zero_pow
-/
theorem coeff_p_pow_eq_zero [CharP R p] {i j : Nat} (hj : j != i) : ((p : 𝕎 R) ^ i).coeff j = 0 := by
  induction i generalizing j with
  | zero =>
    rw [pow_zero]; rw [one_coeff_eq_of_pos]
    exact Nat.pos_of_ne_zero hj
  | succ i hi =>
    rw [pow_succ]; rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]
    cases j
    · rw [verschiebung_coeff_zero, zero_pow hp.out.ne_zero]
    · rw [verschiebung_coeff_succ, hi (ne_of_apply_ne _ hj), zero_pow hp.out.ne_zero]

/--
theorem `coeff_p` / 定理 `coeff_p`

English:
theorem coeff_p
  given: [CharP R p] (i : Nat)
  statement: (p : 𝕎 R).coeff i = if i = 1 then 1 else 0
  proof: by
  split_ifs with hi
  · simpa only [hi, pow_one] using coeff_p_pow p R 1
  · simpa only [pow_one] using coeff_p_pow_eq_zero p R hi

@[simp]

中文:
定理 coeff_p
  条件: [特征p R p] (i : 自然数)
  结论: (p : 𝕎 R).coeff i = if i = 1 then 1 else 0
  证明: by
  split_ifs with hi
  · simpa only [hi, pow_one] using coeff_p_pow p R 1
  · simpa only [pow_one] using coeff_p_pow_eq_zero p R hi

@[simp]

Depends on / 依赖: coeff_p_pow, coeff_p_pow_eq_zero, pow_one, split_ifs
-/
theorem coeff_p [CharP R p] (i : Nat) : (p : 𝕎 R).coeff i = if i = 1 then 1 else 0 := by
  split_ifs with hi
  · simpa only [hi, pow_one] using coeff_p_pow p R 1
  · simpa only [pow_one] using coeff_p_pow_eq_zero p R hi

@[simp]
/--
theorem `coeff_p_zero` / 定理 `coeff_p_zero`

English:
theorem coeff_p_zero
  given: [CharP R p]
  statement: (p : 𝕎 R).coeff 0 = 0
  proof: by
  rw [coeff_p]; rw [if_neg]
  exact zero_ne_one

@[simp]

中文:
定理 coeff_p_zero
  条件: [特征p R p]
  结论: (p : 𝕎 R).coeff 0 = 0
  证明: by
  rw [coeff_p]; rw [if_neg]
  exact zero_ne_one

@[simp]

Depends on / 依赖: coeff_p, if_neg, zero_ne_one
-/
theorem coeff_p_zero [CharP R p] : (p : 𝕎 R).coeff 0 = 0 := by
  rw [coeff_p]; rw [if_neg]
  exact zero_ne_one

@[simp]
/--
theorem `coeff_p_one` / 定理 `coeff_p_one`

English:
theorem coeff_p_one
  given: [CharP R p]
  statement: (p : 𝕎 R).coeff 1 = 1
  proof: by rw [coeff_p, if_pos rfl]

中文:
定理 coeff_p_one
  条件: [特征p R p]
  结论: (p : 𝕎 R).coeff 1 = 1
  证明: by rw [coeff_p, if_pos rfl]

Depends on / 依赖: coeff_p, if_pos
-/
theorem coeff_p_one [CharP R p] : (p : 𝕎 R).coeff 1 = 1 := by rw [coeff_p, if_pos rfl]

/--
theorem `p_nonzero` / 定理 `p_nonzero`

English:
theorem p_nonzero
  given: [Nontrivial R] [CharP R p]
  statement: (p : 𝕎 R) != 0
  proof: by
  intro h
  simpa only [h, zero_coeff, zero_ne_one] using coeff_p_one p R

中文:
定理 p_nonzero
  条件: [非平凡 R] [特征p R p]
  结论: (p : 𝕎 R) != 0
  证明: by
  intro h
  simpa only [h, zero_coeff, zero_ne_one] using coeff_p_one p R

Depends on / 依赖: coeff_p_one, zero_coeff, zero_ne_one
-/
theorem p_nonzero [Nontrivial R] [CharP R p] : (p : 𝕎 R) != 0 := by
  intro h
  simpa only [h, zero_coeff, zero_ne_one] using coeff_p_one p R

/--
theorem `FractionRing.p_nonzero` / 定理 `FractionRing.p_nonzero`

English:
theorem FractionRing.p_nonzero
  given: [Nontrivial R] [CharP R p]
  statement: (p : FractionRing (𝕎 R)) != 0
  proof: by
  simpa using (IsFractionRing.injective (𝕎 R) (FractionRing (𝕎 R))).ne (WittVector.p_nonzero _ _)

中文:
定理 FractionRing.p_nonzero
  条件: [非平凡 R] [特征p R p]
  结论: (p : FractionRing (𝕎 R)) != 0
  证明: by
  simpa using (IsFractionRing.injective (𝕎 R) (FractionRing (𝕎 R))).ne (WittVector.p_nonzero _ _)

Depends on / 依赖: FractionRing, IsFractionRing, IsFractionRing.injective, WittVector, WittVector.p_nonzero, injective, p_nonzero
-/
theorem FractionRing.p_nonzero [Nontrivial R] [CharP R p] : (p : FractionRing (𝕎 R)) != 0 := by
  simpa using (IsFractionRing.injective (𝕎 R) (FractionRing (𝕎 R))).ne (WittVector.p_nonzero _ _)

variable {p R}

-- Porting note: `ghost_calc` failure: the manual instances had to be added.
/--
theorem `verschiebung_mul_frobenius` / 定理 `verschiebung_mul_frobenius`

English:
theorem verschiebung_mul_frobenius
  given: (x y : 𝕎 R)
  proof: by
  have : IsPoly₂ p fun {R} [Rcr : CommRing R] x y => verschiebung (x * frobenius y) :=
    IsPoly.comp₂ (hg := verschiebung_isPoly)
      (hf := IsPoly₂.comp (hh := mulIsPoly₂) (hf := idIsPolyI' p) (hg := frobenius_isPoly p))
  have : IsPoly₂ p fun {R} [CommRing R] x y => verschiebung x * y :=
  

中文:
定理 verschiebung_mul_frobenius
  条件: (x y : 𝕎 R)
  证明: by
  have : IsPoly₂ p fun {R} [Rcr : CommRing R] x y => verschiebung (x * frobenius y) :=
    IsPoly.comp₂ (hg := verschiebung_isPoly)
      (hf := IsPoly₂.comp (hh := mulIsPoly₂) (hf := idIsPolyI' p) (hg := frobenius_isPoly p))
  have : IsPoly₂ p fun {R} [CommRing R] x y => verschiebung x * y :=
  

Depends on / 依赖: CommRing, IsPoly, IsPoly.comp, frobenius, frobenius_isPoly, ghost_calc, ghost_simp, idIsPolyI, mul_assoc, verschiebung, verschiebung_isPoly
-/
theorem verschiebung_mul_frobenius (x y : 𝕎 R) :
    verschiebung (x * frobenius y) = verschiebung x * y := by
  have : IsPoly₂ p fun {R} [Rcr : CommRing R] x y => verschiebung (x * frobenius y) :=
    IsPoly.comp₂ (hg := verschiebung_isPoly)
      (hf := IsPoly₂.comp (hh := mulIsPoly₂) (hf := idIsPolyI' p) (hg := frobenius_isPoly p))
  have : IsPoly₂ p fun {R} [CommRing R] x y => verschiebung x * y :=
    IsPoly₂.comp (hh := mulIsPoly₂) (hf := verschiebung_isPoly) (hg := idIsPolyI' p)
  ghost_calc x y
  rintro ⟨⟩ <;> ghost_simp [mul_assoc]

/--
theorem `mul_charP_coeff_zero` / 定理 `mul_charP_coeff_zero`

English:
theorem mul_charP_coeff_zero
  given: [CharP R p] (x : 𝕎 R)
  statement: (x * p).coeff 0 = 0
  proof: by
  rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_zero]; rw [zero_pow hp.out.ne_zero]

中文:
定理 mul_charP_coeff_zero
  条件: [特征p R p] (x : 𝕎 R)
  结论: (x * p).coeff 0 = 0
  证明: by
  rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_zero]; rw [zero_pow hp.out.ne_zero]

Depends on / 依赖: coeff_frobenius_charP, frobenius_verschiebung, hp.out.ne_zero, ne_zero, verschiebung_coeff_zero, zero_pow
-/
theorem mul_charP_coeff_zero [CharP R p] (x : 𝕎 R) : (x * p).coeff 0 = 0 := by
  rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_zero]; rw [zero_pow hp.out.ne_zero]

/--
theorem `mul_charP_coeff_succ` / 定理 `mul_charP_coeff_succ`

English:
theorem mul_charP_coeff_succ
  given: [CharP R p] (x : 𝕎 R) (i : Nat)
  proof: by
  rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_succ]

中文:
定理 mul_charP_coeff_succ
  条件: [特征p R p] (x : 𝕎 R) (i : 自然数)
  证明: by
  rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_succ]

Depends on / 依赖: coeff_frobenius_charP, frobenius_verschiebung, verschiebung_coeff_succ
-/
theorem mul_charP_coeff_succ [CharP R p] (x : 𝕎 R) (i : Nat) :
    (x * p).coeff (i + 1) = x.coeff i ^ p := by
  rw [← frobenius_verschiebung]; rw [coeff_frobenius_charP]; rw [verschiebung_coeff_succ]

/--
theorem `mul_pow_charP_coeff_zero` / 定理 `mul_pow_charP_coeff_zero`

English:
theorem mul_pow_charP_coeff_zero
  given: [CharP R p] (x : 𝕎 R) {m n : Nat} (h : m < n)
  proof: by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [pow_succ]; rw [← mul_assoc]
    cases m with
    | zero => exact mul_charP_coeff_zero _
    | succ m' =>
      rw [mul_charP_coeff_succ]; rw [ih]; rw [zero_pow hp.out.ne_zero]
      simpa using h

中文:
定理 mul_pow_charP_coeff_zero
  条件: [特征p R p] (x : 𝕎 R) {m n : 自然数} (h : m < n)
  证明: by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [pow_succ]; rw [← mul_assoc]
    cases m with
    | zero => exact mul_charP_coeff_zero _
    | succ m' =>
      rw [mul_charP_coeff_succ]; rw [ih]; rw [zero_pow hp.out.ne_zero]
      simpa using h

Depends on / 依赖: generalizing, hp.out.ne_zero, mul_assoc, mul_charP_coeff_succ, mul_charP_coeff_zero, ne_zero, pow_succ, zero_pow
-/
theorem mul_pow_charP_coeff_zero [CharP R p] (x : 𝕎 R) {m n : Nat} (h : m < n) :
    (x * p ^ n).coeff m = 0 := by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [pow_succ]; rw [← mul_assoc]
    cases m with
    | zero => exact mul_charP_coeff_zero _
    | succ m' =>
      rw [mul_charP_coeff_succ]; rw [ih]; rw [zero_pow hp.out.ne_zero]
      simpa using h

/--
theorem `mul_pow_charP_coeff_succ` / 定理 `mul_pow_charP_coeff_succ`

English:
theorem mul_pow_charP_coeff_succ
  given: [CharP R p] (x : 𝕎 R) {m n : Nat}
  proof: by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [← mul_assoc]; rw [← add_assoc]; rw [mul_charP_coeff_succ]; rw [pow_succ]; rw [pow_mul]
    congr
    exact ih

中文:
定理 mul_pow_charP_coeff_succ
  条件: [特征p R p] (x : 𝕎 R) {m n : 自然数}
  证明: by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [← mul_assoc]; rw [← add_assoc]; rw [mul_charP_coeff_succ]; rw [pow_succ]; rw [pow_mul]
    congr
    exact ih

Depends on / 依赖: add_assoc, generalizing, mul_assoc, mul_charP_coeff_succ, pow_mul, pow_succ
-/
theorem mul_pow_charP_coeff_succ [CharP R p] (x : 𝕎 R) {m n : Nat} :
    (x * p ^ n).coeff (m + n) = x.coeff m ^ (p ^ n) := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]; rw [← mul_assoc]; rw [← add_assoc]; rw [mul_charP_coeff_succ]; rw [pow_succ]; rw [pow_mul]
    congr
    exact ih

/--
theorem `verschiebung_frobenius` / 定理 `verschiebung_frobenius`

English:
theorem verschiebung_frobenius
  given: [CharP R p] (x : 𝕎 R)
  statement: verschiebung (frobenius x) = x * p
  proof: by
  ext ⟨i⟩
  · rw [mul_charP_coeff_zero, verschiebung_coeff_zero]
  · rw [mul_charP_coeff_succ, verschiebung_coeff_succ, coeff_frobenius_charP]

中文:
定理 verschiebung_frobenius
  条件: [特征p R p] (x : 𝕎 R)
  结论: verschiebung (frobenius x) = x * p
  证明: by
  ext ⟨i⟩
  · rw [mul_charP_coeff_zero, verschiebung_coeff_zero]
  · rw [mul_charP_coeff_succ, verschiebung_coeff_succ, coeff_frobenius_charP]

Depends on / 依赖: coeff_frobenius_charP, mul_charP_coeff_succ, mul_charP_coeff_zero, verschiebung_coeff_succ, verschiebung_coeff_zero
-/
theorem verschiebung_frobenius [CharP R p] (x : 𝕎 R) : verschiebung (frobenius x) = x * p := by
  ext ⟨i⟩
  · rw [mul_charP_coeff_zero, verschiebung_coeff_zero]
  · rw [mul_charP_coeff_succ, verschiebung_coeff_succ, coeff_frobenius_charP]

/--
theorem `verschiebung_frobenius_comm` / 定理 `verschiebung_frobenius_comm`

English:
theorem verschiebung_frobenius_comm
  given: [CharP R p]
  proof: fun x => by
  rw [verschiebung_frobenius]; rw [frobenius_verschiebung]

中文:
定理 verschiebung_frobenius_comm
  条件: [特征p R p]
  证明: fun x => by
  rw [verschiebung_frobenius]; rw [frobenius_verschiebung]

Depends on / 依赖: frobenius_verschiebung, verschiebung_frobenius
-/
theorem verschiebung_frobenius_comm [CharP R p] :
    Function.Commute (verschiebung : 𝕎 R -> 𝕎 R) frobenius := fun x => by
  rw [verschiebung_frobenius]; rw [frobenius_verschiebung]

/-!
## Iteration lemmas
-/


open Function

/--
theorem `iterate_verschiebung_coeff_eq_zero` / 定理 `iterate_verschiebung_coeff_eq_zero`

English:
theorem iterate_verschiebung_coeff_eq_zero
  given: (x : 𝕎 R) {n : Nat} {m : Nat} (h : m < n)
  proof: by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [iterate_succ_apply']
    cases m with
    | zero => exact verschiebung_coeff_zero _
    | succ m' =>
      rw [verschiebung_coeff_succ]; rw [ih]
      simpa using h

中文:
定理 iterate_verschiebung_coeff_eq_zero
  条件: (x : 𝕎 R) {n : 自然数} {m : 自然数} (h : m < n)
  证明: by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [iterate_succ_apply']
    cases m with
    | zero => exact verschiebung_coeff_zero _
    | succ m' =>
      rw [verschiebung_coeff_succ]; rw [ih]
      simpa using h

Depends on / 依赖: generalizing, iterate_succ_apply, verschiebung_coeff_succ, verschiebung_coeff_zero
-/
theorem iterate_verschiebung_coeff_eq_zero (x : 𝕎 R) {n : Nat} {m : Nat} (h : m < n) :
    (verschiebung^[n] x).coeff m = 0 := by
  induction n generalizing m with
  | zero => contradiction
  | succ n ih =>
    rw [iterate_succ_apply']
    cases m with
    | zero => exact verschiebung_coeff_zero _
    | succ m' =>
      rw [verschiebung_coeff_succ]; rw [ih]
      simpa using h

/--
theorem `iterate_verschiebung_coeff` / 定理 `iterate_verschiebung_coeff`

English:
theorem iterate_verschiebung_coeff
  given: (x : 𝕎 R) (n k : Nat)
  proof: by
  induction n with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', Nat.add_succ, verschiebung_coeff_succ]; exact ih

中文:
定理 iterate_verschiebung_coeff
  条件: (x : 𝕎 R) (n k : 自然数)
  证明: by
  induction n with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', Nat.add_succ, verschiebung_coeff_succ]; exact ih

Depends on / 依赖: Nat.add_succ, add_succ, iterate_succ_apply, verschiebung_coeff_succ
-/
theorem iterate_verschiebung_coeff (x : 𝕎 R) (n k : Nat) :
    (verschiebung^[n] x).coeff (k + n) = x.coeff k := by
  induction n with
  | zero => simp
  | succ k ih => rw [iterate_succ_apply', Nat.add_succ, verschiebung_coeff_succ]; exact ih

/--
theorem `iterate_verschiebung_mul_left` / 定理 `iterate_verschiebung_mul_left`

English:
theorem iterate_verschiebung_mul_left
  given: (x y : 𝕎 R) (i : Nat)
  proof: by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply']; rw [← verschiebung_mul_frobenius]; rw [ih]; rw [iterate_succ_apply']; rw [iterate_succ_apply]

中文:
定理 iterate_verschiebung_mul_left
  条件: (x y : 𝕎 R) (i : 自然数)
  证明: by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply']; rw [← verschiebung_mul_frobenius]; rw [ih]; rw [iterate_succ_apply']; rw [iterate_succ_apply]

Depends on / 依赖: generalizing, iterate_succ_apply, verschiebung_mul_frobenius
-/
theorem iterate_verschiebung_mul_left (x y : 𝕎 R) (i : Nat) :
    verschiebung^[i] x * y = verschiebung^[i] (x * frobenius^[i] y) := by
  induction i generalizing y with
  | zero => simp
  | succ i ih =>
    rw [iterate_succ_apply']; rw [← verschiebung_mul_frobenius]; rw [ih]; rw [iterate_succ_apply']; rw [iterate_succ_apply]

section CharP

variable [CharP R p]

/--
theorem `iterate_verschiebung_mul` / 定理 `iterate_verschiebung_mul`

English:
theorem iterate_verschiebung_mul
  given: (x y : 𝕎 R) (i j : Nat)
  proof: by
  calc
    _ = verschiebung^[i] (x * frobenius^[i] (verschiebung^[j] y)) := ?_
    _ = verschiebung^[i] (x * verschiebung^[j] (frobenius^[i] y)) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y) * x) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y * frobenius^[j

中文:
定理 iterate_verschiebung_mul
  条件: (x y : 𝕎 R) (i j : 自然数)
  证明: by
  calc
    _ = verschiebung^[i] (x * frobenius^[i] (verschiebung^[j] y)) := ?_
    _ = verschiebung^[i] (x * verschiebung^[j] (frobenius^[i] y)) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y) * x) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y * frobenius^[j

Depends on / 依赖: frobenius, iterate_iterate, iterate_verschie, iterate_verschiebung_mul_left, mul_comm, verschiebung, verschiebung_frobenius_comm, verschiebung_frobenius_comm.iterate_iterate
-/
theorem iterate_verschiebung_mul (x y : 𝕎 R) (i j : Nat) :
    verschiebung^[i] x * verschiebung^[j] y =
      verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y) := by
  calc
    _ = verschiebung^[i] (x * frobenius^[i] (verschiebung^[j] y)) := ?_
    _ = verschiebung^[i] (x * verschiebung^[j] (frobenius^[i] y)) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y) * x) := ?_
    _ = verschiebung^[i] (verschiebung^[j] (frobenius^[i] y * frobenius^[j] x)) := ?_
    _ = verschiebung^[i + j] (frobenius^[i] y * frobenius^[j] x) := ?_
    _ = _ := ?_
  · apply iterate_verschiebung_mul_left
  · rw [verschiebung_frobenius_comm.iterate_iterate]
  · rw [mul_comm]
  · rw [iterate_verschiebung_mul_left]
  · rw [iterate_add_apply]
  · rw [mul_comm]

/--
theorem `iterate_frobenius_coeff` / 定理 `iterate_frobenius_coeff`

English:
theorem iterate_frobenius_coeff
  given: (x : 𝕎 R) (i k : Nat)
  proof: by
  induction i with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply', coeff_frobenius_charP, ih]; ring_nf

中文:
定理 iterate_frobenius_coeff
  条件: (x : 𝕎 R) (i k : 自然数)
  证明: by
  induction i with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply', coeff_frobenius_charP, ih]; ring_nf

Depends on / 依赖: coeff_frobenius_charP, iterate_succ_apply, ring_nf
-/
theorem iterate_frobenius_coeff (x : 𝕎 R) (i k : Nat) :
    (frobenius^[i] x).coeff k = x.coeff k ^ p ^ i := by
  induction i with
  | zero => simp
  | succ i ih => rw [iterate_succ_apply', coeff_frobenius_charP, ih]; ring_nf

/--
theorem `iterate_verschiebung_mul_coeff` / 定理 `iterate_verschiebung_mul_coeff`

English:
theorem iterate_verschiebung_mul_coeff
  given: (x y : 𝕎 R) (i j : Nat)
  proof: by
  calc
    _ = (verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y)).coeff (i + j) := ?_
    _ = (frobenius^[j] x * frobenius^[i] y).coeff 0 := ?_
    _ = (frobenius^[j] x).coeff 0 * (frobenius^[i] y).coeff 0 := ?_
    _ = _ := ?_
  · rw [iterate_verschiebung_mul]
  · convert! iterate_versch

中文:
定理 iterate_verschiebung_mul_coeff
  条件: (x y : 𝕎 R) (i j : 自然数)
  证明: by
  calc
    _ = (verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y)).coeff (i + j) := ?_
    _ = (frobenius^[j] x * frobenius^[i] y).coeff 0 := ?_
    _ = (frobenius^[j] x).coeff 0 * (frobenius^[i] y).coeff 0 := ?_
    _ = _ := ?_
  · rw [iterate_verschiebung_mul]
  · convert! iterate_versch

Depends on / 依赖: convert, frobenius, iterate_frobenius_coeff, iterate_verschiebung_coeff, iterate_verschiebung_mul, mul_coeff_zero, verschiebung, zero_add
-/
theorem iterate_verschiebung_mul_coeff (x y : 𝕎 R) (i j : Nat) :
    (verschiebung^[i] x * verschiebung^[j] y).coeff (i + j) =
      x.coeff 0 ^ p ^ j * y.coeff 0 ^ p ^ i := by
  calc
    _ = (verschiebung^[i + j] (frobenius^[j] x * frobenius^[i] y)).coeff (i + j) := ?_
    _ = (frobenius^[j] x * frobenius^[i] y).coeff 0 := ?_
    _ = (frobenius^[j] x).coeff 0 * (frobenius^[i] y).coeff 0 := ?_
    _ = _ := ?_
  · rw [iterate_verschiebung_mul]
  · convert! iterate_verschiebung_coeff (p := p) (R := R) _ _ _ using 2
    rw [zero_add]
  · apply mul_coeff_zero
  · simp only [iterate_frobenius_coeff]

/--
theorem `iterate_verschiebung_iterate_frobenius` / 定理 `iterate_verschiebung_iterate_frobenius`

English:
theorem iterate_verschiebung_iterate_frobenius
  given: (x : 𝕎 R) (n : Nat)
  proof: by
  rw [← comp_apply (f := verschiebung^[n]),
      ← Function.Commute.comp_iterate verschiebung_frobenius_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']; rw [ih]; rw [pow_succ]; rw [comp_apply]; rw [verschiebung_frobenius]; rw [mul_assoc]

中文:
定理 iterate_verschiebung_iterate_frobenius
  条件: (x : 𝕎 R) (n : 自然数)
  证明: by
  rw [← comp_apply (f := verschiebung^[n]),
      ← Function.Commute.comp_iterate verschiebung_frobenius_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']; rw [ih]; rw [pow_succ]; rw [comp_apply]; rw [verschiebung_frobenius]; rw [mul_assoc]

Depends on / 依赖: Commute, Function, Function.Commute.comp_iterate, comp_apply, comp_iterate, iterate_succ_apply, mul_assoc, pow_succ, verschiebung, verschiebung_frobenius, verschiebung_frobenius_comm
-/
theorem iterate_verschiebung_iterate_frobenius (x : 𝕎 R) (n : Nat) :
    verschiebung^[n] (frobenius^[n] x) = x * (p ^ n) := by
  rw [← comp_apply (f := verschiebung^[n]),
      ← Function.Commute.comp_iterate verschiebung_frobenius_comm]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply']; rw [ih]; rw [pow_succ]; rw [comp_apply]; rw [verschiebung_frobenius]; rw [mul_assoc]

end CharP

end

end WittVector
