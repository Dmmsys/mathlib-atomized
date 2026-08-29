/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.Polynomial.CancelLeads
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : R[X]`.
- `p.content` is the `gcd` of the coefficients of `p`.
- `p.IsPrimitive` indicates that `p.content = 1`.

## Main Results
- `Polynomial.content_mul`: if `p q : R[X]`, then `(p * q).content = p.content * q.content`.
- `Polynomial.NormalizedGcdMonoid`: the polynomial ring of a GCD domain is itself a GCD domain.

## Note

This has nothing to do with minimal polynomials of primitive elements in finite fields.

-/

@[expose] public section


namespace Polynomial

section Primitive

variable {R : Type*} [CommSemiring R]

/--
Definition of `IsPrimitive` / `IsPrimitive` 的定义

English:
definition IsPrimitive
  signature: (p : R[X])
  body: forall r : R, C r ∣ p -> IsUnit r

中文:
定义 是Primitive
  签名: (p : R[X])
  定义体: forall r : R, C r ∣ p -> IsUnit r

Depends on / 依赖: IsUnit
-/
def IsPrimitive (p : R[X]) : Prop :=
  forall r : R, C r ∣ p -> IsUnit r

/--
theorem `isPrimitive_iff_isUnit_of_C_dvd` / 定理 `isPrimitive_iff_isUnit_of_C_dvd`

English:
theorem isPrimitive_iff_isUnit_of_C_dvd
  given: {p : R[X]}
  statement: p.IsPrimitive ↔ forall r : R, C r ∣ p -> IsUnit r
  proof: Iff.rfl

@[simp]

中文:
定理 isPrimitive_iff_isUnit_of_C_dvd
  条件: {p : R[X]}
  结论: p.是Primitive ↔ 对任意 r : R, C r ∣ p -> 是单位 r
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem isPrimitive_iff_isUnit_of_C_dvd {p : R[X]} : p.IsPrimitive ↔ forall r : R, C r ∣ p -> IsUnit r :=
  Iff.rfl

@[simp]
/--
theorem `isPrimitive_one` / 定理 `isPrimitive_one`

English:
theorem isPrimitive_one
  statement: IsPrimitive (1 : R[X])
  proof: fun _ h =>
  isUnit_C.mp (isUnit_of_dvd_one h)

中文:
定理 isPrimitive_one
  结论: 是Primitive (1 : R[X])
  证明: fun _ h =>
  isUnit_C.mp (isUnit_of_dvd_one h)
-/
theorem isPrimitive_one : IsPrimitive (1 : R[X]) := fun _ h =>
  isUnit_C.mp (isUnit_of_dvd_one h)

/--
theorem `Monic.isPrimitive` / 定理 `Monic.isPrimitive`

English:
theorem Monic.isPrimitive
  given: {p : R[X]} (hp : p.Monic)
  statement: p.IsPrimitive
  proof: by
  rintro r ⟨q, h⟩
  exact .of_mul_eq_one (q.coeff p.natDegree) (by rwa [← coeff_C_mul, ← h])

中文:
定理 Monic.isPrimitive
  条件: {p : R[X]} (hp : p.Monic)
  结论: p.是Primitive
  证明: by
  rintro r ⟨q, h⟩
  exact .of_mul_eq_one (q.coeff p.natDegree) (by rwa [← coeff_C_mul, ← h])

Depends on / 依赖: coeff_C_mul, natDegree, of_mul_eq_one, p.natDegree, q.coeff
-/
theorem Monic.isPrimitive {p : R[X]} (hp : p.Monic) : p.IsPrimitive := by
  rintro r ⟨q, h⟩
  exact .of_mul_eq_one (q.coeff p.natDegree) (by rwa [← coeff_C_mul, ← h])

/--
theorem `IsPrimitive.ne_zero` / 定理 `IsPrimitive.ne_zero`

English:
theorem IsPrimitive.ne_zero
  given: [Nontrivial R] {p : R[X]} (hp : p.IsPrimitive)
  statement: p != 0
  proof: by
  rintro rfl
  exact (hp 0 (dvd_zero (C 0))).ne_zero rfl

中文:
定理 是Primitive.ne_zero
  条件: [非平凡 R] {p : R[X]} (hp : p.是Primitive)
  结论: p != 0
  证明: by
  rintro rfl
  exact (hp 0 (dvd_zero (C 0))).ne_zero rfl

Depends on / 依赖: dvd_zero, ne_zero
-/
theorem IsPrimitive.ne_zero [Nontrivial R] {p : R[X]} (hp : p.IsPrimitive) : p != 0 := by
  rintro rfl
  exact (hp 0 (dvd_zero (C 0))).ne_zero rfl

/--
theorem `isPrimitive_of_dvd` / 定理 `isPrimitive_of_dvd`

English:
theorem isPrimitive_of_dvd
  given: {p q : R[X]} (hp : IsPrimitive p) (hq : q ∣ p)
  statement: IsPrimitive q
  proof: fun a ha => isPrimitive_iff_isUnit_of_C_dvd.mp hp a (dvd_trans ha hq)

中文:
定理 isPrimitive_of_dvd
  条件: {p q : R[X]} (hp : 是Primitive p) (hq : q ∣ p)
  结论: 是Primitive q
  证明: fun a ha => isPrimitive_iff_isUnit_of_C_dvd.mp hp a (dvd_trans ha hq)

Depends on / 依赖: dvd_trans, isPrimitive_iff_isUnit_of_C_dvd, isPrimitive_iff_isUnit_of_C_dvd.mp
-/
theorem isPrimitive_of_dvd {p q : R[X]} (hp : IsPrimitive p) (hq : q ∣ p) : IsPrimitive q :=
  fun a ha => isPrimitive_iff_isUnit_of_C_dvd.mp hp a (dvd_trans ha hq)

/--
theorem `_root_.Irreducible.isPrimitive` / 定理 `_root_.Irreducible.isPrimitive`

English:
theorem _root_.Irreducible.isPrimitive
  statement: [NoZeroDivisors R]
  proof: by
  rintro r ⟨q, hq⟩
  suffices ¬IsUnit q by simpa using ((hp.2 hq).resolve_right this).map Polynomial.constantCoeff
  intro H
  have hr : r != 0 := by rintro rfl; simp_all
  obtain ⟨s, hs, rfl⟩ := Polynomial.isUnit_iff.mp H
  simp [hq, Polynomial.natDegree_C_mul hr] at hp'

中文:
定理 _root_.不可约.isPrimitive
  结论: [无零因子 R]
  证明: by
  rintro r ⟨q, hq⟩
  suffices ¬IsUnit q by simpa using ((hp.2 hq).resolve_right this).map Polynomial.constantCoeff
  intro H
  have hr : r != 0 := by rintro rfl; simp_all
  obtain ⟨s, hs, rfl⟩ := Polynomial.isUnit_iff.mp H
  simp [hq, Polynomial.natDegree_C_mul hr] at hp'

Depends on / 依赖: IsUnit, Polynomial, Polynomial.constantCoeff, Polynomial.isUnit_iff.mp, Polynomial.natDegree_C_mul, constantCoeff, isUnit_iff, natDegree_C_mul, resolve_right
-/
theorem _root_.Irreducible.isPrimitive [NoZeroDivisors R]
    {p : Polynomial R} (hp : Irreducible p) (hp' : p.natDegree != 0) : p.IsPrimitive := by
  rintro r ⟨q, hq⟩
  suffices ¬IsUnit q by simpa using ((hp.2 hq).resolve_right this).map Polynomial.constantCoeff
  intro H
  have hr : r != 0 := by rintro rfl; simp_all
  obtain ⟨s, hs, rfl⟩ := Polynomial.isUnit_iff.mp H
  simp [hq, Polynomial.natDegree_C_mul hr] at hp'

/-- In a field, the notion of primitive polynomials is degenerate. -/
@[simp]
/--
theorem `isPrimitive_iff_ne_zero` / 定理 `isPrimitive_iff_ne_zero`

English:
theorem isPrimitive_iff_ne_zero
  given: {F : Type*} [Field F] (p : F[X])
  statement: p.IsPrimitive ↔ p != 0
  proof: ⟨IsPrimitive.ne_zero, fun h _ hrp => .mk0 _ fun hr => ne_zero_of_dvd_ne_zero h hrp hr ▸ C_0⟩

中文:
定理 isPrimitive_iff_ne_zero
  条件: {F : 类型} [域 F] (p : F[X])
  结论: p.是Primitive ↔ p != 0
  证明: ⟨IsPrimitive.ne_zero, fun h _ hrp => .mk0 _ fun hr => ne_zero_of_dvd_ne_zero h hrp hr ▸ C_0⟩

Depends on / 依赖: IsPrimitive, IsPrimitive.ne_zero, ne_zero, ne_zero_of_dvd_ne_zero
-/
theorem isPrimitive_iff_ne_zero {F : Type*} [Field F] (p : F[X]) : p.IsPrimitive ↔ p != 0 :=
⟨IsPrimitive.ne_zero, fun h _ hrp => .mk0 _ fun hr => ne_zero_of_dvd_ne_zero h hrp hr ▸ C_0⟩

end Primitive

variable {R : Type*} [CommRing R]

section NormalizedGCDMonoid

variable [NormalizedGCDMonoid R]

/--
Definition of `content` / `content` 的定义

English:
definition content
  signature: (p : R[X])
  body: p.support.gcd p.coeff

中文:
定义 content
  签名: (p : R[X])
  定义体: p.support.gcd p.coeff

Depends on / 依赖: p.coeff, p.support.gcd, support
-/
def content (p : R[X]) : R :=
  p.support.gcd p.coeff

/--
theorem `content_dvd_coeff` / 定理 `content_dvd_coeff`

English:
theorem content_dvd_coeff
  given: {p : R[X]} (n : Nat)
  statement: p.content ∣ p.coeff n
  proof: by
  by_cases h : n in p.support
  · apply Finset.gcd_dvd h
  rw [mem_support_iff]; rw [Classical.not_not] at h
  rw [h]
  apply dvd_zero

@[simp]

中文:
定理 content_dvd_coeff
  条件: {p : R[X]} (n : 自然数)
  结论: p.content ∣ p.coeff n
  证明: by
  by_cases h : n in p.support
  · apply Finset.gcd_dvd h
  rw [mem_support_iff]; rw [Classical.not_not] at h
  rw [h]
  apply dvd_zero

@[simp]

Depends on / 依赖: Classical, Classical.not_not, Finset, Finset.gcd_dvd, dvd_zero, gcd_dvd, mem_support_iff, not_not, p.support, support
-/
theorem content_dvd_coeff {p : R[X]} (n : Nat) : p.content ∣ p.coeff n := by
  by_cases h : n in p.support
  · apply Finset.gcd_dvd h
  rw [mem_support_iff]; rw [Classical.not_not] at h
  rw [h]
  apply dvd_zero

@[simp]
/--
theorem `content_C` / 定理 `content_C`

English:
theorem content_C
  given: {r : R}
  statement: (C r).content = normalize r
  proof: by
  rw [content]
  by_cases h0 : r = 0
  · simp [h0]
  have h : (C r).support = {0} := support_monomial _ h0
  simp [h]

@[simp]

中文:
定理 content_C
  条件: {r : R}
  结论: (C r).content = normalize r
  证明: by
  rw [content]
  by_cases h0 : r = 0
  · simp [h0]
  have h : (C r).support = {0} := support_monomial _ h0
  simp [h]

@[simp]

Depends on / 依赖: content, support, support_monomial
-/
theorem content_C {r : R} : (C r).content = normalize r := by
  rw [content]
  by_cases h0 : r = 0
  · simp [h0]
  have h : (C r).support = {0} := support_monomial _ h0
  simp [h]

@[simp]
/--
theorem `content_zero` / 定理 `content_zero`

English:
theorem content_zero
  statement: content (0 : R[X]) = 0
  proof: by rw [← C_0, content_C, normalize_zero]

@[simp]

中文:
定理 content_zero
  结论: content (0 : R[X]) = 0
  证明: by rw [← C_0, content_C, normalize_zero]

@[simp]

Depends on / 依赖: content_C, normalize_zero
-/
theorem content_zero : content (0 : R[X]) = 0 := by rw [← C_0, content_C, normalize_zero]

@[simp]
/--
theorem `content_one` / 定理 `content_one`

English:
theorem content_one
  statement: content (1 : R[X]) = 1
  proof: by rw [← C_1, content_C, normalize_one]

中文:
定理 content_one
  结论: content (1 : R[X]) = 1
  证明: by rw [← C_1, content_C, normalize_one]

Depends on / 依赖: content_C, instModule, normalize_one
-/
theorem content_one : content (1 : R[X]) = 1 := by rw [← C_1, content_C, normalize_one]

/--
theorem `content_X_mul` / 定理 `content_X_mul`

English:
theorem content_X_mul
  given: {p : R[X]}
  statement: content (X * p) = content p
  proof: by
  rw [content]; rw [content]; rw [Finset.gcd_def]; rw [Finset.gcd_def]
  refine congr rfl ?_
  have h : (X * p).support = p.support.map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext a
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Ne, mem_support_iff]
    rcases a with - | a
    · simp
    rw [mul_comm]; rw [coeff_mul_X]
    constructor
    · intro h
      use a
    · rintro ⟨b, ⟨h1, h2⟩⟩
      rw [← Nat.succ_injective h2]
      apply h1
  rw [h]
  simp

@[simp]

中文:
定理 content_X_mul
  条件: {p : R[X]}
  结论: content (X * p) = content p
  证明: by
  rw [content]; rw [content]; rw [Finset.gcd_def]; rw [Finset.gcd_def]
  refine congr rfl ?_
  have h : (X * p).support = p.support.map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext a
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Ne, mem_support_iff]
    rcases a with - | a
    · simp
    rw [mul_comm]; rw [coeff_mul_X]
    constructor
    · intro h
      use a
    · rintro ⟨b, ⟨h1, h2⟩⟩
      rw [← Nat.succ_injective h2]
      apply h1
  rw [h]
  simp

@[simp]

Depends on / 依赖: Embedding, Finset, Finset.gcd_def, Finset.mem_map, Function, Function.Embedding.coeFn_mk, Nat.succ, Nat.succ_injective, coeFn_mk, coeff_mul_X, content, gcd_def, mem_map, mem_support_iff, mul_comm, p.support.map, succ_injective, support
-/
theorem content_X_mul {p : R[X]} : content (X * p) = content p := by
  rw [content]; rw [content]; rw [Finset.gcd_def]; rw [Finset.gcd_def]
  refine congr rfl ?_
  have h : (X * p).support = p.support.map ⟨Nat.succ, Nat.succ_injective⟩ := by
    ext a
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Ne, mem_support_iff]
    rcases a with - | a
    · simp
    rw [mul_comm]; rw [coeff_mul_X]
    constructor
    · intro h
      use a
    · rintro ⟨b, ⟨h1, h2⟩⟩
      rw [← Nat.succ_injective h2]
      apply h1
  rw [h]
  simp

@[simp]
/--
theorem `content_X_pow` / 定理 `content_X_pow`

English:
theorem content_X_pow
  given: {k : Nat}
  statement: content ((X : R[X]) ^ k) = 1
  proof: by
  induction k with
  | zero => simp
  | succ k hi => rw [pow_succ', content_X_mul, hi]

@[simp]

中文:
定理 content_X_pow
  条件: {k : 自然数}
  结论: content ((X : R[X]) ^ k) = 1
  证明: by
  induction k with
  | zero => simp
  | succ k hi => rw [pow_succ', content_X_mul, hi]

@[simp]

Depends on / 依赖: content_X_mul, pow_succ
-/
theorem content_X_pow {k : Nat} : content ((X : R[X]) ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k hi => rw [pow_succ', content_X_mul, hi]

@[simp]
/--
theorem `content_X` / 定理 `content_X`

English:
theorem content_X
  statement: content (X : R[X]) = 1
  proof: by rw [← mul_one X, content_X_mul, content_one]

中文:
定理 content_X
  结论: content (X : R[X]) = 1
  证明: by rw [← mul_one X, content_X_mul, content_one]

Depends on / 依赖: content_X_mul, content_one, mul_one
-/
theorem content_X : content (X : R[X]) = 1 := by rw [← mul_one X, content_X_mul, content_one]

/--
theorem `content_C_mul` / 定理 `content_C_mul`

English:
theorem content_C_mul
  given: {R} [CommRing R] [StrongNormalizedGCDMonoid R] (r : R) (p : R[X])
  proof: by
  by_cases h0 : r = 0; · simp [h0]
  rw [content]; rw [content]; rw [← Finset.gcd_mul_left]
  refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]

中文:
定理 content_C_mul
  条件: {R} [交换环 R] [StrongNormalizedGCD幺半群 R] (r : R) (p : R[X])
  证明: by
  by_cases h0 : r = 0; · simp [h0]
  rw [content]; rw [content]; rw [← Finset.gcd_mul_left]
  refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]

Depends on / 依赖: Finset, Finset.gcd_mul_left, content, gcd_mul_left, mem_support_iff
-/
theorem content_C_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] (r : R) (p : R[X]) :
    (C r * p).content = normalize r * p.content := by
  by_cases h0 : r = 0; · simp [h0]
  rw [content]; rw [content]; rw [← Finset.gcd_mul_left]
  refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]

/--
theorem `associated_content_C_mul` / 定理 `associated_content_C_mul`

English:
theorem associated_content_C_mul
  given: (r : R) (p : R[X])
  proof: by
  by_cases h0 : r = 0; · simp [h0]
  refine .trans (.of_eq ?_) (Finset.gcd_mul_left' _ _ _)
  rw [content]; refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]

中文:
定理 associated_content_C_mul
  条件: (r : R) (p : R[X])
  证明: by
  by_cases h0 : r = 0; · simp [h0]
  refine .trans (.of_eq ?_) (Finset.gcd_mul_left' _ _ _)
  rw [content]; refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]

Depends on / 依赖: Finset, Finset.gcd_mul_left, content, gcd_mul_left, mem_support_iff, of_eq
-/
theorem associated_content_C_mul (r : R) (p : R[X]) :
    Associated (C r * p).content (r * p.content) := by
  by_cases h0 : r = 0; · simp [h0]
  refine .trans (.of_eq ?_) (Finset.gcd_mul_left' _ _ _)
  rw [content]; refine congr (congr rfl ?_) ?_ <;> ext <;> simp [h0, mem_support_iff]

-- `simp`-normal form is `normUnit_content`
/--
theorem `normalize_content` / 定理 `normalize_content`

English:
theorem normalize_content
  given: {p : R[X]}
  statement: normalize p.content = p.content
  proof: Finset.normalize_gcd

@[simp]

中文:
定理 normalize_content
  条件: {p : R[X]}
  结论: normalize p.content = p.content
  证明: Finset.normalize_gcd

@[simp]

Depends on / 依赖: Finset, Finset.normalize_gcd, normalize_gcd
-/
theorem normalize_content {p : R[X]} : normalize p.content = p.content :=
  Finset.normalize_gcd

@[simp]
/--
theorem `content_monomial` / 定理 `content_monomial`

English:
theorem content_monomial
  given: {r : R} {k : Nat}
  statement: content (monomial k r) = normalize r
  proof: by
  rw [← C_mul_X_pow_eq_monomial]; rw [← normalize_content]; rw [normalize_eq_normalize_iff_associated]
  grw [associated_content_C_mul, content_X_pow, mul_one]
  exact Associated.rfl

中文:
定理 content_monomial
  条件: {r : R} {k : 自然数}
  结论: content (monomial k r) = normalize r
  证明: by
  rw [← C_mul_X_pow_eq_monomial]; rw [← normalize_content]; rw [normalize_eq_normalize_iff_associated]
  grw [associated_content_C_mul, content_X_pow, mul_one]
  exact Associated.rfl

Depends on / 依赖: Associated, Associated.rfl, C_mul_X_pow_eq_monomial, associated_content_C_mul, content_X_pow, mul_one, normalize_content, normalize_eq_normalize_iff_associated
-/
theorem content_monomial {r : R} {k : Nat} : content (monomial k r) = normalize r := by
  rw [← C_mul_X_pow_eq_monomial]; rw [← normalize_content]; rw [normalize_eq_normalize_iff_associated]
  grw [associated_content_C_mul, content_X_pow, mul_one]
  exact Associated.rfl

/--
theorem `content_eq_zero_iff` / 定理 `content_eq_zero_iff`

English:
theorem content_eq_zero_iff
  given: {p : R[X]}
  statement: content p = 0 ↔ p = 0
  proof: by
  rw [content]; rw [Finset.gcd_eq_zero_iff]
  constructor <;> intro h
  · ext n
    simp_all
  · intro x
    simp [h]

@[simp]

中文:
定理 content_eq_zero_iff
  条件: {p : R[X]}
  结论: content p = 0 ↔ p = 0
  证明: by
  rw [content]; rw [Finset.gcd_eq_zero_iff]
  constructor <;> intro h
  · ext n
    simp_all
  · intro x
    simp [h]

@[simp]

Depends on / 依赖: Finset, Finset.gcd_eq_zero_iff, content, gcd_eq_zero_iff
-/
theorem content_eq_zero_iff {p : R[X]} : content p = 0 ↔ p = 0 := by
  rw [content]; rw [Finset.gcd_eq_zero_iff]
  constructor <;> intro h
  · ext n
    simp_all
  · intro x
    simp [h]

@[simp]
/--
theorem `normUnit_content` / 定理 `normUnit_content`

English:
theorem normUnit_content
  given: {p : R[X]}
  statement: normUnit (content p) = 1
  proof: by
  by_cases hp0 : p.content = 0
  · simp [hp0]
  · ext
    apply mul_left_cancel₀ hp0
    rw [← normalize_apply]; rw [normalize_content]; rw [Units.val_one]; rw [mul_one]

中文:
定理 normUnit_content
  条件: {p : R[X]}
  结论: normUnit (content p) = 1
  证明: by
  by_cases hp0 : p.content = 0
  · simp [hp0]
  · ext
    apply mul_left_cancel₀ hp0
    rw [← normalize_apply]; rw [normalize_content]; rw [Units.val_one]; rw [mul_one]

Depends on / 依赖: Units.val_one, content, mul_one, normalize_apply, normalize_content, p.content, val_one
-/
theorem normUnit_content {p : R[X]} : normUnit (content p) = 1 := by
  by_cases hp0 : p.content = 0
  · simp [hp0]
  · ext
    apply mul_left_cancel₀ hp0
    rw [← normalize_apply]; rw [normalize_content]; rw [Units.val_one]; rw [mul_one]

/--
theorem `content_eq_gcd_range_of_lt` / 定理 `content_eq_gcd_range_of_lt`

English:
theorem content_eq_gcd_range_of_lt
  given: (p : R[X]) (n : Nat) (h : p.natDegree < n)
  proof: by
  apply dvd_antisymm_of_normalize_eq normalize_content Finset.normalize_gcd
  · rw [Finset.dvd_gcd_iff]
    intro i _
    apply content_dvd_coeff _
  · exact Finset.gcd_mono (supp_subset_range h)

中文:
定理 content_eq_gcd_range_of_lt
  条件: (p : R[X]) (n : 自然数) (h : p.natDegree < n)
  证明: by
  apply dvd_antisymm_of_normalize_eq normalize_content Finset.normalize_gcd
  · rw [Finset.dvd_gcd_iff]
    intro i _
    apply content_dvd_coeff _
  · exact Finset.gcd_mono (supp_subset_range h)

Depends on / 依赖: Finset, Finset.dvd_gcd_iff, Finset.gcd_mono, Finset.normalize_gcd, content_dvd_coeff, dvd_antisymm_of_normalize_eq, dvd_gcd_iff, gcd_mono, normalize_content, normalize_gcd, supp_subset_range
-/
theorem content_eq_gcd_range_of_lt (p : R[X]) (n : Nat) (h : p.natDegree < n) :
    p.content = (Finset.range n).gcd p.coeff := by
  apply dvd_antisymm_of_normalize_eq normalize_content Finset.normalize_gcd
  · rw [Finset.dvd_gcd_iff]
    intro i _
    apply content_dvd_coeff _
  · exact Finset.gcd_mono (supp_subset_range h)

/--
theorem `content_eq_gcd_range_succ` / 定理 `content_eq_gcd_range_succ`

English:
theorem content_eq_gcd_range_succ
  given: (p : R[X])
  proof: content_eq_gcd_range_of_lt _ _ (Nat.lt_succ_self _)

中文:
定理 content_eq_gcd_range_succ
  条件: (p : R[X])
  证明: content_eq_gcd_range_of_lt _ _ (Nat.lt_succ_self _)

Depends on / 依赖: Nat.lt_succ_self, content_eq_gcd_range_of_lt, lt_succ_self
-/
theorem content_eq_gcd_range_succ (p : R[X]) :
    p.content = (Finset.range p.natDegree.succ).gcd p.coeff :=
  content_eq_gcd_range_of_lt _ _ (Nat.lt_succ_self _)

/--
theorem `content_eq_gcd_leadingCoeff_content_eraseLead` / 定理 `content_eq_gcd_leadingCoeff_content_eraseLead`

English:
theorem content_eq_gcd_leadingCoeff_content_eraseLead
  given: (p : R[X])
  proof: by
  by_cases h : p = 0
  · simp [h]
  rw [← leadingCoeff_eq_zero]; rw [leadingCoeff]; rw [← Ne]; rw [← mem_support_iff] at h
  rw [content]; rw [← Finset.insert_erase h]; rw [Finset.gcd_insert]; rw [leadingCoeff]; rw [content]; rw [eraseLead_support]
  refine congr rfl (Finset.gcd_congr rfl fun i hi => ?_)
  rw [Finset.mem_erase] at hi
  rw [eraseLead_coeff]; rw [if_neg hi.1]

中文:
定理 content_eq_gcd_leadingCoeff_content_eraseLead
  条件: (p : R[X])
  证明: by
  by_cases h : p = 0
  · simp [h]
  rw [← leadingCoeff_eq_zero]; rw [leadingCoeff]; rw [← Ne]; rw [← mem_support_iff] at h
  rw [content]; rw [← Finset.insert_erase h]; rw [Finset.gcd_insert]; rw [leadingCoeff]; rw [content]; rw [eraseLead_support]
  refine congr rfl (Finset.gcd_congr rfl fun i hi => ?_)
  rw [Finset.mem_erase] at hi
  rw [eraseLead_coeff]; rw [if_neg hi.1]

Depends on / 依赖: Finset, Finset.gcd_congr, Finset.gcd_insert, Finset.insert_erase, Finset.mem_erase, content, eraseLead_coeff, eraseLead_support, gcd_congr, gcd_insert, if_neg, insert_erase, leadingCoeff, leadingCoeff_eq_zero, mem_erase, mem_support_iff
-/
theorem content_eq_gcd_leadingCoeff_content_eraseLead (p : R[X]) :
    p.content = gcd p.leadingCoeff (eraseLead p).content := by
  by_cases h : p = 0
  · simp [h]
  rw [← leadingCoeff_eq_zero]; rw [leadingCoeff]; rw [← Ne]; rw [← mem_support_iff] at h
  rw [content]; rw [← Finset.insert_erase h]; rw [Finset.gcd_insert]; rw [leadingCoeff]; rw [content]; rw [eraseLead_support]
  refine congr rfl (Finset.gcd_congr rfl fun i hi => ?_)
  rw [Finset.mem_erase] at hi
  rw [eraseLead_coeff]; rw [if_neg hi.1]

/--
theorem `dvd_content_iff_C_dvd` / 定理 `dvd_content_iff_C_dvd`

English:
theorem dvd_content_iff_C_dvd
  given: {p : R[X]} {r : R}
  statement: r ∣ p.content ↔ C r ∣ p
  proof: by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    apply h.trans (content_dvd_coeff _)
  · intro h
    rw [content]; rw [Finset.dvd_gcd_iff]
    intro i _
    apply h i

中文:
定理 dvd_content_iff_C_dvd
  条件: {p : R[X]} {r : R}
  结论: r ∣ p.content ↔ C r ∣ p
  证明: by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    apply h.trans (content_dvd_coeff _)
  · intro h
    rw [content]; rw [Finset.dvd_gcd_iff]
    intro i _
    apply h i

Depends on / 依赖: C_dvd_iff_dvd_coeff, Finset, Finset.dvd_gcd_iff, content, content_dvd_coeff, dvd_gcd_iff, h.trans
-/
theorem dvd_content_iff_C_dvd {p : R[X]} {r : R} : r ∣ p.content ↔ C r ∣ p := by
  rw [C_dvd_iff_dvd_coeff]
  constructor
  · intro h i
    apply h.trans (content_dvd_coeff _)
  · intro h
    rw [content]; rw [Finset.dvd_gcd_iff]
    intro i _
    apply h i

/--
theorem `C_content_dvd` / 定理 `C_content_dvd`

English:
theorem C_content_dvd
  given: (p : R[X])
  statement: C p.content ∣ p
  proof: dvd_content_iff_C_dvd.1 dvd_rfl

中文:
定理 C_content_dvd
  条件: (p : R[X])
  结论: C p.content ∣ p
  证明: dvd_content_iff_C_dvd.1 dvd_rfl

Depends on / 依赖: dvd_content_iff_C_dvd, dvd_rfl
-/
theorem C_content_dvd (p : R[X]) : C p.content ∣ p :=
  dvd_content_iff_C_dvd.1 dvd_rfl

/--
theorem `isPrimitive_iff_content_eq_one` / 定理 `isPrimitive_iff_content_eq_one`

English:
theorem isPrimitive_iff_content_eq_one
  given: {p : R[X]}
  statement: p.IsPrimitive ↔ p.content = 1
  proof: by
  rw [← normalize_content]; rw [normalize_eq_one]; rw [IsPrimitive]
  simp_rw [← dvd_content_iff_C_dvd]
  exact ⟨fun h => h p.content (dvd_refl p.content), fun h r hdvd => isUnit_of_dvd_unit hdvd h⟩

中文:
定理 isPrimitive_iff_content_eq_one
  条件: {p : R[X]}
  结论: p.是Primitive ↔ p.content = 1
  证明: by
  rw [← normalize_content]; rw [normalize_eq_one]; rw [IsPrimitive]
  simp_rw [← dvd_content_iff_C_dvd]
  exact ⟨fun h => h p.content (dvd_refl p.content), fun h r hdvd => isUnit_of_dvd_unit hdvd h⟩

Depends on / 依赖: IsPrimitive, content, dvd_content_iff_C_dvd, dvd_refl, isUnit_of_dvd_unit, normalize_content, normalize_eq_one, p.content, simp_rw
-/
theorem isPrimitive_iff_content_eq_one {p : R[X]} : p.IsPrimitive ↔ p.content = 1 := by
  rw [← normalize_content]; rw [normalize_eq_one]; rw [IsPrimitive]
  simp_rw [← dvd_content_iff_C_dvd]
  exact ⟨fun h => h p.content (dvd_refl p.content), fun h r hdvd => isUnit_of_dvd_unit hdvd h⟩

/--
theorem `IsPrimitive.content_eq_one` / 定理 `IsPrimitive.content_eq_one`

English:
theorem IsPrimitive.content_eq_one
  given: {p : R[X]} (hp : p.IsPrimitive)
  statement: p.content = 1
  proof: isPrimitive_iff_content_eq_one.mp hp

中文:
定理 是Primitive.content_eq_one
  条件: {p : R[X]} (hp : p.是Primitive)
  结论: p.content = 1
  证明: isPrimitive_iff_content_eq_one.mp hp

Depends on / 依赖: isPrimitive_iff_content_eq_one, isPrimitive_iff_content_eq_one.mp
-/
theorem IsPrimitive.content_eq_one {p : R[X]} (hp : p.IsPrimitive) : p.content = 1 :=
  isPrimitive_iff_content_eq_one.mp hp

section PrimPart

/--
Definition of `primPart` / `primPart` 的定义

English:
definition primPart
  signature: (p : R[X])
  body: letI := Classical.decEq R
  if p = 0 then 1 else Classical.choose (C_content_dvd p)

中文:
定义 primPart
  签名: (p : R[X])
  定义体: letI := Classical.decEq R
  if p = 0 then 1 else Classical.choose (C_content_dvd p)

Depends on / 依赖: C_content_dvd, Classical, Classical.choose, Classical.decEq
-/
noncomputable def primPart (p : R[X]) : R[X] :=
  letI := Classical.decEq R
  if p = 0 then 1 else Classical.choose (C_content_dvd p)

/--
theorem `eq_C_content_mul_primPart` / 定理 `eq_C_content_mul_primPart`

English:
theorem eq_C_content_mul_primPart
  given: (p : R[X])
  statement: p = C p.content * p.primPart
  proof: by
  by_cases h : p = 0; · simp [h]
  rw [primPart]; rw [if_neg h]; rw [← Classical.choose_spec (C_content_dvd p)]

@[simp]

中文:
定理 eq_C_content_mul_primPart
  条件: (p : R[X])
  结论: p = C p.content * p.primPart
  证明: by
  by_cases h : p = 0; · simp [h]
  rw [primPart]; rw [if_neg h]; rw [← Classical.choose_spec (C_content_dvd p)]

@[simp]

Depends on / 依赖: C_content_dvd, Classical, Classical.choose_spec, choose_spec, if_neg, primPart
-/
theorem eq_C_content_mul_primPart (p : R[X]) : p = C p.content * p.primPart := by
  by_cases h : p = 0; · simp [h]
  rw [primPart]; rw [if_neg h]; rw [← Classical.choose_spec (C_content_dvd p)]

@[simp]
/--
theorem `primPart_zero` / 定理 `primPart_zero`

English:
theorem primPart_zero
  statement: primPart (0 : R[X]) = 1
  proof: if_pos rfl

中文:
定理 primPart_zero
  结论: primPart (0 : R[X]) = 1
  证明: if_pos rfl

Depends on / 依赖: if_pos
-/
theorem primPart_zero : primPart (0 : R[X]) = 1 :=
  if_pos rfl

/--
theorem `isPrimitive_primPart` / 定理 `isPrimitive_primPart`

English:
theorem isPrimitive_primPart
  given: (p : R[X])
  statement: p.primPart.IsPrimitive
  proof: by
  by_cases h : p = 0; · simp [h]
  rw [← content_eq_zero_iff] at h
  rw [isPrimitive_iff_content_eq_one]; rw [← normalize_content]; rw [normalize_eq_one]
  refine isUnit_of_associated_mul (.symm ?_) h
  conv_lhs => rw [p.eq_C_content_mul_primPart]
  apply associated_content_C_mul

中文:
定理 isPrimitive_primPart
  条件: (p : R[X])
  结论: p.primPart.是Primitive
  证明: by
  by_cases h : p = 0; · simp [h]
  rw [← content_eq_zero_iff] at h
  rw [isPrimitive_iff_content_eq_one]; rw [← normalize_content]; rw [normalize_eq_one]
  refine isUnit_of_associated_mul (.symm ?_) h
  conv_lhs => rw [p.eq_C_content_mul_primPart]
  apply associated_content_C_mul

Depends on / 依赖: associated_content_C_mul, content_eq_zero_iff, conv_lhs, eq_C_content_mul_primPart, isPrimitive_iff_content_eq_one, isUnit_of_associated_mul, normalize_content, normalize_eq_one, p.eq_C_content_mul_primPart
-/
theorem isPrimitive_primPart (p : R[X]) : p.primPart.IsPrimitive := by
  by_cases h : p = 0; · simp [h]
  rw [← content_eq_zero_iff] at h
  rw [isPrimitive_iff_content_eq_one]; rw [← normalize_content]; rw [normalize_eq_one]
  refine isUnit_of_associated_mul (.symm ?_) h
  conv_lhs => rw [p.eq_C_content_mul_primPart]
  apply associated_content_C_mul

/--
theorem `content_primPart` / 定理 `content_primPart`

English:
theorem content_primPart
  given: (p : R[X])
  statement: p.primPart.content = 1
  proof: p.isPrimitive_primPart.content_eq_one

中文:
定理 content_primPart
  条件: (p : R[X])
  结论: p.primPart.content = 1
  证明: p.isPrimitive_primPart.content_eq_one

Depends on / 依赖: content_eq_one, isPrimitive_primPart, p.isPrimitive_primPart.content_eq_one
-/
theorem content_primPart (p : R[X]) : p.primPart.content = 1 :=
  p.isPrimitive_primPart.content_eq_one

/--
theorem `primPart_ne_zero` / 定理 `primPart_ne_zero`

English:
theorem primPart_ne_zero
  given: [Nontrivial R] (p : R[X])
  statement: p.primPart != 0
  proof: p.isPrimitive_primPart.ne_zero

中文:
定理 primPart_ne_zero
  条件: [非平凡 R] (p : R[X])
  结论: p.primPart != 0
  证明: p.isPrimitive_primPart.ne_zero

Depends on / 依赖: isPrimitive_primPart, ne_zero, p.isPrimitive_primPart.ne_zero
-/
theorem primPart_ne_zero [Nontrivial R] (p : R[X]) : p.primPart != 0 :=
  p.isPrimitive_primPart.ne_zero

/--
theorem `natDegree_primPart` / 定理 `natDegree_primPart`

English:
theorem natDegree_primPart
  given: (p : R[X])
  statement: p.primPart.natDegree = p.natDegree
  proof: by
  nontriviality R
  by_cases h : C p.content = 0
  · rw [C_eq_zero, content_eq_zero_iff] at h
    simp [h]
  conv_rhs =>
    rw [p.eq_C_content_mul_primPart]; rw [natDegree_mul h p.primPart_ne_zero]; rw [natDegree_C]; rw [zero_add]

@[simp]

中文:
定理 natDegree_primPart
  条件: (p : R[X])
  结论: p.primPart.natDegree = p.natDegree
  证明: by
  nontriviality R
  by_cases h : C p.content = 0
  · rw [C_eq_zero, content_eq_zero_iff] at h
    simp [h]
  conv_rhs =>
    rw [p.eq_C_content_mul_primPart]; rw [natDegree_mul h p.primPart_ne_zero]; rw [natDegree_C]; rw [zero_add]

@[simp]

Depends on / 依赖: C_eq_zero, content, content_eq_zero_iff, conv_rhs, eq_C_content_mul_primPart, natDegree_C, natDegree_mul, nontriviality, p.content, p.eq_C_content_mul_primPart, p.primPart_ne_zero, primPart_ne_zero, zero_add
-/
theorem natDegree_primPart (p : R[X]) : p.primPart.natDegree = p.natDegree := by
  nontriviality R
  by_cases h : C p.content = 0
  · rw [C_eq_zero, content_eq_zero_iff] at h
    simp [h]
  conv_rhs =>
    rw [p.eq_C_content_mul_primPart]; rw [natDegree_mul h p.primPart_ne_zero]; rw [natDegree_C]; rw [zero_add]

@[simp]
/--
theorem `IsPrimitive.primPart_eq` / 定理 `IsPrimitive.primPart_eq`

English:
theorem IsPrimitive.primPart_eq
  given: {p : R[X]} (hp : p.IsPrimitive)
  statement: p.primPart = p
  proof: by
  rw [← one_mul p.primPart]; rw [← C_1]; rw [← hp.content_eq_one]; rw [← p.eq_C_content_mul_primPart]

中文:
定理 是Primitive.primPart_eq
  条件: {p : R[X]} (hp : p.是Primitive)
  结论: p.primPart = p
  证明: by
  rw [← one_mul p.primPart]; rw [← C_1]; rw [← hp.content_eq_one]; rw [← p.eq_C_content_mul_primPart]

Depends on / 依赖: content_eq_one, eq_C_content_mul_primPart, hp.content_eq_one, one_mul, p.eq_C_content_mul_primPart, p.primPart, primPart
-/
theorem IsPrimitive.primPart_eq {p : R[X]} (hp : p.IsPrimitive) : p.primPart = p := by
  rw [← one_mul p.primPart]; rw [← C_1]; rw [← hp.content_eq_one]; rw [← p.eq_C_content_mul_primPart]

/--
theorem `isUnit_primPart_C` / 定理 `isUnit_primPart_C`

English:
theorem isUnit_primPart_C
  given: (r : R)
  statement: IsUnit (C r).primPart
  proof: by
  by_cases h0 : r = 0
  · simp [h0]
  unfold IsUnit
  refine
    ⟨⟨C ↑(normUnit r)⁻¹, C ↑(normUnit r), by rw [← map_mul, Units.inv_mul, C_1], by
        rw [← map_mul]; rw [Units.mul_inv]; rw [C_1]⟩,
      ?_⟩
  rw [← normalize_eq_zero]; rw [← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_rhs => rw [← content_C, ← (C r).eq_C_content_mul_primPart]
  simp only [normalize_apply, map_mul]
  rw [mul_assoc]; rw [← map_mul]; rw [Units.mul_inv]; rw [C_1]; rw [mul_one]

中文:
定理 isUnit_primPart_C
  条件: (r : R)
  结论: 是单位 (C r).primPart
  证明: by
  by_cases h0 : r = 0
  · simp [h0]
  unfold IsUnit
  refine
    ⟨⟨C ↑(normUnit r)⁻¹, C ↑(normUnit r), by rw [← map_mul, Units.inv_mul, C_1], by
        rw [← map_mul]; rw [Units.mul_inv]; rw [C_1]⟩,
      ?_⟩
  rw [← normalize_eq_zero]; rw [← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_rhs => rw [← content_C, ← (C r).eq_C_content_mul_primPart]
  simp only [normalize_apply, map_mul]
  rw [mul_assoc]; rw [← map_mul]; rw [Units.mul_inv]; rw [C_1]; rw [mul_one]

Depends on / 依赖: C_eq_zero, IsUnit, Units.inv_mul, Units.mul_inv, content_C, conv_rhs, eq_C_content_mul_primPart, inv_mul, map_mul, mul_assoc, mul_inv, mul_one, normUnit, normalize_apply, normalize_eq_zero
-/
theorem isUnit_primPart_C (r : R) : IsUnit (C r).primPart := by
  by_cases h0 : r = 0
  · simp [h0]
  unfold IsUnit
  refine
    ⟨⟨C ↑(normUnit r)⁻¹, C ↑(normUnit r), by rw [← map_mul, Units.inv_mul, C_1], by
        rw [← map_mul]; rw [Units.mul_inv]; rw [C_1]⟩,
      ?_⟩
  rw [← normalize_eq_zero]; rw [← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_rhs => rw [← content_C, ← (C r).eq_C_content_mul_primPart]
  simp only [normalize_apply, map_mul]
  rw [mul_assoc]; rw [← map_mul]; rw [Units.mul_inv]; rw [C_1]; rw [mul_one]

/--
theorem `primPart_dvd` / 定理 `primPart_dvd`

English:
theorem primPart_dvd
  given: (p : R[X])
  statement: p.primPart ∣ p
  proof: Dvd.intro_left (C p.content) p.eq_C_content_mul_primPart.symm

中文:
定理 primPart_dvd
  条件: (p : R[X])
  结论: p.primPart ∣ p
  证明: Dvd.intro_left (C p.content) p.eq_C_content_mul_primPart.symm

Depends on / 依赖: Dvd.intro_left, content, eq_C_content_mul_primPart, intro_left, p.content, p.eq_C_content_mul_primPart.symm
-/
theorem primPart_dvd (p : R[X]) : p.primPart ∣ p :=
  Dvd.intro_left (C p.content) p.eq_C_content_mul_primPart.symm

/--
theorem `aeval_primPart_eq_zero` / 定理 `aeval_primPart_eq_zero`

English:
theorem aeval_primPart_eq_zero
  statement: {S : Type*} [Ring S] [IsDomain S] [Algebra R S]
  proof: by
  nontriviality S
  rw [eq_C_content_mul_primPart p]; rw [map_mul]; rw [aeval_C] at hp
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hp
  have : IsDomain R := { Module.nontrivial R S with }
  rwa [(FaithfulSMul.algebraMap_injective R S).ne_iff' (map_zero _), Ne, content_eq_zero_iff]

中文:
定理 aeval_primPart_eq_zero
  结论: {S : 类型} [环 S] [是整环 S] [代数 R S]
  证明: by
  nontriviality S
  rw [eq_C_content_mul_primPart p]; rw [map_mul]; rw [aeval_C] at hp
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hp
  have : IsDomain R := { Module.nontrivial R S with }
  rwa [(FaithfulSMul.algebraMap_injective R S).ne_iff' (map_zero _), Ne, content_eq_zero_iff]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, IsDomain, Module, Module.nontrivial, aeval_C, algebraMap_injective, content_eq_zero_iff, eq_C_content_mul_primPart, eq_zero_of_ne_zero_of_mul_left_eq_zero, map_mul, map_zero, ne_iff, nontrivial, nontriviality
-/
theorem aeval_primPart_eq_zero {S : Type*} [Ring S] [IsDomain S] [Algebra R S]
    [Module.IsTorsionFree R S] {p : R[X]} {s : S} (hpzero : p != 0) (hp : aeval s p = 0) :
    aeval s p.primPart = 0 := by
  nontriviality S
  rw [eq_C_content_mul_primPart p]; rw [map_mul]; rw [aeval_C] at hp
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hp
  have : IsDomain R := { Module.nontrivial R S with }
  rwa [(FaithfulSMul.algebraMap_injective R S).ne_iff' (map_zero _), Ne, content_eq_zero_iff]

/--
theorem `eval₂_primPart_eq_zero` / 定理 `eval₂_primPart_eq_zero`

English:
theorem eval₂_primPart_eq_zero
  statement: {S : Type*} [CommSemiring S] [IsDomain S] {f : R ->+* S}
  proof: by
  rw [eq_C_content_mul_primPart p]; rw [eval₂_mul]; rw [eval₂_C] at hp
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hp
  rwa [hinj.ne_iff' (map_zero _), Ne, content_eq_zero_iff]

中文:
定理 eval₂_primPart_eq_zero
  结论: {S : 类型} [交换半环 S] [是整环 S] {f : R ->+* S}
  证明: by
  rw [eq_C_content_mul_primPart p]; rw [eval₂_mul]; rw [eval₂_C] at hp
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hp
  rwa [hinj.ne_iff' (map_zero _), Ne, content_eq_zero_iff]

Depends on / 依赖: content_eq_zero_iff, eq_C_content_mul_primPart, eq_zero_of_ne_zero_of_mul_left_eq_zero, hinj.ne_iff, map_zero, ne_iff
-/
theorem eval₂_primPart_eq_zero {S : Type*} [CommSemiring S] [IsDomain S] {f : R ->+* S}
    (hinj : Function.Injective f) {p : R[X]} {s : S} (hpzero : p != 0) (hp : eval₂ f s p = 0) :
    eval₂ f s p.primPart = 0 := by
  rw [eq_C_content_mul_primPart p]; rw [eval₂_mul]; rw [eval₂_C] at hp
  refine eq_zero_of_ne_zero_of_mul_left_eq_zero ?_ hp
  rwa [hinj.ne_iff' (map_zero _), Ne, content_eq_zero_iff]

end PrimPart

/--
theorem `gcd_content_eq_of_dvd_sub` / 定理 `gcd_content_eq_of_dvd_sub`

English:
theorem gcd_content_eq_of_dvd_sub
  given: {a : R} {p q : R[X]} (h : C a ∣ p - q)
  proof: by
  rw [content_eq_gcd_range_of_lt p (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _))]
  rw [content_eq_gcd_range_of_lt q (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _))]
  apply Finset.gcd_eq_of_dvd_sub
  intro x _
  obtain ⟨w, hw⟩ := h
  use w.coeff x
  rw [← coeff_sub]; rw [hw]; rw [coeff_C_mul]

中文:
定理 gcd_content_eq_of_dvd_sub
  条件: {a : R} {p q : R[X]} (h : C a ∣ p - q)
  证明: by
  rw [content_eq_gcd_range_of_lt p (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _))]
  rw [content_eq_gcd_range_of_lt q (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _))]
  apply Finset.gcd_eq_of_dvd_sub
  intro x _
  obtain ⟨w, hw⟩ := h
  use w.coeff x
  rw [← coeff_sub]; rw [hw]; rw [coeff_C_mul]

Depends on / 依赖: Finset, Finset.gcd_eq_of_dvd_sub, Nat.lt_succ_self, coeff_C_mul, coeff_sub, content_eq_gcd_range_of_lt, gcd_eq_of_dvd_sub, le_max_left, le_max_right, lt_of_le_of_lt, lt_succ_self, natDegree, p.natDegree, q.natDegree, w.coeff
-/
theorem gcd_content_eq_of_dvd_sub {a : R} {p q : R[X]} (h : C a ∣ p - q) :
    gcd a p.content = gcd a q.content := by
  rw [content_eq_gcd_range_of_lt p (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _))]
  rw [content_eq_gcd_range_of_lt q (max p.natDegree q.natDegree).succ
      (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_succ_self _))]
  apply Finset.gcd_eq_of_dvd_sub
  intro x _
  obtain ⟨w, hw⟩ := h
  use w.coeff x
  rw [← coeff_sub]; rw [hw]; rw [coeff_C_mul]

/--
theorem `content_mul_aux` / 定理 `content_mul_aux`

English:
theorem content_mul_aux
  given: {p q : R[X]}
  proof: by
  rw [gcd_comm (content _) _]; rw [gcd_comm (content _) _]
  apply gcd_content_eq_of_dvd_sub
  rw [← self_sub_C_mul_X_pow]; rw [← self_sub_C_mul_X_pow]; rw [sub_mul]; rw [sub_sub]; rw [add_comm]; rw [sub_add]; rw [sub_sub_cancel]; rw [leadingCoeff_mul]; rw [map_mul]; rw [mul_assoc]; rw [mul_assoc]
  apply dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)

中文:
定理 content_mul_aux
  条件: {p q : R[X]}
  证明: by
  rw [gcd_comm (content _) _]; rw [gcd_comm (content _) _]
  apply gcd_content_eq_of_dvd_sub
  rw [← self_sub_C_mul_X_pow]; rw [← self_sub_C_mul_X_pow]; rw [sub_mul]; rw [sub_sub]; rw [add_comm]; rw [sub_add]; rw [sub_sub_cancel]; rw [leadingCoeff_mul]; rw [map_mul]; rw [mul_assoc]; rw [mul_assoc]
  apply dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)

Depends on / 依赖: Dvd.intro, add_comm, content, dvd_sub, gcd_comm, gcd_content_eq_of_dvd_sub, leadingCoeff_mul, map_mul, mul_assoc, self_sub_C_mul_X_pow, sub_add, sub_mul, sub_sub, sub_sub_cancel
-/
theorem content_mul_aux {p q : R[X]} :
    gcd (p * q).eraseLead.content p.leadingCoeff =
      gcd (p.eraseLead * q).content p.leadingCoeff := by
  rw [gcd_comm (content _) _]; rw [gcd_comm (content _) _]
  apply gcd_content_eq_of_dvd_sub
  rw [← self_sub_C_mul_X_pow]; rw [← self_sub_C_mul_X_pow]; rw [sub_mul]; rw [sub_sub]; rw [add_comm]; rw [sub_add]; rw [sub_sub_cancel]; rw [leadingCoeff_mul]; rw [map_mul]; rw [mul_assoc]; rw [mul_assoc]
  apply dvd_sub (Dvd.intro _ rfl) (Dvd.intro _ rfl)

/--
theorem `associated_content_mul` / 定理 `associated_content_mul`

English:
theorem associated_content_mul
  given: (p q : R[X])
  proof: by
  nontriviality R
  classical
    suffices h : forall (n : Nat) (p q : R[X]),
        (p * q).degree < n -> Associated ((p * q).content) (p.content * q.content) by
      apply h
      apply lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
    intro n p q hpq
    induction n generalizing p q with
    | zero =>
      rw [Nat.cast_zero]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot]; rw [mul_eq_zero] at hpq
      rcases hpq with (rfl | rfl) <;> simp
    | succ n ih => ?_
    by_cases p0 : p = 0
    · simp [p0]
    by_cases q0 : q = 0
    · simp [q0]
    rw [degree_eq_natDegree (mul_ne_zero p0 q0)]; rw [Nat.cast_lt]; rw [Nat.lt_succ_iff_lt_or_eq]; rw [← Nat.cast_lt (α := WithBot Nat)]; rw [← degree_eq_natDegree (mul_ne_zero p0 q0)]; rw [natDegree_mul p0 q0] at hpq
    rcases hpq with (hlt | heq)
    · apply ih _ _ hlt
    rw [← p.natDegree_primPart]; rw [← q.natDegree_primPart]; rw [← Nat.cast_inj (R := WithBot Nat)]; rw [Nat.cast_add]; rw [← degree_eq_natDegree p.primPart_ne_zero]; rw [← degree_eq_natDegree q.primPart_ne_zero] at heq
    rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
    suffices h : (q.primPart * p.primPart).content = 1 by
      grw [mul_assoc, associated_content_C_mul, associated_content_C_mul, mul_comm p.primPart,
        mul_assoc, associated_content_C_mul, associated_content_C_mul, h, mul_one,
        content_primPart, content_primPart, mul_one, mul_one]
    rw [← normalize_content]; rw [normalize_eq_one]; rw [isUnit_iff_dvd_one]; rw [content_eq_gcd_leadingCoeff_content_eraseLead]; rw [leadingCoeff_mul]; rw [gcd_comm]
    apply (gcd_mul_dvd_mul_gcd _ _ _).trans
    rw [content_mul_aux]; rw [(ih ..).gcd_eq_left]; rw [content_primPart]; rw [mul_one]; rw [gcd_comm]; rw [←
      content_eq_gcd_leadingCoeff_content_eraseLead]; rw [content_primPart]; rw [one_mul]; rw [mul_comm q.primPart]; rw [content_mul_aux]; rw [(ih ..).gcd_eq_left]; rw [content_primPart]; rw [mul_one]; rw [gcd_comm]; rw [← content_eq_gcd_leadingCoeff_content_eraseLead]; rw [content_primPart]
    · rw [← heq, degree_mul, WithBot.add_lt_add_iff_right]
      · apply degree_erase_lt p.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply q.primPart_ne_zero
    · rw [mul_comm, ← heq, degree_mul, WithBot.add_lt_add_iff_left]
      · apply degree_erase_lt q.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply p.primPart_ne_zero

@[simp]

中文:
定理 associated_content_mul
  条件: (p q : R[X])
  证明: by
  nontriviality R
  classical
    suffices h : forall (n : Nat) (p q : R[X]),
        (p * q).degree < n -> Associated ((p * q).content) (p.content * q.content) by
      apply h
      apply lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
    intro n p q hpq
    induction n generalizing p q with
    | zero =>
      rw [Nat.cast_zero]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot]; rw [mul_eq_zero] at hpq
      rcases hpq with (rfl | rfl) <;> simp
    | succ n ih => ?_
    by_cases p0 : p = 0
    · simp [p0]
    by_cases q0 : q = 0
    · simp [q0]
    rw [degree_eq_natDegree (mul_ne_zero p0 q0)]; rw [Nat.cast_lt]; rw [Nat.lt_succ_iff_lt_or_eq]; rw [← Nat.cast_lt (α := WithBot Nat)]; rw [← degree_eq_natDegree (mul_ne_zero p0 q0)]; rw [natDegree_mul p0 q0] at hpq
    rcases hpq with (hlt | heq)
    · apply ih _ _ hlt
    rw [← p.natDegree_primPart]; rw [← q.natDegree_primPart]; rw [← Nat.cast_inj (R := WithBot Nat)]; rw [Nat.cast_add]; rw [← degree_eq_natDegree p.primPart_ne_zero]; rw [← degree_eq_natDegree q.primPart_ne_zero] at heq
    rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
    suffices h : (q.primPart * p.primPart).content = 1 by
      grw [mul_assoc, associated_content_C_mul, associated_content_C_mul, mul_comm p.primPart,
        mul_assoc, associated_content_C_mul, associated_content_C_mul, h, mul_one,
        content_primPart, content_primPart, mul_one, mul_one]
    rw [← normalize_content]; rw [normalize_eq_one]; rw [isUnit_iff_dvd_one]; rw [content_eq_gcd_leadingCoeff_content_eraseLead]; rw [leadingCoeff_mul]; rw [gcd_comm]
    apply (gcd_mul_dvd_mul_gcd _ _ _).trans
    rw [content_mul_aux]; rw [(ih ..).gcd_eq_left]; rw [content_primPart]; rw [mul_one]; rw [gcd_comm]; rw [←
      content_eq_gcd_leadingCoeff_content_eraseLead]; rw [content_primPart]; rw [one_mul]; rw [mul_comm q.primPart]; rw [content_mul_aux]; rw [(ih ..).gcd_eq_left]; rw [content_primPart]; rw [mul_one]; rw [gcd_comm]; rw [← content_eq_gcd_leadingCoeff_content_eraseLead]; rw [content_primPart]
    · rw [← heq, degree_mul, WithBot.add_lt_add_iff_right]
      · apply degree_erase_lt p.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply q.primPart_ne_zero
    · rw [mul_comm, ← heq, degree_mul, WithBot.add_lt_add_iff_left]
      · apply degree_erase_lt q.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply p.primPart_ne_zero

@[simp]

Depends on / 依赖: Associated, Nat.WithBot.lt_zero_iff, Nat.cast_zero, Nat.lt_succ_self, WithBot, WithBot.coe_lt_coe, cast_zero, classical, coe_lt_coe, content, degree, degree_eq_bot, degree_le_natDegree, generalizing, lt_of_le_of_lt, lt_succ_self, lt_zero_iff, mul_eq_zero, nontriviality, p.content
-/
theorem associated_content_mul (p q : R[X]) :
    Associated ((p * q).content) (p.content * q.content) := by
  nontriviality R
  classical
    suffices h : forall (n : Nat) (p q : R[X]),
        (p * q).degree < n -> Associated ((p * q).content) (p.content * q.content) by
      apply h
      apply lt_of_le_of_lt degree_le_natDegree (WithBot.coe_lt_coe.2 (Nat.lt_succ_self _))
    intro n p q hpq
    induction n generalizing p q with
    | zero =>
      rw [Nat.cast_zero]; rw [Nat.WithBot.lt_zero_iff]; rw [degree_eq_bot]; rw [mul_eq_zero] at hpq
      rcases hpq with (rfl | rfl) <;> simp
    | succ n ih => ?_
    by_cases p0 : p = 0
    · simp [p0]
    by_cases q0 : q = 0
    · simp [q0]
    rw [degree_eq_natDegree (mul_ne_zero p0 q0)]; rw [Nat.cast_lt]; rw [Nat.lt_succ_iff_lt_or_eq]; rw [← Nat.cast_lt (α := WithBot Nat)]; rw [← degree_eq_natDegree (mul_ne_zero p0 q0)]; rw [natDegree_mul p0 q0] at hpq
    rcases hpq with (hlt | heq)
    · apply ih _ _ hlt
    rw [← p.natDegree_primPart]; rw [← q.natDegree_primPart]; rw [← Nat.cast_inj (R := WithBot Nat)]; rw [Nat.cast_add]; rw [← degree_eq_natDegree p.primPart_ne_zero]; rw [← degree_eq_natDegree q.primPart_ne_zero] at heq
    rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
    suffices h : (q.primPart * p.primPart).content = 1 by
      grw [mul_assoc, associated_content_C_mul, associated_content_C_mul, mul_comm p.primPart,
        mul_assoc, associated_content_C_mul, associated_content_C_mul, h, mul_one,
        content_primPart, content_primPart, mul_one, mul_one]
    rw [← normalize_content]; rw [normalize_eq_one]; rw [isUnit_iff_dvd_one]; rw [content_eq_gcd_leadingCoeff_content_eraseLead]; rw [leadingCoeff_mul]; rw [gcd_comm]
    apply (gcd_mul_dvd_mul_gcd _ _ _).trans
    rw [content_mul_aux]; rw [(ih ..).gcd_eq_left]; rw [content_primPart]; rw [mul_one]; rw [gcd_comm]; rw [←
      content_eq_gcd_leadingCoeff_content_eraseLead]; rw [content_primPart]; rw [one_mul]; rw [mul_comm q.primPart]; rw [content_mul_aux]; rw [(ih ..).gcd_eq_left]; rw [content_primPart]; rw [mul_one]; rw [gcd_comm]; rw [← content_eq_gcd_leadingCoeff_content_eraseLead]; rw [content_primPart]
    · rw [← heq, degree_mul, WithBot.add_lt_add_iff_right]
      · apply degree_erase_lt p.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply q.primPart_ne_zero
    · rw [mul_comm, ← heq, degree_mul, WithBot.add_lt_add_iff_left]
      · apply degree_erase_lt q.primPart_ne_zero
      · rw [Ne, degree_eq_bot]
        apply p.primPart_ne_zero

@[simp]
/--
theorem `content_mul` / 定理 `content_mul`

English:
theorem content_mul
  given: {R} [CommRing R] [StrongNormalizedGCDMonoid R] {p q : R[X]}
  proof: (associated_content_mul ..).eq_of_normalized normalize_content by simp [normalize_content]

中文:
定理 content_mul
  条件: {R} [交换环 R] [StrongNormalizedGCD幺半群 R] {p q : R[X]}
  证明: (associated_content_mul ..).eq_of_normalized normalize_content by simp [normalize_content]

Depends on / 依赖: associated_content_mul, eq_of_normalized, normalize_content
-/
theorem content_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] {p q : R[X]} :
    (p * q).content = p.content * q.content :=
(associated_content_mul ..).eq_of_normalized normalize_content by simp [normalize_content]

/--
theorem `IsPrimitive.mul` / 定理 `IsPrimitive.mul`

English:
theorem IsPrimitive.mul
  given: {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive)
  proof: by
  rw [isPrimitive_iff_content_eq_one]; rw [← normalize_content]; rw [normalize_eq_one]
  refine (associated_content_mul p q).symm.isUnit ?_
  simp_rw [hp.content_eq_one, hq.content_eq_one, mul_one, isUnit_one]

中文:
定理 是Primitive.mul
  条件: {p q : R[X]} (hp : p.是Primitive) (hq : q.是Primitive)
  证明: by
  rw [isPrimitive_iff_content_eq_one]; rw [← normalize_content]; rw [normalize_eq_one]
  refine (associated_content_mul p q).symm.isUnit ?_
  simp_rw [hp.content_eq_one, hq.content_eq_one, mul_one, isUnit_one]

Depends on / 依赖: associated_content_mul, content_eq_one, hp.content_eq_one, hq.content_eq_one, isPrimitive_iff_content_eq_one, isUnit, isUnit_one, mul_one, normalize_content, normalize_eq_one, simp_rw, symm.isUnit
-/
theorem IsPrimitive.mul {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    (p * q).IsPrimitive := by
  rw [isPrimitive_iff_content_eq_one]; rw [← normalize_content]; rw [normalize_eq_one]
  refine (associated_content_mul p q).symm.isUnit ?_
  simp_rw [hp.content_eq_one, hq.content_eq_one, mul_one, isUnit_one]

/--
theorem `associated_primPart_mul` / 定理 `associated_primPart_mul`

English:
theorem associated_primPart_mul
  given: {p q : R[X]} (h0 : p * q != 0)
  proof: by
  rw [Ne]; rw [← content_eq_zero_iff]; rw [← C_eq_zero] at h0
  refine .of_mul_left ?_ .rfl h0
  conv_lhs => rw [← (p * q).eq_C_content_mul_primPart,
    p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart, mul_mul_mul_comm, ← C_mul]
  gcongr
  exact (associated_content_mul ..).symm.map _

@[simp]

中文:
定理 associated_primPart_mul
  条件: {p q : R[X]} (h0 : p * q != 0)
  证明: by
  rw [Ne]; rw [← content_eq_zero_iff]; rw [← C_eq_zero] at h0
  refine .of_mul_left ?_ .rfl h0
  conv_lhs => rw [← (p * q).eq_C_content_mul_primPart,
    p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart, mul_mul_mul_comm, ← C_mul]
  gcongr
  exact (associated_content_mul ..).symm.map _

@[simp]

Depends on / 依赖: C_eq_zero, C_mul, associated_content_mul, content_eq_zero_iff, conv_lhs, eq_C_content_mul_primPart, mul_mul_mul_comm, of_mul_left, p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart, symm.map
-/
theorem associated_primPart_mul {p q : R[X]} (h0 : p * q != 0) :
    Associated (p * q).primPart (p.primPart * q.primPart) := by
  rw [Ne]; rw [← content_eq_zero_iff]; rw [← C_eq_zero] at h0
  refine .of_mul_left ?_ .rfl h0
  conv_lhs => rw [← (p * q).eq_C_content_mul_primPart,
    p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart, mul_mul_mul_comm, ← C_mul]
  gcongr
  exact (associated_content_mul ..).symm.map _

@[simp]
/--
theorem `primPart_mul` / 定理 `primPart_mul`

English:
theorem primPart_mul
  given: {R} [CommRing R] [StrongNormalizedGCDMonoid R] {p q : R[X]} (h0 : p * q != 0)
  proof: by
  rw [Ne]; rw [← content_eq_zero_iff]; rw [← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_lhs =>
    rw [← (p * q).eq_C_content_mul_primPart]; rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
  rw [content_mul]; rw [map_mul]
  ring

中文:
定理 primPart_mul
  条件: {R} [交换环 R] [StrongNormalizedGCD幺半群 R] {p q : R[X]} (h0 : p * q != 0)
  证明: by
  rw [Ne]; rw [← content_eq_zero_iff]; rw [← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_lhs =>
    rw [← (p * q).eq_C_content_mul_primPart]; rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
  rw [content_mul]; rw [map_mul]
  ring

Depends on / 依赖: C_eq_zero, content_eq_zero_iff, content_mul, conv_lhs, eq_C_content_mul_primPart, map_mul, p.eq_C_content_mul_primPart, q.eq_C_content_mul_primPart
-/
theorem primPart_mul {R} [CommRing R] [StrongNormalizedGCDMonoid R] {p q : R[X]} (h0 : p * q != 0) :
    (p * q).primPart = p.primPart * q.primPart := by
  rw [Ne]; rw [← content_eq_zero_iff]; rw [← C_eq_zero] at h0
  apply mul_left_cancel₀ h0
  conv_lhs =>
    rw [← (p * q).eq_C_content_mul_primPart]; rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
  rw [content_mul]; rw [map_mul]
  ring

/--
theorem `IsPrimitive.dvd_primPart_iff_dvd` / 定理 `IsPrimitive.dvd_primPart_iff_dvd`

English:
theorem IsPrimitive.dvd_primPart_iff_dvd
  given: {p q : R[X]} (hp : p.IsPrimitive) (hq : q != 0)
  proof: by
  refine ⟨fun h => h.trans (Dvd.intro_left _ q.eq_C_content_mul_primPart.symm), fun h => ?_⟩
  rcases h with ⟨r, rfl⟩
  exact .trans (by simp [hp.primPart_eq]) (associated_primPart_mul hq).symm.dvd

中文:
定理 是Primitive.dvd_primPart_iff_dvd
  条件: {p q : R[X]} (hp : p.是Primitive) (hq : q != 0)
  证明: by
  refine ⟨fun h => h.trans (Dvd.intro_left _ q.eq_C_content_mul_primPart.symm), fun h => ?_⟩
  rcases h with ⟨r, rfl⟩
  exact .trans (by simp [hp.primPart_eq]) (associated_primPart_mul hq).symm.dvd

Depends on / 依赖: Dvd.intro_left, associated_primPart_mul, eq_C_content_mul_primPart, h.trans, hp.primPart_eq, intro_left, primPart_eq, q.eq_C_content_mul_primPart.symm, symm.dvd
-/
theorem IsPrimitive.dvd_primPart_iff_dvd {p q : R[X]} (hp : p.IsPrimitive) (hq : q != 0) :
    p ∣ q.primPart ↔ p ∣ q := by
  refine ⟨fun h => h.trans (Dvd.intro_left _ q.eq_C_content_mul_primPart.symm), fun h => ?_⟩
  rcases h with ⟨r, rfl⟩
  exact .trans (by simp [hp.primPart_eq]) (associated_primPart_mul hq).symm.dvd

/--
theorem `exists_primitive_lcm_of_isPrimitive` / 定理 `exists_primitive_lcm_of_isPrimitive`

English:
theorem exists_primitive_lcm_of_isPrimitive
  given: {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive)
  proof: by
  classical
    have h : exists (n : Nat) (r : R[X]), r.natDegree = n ∧ r.IsPrimitive ∧ p ∣ r ∧ q ∣ r :=
      ⟨(p * q).natDegree, p * q, rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩
    rcases Nat.find_spec h with ⟨r, rdeg, rprim, pr, qr⟩
    refine ⟨r, rprim, fun s => ⟨?_, fun rs => ⟨pr.trans rs, qr.trans rs⟩⟩⟩
    suffices hs : forall (n : Nat) (s : R[X]), s.natDegree = n -> p ∣ s ∧ q ∣ s -> r ∣ s from
      hs s.natDegree s rfl
    clear s
    by_contra! con
    rcases Nat.find_spec con with ⟨s, sdeg, ⟨ps, qs⟩, rs⟩
    have s0 : s != 0 := by
      contrapose rs
      simp [rs]
    have hs :=
      Nat.find_min' h
        ⟨_, s.natDegree_primPart, s.isPrimitive_primPart, (hp.dvd_primPart_iff_dvd s0).2 ps,
          (hq.dvd_primPart_iff_dvd s0).2 qs⟩
    rw [← rdeg] at hs
    by_cases! sC : s.natDegree <= 0
    · rw [eq_C_of_natDegree_le_zero (le_trans hs sC), isPrimitive_iff_content_eq_one, content_C,
        normalize_eq_one] at rprim
      rw [eq_C_of_natDegree_le_zero (le_trans hs sC)]; rw [← dvd_content_iff_C_dvd] at rs
      apply rs rprim.dvd
    have hcancel := natDegree_cancelLeads_lt_of_natDegree_le_natDegree hs sC
    rw [sdeg] at hcancel
    apply Nat.find_min con hcancel
    refine
      ⟨_, rfl, ⟨dvd_cancelLeads_of_dvd_of_dvd pr ps, dvd_cancelLeads_of_dvd_of_dvd qr qs⟩,
        fun rcs => rs ?_⟩
    rw [← rprim.dvd_primPart_iff_dvd s0]
    rw [cancelLeads]; rw [tsub_eq_zero_iff_le.mpr hs]; rw [pow_zero]; rw [mul_one] at rcs
    have h :=
      dvd_add rcs (Dvd.intro_left (C (leadingCoeff s) * X ^ (natDegree s - natDegree r)) rfl)
    nontriviality R
    have hC0 := rprim.ne_zero
    rw [Ne]; rw [← leadingCoeff_eq_zero]; rw [← C_eq_zero] at hC0
    rw [sub_add_cancel]; rw [← rprim.dvd_primPart_iff_dvd (mul_ne_zero hC0 s0)] at h
    refine h.trans (Associated.dvd ?_)
    grw [associated_primPart_mul (mul_ne_zero hC0 s0)]
    exact associated_unit_mul_left _ _ (isUnit_primPart_C _)

中文:
定理 存在_primitive_lcm_of_isPrimitive
  条件: {p q : R[X]} (hp : p.是Primitive) (hq : q.是Primitive)
  证明: by
  classical
    have h : exists (n : Nat) (r : R[X]), r.natDegree = n ∧ r.IsPrimitive ∧ p ∣ r ∧ q ∣ r :=
      ⟨(p * q).natDegree, p * q, rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩
    rcases Nat.find_spec h with ⟨r, rdeg, rprim, pr, qr⟩
    refine ⟨r, rprim, fun s => ⟨?_, fun rs => ⟨pr.trans rs, qr.trans rs⟩⟩⟩
    suffices hs : forall (n : Nat) (s : R[X]), s.natDegree = n -> p ∣ s ∧ q ∣ s -> r ∣ s from
      hs s.natDegree s rfl
    clear s
    by_contra! con
    rcases Nat.find_spec con with ⟨s, sdeg, ⟨ps, qs⟩, rs⟩
    have s0 : s != 0 := by
      contrapose rs
      simp [rs]
    have hs :=
      Nat.find_min' h
        ⟨_, s.natDegree_primPart, s.isPrimitive_primPart, (hp.dvd_primPart_iff_dvd s0).2 ps,
          (hq.dvd_primPart_iff_dvd s0).2 qs⟩
    rw [← rdeg] at hs
    by_cases! sC : s.natDegree <= 0
    · rw [eq_C_of_natDegree_le_zero (le_trans hs sC), isPrimitive_iff_content_eq_one, content_C,
        normalize_eq_one] at rprim
      rw [eq_C_of_natDegree_le_zero (le_trans hs sC)]; rw [← dvd_content_iff_C_dvd] at rs
      apply rs rprim.dvd
    have hcancel := natDegree_cancelLeads_lt_of_natDegree_le_natDegree hs sC
    rw [sdeg] at hcancel
    apply Nat.find_min con hcancel
    refine
      ⟨_, rfl, ⟨dvd_cancelLeads_of_dvd_of_dvd pr ps, dvd_cancelLeads_of_dvd_of_dvd qr qs⟩,
        fun rcs => rs ?_⟩
    rw [← rprim.dvd_primPart_iff_dvd s0]
    rw [cancelLeads]; rw [tsub_eq_zero_iff_le.mpr hs]; rw [pow_zero]; rw [mul_one] at rcs
    have h :=
      dvd_add rcs (Dvd.intro_left (C (leadingCoeff s) * X ^ (natDegree s - natDegree r)) rfl)
    nontriviality R
    have hC0 := rprim.ne_zero
    rw [Ne]; rw [← leadingCoeff_eq_zero]; rw [← C_eq_zero] at hC0
    rw [sub_add_cancel]; rw [← rprim.dvd_primPart_iff_dvd (mul_ne_zero hC0 s0)] at h
    refine h.trans (Associated.dvd ?_)
    grw [associated_primPart_mul (mul_ne_zero hC0 s0)]
    exact associated_unit_mul_left _ _ (isUnit_primPart_C _)

Depends on / 依赖: IsPrimitive, Nat.find_spec, classical, dvd_mul_left, dvd_mul_right, find_spec, hp.mul, natDegree, pr.trans, qr.trans, r.IsPrimitive, r.natDegree, s.natDegree
-/
theorem exists_primitive_lcm_of_isPrimitive {p q : R[X]} (hp : p.IsPrimitive) (hq : q.IsPrimitive) :
    exists r : R[X], r.IsPrimitive ∧ forall s : R[X], p ∣ s ∧ q ∣ s ↔ r ∣ s := by
  classical
    have h : exists (n : Nat) (r : R[X]), r.natDegree = n ∧ r.IsPrimitive ∧ p ∣ r ∧ q ∣ r :=
      ⟨(p * q).natDegree, p * q, rfl, hp.mul hq, dvd_mul_right _ _, dvd_mul_left _ _⟩
    rcases Nat.find_spec h with ⟨r, rdeg, rprim, pr, qr⟩
    refine ⟨r, rprim, fun s => ⟨?_, fun rs => ⟨pr.trans rs, qr.trans rs⟩⟩⟩
    suffices hs : forall (n : Nat) (s : R[X]), s.natDegree = n -> p ∣ s ∧ q ∣ s -> r ∣ s from
      hs s.natDegree s rfl
    clear s
    by_contra! con
    rcases Nat.find_spec con with ⟨s, sdeg, ⟨ps, qs⟩, rs⟩
    have s0 : s != 0 := by
      contrapose rs
      simp [rs]
    have hs :=
      Nat.find_min' h
        ⟨_, s.natDegree_primPart, s.isPrimitive_primPart, (hp.dvd_primPart_iff_dvd s0).2 ps,
          (hq.dvd_primPart_iff_dvd s0).2 qs⟩
    rw [← rdeg] at hs
    by_cases! sC : s.natDegree <= 0
    · rw [eq_C_of_natDegree_le_zero (le_trans hs sC), isPrimitive_iff_content_eq_one, content_C,
        normalize_eq_one] at rprim
      rw [eq_C_of_natDegree_le_zero (le_trans hs sC)]; rw [← dvd_content_iff_C_dvd] at rs
      apply rs rprim.dvd
    have hcancel := natDegree_cancelLeads_lt_of_natDegree_le_natDegree hs sC
    rw [sdeg] at hcancel
    apply Nat.find_min con hcancel
    refine
      ⟨_, rfl, ⟨dvd_cancelLeads_of_dvd_of_dvd pr ps, dvd_cancelLeads_of_dvd_of_dvd qr qs⟩,
        fun rcs => rs ?_⟩
    rw [← rprim.dvd_primPart_iff_dvd s0]
    rw [cancelLeads]; rw [tsub_eq_zero_iff_le.mpr hs]; rw [pow_zero]; rw [mul_one] at rcs
    have h :=
      dvd_add rcs (Dvd.intro_left (C (leadingCoeff s) * X ^ (natDegree s - natDegree r)) rfl)
    nontriviality R
    have hC0 := rprim.ne_zero
    rw [Ne]; rw [← leadingCoeff_eq_zero]; rw [← C_eq_zero] at hC0
    rw [sub_add_cancel]; rw [← rprim.dvd_primPart_iff_dvd (mul_ne_zero hC0 s0)] at h
    refine h.trans (Associated.dvd ?_)
    grw [associated_primPart_mul (mul_ne_zero hC0 s0)]
    exact associated_unit_mul_left _ _ (isUnit_primPart_C _)

/--
theorem `dvd_iff_content_dvd_content_and_primPart_dvd_primPart` / 定理 `dvd_iff_content_dvd_content_and_primPart_dvd_primPart`

English:
theorem dvd_iff_content_dvd_content_and_primPart_dvd_primPart
  given: {p q : R[X]} (hq : q != 0)
  proof: by
  constructor
  · rintro ⟨r, rfl⟩
    rw [(associated_content_mul ..).dvd_iff_dvd_right]; rw [p.isPrimitive_primPart.dvd_primPart_iff_dvd hq]
    exact ⟨dvd_mul_right .., dvd_mul_of_dvd_left p.primPart_dvd _⟩
  · rintro ⟨h₁, h₂⟩
    rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
    gcongr

中文:
定理 dvd_iff_content_dvd_content_and_primPart_dvd_primPart
  条件: {p q : R[X]} (hq : q != 0)
  证明: by
  constructor
  · rintro ⟨r, rfl⟩
    rw [(associated_content_mul ..).dvd_iff_dvd_right]; rw [p.isPrimitive_primPart.dvd_primPart_iff_dvd hq]
    exact ⟨dvd_mul_right .., dvd_mul_of_dvd_left p.primPart_dvd _⟩
  · rintro ⟨h₁, h₂⟩
    rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
    gcongr

Depends on / 依赖: associated_content_mul, dvd_iff_dvd_right, dvd_mul_of_dvd_left, dvd_mul_right, dvd_primPart_iff_dvd, eq_C_content_mul_primPart, isPrimitive_primPart, p.eq_C_content_mul_primPart, p.isPrimitive_primPart.dvd_primPart_iff_dvd, p.primPart_dvd, primPart_dvd, q.eq_C_content_mul_primPart
-/
theorem dvd_iff_content_dvd_content_and_primPart_dvd_primPart {p q : R[X]} (hq : q != 0) :
    p ∣ q ↔ p.content ∣ q.content ∧ p.primPart ∣ q.primPart := by
  constructor
  · rintro ⟨r, rfl⟩
    rw [(associated_content_mul ..).dvd_iff_dvd_right]; rw [p.isPrimitive_primPart.dvd_primPart_iff_dvd hq]
    exact ⟨dvd_mul_right .., dvd_mul_of_dvd_left p.primPart_dvd _⟩
  · rintro ⟨h₁, h₂⟩
    rw [p.eq_C_content_mul_primPart]; rw [q.eq_C_content_mul_primPart]
    gcongr

/--
Instance `normalizedGcdMonoid` / 实例 `normalizedGcdMonoid`

English:
instance normalizedGcdMonoid
  signature: : NormalizedGCDMonoid R[X]
  body: letI := Classical.decEq R
  normalizedGCDMonoidOfExistsLCM fun p q => by
    rcases exists_primitive_lcm_of_isPrimitive p.isPrimitive_primPart
        q.isPrimitive_primPart with
      ⟨r, rprim, hr⟩
    refine ⟨C (lcm p.content q.content) * r, fun s => ?_⟩
    by_cases hs : s = 0
    · simp [hs]
    by_cases hpq : C (lcm p.content q.content) = 0
    · rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq
      rcases hpq with (hpq | hpq) <;> simp [hpq, hs]
    iterate 3 rw [dvd_iff_content_dvd_content_and_primPart_dvd_primPart hs]
    nontriviality R
    rw [(associated_content_mul ..).dvd_iff_dvd_left]; rw [rprim.content_eq_one]; rw [mul_one]; rw [content_C]; rw [(associated_primPart_mul (mul_ne_zero hpq rprim.ne_zero)).dvd_iff_dvd_left]; rw [rprim.primPart_eq]; rw [normalize_lcm]; rw [lcm_dvd_iff]; rw [(isUnit_primPart_C (lcm p.content q.content)).mul_left_dvd]; rw [← hr s.primPart]
    tauto

中文:
实例 normalizedGcdMonoid
  签名: : 正规化最大公约数幺半群 R[X]
  定义体: letI := Classical.decEq R
  normalizedGCDMonoidOfExistsLCM fun p q => by
    rcases exists_primitive_lcm_of_isPrimitive p.isPrimitive_primPart
        q.isPrimitive_primPart with
      ⟨r, rprim, hr⟩
    refine ⟨C (lcm p.content q.content) * r, fun s => ?_⟩
    by_cases hs : s = 0
    · simp [hs]
    by_cases hpq : C (lcm p.content q.content) = 0
    · rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq
      rcases hpq with (hpq | hpq) <;> simp [hpq, hs]
    iterate 3 rw [dvd_iff_content_dvd_content_and_primPart_dvd_primPart hs]
    nontriviality R
    rw [(associated_content_mul ..).dvd_iff_dvd_left]; rw [rprim.content_eq_one]; rw [mul_one]; rw [content_C]; rw [(associated_primPart_mul (mul_ne_zero hpq rprim.ne_zero)).dvd_iff_dvd_left]; rw [rprim.primPart_eq]; rw [normalize_lcm]; rw [lcm_dvd_iff]; rw [(isUnit_primPart_C (lcm p.content q.content)).mul_left_dvd]; rw [← hr s.primPart]
    tauto

Depends on / 依赖: C_eq_zero, Classical, Classical.decEq, content, content_eq_zero_iff, dvd_iff_content_dvd_content_and_primPart_dv, exists_primitive_lcm_of_isPrimitive, isPrimitive_primPart, iterate, lcm_eq_zero_iff, normalizedGCDMonoidOfExistsLCM, p.content, p.isPrimitive_primPart, q.content, q.isPrimitive_primPart
-/
noncomputable instance normalizedGcdMonoid : NormalizedGCDMonoid R[X] :=
  letI := Classical.decEq R
  normalizedGCDMonoidOfExistsLCM fun p q => by
    rcases exists_primitive_lcm_of_isPrimitive p.isPrimitive_primPart
        q.isPrimitive_primPart with
      ⟨r, rprim, hr⟩
    refine ⟨C (lcm p.content q.content) * r, fun s => ?_⟩
    by_cases hs : s = 0
    · simp [hs]
    by_cases hpq : C (lcm p.content q.content) = 0
    · rw [C_eq_zero, lcm_eq_zero_iff, content_eq_zero_iff, content_eq_zero_iff] at hpq
      rcases hpq with (hpq | hpq) <;> simp [hpq, hs]
    iterate 3 rw [dvd_iff_content_dvd_content_and_primPart_dvd_primPart hs]
    nontriviality R
    rw [(associated_content_mul ..).dvd_iff_dvd_left]; rw [rprim.content_eq_one]; rw [mul_one]; rw [content_C]; rw [(associated_primPart_mul (mul_ne_zero hpq rprim.ne_zero)).dvd_iff_dvd_left]; rw [rprim.primPart_eq]; rw [normalize_lcm]; rw [lcm_dvd_iff]; rw [(isUnit_primPart_C (lcm p.content q.content)).mul_left_dvd]; rw [← hr s.primPart]
    tauto

/--
theorem `degree_gcd_le_left` / 定理 `degree_gcd_le_left`

English:
theorem degree_gcd_le_left
  given: {p : R[X]} (hp : p != 0) (q)
  statement: (gcd p q).degree <= p.degree
  proof: by
  have := natDegree_le_iff_degree_le.mp (natDegree_le_of_dvd (gcd_dvd_left p q) hp)
  rwa [degree_eq_natDegree hp]

中文:
定理 degree_gcd_le_left
  条件: {p : R[X]} (hp : p != 0) (q)
  结论: (最大公约数 p q).degree <= p.degree
  证明: by
  have := natDegree_le_iff_degree_le.mp (natDegree_le_of_dvd (gcd_dvd_left p q) hp)
  rwa [degree_eq_natDegree hp]

Depends on / 依赖: degree_eq_natDegree, gcd_dvd_left, natDegree_le_iff_degree_le, natDegree_le_iff_degree_le.mp, natDegree_le_of_dvd
-/
theorem degree_gcd_le_left {p : R[X]} (hp : p != 0) (q) : (gcd p q).degree <= p.degree := by
  have := natDegree_le_iff_degree_le.mp (natDegree_le_of_dvd (gcd_dvd_left p q) hp)
  rwa [degree_eq_natDegree hp]

/--
theorem `degree_gcd_le_right` / 定理 `degree_gcd_le_right`

English:
theorem degree_gcd_le_right
  given: (p) {q : R[X]} (hq : q != 0)
  statement: (gcd p q).degree <= q.degree
  proof: by
  rw [gcd_comm]
  exact degree_gcd_le_left hq p

中文:
定理 degree_gcd_le_right
  条件: (p) {q : R[X]} (hq : q != 0)
  结论: (最大公约数 p q).degree <= q.degree
  证明: by
  rw [gcd_comm]
  exact degree_gcd_le_left hq p

Depends on / 依赖: degree_gcd_le_left, gcd_comm
-/
theorem degree_gcd_le_right (p) {q : R[X]} (hq : q != 0) : (gcd p q).degree <= q.degree := by
  rw [gcd_comm]
  exact degree_gcd_le_left hq p

end NormalizedGCDMonoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [StrongNormalizedGCDMonoid
  signature: R] : StrongNormalizedGCDMonoid R[X] where
  body: inferInstance
  __ : StrongNormalizationMonoid R[X] := inferInstance

中文:
实例 [StrongNormalizedGCD幺半群
  签名: R] : StrongNormalizedGCD幺半群 R[X] where
  定义体: inferInstance
  __ : StrongNormalizationMonoid R[X] := inferInstance
-/
noncomputable instance [StrongNormalizedGCDMonoid R] : StrongNormalizedGCDMonoid R[X] where
  __ : NormalizedGCDMonoid R[X] := inferInstance
  __ : StrongNormalizationMonoid R[X] := inferInstance

-- We do not add a `GCDMonoid R[X]` instance due to diamond
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsGCDMonoid
  signature: R] : IsGCDMonoid R[X]
  body: have := Classical.arbitrary (NormalizedGCDMonoid R); inferInstance

中文:
实例 [IsGCDMonoid
  签名: R] : IsGCDMonoid R[X]
  定义体: have := Classical.arbitrary (NormalizedGCDMonoid R); inferInstance

Depends on / 依赖: Classical, Classical.arbitrary, NormalizedGCDMonoid, arbitrary
-/
instance [IsGCDMonoid R] : IsGCDMonoid R[X] :=
  have := Classical.arbitrary (NormalizedGCDMonoid R); inferInstance

end Polynomial
