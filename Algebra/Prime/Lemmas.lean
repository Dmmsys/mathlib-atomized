/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Divisibility.Hom
public import Mathlib.Algebra.Group.Irreducible.Lemmas
public import Mathlib.Algebra.GroupWithZero.Equiv
public import Mathlib.Algebra.Prime.Defs
public import Mathlib.Order.Monotone.Defs

/-!
# Associated, prime, and irreducible elements.

In this file we define the predicate `Prime p`
saying that an element of a commutative monoid with zero is prime.
Namely, `Prime p` means that `p` isn't zero, it isn't a unit,
and `p ∣ a * b → p ∣ a ∨ p ∣ b` for all `a`, `b`;

In decomposition monoids (e.g., `ℕ`, `ℤ`), this predicate is equivalent to `Irreducible`,
however this is not true in general.

We also define an equivalence relation `Associated`
saying that two elements of a monoid differ by a multiplication by a unit.
Then we show that the quotient type `Associates` is a monoid
and prove basic properties of this quotient.
-/

public section

assert_not_exists IsOrderedMonoid Multiset

variable {M N : Type*}

section Prime

variable [CommMonoidWithZero M]

section Map

variable [CommMonoidWithZero N] {F : Type*} {G : Type*} [FunLike F M N]
variable [MonoidWithZeroHomClass F M N] [FunLike G N M] [MulHomClass G N M]
variable (f : F) (g : G) {p : M}

/--
theorem `comap_prime` / 定理 `comap_prime`

English:
theorem comap_prime
  given: (hinv : forall a, g (f a : N) = a) (hp : Prime (f p))
  statement: Prime p
  proof: ⟨fun h => hp.1 by simp [h], fun h => hp.2.1 h.map f, fun a b h => by
    refine
        (hp.2.2 (f a) (f b) <| by
              convert! map_dvd f h
              simp).imp
          ?_ ?_ <;>
      · intro h
        convert! ← map_dvd g h <;> apply hinv⟩

中文:
定理 comap_prime
  条件: (hinv : 对任意 a, g (f a : N) = a) (hp : Prime (f p))
  结论: Prime p
  证明: ⟨fun h => hp.1 by simp [h], fun h => hp.2.1 h.map f, fun a b h => by
    refine
        (hp.2.2 (f a) (f b) <| by
              convert! map_dvd f h
              simp).imp
          ?_ ?_ <;>
      · intro h
        convert! ← map_dvd g h <;> apply hinv⟩

Depends on / 依赖: convert, h.map, map_dvd
-/
theorem comap_prime (hinv : forall a, g (f a : N) = a) (hp : Prime (f p)) : Prime p :=
⟨fun h => hp.1 by simp [h], fun h => hp.2.1 h.map f, fun a b h => by
    refine
        (hp.2.2 (f a) (f b) <| by
              convert! map_dvd f h
              simp).imp
          ?_ ?_ <;>
      · intro h
        convert! ← map_dvd g h <;> apply hinv⟩

/--
theorem `MulEquiv.prime_iff` / 定理 `MulEquiv.prime_iff`

English:
theorem MulEquiv.prime_iff
  given: {E : Type*} [EquivLike E M N] [MulEquivClass E M N] (e : E)
  proof: by
  let e := MulEquivClass.toMulEquiv e
  exact ⟨comap_prime e e.symm fun a => by simp,
fun h => (comap_prime e.symm e fun a => by simp) (e.symm_apply_apply p).substr h⟩

中文:
定理 MulEquiv.prime_iff
  条件: {E : 类型} [EquivLike E M N] [MulEquivClass E M N] (e : E)
  证明: by
  let e := MulEquivClass.toMulEquiv e
  exact ⟨comap_prime e e.symm fun a => by simp,
fun h => (comap_prime e.symm e fun a => by simp) (e.symm_apply_apply p).substr h⟩

Depends on / 依赖: MulEquivClass, MulEquivClass.toMulEquiv, comap_prime, e.symm, e.symm_apply_apply, substr, symm_apply_apply, toMulEquiv
-/
theorem MulEquiv.prime_iff {E : Type*} [EquivLike E M N] [MulEquivClass E M N] (e : E) :
    Prime (e p) ↔ Prime p := by
  let e := MulEquivClass.toMulEquiv e
  exact ⟨comap_prime e e.symm fun a => by simp,
fun h => (comap_prime e.symm e fun a => by simp) (e.symm_apply_apply p).substr h⟩

end Map

variable {x y : M}

/--
theorem `prime_units_mul` / 定理 `prime_units_mul`

English:
theorem prime_units_mul
  given: (u : Mˣ)
  statement: Prime (↑u * y) ↔ Prime y
  proof: by simp [Prime]

中文:
定理 prime_units_mul
  条件: (u : Mˣ)
  结论: Prime (↑u * y) ↔ Prime y
  证明: by simp [Prime]
-/
theorem prime_units_mul (u : Mˣ) : Prime (↑u * y) ↔ Prime y := by simp [Prime]

/--
theorem `prime_isUnit_mul` / 定理 `prime_isUnit_mul`

English:
theorem prime_isUnit_mul
  given: (h : IsUnit x)
  statement: Prime (x * y) ↔ Prime y
  proof: let ⟨u, hu⟩ := h
  hu ▸ prime_units_mul u

中文:
定理 prime_isUnit_mul
  条件: (h : IsUnit x)
  结论: Prime (x * y) ↔ Prime y
  证明: let ⟨u, hu⟩ := h
  hu ▸ prime_units_mul u

Depends on / 依赖: prime_units_mul
-/
theorem prime_isUnit_mul (h : IsUnit x) : Prime (x * y) ↔ Prime y :=
  let ⟨u, hu⟩ := h
  hu ▸ prime_units_mul u

/--
theorem `prime_mul_units` / 定理 `prime_mul_units`

English:
theorem prime_mul_units
  given: (u : Mˣ)
  statement: Prime (y * ↑u) ↔ Prime y
  proof: by
  rw [mul_comm]; rw [prime_units_mul]

中文:
定理 prime_mul_units
  条件: (u : Mˣ)
  结论: Prime (y * ↑u) ↔ Prime y
  证明: by
  rw [mul_comm]; rw [prime_units_mul]

Depends on / 依赖: mul_comm, prime_units_mul
-/
theorem prime_mul_units (u : Mˣ) : Prime (y * ↑u) ↔ Prime y := by
  rw [mul_comm]; rw [prime_units_mul]

/--
theorem `prime_mul_isUnit` / 定理 `prime_mul_isUnit`

English:
theorem prime_mul_isUnit
  given: (h : IsUnit x)
  statement: Prime (y * x) ↔ Prime y
  proof: let ⟨u, hu⟩ := h
  hu ▸ prime_mul_units u

中文:
定理 prime_mul_isUnit
  条件: (h : IsUnit x)
  结论: Prime (y * x) ↔ Prime y
  证明: let ⟨u, hu⟩ := h
  hu ▸ prime_mul_units u

Depends on / 依赖: prime_mul_units
-/
theorem prime_mul_isUnit (h : IsUnit x) : Prime (y * x) ↔ Prime y :=
  let ⟨u, hu⟩ := h
  hu ▸ prime_mul_units u

end Prime

section IsCancelMulZero

variable [CommMonoidWithZero M] [IsCancelMulZero M]

/--
theorem `Prime.left_dvd_or_dvd_right_of_dvd_mul` / 定理 `Prime.left_dvd_or_dvd_right_of_dvd_mul`

English:
theorem Prime.left_dvd_or_dvd_right_of_dvd_mul
  statement: {p : M} (hp : Prime p)
  proof: by
  rintro ⟨c, hc⟩
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with (h | ⟨x, rfl⟩)
  · exact Or.inl h
  · rw [mul_left_comm, mul_right_inj' hp.ne_zero] at hc
    exact Or.inr (hc.symm ▸ dvd_mul_right _ _)

中文:
定理 Prime.left_dvd_or_dvd_right_of_dvd_mul
  结论: {p : M} (hp : Prime p)
  证明: by
  rintro ⟨c, hc⟩
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with (h | ⟨x, rfl⟩)
  · exact Or.inl h
  · rw [mul_left_comm, mul_right_inj' hp.ne_zero] at hc
    exact Or.inr (hc.symm ▸ dvd_mul_right _ _)

Depends on / 依赖: Or.inl, Or.inr, dvd_mul_right, hc.symm, hp.ne_zero, mul_left_comm, mul_right_inj, ne_zero
-/
theorem Prime.left_dvd_or_dvd_right_of_dvd_mul {p : M} (hp : Prime p)
    {a b : M} : a ∣ p * b -> p ∣ a ∨ a ∣ b := by
  rintro ⟨c, hc⟩
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with (h | ⟨x, rfl⟩)
  · exact Or.inl h
  · rw [mul_left_comm, mul_right_inj' hp.ne_zero] at hc
    exact Or.inr (hc.symm ▸ dvd_mul_right _ _)

/--
theorem `Prime.pow_dvd_of_dvd_mul_left` / 定理 `Prime.pow_dvd_of_dvd_mul_left`

English:
theorem Prime.pow_dvd_of_dvd_mul_left
  statement: {p a b : M} (hp : Prime p)
  proof: by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_dvd b
  | succ n ih =>
    obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h')
    rw [pow_succ]
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h)
    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← 

中文:
定理 Prime.pow_dvd_of_dvd_mul_left
  结论: {p a b : M} (hp : Prime p)
  证明: by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_dvd b
  | succ n ih =>
    obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h')
    rw [pow_succ]
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h)
    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← 

Depends on / 依赖: dvd_or_dvd, dvd_trans, hp.dvd_or_dvd, hp.ne_zero, le_succ, mul_dvd_mul_iff_left, mul_dvd_mul_left, mul_left_comm, n.le_succ, ne_zero, one_dvd, pow_dvd_pow, pow_ne_zero, pow_succ, pow_zero, resolve_left
-/
theorem Prime.pow_dvd_of_dvd_mul_left {p a b : M} (hp : Prime p)
    (n : Nat) (h : ¬p ∣ a) (h' : p ^ n ∣ a * b) : p ^ n ∣ b := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact one_dvd b
  | succ n ih =>
    obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h')
    rw [pow_succ]
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h)
    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← pow_succ, mul_left_comm]

/--
theorem `Prime.pow_dvd_of_dvd_mul_right` / 定理 `Prime.pow_dvd_of_dvd_mul_right`

English:
theorem Prime.pow_dvd_of_dvd_mul_right
  statement: {p a b : M} (hp : Prime p)
  proof: by
  rw [mul_comm] at h'
  exact hp.pow_dvd_of_dvd_mul_left n h h'

中文:
定理 Prime.pow_dvd_of_dvd_mul_right
  结论: {p a b : M} (hp : Prime p)
  证明: by
  rw [mul_comm] at h'
  exact hp.pow_dvd_of_dvd_mul_left n h h'

Depends on / 依赖: hp.pow_dvd_of_dvd_mul_left, mul_comm, pow_dvd_of_dvd_mul_left
-/
theorem Prime.pow_dvd_of_dvd_mul_right {p a b : M} (hp : Prime p)
    (n : Nat) (h : ¬p ∣ b) (h' : p ^ n ∣ a * b) : p ^ n ∣ a := by
  rw [mul_comm] at h'
  exact hp.pow_dvd_of_dvd_mul_left n h h'

/--
theorem `Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd` / 定理 `Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd`

English:
theorem Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd
  statement: {p a b : M}
  proof: by
  -- Suppose `p ∣ b`, write `b = p * x` and `hy : a ^ n.succ * b ^ n = p ^ n.succ * y`.
  rcases hp.dvd_or_dvd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hpow) with H | hbdiv
  · exact hp.dvd_of_dvd_pow H
  obtain ⟨x, rfl⟩ := hp.dvd_of_dvd_pow hbdiv
  obtain ⟨y, hy⟩ := hpow
  -- Then we can div

中文:
定理 Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd
  结论: {p a b : M}
  证明: by
  -- Suppose `p ∣ b`, write `b = p * x` and `hy : a ^ n.succ * b ^ n = p ^ n.succ * y`.
  rcases hp.dvd_or_dvd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hpow) with H | hbdiv
  · exact hp.dvd_of_dvd_pow H
  obtain ⟨x, rfl⟩ := hp.dvd_of_dvd_pow hbdiv
  obtain ⟨y, hy⟩ := hpow
  -- Then we can div
-/
theorem Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd {p a b : M}
    {n : Nat} (hp : Prime p) (hpow : p ^ n.succ ∣ a ^ n.succ * b ^ n) (hb : ¬p ^ 2 ∣ b) : p ∣ a := by
  -- Suppose `p ∣ b`, write `b = p * x` and `hy : a ^ n.succ * b ^ n = p ^ n.succ * y`.
  rcases hp.dvd_or_dvd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hpow) with H | hbdiv
  · exact hp.dvd_of_dvd_pow H
  obtain ⟨x, rfl⟩ := hp.dvd_of_dvd_pow hbdiv
  obtain ⟨y, hy⟩ := hpow
  -- Then we can divide out a common factor of `p ^ n` from the equation `hy`.
  have : a ^ n.succ * x ^ n = p * y := by
    refine mul_left_cancel₀ (pow_ne_zero n hp.ne_zero) ?_
    rw [← mul_assoc _ p]; rw [← pow_succ]; rw [← hy]; rw [mul_pow]; rw [← mul_assoc (a ^ n.succ)]; rw [mul_comm _ (p ^ n)]; rw [mul_assoc]
  -- So `p ∣ a` (and we're done) or `p ∣ x`, which can't be the case since it implies `p^2 ∣ b`.
  refine hp.dvd_of_dvd_pow ((hp.dvd_or_dvd ⟨_, this⟩).resolve_right fun hdvdx => hb ?_)
  obtain ⟨z, rfl⟩ := hp.dvd_of_dvd_pow hdvdx
  rw [pow_two]; rw [← mul_assoc]
  exact dvd_mul_right _ _

/--
theorem `prime_pow_succ_dvd_mul` / 定理 `prime_pow_succ_dvd_mul`

English:
theorem prime_pow_succ_dvd_mul
  statement: {p x y : M} (h : Prime p)
  proof: by
  rw [or_iff_not_imp_right]
  exact fun a => Prime.pow_dvd_of_dvd_mul_right h (i + 1) a hxy

中文:
定理 prime_pow_succ_dvd_mul
  结论: {p x y : M} (h : Prime p)
  证明: by
  rw [or_iff_not_imp_right]
  exact fun a => Prime.pow_dvd_of_dvd_mul_right h (i + 1) a hxy

Depends on / 依赖: CanLift, NonUnitalStarSubsemiring, Prime.pow_dvd_of_dvd_mul_right, or_iff_not_imp_right, pow_dvd_of_dvd_mul_right
-/
theorem prime_pow_succ_dvd_mul {p x y : M} (h : Prime p)
    {i : Nat} (hxy : p ^ (i + 1) ∣ x * y) : p ^ (i + 1) ∣ x ∨ p ∣ y := by
  rw [or_iff_not_imp_right]
  exact fun a => Prime.pow_dvd_of_dvd_mul_right h (i + 1) a hxy

variable {a p : M}

/--
theorem `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul` / 定理 `succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul`

English:
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
  given: (hp : Prime p) {a b : M} {k l : Nat}
  proof: fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ =>
  have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z) := by
    simpa [mul_comm, pow_add, hx, hy, mul_assoc, mul_left_comm] using hz
  have hp0 : p ^ (k + l) != 0 := pow_ne_zero _ hp.ne_zero
  have hpd : p ∣ x * y := ⟨z, by rwa [mul_right_inj' hp0] at h⟩
  (hp.dvd_o

中文:
定理 succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul
  条件: (hp : Prime p) {a b : M} {k l : 自然数}
  证明: fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ =>
  have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z) := by
    simpa [mul_comm, pow_add, hx, hy, mul_assoc, mul_left_comm] using hz
  have hp0 : p ^ (k + l) != 0 := pow_ne_zero _ hp.ne_zero
  have hpd : p ∣ x * y := ⟨z, by rwa [mul_right_inj' hp0] at h⟩
  (hp.dvd_o

Depends on / 依赖: Or.inl, Or.inr, dvd_or_dvd, hp.dvd_or_dvd, hp.ne_zero, mul_assoc, mul_comm, mul_left_comm, mul_right_inj, ne_zero, pow_add, pow_ne_zero, pow_succ
-/
theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul (hp : Prime p) {a b : M} {k l : Nat} :
    p ^ k ∣ a -> p ^ l ∣ b -> p ^ (k + l + 1) ∣ a * b -> p ^ (k + 1) ∣ a ∨ p ^ (l + 1) ∣ b :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ =>
  have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z) := by
    simpa [mul_comm, pow_add, hx, hy, mul_assoc, mul_left_comm] using hz
  have hp0 : p ^ (k + l) != 0 := pow_ne_zero _ hp.ne_zero
  have hpd : p ∣ x * y := ⟨z, by rwa [mul_right_inj' hp0] at h⟩
  (hp.dvd_or_dvd hpd).elim
    (fun ⟨d, hd⟩ => Or.inl ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩)
    fun ⟨d, hd⟩ => Or.inr ⟨d, by simp [*, pow_succ, mul_comm, mul_left_comm, mul_assoc]⟩

/--
theorem `Prime.not_isSquare` / 定理 `Prime.not_isSquare`

English:
theorem Prime.not_isSquare
  given: (hp : Prime p)
  statement: ¬IsSquare p
  proof: hp.irreducible.not_isSquare

中文:
定理 Prime.not_isSquare
  条件: (hp : Prime p)
  结论: ¬IsSquare p
  证明: hp.irreducible.not_isSquare

Depends on / 依赖: hp.irreducible.not_isSquare, irreducible, not_isSquare
-/
theorem Prime.not_isSquare (hp : Prime p) : ¬IsSquare p :=
  hp.irreducible.not_isSquare

/--
theorem `IsSquare.not_prime` / 定理 `IsSquare.not_prime`

English:
theorem IsSquare.not_prime
  given: (ha : IsSquare a)
  statement: ¬Prime a
  proof: fun h => h.not_isSquare ha

中文:
定理 IsSquare.not_prime
  条件: (ha : IsSquare a)
  结论: ¬Prime a
  证明: fun h => h.not_isSquare ha

Depends on / 依赖: h.not_isSquare, not_isSquare
-/
theorem IsSquare.not_prime (ha : IsSquare a) : ¬Prime a := fun h => h.not_isSquare ha

/--
theorem `not_prime_pow` / 定理 `not_prime_pow`

English:
theorem not_prime_pow
  given: {n : Nat} (hn : n != 1)
  statement: ¬Prime (a ^ n)
  proof: fun hp =>
  not_irreducible_pow hn hp.irreducible

中文:
定理 not_prime_pow
  条件: {n : 自然数} (hn : n != 1)
  结论: ¬Prime (a ^ n)
  证明: fun hp =>
  not_irreducible_pow hn hp.irreducible
-/
theorem not_prime_pow {n : Nat} (hn : n != 1) : ¬Prime (a ^ n) := fun hp =>
  not_irreducible_pow hn hp.irreducible

end IsCancelMulZero

section CommMonoidWithZero

/--
theorem `DvdNotUnit.isUnit_of_irreducible_right` / 定理 `DvdNotUnit.isUnit_of_irreducible_right`

English:
theorem DvdNotUnit.isUnit_of_irreducible_right
  statement: [CommMonoidWithZero M] {p q : M}
  proof: by
  obtain ⟨_, x, hx, hx'⟩ := h
  exact ((irreducible_iff.1 hq).right hx').resolve_right hx

中文:
定理 DvdNotUnit.isUnit_of_irreducible_right
  结论: [CommMonoidWithZero M] {p q : M}
  证明: by
  obtain ⟨_, x, hx, hx'⟩ := h
  exact ((irreducible_iff.1 hq).right hx').resolve_right hx

Depends on / 依赖: irreducible_iff, resolve_right
-/
theorem DvdNotUnit.isUnit_of_irreducible_right [CommMonoidWithZero M] {p q : M}
    (h : DvdNotUnit p q) (hq : Irreducible q) : IsUnit p := by
  obtain ⟨_, x, hx, hx'⟩ := h
  exact ((irreducible_iff.1 hq).right hx').resolve_right hx

/--
theorem `not_irreducible_of_not_isUnit_of_dvdNotUnit` / 定理 `not_irreducible_of_not_isUnit_of_dvdNotUnit`

English:
theorem not_irreducible_of_not_isUnit_of_dvdNotUnit
  statement: [CommMonoidWithZero M] {p q : M}
  proof: mt h.isUnit_of_irreducible_right hp

@[deprecated (since := "2026-08-02")]
alias not_irreducible_of_not_unit_dvdNotUnit := not_irreducible_of_not_isUnit_of_dvdNotUnit

中文:
定理 not_irreducible_of_not_isUnit_of_dvdNotUnit
  结论: [CommMonoidWithZero M] {p q : M}
  证明: mt h.isUnit_of_irreducible_right hp

@[deprecated (since := "2026-08-02")]
alias not_irreducible_of_not_unit_dvdNotUnit := not_irreducible_of_not_isUnit_of_dvdNotUnit

Depends on / 依赖: h.isUnit_of_irreducible_right, isUnit_of_irreducible_right
-/
theorem not_irreducible_of_not_isUnit_of_dvdNotUnit [CommMonoidWithZero M] {p q : M}
    (hp : ¬IsUnit p) (h : DvdNotUnit p q) : ¬Irreducible q :=
  mt h.isUnit_of_irreducible_right hp

@[deprecated (since := "2026-08-02")]
alias not_irreducible_of_not_unit_dvdNotUnit := not_irreducible_of_not_isUnit_of_dvdNotUnit

/--
theorem `DvdNotUnit.not_isUnit` / 定理 `DvdNotUnit.not_isUnit`

English:
theorem DvdNotUnit.not_isUnit
  given: [CommMonoidWithZero M] {p q : M} (hp : DvdNotUnit p q)
  proof: by
  obtain ⟨-, x, hx, rfl⟩ := hp
  exact fun hc => hx (isUnit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (isUnit_iff_dvd_one.mp hc)))

@[deprecated (since := "2026-08-02")]
alias DvdNotUnit.not_unit := DvdNotUnit.not_isUnit

中文:
定理 DvdNotUnit.not_isUnit
  条件: [CommMonoidWithZero M] {p q : M} (hp : DvdNotUnit p q)
  证明: by
  obtain ⟨-, x, hx, rfl⟩ := hp
  exact fun hc => hx (isUnit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (isUnit_iff_dvd_one.mp hc)))

@[deprecated (since := "2026-08-02")]
alias DvdNotUnit.not_unit := DvdNotUnit.not_isUnit

Depends on / 依赖: dvd_of_mul_left_dvd, isUnit_iff_dvd_one, isUnit_iff_dvd_one.mp, isUnit_iff_dvd_one.mpr
-/
theorem DvdNotUnit.not_isUnit [CommMonoidWithZero M] {p q : M} (hp : DvdNotUnit p q) :
    ¬IsUnit q := by
  obtain ⟨-, x, hx, rfl⟩ := hp
  exact fun hc => hx (isUnit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (isUnit_iff_dvd_one.mp hc)))

@[deprecated (since := "2026-08-02")]
alias DvdNotUnit.not_unit := DvdNotUnit.not_isUnit

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CommMonoidWithZero M] [IsCancelMulZero M]

/--
theorem `DvdNotUnit.ne` / 定理 `DvdNotUnit.ne`

English:
theorem DvdNotUnit.ne
  given: {p q : M} (h : DvdNotUnit p q)
  statement: p != q
  proof: by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  simp_all

中文:
定理 DvdNotUnit.ne
  条件: {p q : M} (h : DvdNotUnit p q)
  结论: p != q
  证明: by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  simp_all

Depends on / 依赖: hcontra
-/
theorem DvdNotUnit.ne {p q : M} (h : DvdNotUnit p q) : p != q := by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  simp_all

/--
theorem `pow_injective_of_not_isUnit` / 定理 `pow_injective_of_not_isUnit`

English:
theorem pow_injective_of_not_isUnit
  statement: {q : M} (hq : ¬IsUnit q)
  proof: by
  refine .of_lt_imp_ne fun n m h => DvdNotUnit.ne ⟨pow_ne_zero n hq', q ^ (m - n), ?_, ?_⟩
  · exact not_isUnit_of_not_isUnit_dvd hq (dvd_pow (dvd_refl _) (Nat.sub_pos_of_lt h).ne')
  · exact (pow_mul_pow_sub q h.le).symm

中文:
定理 pow_injective_of_not_isUnit
  结论: {q : M} (hq : ¬IsUnit q)
  证明: by
  refine .of_lt_imp_ne fun n m h => DvdNotUnit.ne ⟨pow_ne_zero n hq', q ^ (m - n), ?_, ?_⟩
  · exact not_isUnit_of_not_isUnit_dvd hq (dvd_pow (dvd_refl _) (Nat.sub_pos_of_lt h).ne')
  · exact (pow_mul_pow_sub q h.le).symm

Depends on / 依赖: DvdNotUnit, DvdNotUnit.ne, Nat.sub_pos_of_lt, dvd_pow, dvd_refl, h.le, not_isUnit_of_not_isUnit_dvd, of_lt_imp_ne, pow_mul_pow_sub, pow_ne_zero, sub_pos_of_lt
-/
theorem pow_injective_of_not_isUnit {q : M} (hq : ¬IsUnit q)
    (hq' : q != 0) : Function.Injective fun n : Nat => q ^ n := by
  refine .of_lt_imp_ne fun n m h => DvdNotUnit.ne ⟨pow_ne_zero n hq', q ^ (m - n), ?_, ?_⟩
  · exact not_isUnit_of_not_isUnit_dvd hq (dvd_pow (dvd_refl _) (Nat.sub_pos_of_lt h).ne')
  · exact (pow_mul_pow_sub q h.le).symm

/--
theorem `pow_inj_of_not_isUnit` / 定理 `pow_inj_of_not_isUnit`

English:
theorem pow_inj_of_not_isUnit
  statement: {q : M} (hq : ¬IsUnit q)
  proof: (pow_injective_of_not_isUnit hq hq').eq_iff

中文:
定理 pow_inj_of_not_isUnit
  结论: {q : M} (hq : ¬IsUnit q)
  证明: (pow_injective_of_not_isUnit hq hq').eq_iff

Depends on / 依赖: eq_iff, pow_injective_of_not_isUnit
-/
theorem pow_inj_of_not_isUnit {q : M} (hq : ¬IsUnit q)
    (hq' : q != 0) {m n : Nat} : q ^ m = q ^ n ↔ m = n :=
  (pow_injective_of_not_isUnit hq hq').eq_iff

end CancelCommMonoidWithZero

/--
lemma `IsRelPrime.of_map` / 引理 `IsRelPrime.of_map`

English:
lemma IsRelPrime.of_map
  proof: fun _ h₁ h₂ => .of_map _ _ (hab (map_dvd f h₁) (map_dvd f h₂))

中文:
引理 IsRelPrime.of_map
  证明: fun _ h₁ h₂ => .of_map _ _ (hab (map_dvd f h₁) (map_dvd f h₂))

Depends on / 依赖: map_dvd, of_map
-/
lemma IsRelPrime.of_map
    {M N F : Type*} [Monoid M] [Monoid N] [FunLike F M N] [MulHomClass F M N]
    (f : F) [IsLocalHom f] {a b : M}
    (hab : IsRelPrime (f a) (f b)) : IsRelPrime a b :=
  fun _ h₁ h₂ => .of_map _ _ (hab (map_dvd f h₁) (map_dvd f h₂))
