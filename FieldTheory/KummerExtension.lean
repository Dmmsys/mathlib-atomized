/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.RingTheory.Norm.Basic

/-!
# Kummer Extensions

Let `K` be a field, `n` be an integer such that `K` contains a primitive `n`-th root of unity.
Kummer theory is about the classification of finite extensions of `L` whose Galois group is cyclic
of order `n`.

## Main result
- `isCyclic_tfae`:
  Suppose `L/K` is a finite extension of dimension `n`
  Then `L/K` is cyclic iff
  `L` is a splitting field of some irreducible polynomial of the form `Xⁿ - a : K[X]` iff
  `L = K[α]` for some `αⁿ ∈ K`.

- `autEquivRootsOfUnity`:
  Given an instance `IsSplittingField K L (X ^ n - C a)`
  (perhaps via `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top`),
  then the Galois group is isomorphic to `rootsOfUnity n K`, by sending
  `σ ↦ σ α / α` for `α ^ n = a`, and the inverse is given by `μ ↦ (α ↦ μ • α)`.

- `autEquivZmod`:
  Furthermore, given an explicit choice `ζ` of a primitive `n`-th root of unity, the Galois group is
  then isomorphic to `Multiplicative (ZMod n)` whose inverse is given by
  `i ↦ (α ↦ ζⁱ • α)`.

## Other results
Criteria for `X ^ n - C a` to be irreducible is given:
- `X_pow_sub_C_irreducible_iff_of_prime_pow`:
  For `n = p ^ k` an odd prime power, `X ^ n - C a` is irreducible iff `a` is not a `p`-th power.
- `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`:
  For `n` odd, `X ^ n - C a` is irreducible iff `a` is not a `p`-th power for all prime `p ∣ n`.
- `X_pow_sub_C_irreducible_iff_of_odd`:
  For `n` odd, `X ^ n - C a` is irreducible iff `a` is not a `d`-th power for `d ∣ n` and `d ≠ 1`.

TODO: criteria for even `n`. See [serge_lang_algebra] VI,§9.

TODO: relate Kummer extensions of degree 2 with the class `Algebra.IsQuadraticExtension`.

TODO: treat the case where the characteristic `p` of the field divides `n`, so that `K` never
contains a primitive `n`-th root of unity.
For the Galois group part, this is Artin-Schreier theory;
it also holds that `X ^ p - C a` is irreducible iff `a` is not a `p`-th power in `K`.

-/

@[expose] public section
universe u

variable {K : Type u} [Field K]

open Polynomial IntermediateField AdjoinRoot

section Splits

/--
theorem `X_pow_sub_C_splits_of_isPrimitiveRoot` / 定理 `X_pow_sub_C_splits_of_isPrimitiveRoot`

English:
theorem X_pow_sub_C_splits_of_isPrimitiveRoot
  proof: by
  cases n.eq_zero_or_pos with
  | inl hn =>
    simp only [hn, pow_zero, ← C.map_one, ← map_sub, Splits.C]
  | inr hn =>
    rw [splits_iff_card_roots]; rw [← nthRoots]; rw [hζ.card_nthRoots]; rw [natDegree_X_pow_sub_C]; rw [if_pos ⟨α]; rw [e⟩]

中文:
定理 X_pow_sub_C_splits_of_isPrimitiveRoot
  证明: by
  cases n.eq_zero_or_pos with
  | inl hn =>
    simp only [hn, pow_zero, ← C.map_one, ← map_sub, Splits.C]
  | inr hn =>
    rw [splits_iff_card_roots]; rw [← nthRoots]; rw [hζ.card_nthRoots]; rw [natDegree_X_pow_sub_C]; rw [if_pos ⟨α]; rw [e⟩]

Depends on / 依赖: C.map_one, Splits, Splits.C, card_nthRoots, eq_zero_or_pos, if_pos, map_one, map_sub, n.eq_zero_or_pos, natDegree_X_pow_sub_C, nthRoots, pow_zero, splits_iff_card_roots
-/
theorem X_pow_sub_C_splits_of_isPrimitiveRoot
    {n : Nat} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (e : α ^ n = a) :
    (X ^ n - C a).Splits := by
  cases n.eq_zero_or_pos with
  | inl hn =>
    simp only [hn, pow_zero, ← C.map_one, ← map_sub, Splits.C]
  | inr hn =>
    rw [splits_iff_card_roots]; rw [← nthRoots]; rw [hζ.card_nthRoots]; rw [natDegree_X_pow_sub_C]; rw [if_pos ⟨α]; rw [e⟩]

-- make this private, as we only use it to prove a strictly more general version
private
/--
theorem `X_pow_sub_C_eq_prod'` / 定理 `X_pow_sub_C_eq_prod'`

English:
theorem X_pow_sub_C_eq_prod'
  proof: by
  rw [(X_pow_sub_C_splits_of_isPrimitiveRoot hζ e).eq_prod_roots_of_monic
    (monic_X_pow_sub_C _ hn.ne')]; rw [← nthRoots]; rw [hζ.nthRoots_eq e]; rw [Multiset.map_map]
  rfl

中文:
定理 X_pow_sub_C_eq_prod'
  证明: by
  rw [(X_pow_sub_C_splits_of_isPrimitiveRoot hζ e).eq_prod_roots_of_monic
    (monic_X_pow_sub_C _ hn.ne')]; rw [← nthRoots]; rw [hζ.nthRoots_eq e]; rw [Multiset.map_map]
  rfl

Depends on / 依赖: Multiset, Multiset.map_map, X_pow_sub_C_splits_of_isPrimitiveRoot, eq_prod_roots_of_monic, hn.ne, map_map, monic_X_pow_sub_C, nthRoots, nthRoots_eq
-/
theorem X_pow_sub_C_eq_prod'
    {n : Nat} {ζ : K} (hζ : IsPrimitiveRoot ζ n) {α a : K} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i in Finset.range n, (X - C (ζ ^ i * α)) := by
  rw [(X_pow_sub_C_splits_of_isPrimitiveRoot hζ e).eq_prod_roots_of_monic
    (monic_X_pow_sub_C _ hn.ne')]; rw [← nthRoots]; rw [hζ.nthRoots_eq e]; rw [Multiset.map_map]
  rfl

/--
lemma `X_pow_sub_C_eq_prod` / 引理 `X_pow_sub_C_eq_prod`

English:
lemma X_pow_sub_C_eq_prod
  statement: {R : Type*} [CommRing R] [IsDomain R]
  proof: by
  let K := FractionRing R
  let i := algebraMap R K
  have h := FaithfulSMul.algebraMap_injective R K
  apply_fun Polynomial.map i using map_injective i h
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_mul, map_pow,
    Polynomial.map_prod, Polynomial.map_mul]
using X_pow

中文:
引理 X_pow_sub_C_eq_prod
  结论: {R : 类型} [交换环 R] [是整环 R]
  证明: by
  let K := FractionRing R
  let i := algebraMap R K
  have h := FaithfulSMul.algebraMap_injective R K
  apply_fun Polynomial.map i using map_injective i h
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_mul, map_pow,
    Polynomial.map_prod, Polynomial.map_mul]
using X_pow

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, FractionRing, Polynomial, Polynomial.map, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_prod, Polynomial.map_sub, X_pow_sub_C_eq_prod, algebraMap, algebraMap_injective, apply_fun, map_C, map_X, map_injective, map_mul, map_of_injective, map_pow, map_prod
-/
lemma X_pow_sub_C_eq_prod {R : Type*} [CommRing R] [IsDomain R]
    {n : Nat} {ζ : R} (hζ : IsPrimitiveRoot ζ n) {α a : R} (hn : 0 < n) (e : α ^ n = a) :
    (X ^ n - C a) = ∏ i in Finset.range n, (X - C (ζ ^ i * α)) := by
  let K := FractionRing R
  let i := algebraMap R K
  have h := FaithfulSMul.algebraMap_injective R K
  apply_fun Polynomial.map i using map_injective i h
  simpa only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, map_mul, map_pow,
    Polynomial.map_prod, Polynomial.map_mul]
using X_pow_sub_C_eq_prod' (hζ.map_of_injective h) hn map_pow i α n ▸ congrArg i e

end Splits

section Irreducible

/--
theorem `X_pow_mul_sub_C_irreducible` / 定理 `X_pow_mul_sub_C_irreducible`

English:
theorem X_pow_mul_sub_C_irreducible
  proof: by
  have hm' : m != 0 := by
    rintro rfl
    rw [pow_zero]; rw [← C.map_one]; rw [← map_sub] at hm
    exact not_irreducible_C _ hm
  simpa [pow_mul] using irreducible_comp (monic_X_pow_sub_C a hm') (monic_X_pow n) hm
    (by simpa only [Polynomial.map_pow, map_X] using hn)

中文:
定理 X_pow_mul_sub_C_irreducible
  证明: by
  have hm' : m != 0 := by
    rintro rfl
    rw [pow_zero]; rw [← C.map_one]; rw [← map_sub] at hm
    exact not_irreducible_C _ hm
  simpa [pow_mul] using irreducible_comp (monic_X_pow_sub_C a hm') (monic_X_pow n) hm
    (by simpa only [Polynomial.map_pow, map_X] using hn)

Depends on / 依赖: C.map_one, Polynomial, Polynomial.map_pow, irreducible_comp, map_X, map_one, map_pow, map_sub, monic_X_pow, monic_X_pow_sub_C, not_irreducible_C, pow_mul, pow_zero
-/
theorem X_pow_mul_sub_C_irreducible
    {n m : Nat} {a : K} (hm : Irreducible (X ^ m - C a))
    (hn : forall (E : Type u) [Field E] [Algebra K E] (x : E) (_ : minpoly K x = X ^ m - C a),
      Irreducible (X ^ n - C (AdjoinSimple.gen K x))) :
    Irreducible (X ^ (n * m) - C a) := by
  have hm' : m != 0 := by
    rintro rfl
    rw [pow_zero]; rw [← C.map_one]; rw [← map_sub] at hm
    exact not_irreducible_C _ hm
  simpa [pow_mul] using irreducible_comp (monic_X_pow_sub_C a hm') (monic_X_pow n) hm
    (by simpa only [Polynomial.map_pow, map_X] using hn)

-- TODO: generalize to even `n`
/--
theorem `X_pow_sub_C_irreducible_of_odd` / 定理 `X_pow_sub_C_irreducible_of_odd`

English:
theorem X_pow_sub_C_irreducible_of_odd
  proof: by
  induction n using induction_on_primes generalizing K a with
  | zero => simp [← Nat.not_even_iff_odd] at hn
  | one => simpa using irreducible_X_sub_C a
  | prime_mul p n hp IH =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mu

中文:
定理 X_pow_sub_C_irreducible_of_odd
  证明: by
  induction n using induction_on_primes generalizing K a with
  | zero => simp [← Nat.not_even_iff_odd] at hn
  | one => simpa using irreducible_X_sub_C a
  | prime_mul p n hp IH =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mu

Depends on / 依赖: IsIntegral, Nat.not_even_iff_odd, Nat.o, WithBot, WithBot.natCast_ne_bot, X_pow_mul_sub_C_irreducible, X_pow_sub_C_irreducible_of_prime, congr_arg, degree, degree_X_pow_sub_C, degree_zero, dif_neg, dvd_mul_right, generalizing, hp.pos, hx.symm.trans, induction_on_primes, irreducible_X_sub_C, mul_comm, natCast_ne_bot
-/
theorem X_pow_sub_C_irreducible_of_odd
    {n : Nat} (hn : Odd n) {a : K} (ha : forall p : Nat, p.Prime -> p ∣ n -> forall b : K, b ^ p != a) :
    Irreducible (X ^ n - C a) := by
  induction n using induction_on_primes generalizing K a with
  | zero => simp [← Nat.not_even_iff_odd] at hn
  | one => simpa using irreducible_X_sub_C a
  | prime_mul p n hp IH =>
    rw [mul_comm]
    apply X_pow_mul_sub_C_irreducible
      (X_pow_sub_C_irreducible_of_prime hp (ha p hp (dvd_mul_right _ _)))
    intro E _ _ x hx
    have : IsIntegral K x := not_not.mp fun h => by
      simpa only [degree_zero, degree_X_pow_sub_C hp.pos,
        WithBot.natCast_ne_bot] using congr_arg degree (hx.symm.trans (dif_neg h))
    apply IH (Nat.odd_mul.mp hn).2
    intro q hq hqn b hb
    apply ha q hq (dvd_mul_of_dvd_right hqn p) (Algebra.norm _ b)
    rw [← map_pow]; rw [hb]; rw [← adjoin.powerBasis_gen this]; rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly]
    simp [minpoly_gen, hx, hp.ne_zero.symm, (Nat.odd_mul.mp hn).1.neg_pow]

/--
theorem `X_pow_sub_C_irreducible_iff_forall_prime_of_odd` / 定理 `X_pow_sub_C_irreducible_iff_forall_prime_of_odd`

English:
theorem X_pow_sub_C_irreducible_iff_forall_prime_of_odd
  given: {n : Nat} (hn : Odd n) {a : K}
  proof: ⟨fun e _ hp hpn => pow_ne_of_irreducible_X_pow_sub_C e hpn hp.ne_one,
    X_pow_sub_C_irreducible_of_odd hn⟩

中文:
定理 X_pow_sub_C_irreducible_iff_对任意_prime_of_odd
  条件: {n : 自然数} (hn : Odd n) {a : K}
  证明: ⟨fun e _ hp hpn => pow_ne_of_irreducible_X_pow_sub_C e hpn hp.ne_one,
    X_pow_sub_C_irreducible_of_odd hn⟩

Depends on / 依赖: X_pow_sub_C_irreducible_of_odd, hp.ne_one, ne_one, pow_ne_of_irreducible_X_pow_sub_C
-/
theorem X_pow_sub_C_irreducible_iff_forall_prime_of_odd {n : Nat} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (forall p : Nat, p.Prime -> p ∣ n -> forall b : K, b ^ p != a) :=
  ⟨fun e _ hp hpn => pow_ne_of_irreducible_X_pow_sub_C e hpn hp.ne_one,
    X_pow_sub_C_irreducible_of_odd hn⟩

/--
theorem `X_pow_sub_C_irreducible_iff_of_odd` / 定理 `X_pow_sub_C_irreducible_iff_of_odd`

English:
theorem X_pow_sub_C_irreducible_iff_of_odd
  given: {n : Nat} (hn : Odd n) {a : K}
  proof: ⟨fun e _ => pow_ne_of_irreducible_X_pow_sub_C e,
    fun H => X_pow_sub_C_irreducible_of_odd hn fun p hp hpn => (H p hpn hp.ne_one)⟩

中文:
定理 X_pow_sub_C_irreducible_iff_of_odd
  条件: {n : 自然数} (hn : Odd n) {a : K}
  证明: ⟨fun e _ => pow_ne_of_irreducible_X_pow_sub_C e,
    fun H => X_pow_sub_C_irreducible_of_odd hn fun p hp hpn => (H p hpn hp.ne_one)⟩

Depends on / 依赖: H.normal_of_isMulCommutative.eq_bot_or_eq_top, X_pow_sub_C_irreducible_of_odd, eq_bot_or_eq_top, hp.ne_one, ne_one, normal_of_isMulCommutative, pow_ne_of_irreducible_X_pow_sub_C
-/
theorem X_pow_sub_C_irreducible_iff_of_odd {n : Nat} (hn : Odd n) {a : K} :
    Irreducible (X ^ n - C a) ↔ (forall d, d ∣ n -> d != 1 -> forall b : K, b ^ d != a) :=
  ⟨fun e _ => pow_ne_of_irreducible_X_pow_sub_C e,
    fun H => X_pow_sub_C_irreducible_of_odd hn fun p hp hpn => (H p hpn hp.ne_one)⟩

-- TODO: generalize to `p = 2`
/--
theorem `X_pow_sub_C_irreducible_of_prime_pow` / 定理 `X_pow_sub_C_irreducible_of_prime_pow`

English:
theorem X_pow_sub_C_irreducible_of_prime_pow
  proof: by
  apply X_pow_sub_C_irreducible_of_odd (hp.odd_of_ne_two hp').pow
  intro q hq hq'
  simpa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hq')] using ha

中文:
定理 X_pow_sub_C_irreducible_of_prime_pow
  证明: by
  apply X_pow_sub_C_irreducible_of_odd (hp.odd_of_ne_two hp').pow
  intro q hq hq'
  simpa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hq')] using ha

Depends on / 依赖: Nat.prime_dvd_prime_iff_eq, X_pow_sub_C_irreducible_of_odd, dvd_of_dvd_pow, hp.odd_of_ne_two, hq.dvd_of_dvd_pow, odd_of_ne_two, prime_dvd_prime_iff_eq
-/
theorem X_pow_sub_C_irreducible_of_prime_pow
    {p : Nat} (hp : p.Prime) (hp' : p != 2) (n : Nat) {a : K} (ha : forall b : K, b ^ p != a) :
    Irreducible (X ^ (p ^ n) - C a) := by
  apply X_pow_sub_C_irreducible_of_odd (hp.odd_of_ne_two hp').pow
  intro q hq hq'
  simpa [(Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hq')] using ha

/--
theorem `X_pow_sub_C_irreducible_iff_of_prime_pow` / 定理 `X_pow_sub_C_irreducible_iff_of_prime_pow`

English:
theorem X_pow_sub_C_irreducible_iff_of_prime_pow
  proof: ⟨(pow_ne_of_irreducible_X_pow_sub_C · (dvd_pow dvd_rfl hn) hp.ne_one),
    X_pow_sub_C_irreducible_of_prime_pow hp hp' n⟩

中文:
定理 X_pow_sub_C_irreducible_iff_of_prime_pow
  证明: ⟨(pow_ne_of_irreducible_X_pow_sub_C · (dvd_pow dvd_rfl hn) hp.ne_one),
    X_pow_sub_C_irreducible_of_prime_pow hp hp' n⟩

Depends on / 依赖: X_pow_sub_C_irreducible_of_prime_pow, dvd_pow, dvd_rfl, hp.ne_one, ne_one, pow_ne_of_irreducible_X_pow_sub_C
-/
theorem X_pow_sub_C_irreducible_iff_of_prime_pow
    {p : Nat} (hp : p.Prime) (hp' : p != 2) {n} (hn : n != 0) {a : K} :
    Irreducible (X ^ p ^ n - C a) ↔ forall b, b ^ p != a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · (dvd_pow dvd_rfl hn) hp.ne_one),
    X_pow_sub_C_irreducible_of_prime_pow hp hp' n⟩

end Irreducible

/-!
### Galois Group of `K[n√a]`
We first develop the theory for a specific `K[n√a] := AdjoinRoot (X ^ n - C a)`.
The main result is the description of the Galois group: `autAdjoinRootXPowSubCEquiv`.
-/

variable {n : Nat} (hζ : (primitiveRoots n K).Nonempty)
variable (a : K) (H : Irreducible (X ^ n - C a))

set_option quotPrecheck false in
scoped[KummerExtension] notation3 "K[" n "√" a "]" => AdjoinRoot (Polynomial.X ^ n - Polynomial.C a)

attribute [nolint docBlame] KummerExtension.«termK[_√_]»

open scoped KummerExtension

section AdjoinRoot

include hζ H in
/--
theorem `Polynomial.separable_X_pow_sub_C_of_irreducible` / 定理 `Polynomial.separable_X_pow_sub_C_of_irreducible`

English:
theorem Polynomial.separable_X_pow_sub_C_of_irreducible
  statement: (X ^ n - C a).Separable
  proof: by
  let := Fact.mk H
  let : Algebra K K[n√a] := inferInstance
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  by_cases hn' : n = 1
  · rw [hn', pow_one]; exact separable_X_sub_C
  have ⟨ζ, hζ⟩ := hζ
  rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducibl

中文:
定理 多项式.separable_X_pow_sub_C_of_irreducible
  结论: (X ^ n - C a).可分
  证明: by
  let := Fact.mk H
  let : Algebra K K[n√a] := inferInstance
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  by_cases hn' : n = 1
  · rw [hn', pow_one]; exact separable_X_sub_C
  have ⟨ζ, hζ⟩ := hζ
  rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducibl

Depends on / 依赖: AdjoinRoot, AdjoinRoot.algebraMap_eq, Algebra, Fact.mk, Nat.pos_iff_ne_zero.mpr, Nat.pos_of_ne_zero, Polynomial, Polynomial.map_pow, Polynomial.map_sub, X_pow_sub_C_eq_prod, algebraMap, algebraMap_eq, injective, map_C, map_X, map_of_injective, map_pow, map_sub, mem_primitiveRoots, ne_zero_of_irreducible_X_pow_sub_C
-/
theorem Polynomial.separable_X_pow_sub_C_of_irreducible : (X ^ n - C a).Separable := by
  let := Fact.mk H
  let : Algebra K K[n√a] := inferInstance
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  by_cases hn' : n = 1
  · rw [hn', pow_one]; exact separable_X_sub_C
  have ⟨ζ, hζ⟩ := hζ
  rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
  rw [← separable_map (algebraMap K K[n√a]), Polynomial.map_sub, Polynomial.map_pow, map_C, map_X,
    AdjoinRoot.algebraMap_eq,
    X_pow_sub_C_eq_prod (hζ.map_of_injective (algebraMap K _).injective) hn
    (root_X_pow_sub_C_pow n a), separable_prod_X_sub_C_iff']
  exact (hζ.map_of_injective (algebraMap K K[n√a]).injective).injOn_pow_mul
    (root_X_pow_sub_C_ne_zero (lt_of_le_of_ne (show 1 <= n from hn) (Ne.symm hn')) _)

variable (n)

/-- The natural embedding of the roots of unity of `K` into `Gal(K[ⁿ√a]/K)`, by sending
`η ↦ (ⁿ√a ↦ η • ⁿ√a)`. Also see `autAdjoinRootXPowSubC` for the `AlgEquiv` version. -/
noncomputable
/--
Definition of `autAdjoinRootXPowSubCHom` / `autAdjoinRootXPowSubCHom` 的定义

English:
definition autAdjoinRootXPowSubCHom
  signature: :
  body: liftAlgHom (X ^ n - C a) (Algebra.ofId _ _) (((η : Kˣ) : K) • (root _) : K[n√a]) by
    have := (mem_rootsOfUnity' _ _).mp η.prop
    change aeval _ _ = _
    rw [map_sub]; rw [map_pow]; rw [aeval_C]; rw [aeval_X]; rw [Algebra.smul_def]; rw [mul_pow]; rw [root_X_pow_sub_C_pow]; rw [AdjoinRoot.algebr

中文:
定义 autAdjoinRootXPowSubCHom
  签名: :
  定义体: liftAlgHom (X ^ n - C a) (Algebra.ofId _ _) (((η : Kˣ) : K) • (root _) : K[n√a]) by
    have := (mem_rootsOfUnity' _ _).mp η.prop
    change aeval _ _ = _
    rw [map_sub]; rw [map_pow]; rw [aeval_C]; rw [aeval_X]; rw [Algebra.smul_def]; rw [mul_pow]; rw [root_X_pow_sub_C_pow]; rw [AdjoinRoot.algebr

Depends on / 依赖: AdjoinRoot, AdjoinRoot.algebraMap_eq, Algebra, Algebra.ofId, Algebra.smul_def, aeval_C, aeval_X, algHom_ext, algebraMap_eq, liftAlgHom, map_mul, map_one, map_pow, map_sub, mem_rootsOfUnity, mul_pow, mul_smul, one_mul, root_X_pow_sub_C_pow, smul_comm
-/
def autAdjoinRootXPowSubCHom :
    rootsOfUnity n K ->* (K[n√a] ->ₐ[K] K[n√a]) where
toFun η := liftAlgHom (X ^ n - C a) (Algebra.ofId _ _) (((η : Kˣ) : K) • (root _) : K[n√a]) by
    have := (mem_rootsOfUnity' _ _).mp η.prop
    change aeval _ _ = _
    rw [map_sub]; rw [map_pow]; rw [aeval_C]; rw [aeval_X]; rw [Algebra.smul_def]; rw [mul_pow]; rw [root_X_pow_sub_C_pow]; rw [AdjoinRoot.algebraMap_eq]; rw [← map_pow]; rw [this]; rw [map_one]; rw [one_mul]; rw [sub_self]
map_one' := algHom_ext by simp
map_mul' := fun ε η => algHom_ext by simp [mul_smul, smul_comm ((ε : Kˣ) : K)]

/-- The natural embedding of the roots of unity of `K` into `Gal(K[ⁿ√a]/K)`, by sending
`η ↦ (ⁿ√a ↦ η • ⁿ√a)`. This is an isomorphism when `K` contains a primitive root of unity.
See `autAdjoinRootXPowSubCEquiv`. -/
noncomputable
/--
Definition of `autAdjoinRootXPowSubC` / `autAdjoinRootXPowSubC` 的定义

English:
definition autAdjoinRootXPowSubC
  signature: :
  body: (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp (autAdjoinRootXPowSubCHom n a).toHomUnits

中文:
定义 autAdjoinRootXPowSubC
  签名: :
  定义体: (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp (autAdjoinRootXPowSubCHom n a).toHomUnits

Depends on / 依赖: AlgEquiv, AlgEquiv.algHomUnitsEquiv, algHomUnitsEquiv, autAdjoinRootXPowSubCHom, toHomUnits, toMonoidHom, toMonoidHom.comp
-/
def autAdjoinRootXPowSubC :
    rootsOfUnity n K ->* (K[n√a] ≃ₐ[K] K[n√a]) :=
  (AlgEquiv.algHomUnitsEquiv _ _).toMonoidHom.comp (autAdjoinRootXPowSubCHom n a).toHomUnits

variable {n}

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `autAdjoinRootXPowSubC_root` / 引理 `autAdjoinRootXPowSubC_root`

English:
lemma autAdjoinRootXPowSubC_root
  given: (η)
  proof: by
  dsimp [autAdjoinRootXPowSubC, autAdjoinRootXPowSubCHom, AlgEquiv.algHomUnitsEquiv]
  exact liftAlgHom_root _ (Algebra.ofId _ _) ..

中文:
引理 autAdjoinRootXPowSubC_root
  条件: (η)
  证明: by
  dsimp [autAdjoinRootXPowSubC, autAdjoinRootXPowSubCHom, AlgEquiv.algHomUnitsEquiv]
  exact liftAlgHom_root _ (Algebra.ofId _ _) ..

Depends on / 依赖: AlgEquiv, AlgEquiv.algHomUnitsEquiv, Algebra, Algebra.ofId, algHomUnitsEquiv, autAdjoinRootXPowSubC, autAdjoinRootXPowSubCHom, liftAlgHom_root
-/
lemma autAdjoinRootXPowSubC_root (η) :
    autAdjoinRootXPowSubC n a η (root _) = ((η : Kˣ) : K) • root _ := by
  dsimp [autAdjoinRootXPowSubC, autAdjoinRootXPowSubCHom, AlgEquiv.algHomUnitsEquiv]
  exact liftAlgHom_root _ (Algebra.ofId _ _) ..

variable {a}

/-- The inverse function of `autAdjoinRootXPowSubC` if `K` has all roots of unity.
See `autAdjoinRootXPowSubCEquiv`. -/
noncomputable
/--
Definition of `AdjoinRootXPowSubCEquivToRootsOfUnity` / `AdjoinRootXPowSubCEquivToRootsOfUnity` 的定义

English:
definition AdjoinRootXPowSubCEquivToRootsOfUnity
  signature: [NeZero n] (σ : K[n√a] ≃ₐ[K] K[n√a])
  body: letI := Fact.mk H
  letI : IsDomain K[n√a] := inferInstance
  letI := Classical.decEq K
  (rootsOfUnityEquivOfPrimitiveRoots (n := n) (algebraMap K K[n√a]).injective hζ).symm
    (rootsOfUnity.mkOfPowEq (if a = 0 then 1 else σ (root _) / root _) (by
    -- The if is needed in case `n = 1` and `a = 0

中文:
定义 AdjoinRootXPowSubCEquivToRootsOfUnity
  签名: [NeZero n] (σ : K[n√a] ≃ₐ[K] K[n√a])
  定义体: letI := Fact.mk H
  letI : IsDomain K[n√a] := inferInstance
  letI := Classical.decEq K
  (rootsOfUnityEquivOfPrimitiveRoots (n := n) (algebraMap K K[n√a]).injective hζ).symm
    (rootsOfUnity.mkOfPowEq (if a = 0 then 1 else σ (root _) / root _) (by
    -- The if is needed in case `n = 1` and `a = 0

Depends on / 依赖: Classical, Classical.decEq, Fact.mk, IsDomain, Semigroup, Semigroup.mem_center_iff, Submonoid, Submonoid.smul_def, algebraMap, injective, mem_center_iff, mkOfPowEq, rootsOfUnity, rootsOfUnity.mkOfPowEq, rootsOfUnityEquivOfPrimitiveRoots, simp_rw, smul_def, smul_smul
-/
def AdjoinRootXPowSubCEquivToRootsOfUnity [NeZero n] (σ : K[n√a] ≃ₐ[K] K[n√a]) :
    rootsOfUnity n K :=
  letI := Fact.mk H
  letI : IsDomain K[n√a] := inferInstance
  letI := Classical.decEq K
  (rootsOfUnityEquivOfPrimitiveRoots (n := n) (algebraMap K K[n√a]).injective hζ).symm
    (rootsOfUnity.mkOfPowEq (if a = 0 then 1 else σ (root _) / root _) (by
    -- The if is needed in case `n = 1` and `a = 0` and `K[n√a] = K`.
    split
    · exact one_pow _
    rw [div_pow]; rw [← map_pow]
    simp only [root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq, AlgEquiv.commutes]
    rw [div_self]
    rwa [Ne, map_eq_zero_iff _ (algebraMap K _).injective]))

/-- The equivalence between the roots of unity of `K` and `Gal(K[ⁿ√a]/K)`. -/
noncomputable
/--
Definition of `autAdjoinRootXPowSubCEquiv` / `autAdjoinRootXPowSubCEquiv` 的定义

English:
definition autAdjoinRootXPowSubCEquiv
  signature: [NeZero n]
  body: autAdjoinRootXPowSubC n a
  invFun := AdjoinRootXPowSubCEquivToRootsOfUnity hζ H
  left_inv := by
    intro η
    have := Fact.mk H
    have : IsDomain K[n√a] := inferInstance
    let : Algebra K K[n√a] := inferInstance
    apply (rootsOfUnityEquivOfPrimitiveRoots (algebraMap K K[n√a]).injective hζ)

中文:
定义 autAdjoinRootXPowSubCEquiv
  签名: [NeZero n]
  定义体: autAdjoinRootXPowSubC n a
  invFun := AdjoinRootXPowSubCEquivToRootsOfUnity hζ H
  left_inv := by
    intro η
    have := Fact.mk H
    have : IsDomain K[n√a] := inferInstance
    let : Algebra K K[n√a] := inferInstance
    apply (rootsOfUnityEquivOfPrimitiveRoots (algebraMap K K[n√a]).injective hζ)

Depends on / 依赖: SMulCommClass, SMulCommClass.symm, Submonoid, Submonoid.center, autAdjoinRootXPowSubC, center
-/
def autAdjoinRootXPowSubCEquiv [NeZero n] :
    rootsOfUnity n K ≃* (K[n√a] ≃ₐ[K] K[n√a]) where
  __ := autAdjoinRootXPowSubC n a
  invFun := AdjoinRootXPowSubCEquivToRootsOfUnity hζ H
  left_inv := by
    intro η
    have := Fact.mk H
    have : IsDomain K[n√a] := inferInstance
    let : Algebra K K[n√a] := inferInstance
    apply (rootsOfUnityEquivOfPrimitiveRoots (algebraMap K K[n√a]).injective hζ).injective
    ext
    simp only [AdjoinRoot.algebraMap_eq, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      autAdjoinRootXPowSubC_root, Algebra.smul_def, MulEquiv.apply_symm_apply,
      rootsOfUnity.val_mkOfPowEq_coe, val_rootsOfUnityEquivOfPrimitiveRoots_apply_coe,
      AdjoinRootXPowSubCEquivToRootsOfUnity]
    split_ifs with h
    · obtain rfl := not_imp_not.mp (fun hn => ne_zero_of_irreducible_X_pow_sub_C' hn H) h
      have : (η : Kˣ) = 1 := (pow_one _).symm.trans η.prop
      simp only [this, Units.val_one, map_one]
    · exact mul_div_cancel_right₀ _ (root_X_pow_sub_C_ne_zero' (NeZero.pos n) h)
  right_inv := by
    intro e
    have := Fact.mk H
    let : Algebra K K[n√a] := inferInstance
    apply AlgEquiv.coe_toAlgHom_injective
    apply AdjoinRoot.algHom_ext
    simp only [AdjoinRootXPowSubCEquivToRootsOfUnity, AdjoinRoot.algebraMap_eq, OneHom.toFun_eq_coe,
      MonoidHom.toOneHom_coe, AlgEquiv.coe_toAlgHom, autAdjoinRootXPowSubC_root, Algebra.smul_def]
    rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply]; rw [rootsOfUnity.val_mkOfPowEq_coe]
    split_ifs with h
    · obtain rfl := not_imp_not.mp (fun hn => ne_zero_of_irreducible_X_pow_sub_C' hn H) h
      rw [(pow_one _).symm.trans (root_X_pow_sub_C_pow 1 a)]; rw [one_mul]; rw [← AdjoinRoot.algebraMap_eq]; rw [AlgEquiv.commutes]
    · refine div_mul_cancel₀ _ (root_X_pow_sub_C_ne_zero' (NeZero.pos n) h)

/--
lemma `autAdjoinRootXPowSubCEquiv_root` / 引理 `autAdjoinRootXPowSubCEquiv_root`

English:
lemma autAdjoinRootXPowSubCEquiv_root
  given: [NeZero n] (η)
  proof: autAdjoinRootXPowSubC_root a η

中文:
引理 autAdjoinRootXPowSubCEquiv_root
  条件: [NeZero n] (η)
  证明: autAdjoinRootXPowSubC_root a η

Depends on / 依赖: autAdjoinRootXPowSubC_root
-/
lemma autAdjoinRootXPowSubCEquiv_root [NeZero n] (η) :
    autAdjoinRootXPowSubCEquiv hζ H η (root _) = ((η : Kˣ) : K) • root _ :=
  autAdjoinRootXPowSubC_root a η

/--
lemma `autAdjoinRootXPowSubCEquiv_symm_smul` / 引理 `autAdjoinRootXPowSubCEquiv_symm_smul`

English:
lemma autAdjoinRootXPowSubCEquiv_symm_smul
  given: [NeZero n] (σ)
  proof: by
  have := Fact.mk H
  simp only [autAdjoinRootXPowSubCEquiv, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk, AdjoinRootXPowSubCEquivToRootsOfUnity,
    AdjoinRoot.algebraMap_eq, rootsOfUnity.mkOfPowEq, Units.smul_def, Algebra.smul_def,
   

中文:
引理 autAdjoinRootXPowSubCEquiv_symm_smul
  条件: [NeZero n] (σ)
  证明: by
  have := Fact.mk H
  simp only [autAdjoinRootXPowSubCEquiv, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk, AdjoinRootXPowSubCEquivToRootsOfUnity,
    AdjoinRoot.algebraMap_eq, rootsOfUnity.mkOfPowEq, Units.smul_def, Algebra.smul_def,
   

Depends on / 依赖: AdjoinRoot, AdjoinRoot.algebraMap_eq, AdjoinRootXPowSubCEquivToRootsOfUnity, Algebra, Algebra.smul_def, Equiv.coe_fn_symm_mk, Fact.mk, MonoidHom, MonoidHom.toOneHom_coe, MulEquiv, MulEquiv.coe_mk, MulEquiv.symm_mk, OneHom, OneHom.toFun_eq_coe, Units.smul_def, Units.val_ofPowEqOne, algebraMap_eq, autAdjoinRootXPowSubCEquiv, coe_fn_symm_mk, coe_mk
-/
lemma autAdjoinRootXPowSubCEquiv_symm_smul [NeZero n] (σ) :
    ((autAdjoinRootXPowSubCEquiv hζ H).symm σ : Kˣ) • (root _ : K[n√a]) = σ (root _) := by
  have := Fact.mk H
  simp only [autAdjoinRootXPowSubCEquiv, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MulEquiv.symm_mk, MulEquiv.coe_mk, Equiv.coe_fn_symm_mk, AdjoinRootXPowSubCEquivToRootsOfUnity,
    AdjoinRoot.algebraMap_eq, rootsOfUnity.mkOfPowEq, Units.smul_def, Algebra.smul_def,
    rootsOfUnityEquivOfPrimitiveRoots_symm_apply, Units.val_ofPowEqOne, ite_mul, one_mul]
  simp_rw [← root_X_pow_sub_C_eq_zero_iff H]
  split_ifs with h
  · rw [h, map_zero]
  · rw [div_mul_cancel₀ _ h]

end AdjoinRoot

/-! ### Galois Group of `IsSplittingField K L (X ^ n - C a)` -/

section IsSplittingField

variable {a}
variable {L : Type*} [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)]

include hζ in
/--
lemma `isSplittingField_AdjoinRoot_X_pow_sub_C` / 引理 `isSplittingField_AdjoinRoot_X_pow_sub_C`

English:
lemma isSplittingField_AdjoinRoot_X_pow_sub_C
  proof: Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    IsSplittingField K K[n√a] (X ^ n - C a) := by
  have := Fact.mk H
  let : Algebra K K[n√a] := inferInstance
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hζ
    rw

中文:
引理 isSplittingField_AdjoinRoot_X_pow_sub_C
  证明: Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    IsSplittingField K K[n√a] (X ^ n - C a) := by
  have := Fact.mk H
  let : Algebra K K[n√a] := inferInstance
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hζ
    rw

Depends on / 依赖: Fact.mk
-/
lemma isSplittingField_AdjoinRoot_X_pow_sub_C :
    haveI := Fact.mk H
    letI : Algebra K K[n√a] := inferInstance
    IsSplittingField K K[n√a] (X ^ n - C a) := by
  have := Fact.mk H
  let : Algebra K K[n√a] := inferInstance
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hζ
    rw [mem_primitiveRoots (Nat.pos_of_ne_zero <| ne_zero_of_irreducible_X_pow_sub_C H)] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective)
      (root_X_pow_sub_C_pow n a)
  · rw [eq_top_iff, ← AdjoinRoot.adjoinRoot_eq_top]
    apply Algebra.adjoin_mono
    have := ne_zero_of_irreducible_X_pow_sub_C H
    rw [Set.singleton_subset_iff]; rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero
      (Nat.pos_of_ne_zero this) a)]; rw [aeval_def]; rw [AdjoinRoot.algebraMap_eq]; rw [AdjoinRoot.eval₂_root]

variable {α : L} (hα : α ^ n = algebraMap K L a)

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, then a choice of `ⁿ√a` gives an equivalence of
`L` with `K[n√a]`. -/
noncomputable
/--
Definition of `adjoinRootXPowSubCEquiv` / `adjoinRootXPowSubCEquiv` 的定义

English:
definition adjoinRootXPowSubCEquiv
  signature: (hζ : (primitiveRoots n K).Nonempty) (H : Irreducible (X ^ n - C a))
  body: .ofBijective (AdjoinRoot.liftAlgHom (X ^ n - C a) (Algebra.ofId _ _) α (by simp [hα])) by
    have := Fact.mk H
    let := isSplittingField_AdjoinRoot_X_pow_sub_C hζ H
    refine ⟨(liftAlgHom (X ^ n - C a) _ α _).injective, ?_⟩
    rw [← AlgHom.range_eq_top]; rw [← IsSplittingField.adjoin_rootSet _ 

中文:
定义 adjoinRootXPowSubCEquiv
  签名: (hζ : (primitiveRoots n K).非空) (H : 不可约 (X ^ n - C a))
  定义体: .ofBijective (AdjoinRoot.liftAlgHom (X ^ n - C a) (Algebra.ofId _ _) α (by simp [hα])) by
    have := Fact.mk H
    let := isSplittingField_AdjoinRoot_X_pow_sub_C hζ H
    refine ⟨(liftAlgHom (X ^ n - C a) _ α _).injective, ?_⟩
    rw [← AlgHom.range_eq_top]; rw [← IsSplittingField.adjoin_rootSet _ 

Depends on / 依赖: AdjoinRoot, AdjoinRoot.liftAlgHom, AlgHom, AlgHom.range_eq_top, Algebra, Algebra.ofId, Fact.mk, IsSplittingField, IsSplittingField.adjoin_rootSet, IsSplittingField.splits, Splits, Splits.adjoin_rootSet_eq_range, adjoin_rootSet, adjoin_rootSet_eq_range, eq_comm, injective, isSplittingField_AdjoinRoot_X_pow_sub_C, liftAlgHom, ofBijective, range_eq_top
-/
def adjoinRootXPowSubCEquiv (hζ : (primitiveRoots n K).Nonempty) (H : Irreducible (X ^ n - C a))
    (hα : α ^ n = algebraMap K L a) : K[n√a] ≃ₐ[K] L :=
.ofBijective (AdjoinRoot.liftAlgHom (X ^ n - C a) (Algebra.ofId _ _) α (by simp [hα])) by
    have := Fact.mk H
    let := isSplittingField_AdjoinRoot_X_pow_sub_C hζ H
    refine ⟨(liftAlgHom (X ^ n - C a) _ α _).injective, ?_⟩
    rw [← AlgHom.range_eq_top]; rw [← IsSplittingField.adjoin_rootSet _ (X ^ n - C a)]; rw [eq_comm]; rw [Splits.adjoin_rootSet_eq_range]; rw [IsSplittingField.adjoin_rootSet]
    exact IsSplittingField.splits _ _

/--
lemma `adjoinRootXPowSubCEquiv_root` / 引理 `adjoinRootXPowSubCEquiv_root`

English:
lemma adjoinRootXPowSubCEquiv_root
  proof: by
  rw [adjoinRootXPowSubCEquiv]; rw [AlgEquiv.coe_ofBijective]; rw [liftAlgHom_root]

中文:
引理 adjoinRootXPowSubCEquiv_root
  证明: by
  rw [adjoinRootXPowSubCEquiv]; rw [AlgEquiv.coe_ofBijective]; rw [liftAlgHom_root]

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_ofBijective, Commute, Commute.left_comm, adjoinRootXPowSubCEquiv, coe_ofBijective, left_comm, liftAlgHom_root, m.prop.comm
-/
lemma adjoinRootXPowSubCEquiv_root :
    adjoinRootXPowSubCEquiv hζ H hα (root _) = α := by
  rw [adjoinRootXPowSubCEquiv]; rw [AlgEquiv.coe_ofBijective]; rw [liftAlgHom_root]

/--
lemma `adjoinRootXPowSubCEquiv_symm_eq_root` / 引理 `adjoinRootXPowSubCEquiv_symm_eq_root`

English:
lemma adjoinRootXPowSubCEquiv_symm_eq_root
  proof: by
  apply (adjoinRootXPowSubCEquiv hζ H hα).injective
  rw [(adjoinRootXPowSubCEquiv hζ H hα).apply_symm_apply]; rw [adjoinRootXPowSubCEquiv_root]

include hζ H hα in

中文:
引理 adjoinRootXPowSubCEquiv_symm_eq_root
  证明: by
  apply (adjoinRootXPowSubCEquiv hζ H hα).injective
  rw [(adjoinRootXPowSubCEquiv hζ H hα).apply_symm_apply]; rw [adjoinRootXPowSubCEquiv_root]

include hζ H hα in

Depends on / 依赖: SMulCommClass, SMulCommClass.symm, adjoinRootXPowSubCEquiv, adjoinRootXPowSubCEquiv_root, apply_symm_apply, injective
-/
lemma adjoinRootXPowSubCEquiv_symm_eq_root :
    (adjoinRootXPowSubCEquiv hζ H hα).symm α = root _ := by
  apply (adjoinRootXPowSubCEquiv hζ H hα).injective
  rw [(adjoinRootXPowSubCEquiv hζ H hα).apply_symm_apply]; rw [adjoinRootXPowSubCEquiv_root]

include hζ H hα in
/--
lemma `Algebra.adjoin_root_eq_top_of_isSplittingField` / 引理 `Algebra.adjoin_root_eq_top_of_isSplittingField`

English:
lemma Algebra.adjoin_root_eq_top_of_isSplittingField
  proof: by
  apply Subalgebra.map_injective (B := K[n√a]) (f := (adjoinRootXPowSubCEquiv hζ H hα).symm)
    (adjoinRootXPowSubCEquiv hζ H hα).symm.injective
  rw [Algebra.map_top]; rw [(AlgHom.range_eq_top _).mpr
    (adjoinRootXPowSubCEquiv hζ H hα).symm.surjective]; rw [AlgHom.map_adjoin]; rw [Set.image_s

中文:
引理 代数.adjoin_root_eq_top_of_isSplittingField
  证明: by
  apply Subalgebra.map_injective (B := K[n√a]) (f := (adjoinRootXPowSubCEquiv hζ H hα).symm)
    (adjoinRootXPowSubCEquiv hζ H hα).symm.injective
  rw [Algebra.map_top]; rw [(AlgHom.range_eq_top _).mpr
    (adjoinRootXPowSubCEquiv hζ H hα).symm.surjective]; rw [AlgHom.map_adjoin]; rw [Set.image_s

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_toAlgHom, AlgHom, AlgHom.map_adjoin, AlgHom.range_eq_top, Algebra, Algebra.map_top, Set.image_singleton, Subalgebra, Subalgebra.map_injective, adjoinRootXPowSubCEquiv, adjoinRootXPowSubCEquiv_symm_eq_root, adjoinRoot_eq_top, coe_toAlgHom, image_singleton, injective, map_adjoin, map_injective, map_top, range_eq_top
-/
lemma Algebra.adjoin_root_eq_top_of_isSplittingField :
    Algebra.adjoin K {α} = ⊤ := by
  apply Subalgebra.map_injective (B := K[n√a]) (f := (adjoinRootXPowSubCEquiv hζ H hα).symm)
    (adjoinRootXPowSubCEquiv hζ H hα).symm.injective
  rw [Algebra.map_top]; rw [(AlgHom.range_eq_top _).mpr
    (adjoinRootXPowSubCEquiv hζ H hα).symm.surjective]; rw [AlgHom.map_adjoin]; rw [Set.image_singleton]; rw [AlgEquiv.coe_toAlgHom]; rw [adjoinRootXPowSubCEquiv_symm_eq_root]; rw [adjoinRoot_eq_top]

include hζ H hα in
/--
lemma `IntermediateField.adjoin_root_eq_top_of_isSplittingField` / 引理 `IntermediateField.adjoin_root_eq_top_of_isSplittingField`

English:
lemma IntermediateField.adjoin_root_eq_top_of_isSplittingField
  proof: by
  refine (IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ ?_).symm
  exact (Algebra.adjoin_root_eq_top_of_isSplittingField hζ H hα).symm

中文:
引理 中间域.adjoin_root_eq_top_of_isSplittingField
  证明: by
  refine (IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ ?_).symm
  exact (Algebra.adjoin_root_eq_top_of_isSplittingField hζ H hα).symm

Depends on / 依赖: Algebra, Algebra.adjoin_root_eq_top_of_isSplittingField, IntermediateField, IntermediateField.eq_adjoin_of_eq_algebra_adjoin, adjoin_root_eq_top_of_isSplittingField, eq_adjoin_of_eq_algebra_adjoin
-/
lemma IntermediateField.adjoin_root_eq_top_of_isSplittingField :
    K⟮α⟯ = ⊤ := by
  refine (IntermediateField.eq_adjoin_of_eq_algebra_adjoin _ _ _ ?_).symm
  exact (Algebra.adjoin_root_eq_top_of_isSplittingField hζ H hα).symm

variable (a) (L)

/-- An arbitrary choice of `ⁿ√a` in the splitting field of `Xⁿ - a`. -/
noncomputable
/--
Definition of `rootOfSplitsXPowSubC` / `rootOfSplitsXPowSubC` 的定义

English:
abbreviation rootOfSplitsXPowSubC
  signature: (hn : 0 < n) (a : K)
  body: (rootOfSplits (IsSplittingField.splits L (X ^ n - C a))
      (by simpa [degree_X_pow_sub_C hn] using Nat.pos_iff_ne_zero.mp hn))

中文:
缩写 rootOfSplitsXPowSubC
  签名: (hn : 0 < n) (a : K)
  定义体: (rootOfSplits (IsSplittingField.splits L (X ^ n - C a))
      (by simpa [degree_X_pow_sub_C hn] using Nat.pos_iff_ne_zero.mp hn))

Depends on / 依赖: IsSplittingField, IsSplittingField.splits, Nat.pos_iff_ne_zero.mp, degree_X_pow_sub_C, pos_iff_ne_zero, rootOfSplits, splits
-/
abbrev rootOfSplitsXPowSubC (hn : 0 < n) (a : K)
    (L) [Field L] [Algebra K L] [IsSplittingField K L (X ^ n - C a)] : L :=
  (rootOfSplits (IsSplittingField.splits L (X ^ n - C a))
      (by simpa [degree_X_pow_sub_C hn] using Nat.pos_iff_ne_zero.mp hn))

/--
lemma `rootOfSplitsXPowSubC_pow` / 引理 `rootOfSplitsXPowSubC_pow`

English:
lemma rootOfSplitsXPowSubC_pow
  given: [NeZero n]
  proof: by
  have := eval_rootOfSplits (IsSplittingField.splits L (X ^ n - C a))
    (by simp [degree_X_pow_sub_C (NeZero.pos n), NeZero.ne n])
  simpa only [eval_map, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] using this

中文:
引理 rootOfSplitsXPowSubC_pow
  条件: [NeZero n]
  证明: by
  have := eval_rootOfSplits (IsSplittingField.splits L (X ^ n - C a))
    (by simp [degree_X_pow_sub_C (NeZero.pos n), NeZero.ne n])
  simpa only [eval_map, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] using this

Depends on / 依赖: IsSplittingField, IsSplittingField.splits, NeZero, NeZero.ne, NeZero.pos, degree_X_pow_sub_C, eval_map, eval_rootOfSplits, splits, sub_eq_zero
-/
lemma rootOfSplitsXPowSubC_pow [NeZero n] :
    (rootOfSplitsXPowSubC (NeZero.pos n) a L) ^ n = algebraMap K L a := by
  have := eval_rootOfSplits (IsSplittingField.splits L (X ^ n - C a))
    (by simp [degree_X_pow_sub_C (NeZero.pos n), NeZero.ne n])
  simpa only [eval_map, eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] using this

variable {a}

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, then `Gal(L/K)` is isomorphic to the
roots of unity in `K` if `K` contains all of them.
Note that this does not depend on a choice of `ⁿ√a`. -/
noncomputable
/--
Definition of `autEquivRootsOfUnity` / `autEquivRootsOfUnity` 的定义

English:
definition autEquivRootsOfUnity
  signature: [NeZero n]
  body: (AlgEquiv.autCongr (adjoinRootXPowSubCEquiv hζ H (rootOfSplitsXPowSubC_pow a L)).symm).trans
    (autAdjoinRootXPowSubCEquiv hζ H).symm

中文:
定义 autEquivRootsOfUnity
  签名: [NeZero n]
  定义体: (AlgEquiv.autCongr (adjoinRootXPowSubCEquiv hζ H (rootOfSplitsXPowSubC_pow a L)).symm).trans
    (autAdjoinRootXPowSubCEquiv hζ H).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.autCongr, adjoinRootXPowSubCEquiv, autAdjoinRootXPowSubCEquiv, autCongr, rootOfSplitsXPowSubC_pow
-/
def autEquivRootsOfUnity [NeZero n] :
    Gal(L/K) ≃* (rootsOfUnity n K) :=
  (AlgEquiv.autCongr (adjoinRootXPowSubCEquiv hζ H (rootOfSplitsXPowSubC_pow a L)).symm).trans
    (autAdjoinRootXPowSubCEquiv hζ H).symm

/--
lemma `autEquivRootsOfUnity_apply_rootOfSplit` / 引理 `autEquivRootsOfUnity_apply_rootOfSplit`

English:
lemma autEquivRootsOfUnity_apply_rootOfSplit
  given: [NeZero n] (σ : Gal(L/K))
  proof: by
  obtain ⟨η, rfl⟩ := (autEquivRootsOfUnity hζ H L).symm.surjective σ
  rw [MulEquiv.apply_symm_apply]; rw [autEquivRootsOfUnity]
  simp only [MulEquiv.symm_trans_apply, AlgEquiv.autCongr_symm, AlgEquiv.symm_symm,
    MulEquiv.symm_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    adjoinRoo

中文:
引理 autEquivRootsOfUnity_apply_rootOfSplit
  条件: [NeZero n] (σ : Gal(L/K))
  证明: by
  obtain ⟨η, rfl⟩ := (autEquivRootsOfUnity hζ H L).symm.surjective σ
  rw [MulEquiv.apply_symm_apply]; rw [autEquivRootsOfUnity]
  simp only [MulEquiv.symm_trans_apply, AlgEquiv.autCongr_symm, AlgEquiv.symm_symm,
    MulEquiv.symm_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    adjoinRoo

Depends on / 依赖: AlgEquiv, AlgEquiv.autCongr_apply, AlgEquiv.autCongr_symm, AlgEquiv.symm_symm, AlgEquiv.trans_apply, MulEquiv, MulEquiv.apply_symm_apply, MulEquiv.symm_symm, MulEquiv.symm_trans_apply, adjoinRootXPowSubCEquiv_root, adjoinRootXPowSubCEquiv_symm_eq_root, apply_symm_apply, autAdjoinRootXPowSubCEquiv_root, autCongr_apply, autCongr_symm, autEquivRootsOfUnity, map_smul, surjective, symm.surjective, symm_symm
-/
lemma autEquivRootsOfUnity_apply_rootOfSplit [NeZero n] (σ : Gal(L/K)) :
    σ (rootOfSplitsXPowSubC (NeZero.pos n) a L) =
      autEquivRootsOfUnity hζ H L σ • (rootOfSplitsXPowSubC (NeZero.pos n) a L) := by
  obtain ⟨η, rfl⟩ := (autEquivRootsOfUnity hζ H L).symm.surjective σ
  rw [MulEquiv.apply_symm_apply]; rw [autEquivRootsOfUnity]
  simp only [MulEquiv.symm_trans_apply, AlgEquiv.autCongr_symm, AlgEquiv.symm_symm,
    MulEquiv.symm_symm, AlgEquiv.autCongr_apply, AlgEquiv.trans_apply,
    adjoinRootXPowSubCEquiv_symm_eq_root, autAdjoinRootXPowSubCEquiv_root, map_smul,
    adjoinRootXPowSubCEquiv_root]
  rfl

include hα in
/--
lemma `autEquivRootsOfUnity_smul` / 引理 `autEquivRootsOfUnity_smul`

English:
lemma autEquivRootsOfUnity_smul
  given: [NeZero n] (σ : Gal(L/K))
  proof: by
  have ⟨ζ, hζ'⟩ := hζ
  have hn := NeZero.pos n
  rw [mem_primitiveRoots hn] at hζ'
  rw [← mem_nthRoots hn]; rw [(hζ'.map_of_injective (algebraMap K L).injective).nthRoots_eq
    (rootOfSplitsXPowSubC_pow a L)] at hα
  simp only [Multiset.mem_map, Multiset.mem_range] at hα
  obtain ⟨i, _, rfl⟩ :

中文:
引理 autEquivRootsOfUnity_smul
  条件: [NeZero n] (σ : Gal(L/K))
  证明: by
  have ⟨ζ, hζ'⟩ := hζ
  have hn := NeZero.pos n
  rw [mem_primitiveRoots hn] at hζ'
  rw [← mem_nthRoots hn]; rw [(hζ'.map_of_injective (algebraMap K L).injective).nthRoots_eq
    (rootOfSplitsXPowSubC_pow a L)] at hα
  simp only [Multiset.mem_map, Multiset.mem_range] at hα
  obtain ⟨i, _, rfl⟩ :

Depends on / 依赖: Algebra, Algebra.smul_def, Multiset, Multiset.mem_map, Multiset.mem_range, NeZero, NeZero.pos, algebraMap, autEquivRootsOfUnity_apply_rootOfSplit, injective, map_of_injective, map_pow, map_smul, mem_map, mem_nthRoots, mem_primitiveRoots, mem_range, nthRoots_eq, rootOfSplitsXPowSubC_pow, smul_comm
-/
lemma autEquivRootsOfUnity_smul [NeZero n] (σ : Gal(L/K)) :
    autEquivRootsOfUnity hζ H L σ • α = σ α := by
  have ⟨ζ, hζ'⟩ := hζ
  have hn := NeZero.pos n
  rw [mem_primitiveRoots hn] at hζ'
  rw [← mem_nthRoots hn]; rw [(hζ'.map_of_injective (algebraMap K L).injective).nthRoots_eq
    (rootOfSplitsXPowSubC_pow a L)] at hα
  simp only [Multiset.mem_map, Multiset.mem_range] at hα
  obtain ⟨i, _, rfl⟩ := hα
  simp only [← map_pow, ← Algebra.smul_def, map_smul,
    autEquivRootsOfUnity_apply_rootOfSplit hζ H L]
  exact smul_comm _ _ _

/-- Suppose `L/K` is the splitting field of `Xⁿ - a`, and `ζ` is an `n`-th primitive root of unity
in `K`, then `Gal(L/K)` is isomorphic to `ZMod n`. -/
noncomputable
/--
Definition of `autEquivZmod` / `autEquivZmod` 的定义

English:
definition autEquivZmod
  signature: [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n)
  body: haveI hn := ne_zero_of_irreducible_X_pow_sub_C H
  (autEquivRootsOfUnity ⟨ζ, (mem_primitiveRoots <| Nat.pos_of_ne_zero hn).mpr hζ⟩ H L).trans
    ((MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq (hζ.isUnit_unit' hn)).symm).trans
        (hζ.isUnit_unit' hn).zmodEquivZPowers.symm.toMultiplicative

中文:
定义 autEquivZmod
  签名: [NeZero n] {ζ : K} (hζ : 是PrimitiveRoot ζ n)
  定义体: haveI hn := ne_zero_of_irreducible_X_pow_sub_C H
  (autEquivRootsOfUnity ⟨ζ, (mem_primitiveRoots <| Nat.pos_of_ne_zero hn).mpr hζ⟩ H L).trans
    ((MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq (hζ.isUnit_unit' hn)).symm).trans
        (hζ.isUnit_unit' hn).zmodEquivZPowers.symm.toMultiplicative

Depends on / 依赖: IsPrimitiveRoot, IsPrimitiveRoot.zpowers_eq, MulEquiv, MulEquiv.subgroupCongr, Nat.pos_of_ne_zero, autEquivRootsOfUnity, isUnit_unit, mem_primitiveRoots, ne_zero_of_irreducible_X_pow_sub_C, pos_of_ne_zero, subgroupCongr, toMultiplicativeRight, zmodEquivZPowers, zmodEquivZPowers.symm.toMultiplicativeRight, zpowers_eq
-/
def autEquivZmod [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) :
    Gal(L/K) ≃* Multiplicative (ZMod n) :=
  haveI hn := ne_zero_of_irreducible_X_pow_sub_C H
  (autEquivRootsOfUnity ⟨ζ, (mem_primitiveRoots <| Nat.pos_of_ne_zero hn).mpr hζ⟩ H L).trans
    ((MulEquiv.subgroupCongr (IsPrimitiveRoot.zpowers_eq (hζ.isUnit_unit' hn)).symm).trans
        (hζ.isUnit_unit' hn).zmodEquivZPowers.symm.toMultiplicativeRight)

include hα in
/--
lemma `autEquivZmod_symm_apply_intCast` / 引理 `autEquivZmod_symm_apply_intCast`

English:
lemma autEquivZmod_symm_apply_intCast
  given: [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : Int)
  proof: by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  rw [← autEquivRootsOfUnity_smul ⟨ζ]; rw [(mem_primitiveRoots hn).mpr hζ⟩ H L hα]
  simp [MulEquiv.subgroupCongr_symm_apply, Subgroup.smul_def, Units.smul_def, autEquivZmod]

include hα in

中文:
引理 autEquivZmod_symm_apply_intCast
  条件: [NeZero n] {ζ : K} (hζ : 是PrimitiveRoot ζ n) (m : 整数)
  证明: by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  rw [← autEquivRootsOfUnity_smul ⟨ζ]; rw [(mem_primitiveRoots hn).mpr hζ⟩ H L hα]
  simp [MulEquiv.subgroupCongr_symm_apply, Subgroup.smul_def, Units.smul_def, autEquivZmod]

include hα in

Depends on / 依赖: MulEquiv, MulEquiv.subgroupCongr_symm_apply, Nat.pos_iff_ne_zero.mpr, Subgroup, Subgroup.smul_def, Units.smul_def, autEquivRootsOfUnity_smul, autEquivZmod, mem_primitiveRoots, ne_zero_of_irreducible_X_pow_sub_C, pos_iff_ne_zero, smul_def, subgroupCongr_symm_apply
-/
lemma autEquivZmod_symm_apply_intCast [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : Int) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  rw [← autEquivRootsOfUnity_smul ⟨ζ]; rw [(mem_primitiveRoots hn).mpr hζ⟩ H L hα]
  simp [MulEquiv.subgroupCongr_symm_apply, Subgroup.smul_def, Units.smul_def, autEquivZmod]

include hα in
/--
lemma `autEquivZmod_symm_apply_natCast` / 引理 `autEquivZmod_symm_apply_natCast`

English:
lemma autEquivZmod_symm_apply_natCast
  given: [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : Nat)
  proof: by
  simpa only [Int.cast_natCast, zpow_natCast] using autEquivZmod_symm_apply_intCast H L hα hζ m

include hζ H in

中文:
引理 autEquivZmod_symm_apply_natCast
  条件: [NeZero n] {ζ : K} (hζ : 是PrimitiveRoot ζ n) (m : 自然数)
  证明: by
  simpa only [Int.cast_natCast, zpow_natCast] using autEquivZmod_symm_apply_intCast H L hα hζ m

include hζ H in

Depends on / 依赖: Int.cast_natCast, autEquivZmod_symm_apply_intCast, cast_natCast, zpow_natCast
-/
lemma autEquivZmod_symm_apply_natCast [NeZero n] {ζ : K} (hζ : IsPrimitiveRoot ζ n) (m : Nat) :
    (autEquivZmod H L hζ).symm (Multiplicative.ofAdd (m : ZMod n)) α = ζ ^ m • α := by
  simpa only [Int.cast_natCast, zpow_natCast] using autEquivZmod_symm_apply_intCast H L hα hζ m

include hζ H in
/--
lemma `isCyclic_of_isSplittingField_X_pow_sub_C` / 引理 `isCyclic_of_isSplittingField_X_pow_sub_C`

English:
lemma isCyclic_of_isSplittingField_X_pow_sub_C
  given: [NeZero n]
  statement: IsCyclic Gal(L/K)
  proof: have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  isCyclic_of_surjective _
    (autEquivZmod H _ <| (mem_primitiveRoots hn).mp hζ.choose_spec).symm.surjective

include hζ H in

中文:
引理 isCyclic_of_isSplittingField_X_pow_sub_C
  条件: [NeZero n]
  结论: 是循环 Gal(L/K)
  证明: have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  isCyclic_of_surjective _
    (autEquivZmod H _ <| (mem_primitiveRoots hn).mp hζ.choose_spec).symm.surjective

include hζ H in

Depends on / 依赖: Nat.pos_iff_ne_zero.mpr, autEquivZmod, choose_spec, isCyclic_of_surjective, mem_primitiveRoots, ne_zero_of_irreducible_X_pow_sub_C, pos_iff_ne_zero, surjective, symm.surjective
-/
lemma isCyclic_of_isSplittingField_X_pow_sub_C [NeZero n] : IsCyclic Gal(L/K) :=
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  isCyclic_of_surjective _
    (autEquivZmod H _ <| (mem_primitiveRoots hn).mp hζ.choose_spec).symm.surjective

include hζ H in
/--
lemma `isGalois_of_isSplittingField_X_pow_sub_C` / 引理 `isGalois_of_isSplittingField_X_pow_sub_C`

English:
lemma isGalois_of_isSplittingField_X_pow_sub_C
  statement: IsGalois K L
  proof: IsGalois.of_separable_splitting_field (separable_X_pow_sub_C_of_irreducible hζ a H)

include hζ H in

中文:
引理 isGalois_of_isSplittingField_X_pow_sub_C
  结论: 是Galois K L
  证明: IsGalois.of_separable_splitting_field (separable_X_pow_sub_C_of_irreducible hζ a H)

include hζ H in

Depends on / 依赖: IsGalois, IsGalois.of_separable_splitting_field, of_separable_splitting_field, separable_X_pow_sub_C_of_irreducible
-/
lemma isGalois_of_isSplittingField_X_pow_sub_C : IsGalois K L :=
  IsGalois.of_separable_splitting_field (separable_X_pow_sub_C_of_irreducible hζ a H)

include hζ H in
/--
lemma `finrank_of_isSplittingField_X_pow_sub_C` / 引理 `finrank_of_isSplittingField_X_pow_sub_C`

English:
lemma finrank_of_isSplittingField_X_pow_sub_C
  statement: Module.finrank K L = n
  proof: by
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ n - C a)
  have := isGalois_of_isSplittingField_X_pow_sub_C hζ H L
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  have : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C H⟩
  rw [← IsGalois.card_aut_eq_fi

中文:
引理 finrank_of_isSplittingField_X_pow_sub_C
  结论: 模.finrank K L = n
  证明: by
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ n - C a)
  have := isGalois_of_isSplittingField_X_pow_sub_C hζ H L
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  have : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C H⟩
  rw [← IsGalois.card_aut_eq_fi

Depends on / 依赖: IsGalois, IsGalois.card_aut_eq_finrank, IsSplittingField, Multiplicative, Multiplicative.toAdd, Nat.card_congr, Nat.card_zmod, Nat.pos_iff_ne_zero.mpr, NeZero, Polynomial, Polynomial.IsSplittingField.finiteDimensional, autEquivZmod, card_aut_eq_finrank, card_congr, card_zmod, choose_spec, finiteDimensional, isGalois_of_isSplittingField_X_pow_sub_C, mem_primitiveRoots, ne_zero_of_irreducible_X_pow_sub_C
-/
lemma finrank_of_isSplittingField_X_pow_sub_C : Module.finrank K L = n := by
  have := Polynomial.IsSplittingField.finiteDimensional L (X ^ n - C a)
  have := isGalois_of_isSplittingField_X_pow_sub_C hζ H L
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  have : NeZero n := ⟨ne_zero_of_irreducible_X_pow_sub_C H⟩
  rw [← IsGalois.card_aut_eq_finrank]; rw [Nat.card_congr ((autEquivZmod H L <|
    (mem_primitiveRoots hn).mp hζ.choose_spec).toEquiv.trans Multiplicative.toAdd)]; rw [Nat.card_zmod]

end IsSplittingField

/-! ### Cyclic extensions of order `n` when `K` has all `n`-th roots of unity. -/

section IsCyclic

variable {L} [Field L] [Algebra K L] [FiniteDimensional K L]
variable (hK : (primitiveRoots (Module.finrank K L) K).Nonempty)

open Module
variable (K L)

include hK in
/--
lemma `exists_root_adjoin_eq_top_of_isCyclic` / 引理 `exists_root_adjoin_eq_top_of_isCyclic`

English:
lemma exists_root_adjoin_eq_top_of_isCyclic
  given: [IsGalois K L] [IsCyclic Gal(L/K)]
  proof: by
  -- Let `ζ` be an `n`-th root of unity, and `σ` be a generator of `Gal(L/K)`.
  have ⟨ζ, hζ⟩ := hK
  rw [mem_primitiveRoots finrank_pos] at hζ
  obtain ⟨σ, hσ⟩ := ‹IsCyclic Gal(L/K)›
  have hσ' := orderOf_eq_card_of_forall_mem_zpowers hσ
  -- Since the minimal polynomial of `σ` over `K` is `Xⁿ -

中文:
引理 存在_root_adjoin_eq_top_of_isCyclic
  条件: [是Galois K L] [是循环 Gal(L/K)]
  证明: by
  -- Let `ζ` be an `n`-th root of unity, and `σ` be a generator of `Gal(L/K)`.
  have ⟨ζ, hζ⟩ := hK
  rw [mem_primitiveRoots finrank_pos] at hζ
  obtain ⟨σ, hσ⟩ := ‹IsCyclic Gal(L/K)›
  have hσ' := orderOf_eq_card_of_forall_mem_zpowers hσ
  -- Since the minimal polynomial of `σ` over `K` is `Xⁿ -
-/
lemma exists_root_adjoin_eq_top_of_isCyclic [IsGalois K L] [IsCyclic Gal(L/K)] :
    exists (α : L), α ^ (finrank K L) in Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤ := by
  -- Let `ζ` be an `n`-th root of unity, and `σ` be a generator of `Gal(L/K)`.
  have ⟨ζ, hζ⟩ := hK
  rw [mem_primitiveRoots finrank_pos] at hζ
  obtain ⟨σ, hσ⟩ := ‹IsCyclic Gal(L/K)›
  have hσ' := orderOf_eq_card_of_forall_mem_zpowers hσ
  -- Since the minimal polynomial of `σ` over `K` is `Xⁿ - 1`,
  -- `σ` has an eigenvector `v` with eigenvalue `ζ`.
  have : IsRoot (minpoly K σ.toLinearMap) ζ := by
    rw [IsGalois.card_aut_eq_finrank] at hσ'
    simpa [minpoly_algEquiv_toLinearMap σ (isOfFinOrder_of_finite σ), hσ',
      sub_eq_zero] using hζ.pow_eq_one
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot this).exists_hasEigenvector
  have hv' := hv.pow_apply
  simp_rw [← AlgEquiv.pow_toLinearMap, AlgEquiv.toLinearMap_apply] at hv'
  -- We claim that `v` is the desired root.
  refine ⟨v, ?_, ?_⟩
  · -- Since `v ^ n` is fixed by `σ` (`σ (v ^ n) = ζ ^ n • v ^ n = v ^ n`), it is in `K`.
    rw [← IntermediateField.mem_bot]; rw [← OrderIso.map_bot IsGalois.intermediateFieldEquivSubgroup.symm]
    intro ⟨σ', hσ'⟩
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    rw [smul_pow']; rw [Submonoid.smul_def]; rw [AlgEquiv.smul_def]; rw [hv']; rw [smul_pow]; rw [← pow_mul]; rw [mul_comm]; rw [pow_mul]; rw [hζ.pow_eq_one]; rw [one_pow]; rw [one_smul]
  · -- Since `σ` does not fix `K⟮α⟯`, `K⟮α⟯` is `L`.
    apply IsGalois.intermediateFieldEquivSubgroup.injective
    rw [map_top]; rw [eq_top_iff]
    intro σ' hσ'
    obtain ⟨n, rfl : σ ^ n = σ'⟩ := mem_powers_iff_mem_zpowers.mpr (hσ σ')
    have := hσ' ⟨v, IntermediateField.mem_adjoin_simple_self K v⟩
    simp only [AlgEquiv.smul_def, hv'] at this
    conv_rhs at this => rw [← one_smul K v]
    obtain ⟨k, rfl⟩ := hζ.dvd_of_pow_eq_one n (smul_left_injective K hv.2 this)
    rw [pow_mul]; rw [← IsGalois.card_aut_eq_finrank]; rw [pow_card_eq_one']; rw [one_pow]
    exact one_mem _

variable {K L}

/--
lemma `irreducible_X_pow_sub_C_of_root_adjoin_eq_top` / 引理 `irreducible_X_pow_sub_C_of_root_adjoin_eq_top`

English:
lemma irreducible_X_pow_sub_C_of_root_adjoin_eq_top
  proof: by
  have : X ^ (finrank K L) - C a = minpoly K α := by
    refine minpoly.unique _ _ (monic_X_pow_sub_C _ finrank_pos.ne.symm) ?_ ?_
    · simp only [aeval_def, eval₂_sub, eval₂_X_pow, ha, eval₂_C, sub_self]
    · intro q hq hq'
      refine le_trans ?_ (degree_le_of_dvd (minpoly.dvd _ _ hq') hq.ne

中文:
引理 irreducible_X_pow_sub_C_of_root_adjoin_eq_top
  证明: by
  have : X ^ (finrank K L) - C a = minpoly K α := by
    refine minpoly.unique _ _ (monic_X_pow_sub_C _ finrank_pos.ne.symm) ?_ ?_
    · simp only [aeval_def, eval₂_sub, eval₂_X_pow, ha, eval₂_C, sub_self]
    · intro q hq hq'
      refine le_trans ?_ (degree_le_of_dvd (minpoly.dvd _ _ hq') hq.ne

Depends on / 依赖: IntermediateField, IntermediateField.adjoin.finrank, IsIntegral, IsIntegral.of_finite, Nat.cast_le, adjoin, aeval_def, cast_le, degree_X_pow_sub_C, degree_eq_natDegree, degree_le_of_dvd, finrank, finrank_pos, finrank_pos.ne.symm, hq.ne_zero, le_trans, minpoly, minpoly.dvd, minpoly.ne_zero, minpoly.unique
-/
lemma irreducible_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    Irreducible (X ^ (finrank K L) - C a) := by
  have : X ^ (finrank K L) - C a = minpoly K α := by
    refine minpoly.unique _ _ (monic_X_pow_sub_C _ finrank_pos.ne.symm) ?_ ?_
    · simp only [aeval_def, eval₂_sub, eval₂_X_pow, ha, eval₂_C, sub_self]
    · intro q hq hq'
      refine le_trans ?_ (degree_le_of_dvd (minpoly.dvd _ _ hq') hq.ne_zero)
      rw [degree_X_pow_sub_C finrank_pos]; rw [degree_eq_natDegree (minpoly.ne_zero (IsIntegral.of_finite K α))]; rw [← IntermediateField.adjoin.finrank (IsIntegral.of_finite K α)]; rw [hα]; rw [Nat.cast_le]
      exact (finrank_top K L).ge
  exact this ▸ minpoly.irreducible (IsIntegral.of_finite K α)

include hK in
/--
lemma `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top` / 引理 `isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top`

English:
lemma isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
  proof: by
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hK
    rw [mem_primitiveRoots finrank_pos] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective) ha
  · rw [eq_top_iff, ← In

中文:
引理 isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
  证明: by
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hK
    rw [mem_primitiveRoots finrank_pos] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective) ha
  · rw [eq_top_iff, ← In

Depends on / 依赖: Algebra, Algebra.adjoin_mono, IntermediateField, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic, IntermediateField.top_toSubalgebra, IsAlgebraic, IsAlgebraic.of_finite, Polynomial, Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_sub, Set.singleton_subset_iff, X_pow_sub_C_ne_, X_pow_sub_C_splits_of_isPrimitiveRoot, adjoin_mono, adjoin_simple_toSubalgebra_of_isAlgebraic, algebraMap, eq_top_iff, finrank_pos
-/
lemma isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top
    {a : K} {α : L} (ha : α ^ (finrank K L) = algebraMap K L a) (hα : K⟮α⟯ = ⊤) :
    IsSplittingField K L (X ^ (finrank K L) - C a) := by
  constructor
  · rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      Polynomial.map_X]
    have ⟨_, hζ⟩ := hK
    rw [mem_primitiveRoots finrank_pos] at hζ
    exact X_pow_sub_C_splits_of_isPrimitiveRoot (hζ.map_of_injective (algebraMap K _).injective) ha
  · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hα,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite K α)]
    apply Algebra.adjoin_mono
    rw [Set.singleton_subset_iff]; rw [mem_rootSet_of_ne (X_pow_sub_C_ne_zero finrank_pos a)]; rw [aeval_def]; rw [eval₂_sub]; rw [eval₂_X_pow]; rw [eval₂_C]; rw [ha]; rw [sub_self]

end IsCyclic

open Module in
/--
lemma `isCyclic_tfae` / 引理 `isCyclic_tfae`

English:
lemma isCyclic_tfae
  statement: (K L) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  proof: by
  have : NeZero (Module.finrank K L) := NeZero.of_pos finrank_pos
  tfae_have 1 -> 3
  | ⟨inst₁, inst₂⟩ => exists_root_adjoin_eq_top_of_isCyclic K L hK
  tfae_have 3 -> 2
  | ⟨α, ⟨a, ha⟩, hα⟩ => ⟨a, irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα,
      isSplittingField_X_pow_sub_C_of_ro

中文:
引理 isCyclic_tfae
  结论: (K L) [域 K] [域 L] [代数 K L] [有限维 K L]
  证明: by
  have : NeZero (Module.finrank K L) := NeZero.of_pos finrank_pos
  tfae_have 1 -> 3
  | ⟨inst₁, inst₂⟩ => exists_root_adjoin_eq_top_of_isCyclic K L hK
  tfae_have 3 -> 2
  | ⟨α, ⟨a, ha⟩, hα⟩ => ⟨a, irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα,
      isSplittingField_X_pow_sub_C_of_ro

Depends on / 依赖: Module, Module.finrank, NeZero, NeZero.of_pos, exists_root_adjoin_eq_top_of_isCyclic, finrank, finrank_pos, ha.symm, irreducible_X_pow_sub_C_of_root_adjoin_eq_top, isCyclic_of_isSplittingField_X_pow_sub_C, isGalois_of_isSplittingField_X_pow_sub_C, isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top, of_pos, tfae_finish, tfae_have
-/
lemma isCyclic_tfae (K L) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (hK : (primitiveRoots (Module.finrank K L) K).Nonempty) :
    List.TFAE [
      IsGalois K L ∧ IsCyclic Gal(L/K),
      exists a : K, Irreducible (X ^ (finrank K L) - C a) ∧
        IsSplittingField K L (X ^ (finrank K L) - C a),
      exists (α : L), α ^ (finrank K L) in Set.range (algebraMap K L) ∧ K⟮α⟯ = ⊤] := by
  have : NeZero (Module.finrank K L) := NeZero.of_pos finrank_pos
  tfae_have 1 -> 3
  | ⟨inst₁, inst₂⟩ => exists_root_adjoin_eq_top_of_isCyclic K L hK
  tfae_have 3 -> 2
  | ⟨α, ⟨a, ha⟩, hα⟩ => ⟨a, irreducible_X_pow_sub_C_of_root_adjoin_eq_top ha.symm hα,
      isSplittingField_X_pow_sub_C_of_root_adjoin_eq_top hK ha.symm hα⟩
  tfae_have 2 -> 1
  | ⟨a, H, inst⟩ => ⟨isGalois_of_isSplittingField_X_pow_sub_C hK H L,
      isCyclic_of_isSplittingField_X_pow_sub_C hK H L⟩
  tfae_finish
