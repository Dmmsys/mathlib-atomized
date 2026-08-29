/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.Norm.Transitivity

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `GaloisField p n` is defined as the splitting field of `X^(p^n) - X` over `ZMod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `GaloisField p n` is a field with `p ^ n` elements

## Main Results

- `GaloisField.algEquivGaloisField`: Any finite field is isomorphic to some Galois field
- `FiniteField.algEquivOfCardEq`: Uniqueness of finite fields : algebra isomorphism
- `FiniteField.ringEquivOfCardEq`: Uniqueness of finite fields : ring isomorphism
- `card_algHom_of_finrank_dvd`: if `[K:F] ∣ [L:F]` then `#(K →ₐ[F] L) = [K:F]`
- `nonempty_algHom_iff_finrank_dvd`: `(K →ₐ[F] L)` is nonempty iff `[K:F] ∣ [L:F]`. This and the
  above result helps to classify the category of finite fields.

-/

@[expose] public section


noncomputable section


open Polynomial Finset

open scoped Polynomial

/--
Instance `FiniteField.isSplittingField_sub` / 实例 `FiniteField.isSplittingField_sub`

English:
instance FiniteField.isSplittingField_sub
  signature: (K F : Type*) [Field K] [Fintype K]
  body: by
    have h : (X ^ Fintype.card K - X : K[X]).natDegree = Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
    rw [splits_iff_card_roots]; rw [Polynomial.map_sub]; rw [Polynomial.map_pow]; rw [map_X]; rw [h]; rw [FiniteField.roots_X_pow_card_sub_X K]; rw [← F

中文:
实例 FiniteField.isSplittingField_sub
  签名: (K F : 类型) [域 K] [有限类型 K]
  定义体: by
    have h : (X ^ Fintype.card K - X : K[X]).natDegree = Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
    rw [splits_iff_card_roots]; rw [Polynomial.map_sub]; rw [Polynomial.map_pow]; rw [map_X]; rw [h]; rw [FiniteField.roots_X_pow_card_sub_X K]; rw [← F

Depends on / 依赖: Algebra, Algebra.adjoin, FiniteField, FiniteField.X_pow_card_sub_X_natDegree_eq, FiniteField.roots_X_pow_card_sub_X, Finset, Finset.card_def, Finset.card_univ, Fintype, Fintype.card, Fintype.one_lt_card, Polynomial, Polynomial.map_pow, Polynomial.map_sub, X_pow_card_sub_X_natDegree_eq, adjoin, adjoin_rootSet, aroots, card_def, card_univ
-/
instance FiniteField.isSplittingField_sub (K F : Type*) [Field K] [Fintype K]
    [Field F] [Algebra F K] : IsSplittingField F K (X ^ Fintype.card K - X) where
  splits' := by
    have h : (X ^ Fintype.card K - X : K[X]).natDegree = Fintype.card K :=
      FiniteField.X_pow_card_sub_X_natDegree_eq K Fintype.one_lt_card
    rw [splits_iff_card_roots]; rw [Polynomial.map_sub]; rw [Polynomial.map_pow]; rw [map_X]; rw [h]; rw [FiniteField.roots_X_pow_card_sub_X K]; rw [← Finset.card_def]; rw [Finset.card_univ]
  adjoin_rootSet' := by
    classical
    trans Algebra.adjoin F ((roots (X ^ Fintype.card K - X : K[X])).toFinset : Set K)
    · simp only [rootSet, aroots, Polynomial.map_pow, map_X, Polynomial.map_sub]
    · rw [FiniteField.roots_X_pow_card_sub_X, val_toFinset, coe_univ, Algebra.adjoin_univ]

/--
theorem `galois_poly_separable` / 定理 `galois_poly_separable`

English:
theorem galois_poly_separable
  given: {K : Type*} [CommRing K] (p q : Nat) [CharP K p] (h : p ∣ q)
  proof: by
  use 1, X ^ q - X - 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h
  rw [derivative_sub]; rw [derivative_X_pow]; rw [derivative_X]; rw [C_eq_natCast]; rw [h]
  ring

中文:
定理 galois_poly_separable
  条件: {K : 类型} [交换环 K] (p q : 自然数) [特征p K p] (h : p ∣ q)
  证明: by
  use 1, X ^ q - X - 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h
  rw [derivative_sub]; rw [derivative_X_pow]; rw [derivative_X]; rw [C_eq_natCast]; rw [h]
  ring

Depends on / 依赖: C_eq_natCast, CharP.cast_eq_zero_iff, cast_eq_zero_iff, derivative_X, derivative_X_pow, derivative_sub
-/
theorem galois_poly_separable {K : Type*} [CommRing K] (p q : Nat) [CharP K p] (h : p ∣ q) :
    Separable (X ^ q - X : K[X]) := by
  use 1, X ^ q - X - 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h
  rw [derivative_sub]; rw [derivative_X_pow]; rw [derivative_X]; rw [C_eq_natCast]; rw [h]
  ring

variable (p : Nat) [Fact p.Prime] (n : Nat)

/--
Definition of `GaloisField` / `GaloisField` 的定义

English:
definition GaloisField
  body: SplittingField (X ^ p ^ n - X : (ZMod p)[X])
deriving Inhabited, Field, CharP _ p,
  Algebra (ZMod p),
  Finite, FiniteDimensional (ZMod p),
  IsSplittingField (ZMod p) _ (X ^ p ^ n - X)

中文:
定义 GaloisField
  定义体: SplittingField (X ^ p ^ n - X : (ZMod p)[X])
deriving Inhabited, Field, CharP _ p,
  Algebra (ZMod p),
  Finite, FiniteDimensional (ZMod p),
  IsSplittingField (ZMod p) _ (X ^ p ^ n - X)

Depends on / 依赖: SplittingField
-/
def GaloisField := SplittingField (X ^ p ^ n - X : (ZMod p)[X])
deriving Inhabited, Field, CharP _ p,
  Algebra (ZMod p),
  Finite, FiniteDimensional (ZMod p),
  IsSplittingField (ZMod p) _ (X ^ p ^ n - X)

namespace GaloisField

variable (p : Nat) [h_prime : Fact p.Prime] (n : Nat)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `finrank` / 定理 `finrank`

English:
theorem finrank
  given: {n} (h : n != 0)
  statement: Module.finrank (ZMod p) (GaloisField p n) = n
  proof: by
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  set g_poly := (X ^ p ^ n - X : (ZMod p)[X])
  have hp : 1 < p := h_prime.out.one_lt
  have aux : g_poly != 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp
  have key : Fintype.card (g_poly.rootSet (GaloisField p n)) =

中文:
定理 finrank
  条件: {n} (h : n != 0)
  结论: 模.finrank (ZMod p) (GaloisField p n) = n
  证明: by
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  set g_poly := (X ^ p ^ n - X : (ZMod p)[X])
  have hp : 1 < p := h_prime.out.one_lt
  have aux : g_poly != 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp
  have key : Fintype.card (g_poly.rootSet (GaloisField p n)) =

Depends on / 依赖: FiniteField, FiniteField.X_, FiniteField.X_pow_card_pow_sub_X_ne_zero, Fintype, Fintype.card, Fintype.ofFinite, GaloisField, SplittingField, SplittingField.splits, X_pow_card_pow_sub_X_ne_zero, card_rootSet_eq_natDegree, dvd_pow, dvd_refl, g_poly, g_poly.natDegree, g_poly.rootSet, galois_poly_separable, h_prime, h_prime.out.one_lt, natDegree
-/
theorem finrank {n} (h : n != 0) : Module.finrank (ZMod p) (GaloisField p n) = n := by
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  set g_poly := (X ^ p ^ n - X : (ZMod p)[X])
  have hp : 1 < p := h_prime.out.one_lt
  have aux : g_poly != 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp
  have key : Fintype.card (g_poly.rootSet (GaloisField p n)) = g_poly.natDegree :=
    card_rootSet_eq_natDegree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h))
      (SplittingField.splits (g_poly : (ZMod p)[X]))
  have nat_degree_eq : g_poly.natDegree = p ^ n :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq _ h hp
  rw [nat_degree_eq] at key
  suffices g_poly.rootSet (GaloisField p n) = Set.univ by
    simp_rw [this, ← Fintype.ofEquiv_card (Equiv.Set.univ _)] at key
    -- Porting note: prevents `card_eq_pow_finrank` from using a wrong instance for `Fintype`
    rw [@Module.card_eq_pow_finrank (K := ZMod p)]; rw [ZMod.card] at key
    exact Nat.pow_right_injective (Nat.Prime.one_lt' p).out key
  rw [Set.eq_univ_iff_forall]
  suffices forall (x) (hx : x in (⊤ : Subalgebra (ZMod p) (GaloisField p n))),
      x in (X ^ p ^ n - X : (ZMod p)[X]).rootSet (GaloisField p n)
    by simpa
  rw [← SplittingField.adjoin_rootSet]
  simp_rw [Algebra.mem_adjoin_iff]
  intro x hx
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  simp only [g_poly] at aux
  refine Subring.closure_induction ?_ ?_ ?_ ?_ ?_ ?_ hx
    <;> simp_rw [mem_rootSet_of_ne aux]
  · rintro x (⟨r, rfl⟩ | hx)
    · simp only [map_sub, map_pow, aeval_X]
      rw [← map_pow]; rw [ZMod.pow_card_pow]; rw [sub_self]
    · dsimp only [GaloisField] at hx
      rwa [mem_rootSet_of_ne aux] at hx
  · rw [← coeff_zero_eq_aeval_zero']
    simp only [coeff_X_pow, coeff_X_zero, sub_zero, _root_.map_eq_zero, ite_eq_right_iff,
      one_ne_zero, coeff_sub]
    intro hn
    exact Nat.not_lt_zero 1 (eq_zero_of_pow_eq_zero hn.symm ▸ hp)
  · simp
  · simp only [aeval_X_pow, aeval_X, map_sub, add_pow_char_pow, sub_eq_zero]
    intro x y _ _ hx hy
    rw [hx]; rw [hy]
  · intro x _ hx
    simp only [g_poly, sub_eq_zero, aeval_X_pow, aeval_X, map_sub, sub_neg_eq_add] at *
    rw [neg_pow]; rw [hx]; rw [neg_one_pow_char_pow]
    simp
  · simp only [aeval_X_pow, aeval_X, map_sub, mul_pow, sub_eq_zero]
    intro x y _ _ hx hy
    rw [hx]; rw [hy]

/--
theorem `card` / 定理 `card`

English:
theorem card
  given: (h : n != 0)
  statement: Nat.card (GaloisField p n) = p ^ n
  proof: by
  let b := IsNoetherian.finsetBasis (ZMod p) (GaloisField p n)
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  rw [Nat.card_eq_fintype_card]; rw [Module.card_fintype b]; rw [← Module.finrank_eq_card_basis b]; rw [ZMod.card]; rw [finrank p h]

中文:
定理 card
  条件: (h : n != 0)
  结论: 自然数.card (GaloisField p n) = p ^ n
  证明: by
  let b := IsNoetherian.finsetBasis (ZMod p) (GaloisField p n)
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  rw [Nat.card_eq_fintype_card]; rw [Module.card_fintype b]; rw [← Module.finrank_eq_card_basis b]; rw [ZMod.card]; rw [finrank p h]

Depends on / 依赖: Fintype, Fintype.ofFinite, GaloisField, IsNoetherian, IsNoetherian.finsetBasis, Module, Module.card_fintype, Module.finrank_eq_card_basis, Nat.card_eq_fintype_card, ZMod.card, card_eq_fintype_card, card_fintype, finrank, finrank_eq_card_basis, finsetBasis, ofFinite
-/
theorem card (h : n != 0) : Nat.card (GaloisField p n) = p ^ n := by
  let b := IsNoetherian.finsetBasis (ZMod p) (GaloisField p n)
  have : Fintype (GaloisField p n) := Fintype.ofFinite (GaloisField p n)
  rw [Nat.card_eq_fintype_card]; rw [Module.card_fintype b]; rw [← Module.finrank_eq_card_basis b]; rw [ZMod.card]; rw [finrank p h]

/--
theorem `splits_zmod_X_pow_sub_X` / 定理 `splits_zmod_X_pow_sub_X`

English:
theorem splits_zmod_X_pow_sub_X
  statement: Splits (X ^ p - X : (ZMod p)[X])
  proof: by
  have hp : 1 < p := h_prime.out.one_lt
  have h1 : roots (X ^ p - X : (ZMod p)[X]) = Finset.univ.val := by
    convert! FiniteField.roots_X_pow_card_sub_X (ZMod p)
    exact (ZMod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  -- We discharge the `p = 0` separa

中文:
定理 splits_zmod_X_pow_sub_X
  结论: Splits (X ^ p - X : (ZMod p)[X])
  证明: by
  have hp : 1 < p := h_prime.out.one_lt
  have h1 : roots (X ^ p - X : (ZMod p)[X]) = Finset.univ.val := by
    convert! FiniteField.roots_X_pow_card_sub_X (ZMod p)
    exact (ZMod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  -- We discharge the `p = 0` separa

Depends on / 依赖: FiniteField, FiniteField.X_pow_card_sub_X_natDegree_eq, FiniteField.roots_X_pow_card_sub_X, Finset, Finset.univ.val, X_pow_card_sub_X_natDegree_eq, ZMod.card, convert, h_prime, h_prime.out.one_lt, one_lt, roots_X_pow_card_sub_X
-/
theorem splits_zmod_X_pow_sub_X : Splits (X ^ p - X : (ZMod p)[X]) := by
  have hp : 1 < p := h_prime.out.one_lt
  have h1 : roots (X ^ p - X : (ZMod p)[X]) = Finset.univ.val := by
    convert! FiniteField.roots_X_pow_card_sub_X (ZMod p)
    exact (ZMod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_natDegree_eq (ZMod p) hp
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `ZMod p`.
  cases p; cases hp
  rw [splits_iff_card_roots]; rw [h1]; rw [← Finset.card_def]; rw [Finset.card_univ]; rw [h2]; rw [ZMod.card]

/--
Definition of `equivZmodP` / `equivZmodP` 的定义

English:
definition equivZmodP
  signature: : GaloisField p 1 ≃ₐ[ZMod p] ZMod p
  body: have h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
  have inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm

中文:
定义 equivZmodP
  签名: : GaloisField p 1 ≃ₐ[ZMod p] ZMod p
  定义体: have h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
  have inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm

Depends on / 依赖: Fintype, Fintype.card, IsSplittingField, IsSplittingField.algEquiv, ZMod.card, algEquiv, infer_instance, pow_one
-/
def equivZmodP : GaloisField p 1 ≃ₐ[ZMod p] ZMod p :=
  have h : (X ^ p ^ 1 : (ZMod p)[X]) = X ^ Fintype.card (ZMod p) := by rw [pow_one, ZMod.card p]
  have inst : IsSplittingField (ZMod p) (ZMod p) (X ^ p ^ 1 - X) := by rw [h]; infer_instance
  (@IsSplittingField.algEquiv _ (ZMod p) _ _ _ (X ^ p ^ 1 - X : (ZMod p)[X]) inst).symm

section Fintype

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

/--
theorem `_root_.FiniteField.splits_X_pow_card_sub_X` / 定理 `_root_.FiniteField.splits_X_pow_card_sub_X`

English:
theorem _root_.FiniteField.splits_X_pow_card_sub_X
  proof: (FiniteField.isSplittingField_sub K (ZMod p)).splits

中文:
定理 _root_.FiniteField.splits_X_pow_card_sub_X
  证明: (FiniteField.isSplittingField_sub K (ZMod p)).splits

Depends on / 依赖: FiniteField, FiniteField.isSplittingField_sub, isSplittingField_sub, splits
-/
theorem _root_.FiniteField.splits_X_pow_card_sub_X :
    Splits (map (algebraMap (ZMod p) K) (X ^ Fintype.card K - X)) :=
  (FiniteField.isSplittingField_sub K (ZMod p)).splits

/--
theorem `_root_.FiniteField.isSplittingField_of_card_eq` / 定理 `_root_.FiniteField.isSplittingField_of_card_eq`

English:
theorem _root_.FiniteField.isSplittingField_of_card_eq
  given: (h : Fintype.card K = p ^ n)
  proof: h ▸ FiniteField.isSplittingField_sub K (ZMod p)

中文:
定理 _root_.FiniteField.isSplittingField_of_card_eq
  条件: (h : 有限类型.card K = p ^ n)
  证明: h ▸ FiniteField.isSplittingField_sub K (ZMod p)

Depends on / 依赖: FiniteField, FiniteField.isSplittingField_sub, isSplittingField_sub
-/
theorem _root_.FiniteField.isSplittingField_of_card_eq (h : Fintype.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) :=
  h ▸ FiniteField.isSplittingField_sub K (ZMod p)

/--
Definition of `algEquivGaloisFieldOfFintype` / `algEquivGaloisFieldOfFintype` 的定义

English:
definition algEquivGaloisFieldOfFintype
  signature: (h : Fintype.card K = p ^ n)
  body: haveI := FiniteField.isSplittingField_of_card_eq _ _ h
  IsSplittingField.algEquiv _ _

中文:
定义 algEquivGaloisFieldOfFintype
  签名: (h : 有限类型.card K = p ^ n)
  定义体: haveI := FiniteField.isSplittingField_of_card_eq _ _ h
  IsSplittingField.algEquiv _ _

Depends on / 依赖: FiniteField, FiniteField.isSplittingField_of_card_eq, IsSplittingField, IsSplittingField.algEquiv, algEquiv, isSplittingField_of_card_eq
-/
def algEquivGaloisFieldOfFintype (h : Fintype.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Fintype

section Finite

variable {K : Type*} [Field K] [Algebra (ZMod p) K]

/--
theorem `_root_.FiniteField.splits_X_pow_nat_card_sub_X` / 定理 `_root_.FiniteField.splits_X_pow_nat_card_sub_X`

English:
theorem _root_.FiniteField.splits_X_pow_nat_card_sub_X
  given: [Finite K]
  proof: by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.isSplittingField_sub K (ZMod p)).splits

中文:
定理 _root_.FiniteField.splits_X_pow_nat_card_sub_X
  条件: [有限 K]
  证明: by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.isSplittingField_sub K (ZMod p)).splits

Depends on / 依赖: FiniteField, FiniteField.isSplittingField_sub, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, card_eq_fintype_card, isSplittingField_sub, ofFinite, splits
-/
theorem _root_.FiniteField.splits_X_pow_nat_card_sub_X [Finite K] :
    Splits (map (algebraMap (ZMod p) K) (X ^ Nat.card K - X)) := by
  have : Fintype K := Fintype.ofFinite K
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.isSplittingField_sub K (ZMod p)).splits

/--
theorem `_root_.FiniteField.isSplittingField_of_nat_card_eq` / 定理 `_root_.FiniteField.isSplittingField_of_nat_card_eq`

English:
theorem _root_.FiniteField.isSplittingField_of_nat_card_eq
  given: (h : Nat.card K = p ^ n)
  proof: by
  have : Finite K := (Nat.card_pos_iff.mp (h ▸ pow_pos h_prime.1.pos n)).2
  have : Fintype K := Fintype.ofFinite K
  rw [← h]; rw [Nat.card_eq_fintype_card]
  exact FiniteField.isSplittingField_sub K (ZMod p)

中文:
定理 _root_.FiniteField.isSplittingField_of_nat_card_eq
  条件: (h : 自然数.card K = p ^ n)
  证明: by
  have : Finite K := (Nat.card_pos_iff.mp (h ▸ pow_pos h_prime.1.pos n)).2
  have : Fintype K := Fintype.ofFinite K
  rw [← h]; rw [Nat.card_eq_fintype_card]
  exact FiniteField.isSplittingField_sub K (ZMod p)

Depends on / 依赖: Finite, FiniteField, FiniteField.isSplittingField_sub, Fintype, Fintype.ofFinite, Nat.card_eq_fintype_card, Nat.card_pos_iff.mp, card_eq_fintype_card, card_pos_iff, h_prime, isSplittingField_sub, ofFinite, pow_pos
-/
theorem _root_.FiniteField.isSplittingField_of_nat_card_eq (h : Nat.card K = p ^ n) :
    IsSplittingField (ZMod p) K (X ^ p ^ n - X) := by
  have : Finite K := (Nat.card_pos_iff.mp (h ▸ pow_pos h_prime.1.pos n)).2
  have : Fintype K := Fintype.ofFinite K
  rw [← h]; rw [Nat.card_eq_fintype_card]
  exact FiniteField.isSplittingField_sub K (ZMod p)

/--
theorem `_root_.Polynomial.splits_X_pow_nat_card_sub_X` / 定理 `_root_.Polynomial.splits_X_pow_nat_card_sub_X`

English:
theorem _root_.Polynomial.splits_X_pow_nat_card_sub_X
  proof: by
  cases fintypeOrInfinite K
  · have := (IsSplittingField.splits (L := K) (X ^ (Fintype.card K) - X : K[X]))
    simpa [Algebra.algebraMap_self, map_sub, map_pow, map_X] using this
  · rw [← Polynomial.splits_neg_iff]
    simpa [Nat.card_eq_zero_of_infinite, pow_zero, neg_sub] using Splits.X_sub_

中文:
定理 _root_.多项式.splits_X_pow_nat_card_sub_X
  证明: by
  cases fintypeOrInfinite K
  · have := (IsSplittingField.splits (L := K) (X ^ (Fintype.card K) - X : K[X]))
    simpa [Algebra.algebraMap_self, map_sub, map_pow, map_X] using this
  · rw [← Polynomial.splits_neg_iff]
    simpa [Nat.card_eq_zero_of_infinite, pow_zero, neg_sub] using Splits.X_sub_

Depends on / 依赖: Algebra, Algebra.algebraMap_self, Fintype, Fintype.card, IsSplittingField, IsSplittingField.splits, Nat.card_eq_zero_of_infinite, Polynomial, Polynomial.splits_neg_iff, Splits, Splits.X_sub_C, X_sub_C, algebraMap_self, card_eq_zero_of_infinite, fintypeOrInfinite, map_X, map_pow, map_sub, neg_sub, pow_zero
-/
theorem _root_.Polynomial.splits_X_pow_nat_card_sub_X :
    Splits (X ^ (Nat.card K) - X : K[X]) := by
  cases fintypeOrInfinite K
  · have := (IsSplittingField.splits (L := K) (X ^ (Fintype.card K) - X : K[X]))
    simpa [Algebra.algebraMap_self, map_sub, map_pow, map_X] using this
  · rw [← Polynomial.splits_neg_iff]
    simpa [Nat.card_eq_zero_of_infinite, pow_zero, neg_sub] using Splits.X_sub_C (1 : K)

instance (priority := 100) {K K' : Type*} [Field K] [Field K'] [Finite K'] [Algebra K K'] :
    IsGalois K K' := by
  cases nonempty_fintype K'
  obtain ⟨p, hp⟩ := CharP.exists K
  have : CharP K p := hp
  have : CharP K' p := charP_of_injective_algebraMap' K p
  exact IsGalois.of_separable_splitting_field
    (galois_poly_separable p (Fintype.card K')
      (let ⟨n, _, hn⟩ := FiniteField.card K' p
      hn.symm ▸ dvd_pow_self p n.ne_zero))

/--
Definition of `algEquivGaloisField` / `algEquivGaloisField` 的定义

English:
definition algEquivGaloisField
  signature: (h : Nat.card K = p ^ n)
  body: haveI := FiniteField.isSplittingField_of_nat_card_eq _ _ h
  IsSplittingField.algEquiv _ _

中文:
定义 algEquivGaloisField
  签名: (h : 自然数.card K = p ^ n)
  定义体: haveI := FiniteField.isSplittingField_of_nat_card_eq _ _ h
  IsSplittingField.algEquiv _ _

Depends on / 依赖: FiniteField, FiniteField.isSplittingField_of_nat_card_eq, IsSplittingField, IsSplittingField.algEquiv, algEquiv, isSplittingField_of_nat_card_eq
-/
def algEquivGaloisField (h : Nat.card K = p ^ n) : K ≃ₐ[ZMod p] GaloisField p n :=
  haveI := FiniteField.isSplittingField_of_nat_card_eq _ _ h
  IsSplittingField.algEquiv _ _

end Finite

end GaloisField

namespace FiniteField

variable {K K' : Type*} [Field K] [Field K']

section norm

variable [Algebra K K'] [Finite K']

/--
theorem `algebraMap_norm_eq_pow` / 定理 `algebraMap_norm_eq_pow`

English:
theorem algebraMap_norm_eq_pow
  given: {x : K'}
  proof: by
  have := Finite.of_injective _ (algebraMap K K').injective
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  simp_rw [← Fintype.card_eq_nat_card, Algebra.norm_eq_prod_automorphisms,
    ← (bijective_frobeniusAlgEquivOfAlgebraic_pow K K').prod_comp, AlgEquiv.coe_pow,
    coe_frobeniusA

中文:
定理 algebraMap_norm_eq_pow
  条件: {x : K'}
  证明: by
  have := Finite.of_injective _ (algebraMap K K').injective
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  simp_rw [← Fintype.card_eq_nat_card, Algebra.norm_eq_prod_automorphisms,
    ← (bijective_frobeniusAlgEquivOfAlgebraic_pow K K').prod_comp, AlgEquiv.coe_pow,
    coe_frobeniusA

Depends on / 依赖: AlgEquiv, AlgEquiv.coe_pow, Algebra, Algebra.norm_eq_prod_automorphisms, Fin.sum_univ_eq_sum_range, Finite, Finite.of_injective, Finset, Finset.prod_pow_eq_pow_sum, Fintype, Fintype.card_eq_nat_card, Fintype.ofFinite, Fintype.one_lt_card, Module, Module.card_eq_pow_finrank, Nat.geomSum_eq, algebraMap, bijective_frobeniusAlgEquivOfAlgebraic_pow, card_eq_nat_card, card_eq_pow_finrank
-/
theorem algebraMap_norm_eq_pow {x : K'} :
    algebraMap K K' (Algebra.norm K x) = x ^ ((Nat.card K' - 1) / (Nat.card K - 1)) := by
  have := Finite.of_injective _ (algebraMap K K').injective
  have := Fintype.ofFinite K
  have := Fintype.ofFinite K'
  simp_rw [← Fintype.card_eq_nat_card, Algebra.norm_eq_prod_automorphisms,
    ← (bijective_frobeniusAlgEquivOfAlgebraic_pow K K').prod_comp, AlgEquiv.coe_pow,
    coe_frobeniusAlgEquivOfAlgebraic, pow_iterate, Finset.prod_pow_eq_pow_sum,
    Fin.sum_univ_eq_sum_range, Nat.geomSum_eq Fintype.one_lt_card, ← Module.card_eq_pow_finrank]

variable (K K')

/--
theorem `unitsMap_norm_surjective` / 定理 `unitsMap_norm_surjective`

English:
theorem unitsMap_norm_surjective
  statement: Function.Surjective (Units.map <| Algebra.norm K (S := K'))
  proof: have := Finite.of_injective_finite_range (algebraMap K K').injective
MonoidHom.surjective_of_card_ker_le_div _ by
    simp_rw [Nat.card_units]
    classical
    have := Fintype.ofFinite K'ˣ
    convert!
IsCyclic.card_pow_eq_one_le (α := K'ˣ)
        Nat.div_pos
            (Nat.sub_le_sub_right (Nat

中文:
定理 unitsMap_norm_surjective
  结论: 函数.满射 (单位群.map <| 代数.norm K (S := K'))
  证明: have := Finite.of_injective_finite_range (algebraMap K K').injective
MonoidHom.surjective_of_card_ker_le_div _ by
    simp_rw [Nat.card_units]
    classical
    have := Fintype.ofFinite K'ˣ
    convert!
IsCyclic.card_pow_eq_one_le (α := K'ˣ)
        Nat.div_pos
            (Nat.sub_le_sub_right (Nat
-/
theorem unitsMap_norm_surjective : Function.Surjective (Units.map <| Algebra.norm K (S := K')) :=
  have := Finite.of_injective_finite_range (algebraMap K K').injective
MonoidHom.surjective_of_card_ker_le_div _ by
    simp_rw [Nat.card_units]
    classical
    have := Fintype.ofFinite K'ˣ
    convert!
IsCyclic.card_pow_eq_one_le (α := K'ˣ)
        Nat.div_pos
            (Nat.sub_le_sub_right (Nat.card_le_card_of_injective _ (algebraMap K K').injective)
              _) <|
          Nat.sub_pos_of_lt Finite.one_lt_card
    rw [← Set.ncard_coe_finset]; rw [← SetLike.coe_sort_coe]; rw [Nat.card_coe_set_eq]; congr 1; ext
    simp [Units.ext_iff, ← (algebraMap K K').injective.eq_iff, algebraMap_norm_eq_pow]

/--
theorem `norm_surjective` / 定理 `norm_surjective`

English:
theorem norm_surjective
  statement: Function.Surjective (Algebra.norm K (S := K'))
  proof: fun k => by
  obtain rfl | ne := eq_or_ne k 0
  · exact ⟨0, Algebra.norm_zero ..⟩
  have ⟨x, eq⟩ := unitsMap_norm_surjective K K' (Units.mk0 k ne)
  exact ⟨x, congr_arg (·.1) eq⟩

中文:
定理 norm_surjective
  结论: 函数.满射 (代数.norm K (S := K'))
  证明: fun k => by
  obtain rfl | ne := eq_or_ne k 0
  · exact ⟨0, Algebra.norm_zero ..⟩
  have ⟨x, eq⟩ := unitsMap_norm_surjective K K' (Units.mk0 k ne)
  exact ⟨x, congr_arg (·.1) eq⟩

Depends on / 依赖: Algebra, Algebra.norm_zero, Units.mk0, congr_arg, eq_or_ne, norm_zero, unitsMap_norm_surjective
-/
theorem norm_surjective : Function.Surjective (Algebra.norm K (S := K')) := fun k => by
  obtain rfl | ne := eq_or_ne k 0
  · exact ⟨0, Algebra.norm_zero ..⟩
  have ⟨x, eq⟩ := unitsMap_norm_surjective K K' (Units.mk0 k ne)
  exact ⟨x, congr_arg (·.1) eq⟩

end norm

variable [Fintype K] [Fintype K']

/--
Definition of `algEquivOfCardEq` / `algEquivOfCardEq` 的定义

English:
definition algEquivOfCardEq
  signature: (p : Nat) [h_prime : Fact p.Prime] [Algebra (ZMod p) K] [Algebra (ZMod p) K']
  body: by
  have : CharP K p := by rw [← Algebra.charP_iff (ZMod p) K p]; exact ZMod.charP p
  have : CharP K' p := by rw [← Algebra.charP_iff (ZMod p) K' p]; exact ZMod.charP p
  choose n a hK using FiniteField.card K p
  choose n' a' hK' using FiniteField.card K' p
  rw [hK]; rw [hK'] at hKK'
  have hGal

中文:
定义 algEquivOfCardEq
  签名: (p : 自然数) [h_prime : Fact p.素] [代数 (ZMod p) K] [代数 (ZMod p) K']
  定义体: by
  have : CharP K p := by rw [← Algebra.charP_iff (ZMod p) K p]; exact ZMod.charP p
  have : CharP K' p := by rw [← Algebra.charP_iff (ZMod p) K' p]; exact ZMod.charP p
  choose n a hK using FiniteField.card K p
  choose n' a' hK' using FiniteField.card K' p
  rw [hK]; rw [hK'] at hKK'
  have hGal

Depends on / 依赖: AlgEquiv, AlgEquiv.trans, Algebra, Algebra.charP_iff, FiniteField, FiniteField.card, GaloisField, GaloisField.algEquivGaloisFieldOfFintype, Nat.pow_right_injective, ZMod.charP, algEquivGaloisFieldOfFintype, charP_iff, h_prime, h_prime.out.one_lt, one_lt, pow_right_injective
-/
def algEquivOfCardEq (p : Nat) [h_prime : Fact p.Prime] [Algebra (ZMod p) K] [Algebra (ZMod p) K']
    (hKK' : Fintype.card K = Fintype.card K') : K ≃ₐ[ZMod p] K' := by
  have : CharP K p := by rw [← Algebra.charP_iff (ZMod p) K p]; exact ZMod.charP p
  have : CharP K' p := by rw [← Algebra.charP_iff (ZMod p) K' p]; exact ZMod.charP p
  choose n a hK using FiniteField.card K p
  choose n' a' hK' using FiniteField.card K' p
  rw [hK]; rw [hK'] at hKK'
  have hGalK := GaloisField.algEquivGaloisFieldOfFintype p n hK
  have hK'Gal := (GaloisField.algEquivGaloisFieldOfFintype p n' hK').symm
  rw [Nat.pow_right_injective h_prime.out.one_lt hKK'] at *
  exact AlgEquiv.trans hGalK hK'Gal

/--
Definition of `ringEquivOfCardEq` / `ringEquivOfCardEq` 的定义

English:
definition ringEquivOfCardEq
  signature: (hKK' : Fintype.card K = Fintype.card K')
  body: by
  choose p _char_p_K using CharP.exists K
  choose p' _char_p'_K' using CharP.exists K'
  choose n hp hK using FiniteField.card K p
  choose n' hp' hK' using FiniteField.card K' p'
  have hpp' : p = p' := by
    by_contra hne
    simpa [← hK, hK', hKK', hp'.ne_one] using Nat.coprime_pow_primes n 

中文:
定义 ringEquivOfCardEq
  签名: (hKK' : 有限类型.card K = 有限类型.card K')
  定义体: by
  choose p _char_p_K using CharP.exists K
  choose p' _char_p'_K' using CharP.exists K'
  choose n hp hK using FiniteField.card K p
  choose n' hp' hK' using FiniteField.card K' p'
  have hpp' : p = p' := by
    by_contra hne
    simpa [← hK, hK', hKK', hp'.ne_one] using Nat.coprime_pow_primes n 

Depends on / 依赖: Algebra, CharP.exists, FiniteField, FiniteField.card, Nat.coprime_pow_primes, ZMod.algebra, _char_p, _char_p_K, algEquivOfCardEq, algebra, coprime_pow_primes, fact_iff, ne_one
-/
def ringEquivOfCardEq (hKK' : Fintype.card K = Fintype.card K') : K ≃+* K' := by
  choose p _char_p_K using CharP.exists K
  choose p' _char_p'_K' using CharP.exists K'
  choose n hp hK using FiniteField.card K p
  choose n' hp' hK' using FiniteField.card K' p'
  have hpp' : p = p' := by
    by_contra hne
    simpa [← hK, hK', hKK', hp'.ne_one] using Nat.coprime_pow_primes n n' hp hp' hne
  rw [← hpp'] at _char_p'_K'
  haveI := fact_iff.2 hp
  letI : Algebra (ZMod p) K := ZMod.algebra _ _
  letI : Algebra (ZMod p) K' := ZMod.algebra _ _
  exact ↑(algEquivOfCardEq p hKK')

/--
theorem `pow_finrank_eq_natCard` / 定理 `pow_finrank_eq_natCard`

English:
theorem pow_finrank_eq_natCard
  statement: (p : Nat) [Fact p.Prime]
  proof: by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)]; rw [Nat.card_zmod]

中文:
定理 pow_finrank_eq_natCard
  结论: (p : 自然数) [Fact p.素]
  证明: by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)]; rw [Nat.card_zmod]

Depends on / 依赖: Module, Module.natCard_eq_pow_finrank, Nat.card_zmod, card_zmod, natCard_eq_pow_finrank
-/
theorem pow_finrank_eq_natCard (p : Nat) [Fact p.Prime]
    (k : Type*) [AddCommGroup k] [Finite k] [Module (ZMod p) k] :
    p ^ Module.finrank (ZMod p) k = Nat.card k := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod p)]; rw [Nat.card_zmod]

/--
theorem `pow_finrank_eq_card` / 定理 `pow_finrank_eq_card`

English:
theorem pow_finrank_eq_card
  statement: (p : Nat) [Fact p.Prime]
  proof: by
  rw [pow_finrank_eq_natCard]; rw [Fintype.card_eq_nat_card]

中文:
定理 pow_finrank_eq_card
  结论: (p : 自然数) [Fact p.素]
  证明: by
  rw [pow_finrank_eq_natCard]; rw [Fintype.card_eq_nat_card]

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, card_eq_nat_card, pow_finrank_eq_natCard
-/
theorem pow_finrank_eq_card (p : Nat) [Fact p.Prime]
    (k : Type*) [AddCommGroup k] [Fintype k] [Module (ZMod p) k] :
    p ^ Module.finrank (ZMod p) k = Fintype.card k := by
  rw [pow_finrank_eq_natCard]; rw [Fintype.card_eq_nat_card]

section
variable {F K L : Type*} [Field F] [Field K] [Algebra F K] [Field L] [Algebra F L] [Finite L]

/--
theorem `nonempty_algHom_of_finrank_dvd` / 定理 `nonempty_algHom_of_finrank_dvd`

English:
theorem nonempty_algHom_of_finrank_dvd
  given: (h : Module.finrank F K ∣ Module.finrank F L)
  proof: by
  have := Finite.of_injective _ (algebraMap F L).injective
  have := Fintype.ofFinite F
  have := Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos h Module.finrank_pos)
  have := Module.finite_of_finite F (M := K)
  have := Fintype.ofFinite K
  have := Fintype.ofFinite L
  refine ⟨Polynomial.I

中文:
定理 nonempty_algHom_of_finrank_dvd
  条件: (h : 模.finrank F K ∣ 模.finrank F L)
  证明: by
  have := Finite.of_injective _ (algebraMap F L).injective
  have := Fintype.ofFinite F
  have := Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos h Module.finrank_pos)
  have := Module.finite_of_finite F (M := K)
  have := Fintype.ofFinite K
  have := Fintype.ofFinite L
  refine ⟨Polynomial.I

Depends on / 依赖: Finite, Finite.of_injective, FiniteField, FiniteField.X_pow_card_sub_X_ne_zero, FiniteField.isSplittingField_sub, Fintype, Fintype.card, Fintype.ofFinite, Fintype.one_lt_card, IsSplittingField, Module, Module.ca, Module.finite_of_finite, Module.finite_of_finrank_pos, Module.finrank_pos, Nat.pos_of_dvd_of_pos, Polynomial, Polynomial.IsSplittingField.lift, X_pow_card_sub_X_ne_zero, algebraMap
-/
theorem nonempty_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L) :
    Nonempty (K ->ₐ[F] L) := by
  have := Finite.of_injective _ (algebraMap F L).injective
  have := Fintype.ofFinite F
  have := Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos h Module.finrank_pos)
  have := Module.finite_of_finite F (M := K)
  have := Fintype.ofFinite K
  have := Fintype.ofFinite L
  refine ⟨Polynomial.IsSplittingField.lift _ (X ^ Fintype.card K - X) ?_⟩
  refine (FiniteField.isSplittingField_sub L F).splits.of_dvd ?_ ?_
  · exact map_ne_zero (FiniteField.X_pow_card_sub_X_ne_zero _ Fintype.one_lt_card)
  · rw [Module.card_eq_pow_finrank (K := F), Module.card_eq_pow_finrank (K := F) (V := L)]
    exact (map_dvd_map' _).mpr (dvd_pow_pow_sub_self_of_dvd h)

/--
theorem `natCard_algHom_of_finrank_dvd` / 定理 `natCard_algHom_of_finrank_dvd`

English:
theorem natCard_algHom_of_finrank_dvd
  given: (h : Module.finrank F K ∣ Module.finrank F L)
  proof: by
  obtain ⟨f⟩ := nonempty_algHom_of_finrank_dvd h
  algebraize [f.toRingHom]
  have := Finite.of_injective _ (algebraMap K L).injective
  rw [Nat.card_congr (Normal.algHomEquivAut F L K)]; rw [IsGalois.card_aut_eq_finrank]

中文:
定理 natCard_algHom_of_finrank_dvd
  条件: (h : 模.finrank F K ∣ 模.finrank F L)
  证明: by
  obtain ⟨f⟩ := nonempty_algHom_of_finrank_dvd h
  algebraize [f.toRingHom]
  have := Finite.of_injective _ (algebraMap K L).injective
  rw [Nat.card_congr (Normal.algHomEquivAut F L K)]; rw [IsGalois.card_aut_eq_finrank]

Depends on / 依赖: Finite, Finite.of_injective, IsGalois, IsGalois.card_aut_eq_finrank, Nat.card_congr, Normal, Normal.algHomEquivAut, algHomEquivAut, algebraMap, algebraize, card_aut_eq_finrank, card_congr, f.toRingHom, injective, nonempty_algHom_of_finrank_dvd, of_injective, toRingHom
-/
theorem natCard_algHom_of_finrank_dvd (h : Module.finrank F K ∣ Module.finrank F L) :
    Nat.card (K ->ₐ[F] L) = Module.finrank F K := by
  obtain ⟨f⟩ := nonempty_algHom_of_finrank_dvd h
  algebraize [f.toRingHom]
  have := Finite.of_injective _ (algebraMap K L).injective
  rw [Nat.card_congr (Normal.algHomEquivAut F L K)]; rw [IsGalois.card_aut_eq_finrank]

/--
theorem `card_algHom_of_finrank_dvd` / 定理 `card_algHom_of_finrank_dvd`

English:
theorem card_algHom_of_finrank_dvd
  statement: [Finite K]
  proof: by
  rw [Fintype.card_eq_nat_card]; rw [natCard_algHom_of_finrank_dvd h]

中文:
定理 card_algHom_of_finrank_dvd
  结论: [有限 K]
  证明: by
  rw [Fintype.card_eq_nat_card]; rw [natCard_algHom_of_finrank_dvd h]

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card, card_eq_nat_card, natCard_algHom_of_finrank_dvd
-/
theorem card_algHom_of_finrank_dvd [Finite K]
    (h : Module.finrank F K ∣ Module.finrank F L) :
    Fintype.card (K ->ₐ[F] L) = Module.finrank F K := by
  rw [Fintype.card_eq_nat_card]; rw [natCard_algHom_of_finrank_dvd h]

/--
theorem `nonempty_algHom_iff_finrank_dvd` / 定理 `nonempty_algHom_iff_finrank_dvd`

English:
theorem nonempty_algHom_iff_finrank_dvd
  proof: by
  refine ⟨fun ⟨f⟩ => ?_, nonempty_algHom_of_finrank_dvd⟩
  algebraize [f.toRingHom]
  rw [← Module.finrank_mul_finrank F K L]
  exact dvd_mul_right _ _

中文:
定理 nonempty_algHom_iff_finrank_dvd
  证明: by
  refine ⟨fun ⟨f⟩ => ?_, nonempty_algHom_of_finrank_dvd⟩
  algebraize [f.toRingHom]
  rw [← Module.finrank_mul_finrank F K L]
  exact dvd_mul_right _ _

Depends on / 依赖: Module, Module.finrank_mul_finrank, algebraize, dvd_mul_right, f.toRingHom, finrank_mul_finrank, nonempty_algHom_of_finrank_dvd, toRingHom
-/
theorem nonempty_algHom_iff_finrank_dvd :
    Nonempty (K ->ₐ[F] L) ↔ Module.finrank F K ∣ Module.finrank F L := by
  refine ⟨fun ⟨f⟩ => ?_, nonempty_algHom_of_finrank_dvd⟩
  algebraize [f.toRingHom]
  rw [← Module.finrank_mul_finrank F K L]
  exact dvd_mul_right _ _

end

end FiniteField
