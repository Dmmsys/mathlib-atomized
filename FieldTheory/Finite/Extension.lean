/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Kevin Buzzard
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Extensions of finite fields

In this file we develop the theory of extensions of finite fields.

If `k` is a finite field (of cardinality `q = p ^ m`), then there is a unique (up to in general
non-unique isomorphism) extension `l` of `k` of any given degree `n > 0`.

This extension is Galois with cyclic Galois group of degree `n`, and the (arithmetic) Frobenius map
`x ↦ x ^ q` is a generator.


## Main definition

* `FiniteField.Extension k p n` is a non-canonically chosen extension of `k` of degree `n`
  (for `n > 0`).

## Main Results

* `FiniteField.algEquivExtension`: any other field extension `l/k` of degree `n` is (non-uniquely)
  isomorphic to our chosen `FiniteField.Extension k p n`.

-/

@[expose] public section

noncomputable section

variable (k : Type*) [Field k] [Finite k]
variable (p : Nat) [Fact p.Prime] [CharP k p]
variable (n : Nat) [NeZero n]

open Polynomial

namespace FiniteField

/--
Definition of `Extension` / `Extension` 的定义

English:
definition Extension
  signature: : Type
  body: letI := ZMod.algebra k p
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)

中文:
定义 扩张
  签名: : 类型
  定义体: letI := ZMod.algebra k p
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)

Depends on / 依赖: GaloisField, Module, Module.finrank, ZMod.algebra, algebra, finrank
-/
def Extension : Type :=
  letI := ZMod.algebra k p
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)

/--
theorem `finrank_zmod_extension` / 定理 `finrank_zmod_extension`

English:
theorem finrank_zmod_extension
  given: [Algebra (ZMod p) k]
  proof: by
  let := ZMod.algebra k p
  unfold Extension
  convert!
GaloisField.finrank p (n := Module.finrank (ZMod p) k * n)
mul_ne_zero Module.finrank_pos.ne' NeZero.ne n
  subsingleton

中文:
定理 finrank_zmod_extension
  条件: [代数 (ZMod p) k]
  证明: by
  let := ZMod.algebra k p
  unfold Extension
  convert!
GaloisField.finrank p (n := Module.finrank (ZMod p) k * n)
mul_ne_zero Module.finrank_pos.ne' NeZero.ne n
  subsingleton

Depends on / 依赖: Extension, GaloisField, GaloisField.finrank, Module, Module.finrank, Module.finrank_pos.ne, NeZero, NeZero.ne, ZMod.algebra, algebra, convert, finrank, finrank_pos, mul_ne_zero, subsingleton
-/
theorem finrank_zmod_extension [Algebra (ZMod p) k] :
    Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k * n := by
  let := ZMod.algebra k p
  unfold Extension
  convert!
GaloisField.finrank p (n := Module.finrank (ZMod p) k * n)
mul_ne_zero Module.finrank_pos.ne' NeZero.ne n
  subsingleton

/--
theorem `nonempty_algHom_extension` / 定理 `nonempty_algHom_extension`

English:
theorem nonempty_algHom_extension
  given: [Algebra (ZMod p) k]
  proof: nonempty_algHom_of_finrank_dvd (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)

中文:
定理 nonempty_algHom_extension
  条件: [代数 (ZMod p) k]
  证明: nonempty_algHom_of_finrank_dvd (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)

Depends on / 依赖: dvd_mul_right, finrank_zmod_extension, nonempty_algHom_of_finrank_dvd
-/
theorem nonempty_algHom_extension [Algebra (ZMod p) k] :
    Nonempty (k ->ₐ[ZMod p] Extension k p n) :=
  nonempty_algHom_of_finrank_dvd (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra k (Extension k p n)
  body: letI := ZMod.algebra k p
  (nonempty_algHom_extension k p n).some.toAlgebra

中文:
实例 :
  签名: 代数 k (扩张 k p n)
  定义体: letI := ZMod.algebra k p
  (nonempty_algHom_extension k p n).some.toAlgebra

Depends on / 依赖: ZMod.algebra, algebra, nonempty_algHom_extension, some.toAlgebra, toAlgebra
-/
noncomputable instance : Algebra k (Extension k p n) :=
  letI := ZMod.algebra k p
  (nonempty_algHom_extension k p n).some.toAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module.Finite k (Extension k p n)
  body: .of_finite

中文:
实例 :
  签名: 模.有限 k (扩张 k p n)
  定义体: .of_finite

Depends on / 依赖: of_finite
-/
instance : Module.Finite k (Extension k p n) :=
  .of_finite

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Algebra
  signature: (ZMod p) k] : IsScalarTower (ZMod p) k (Extension k p n)
  body: -- there is at most one map from `𝔽_p` to any ring
.of_algebraMap_eq' Subsingleton.elim _ _

中文:
实例 [代数
  签名: (ZMod p) k] : 标量塔 (ZMod p) k (扩张 k p n)
  定义体: -- there is at most one map from `𝔽_p` to any ring
.of_algebraMap_eq' Subsingleton.elim _ _
-/
instance [Algebra (ZMod p) k] : IsScalarTower (ZMod p) k (Extension k p n) :=
  -- there is at most one map from `𝔽_p` to any ring
.of_algebraMap_eq' Subsingleton.elim _ _

/--
theorem `natCard_extension` / 定理 `natCard_extension`

English:
theorem natCard_extension
  statement: Nat.card (Extension k p n) = Nat.card k ^ n
  proof: by
  let := ZMod.algebra k p
  rw [← pow_finrank_eq_natCard p]; rw [← pow_finrank_eq_natCard p]; rw [finrank_zmod_extension]; rw [pow_mul]

中文:
定理 natCard_extension
  结论: 自然数.card (扩张 k p n) = 自然数.card k ^ n
  证明: by
  let := ZMod.algebra k p
  rw [← pow_finrank_eq_natCard p]; rw [← pow_finrank_eq_natCard p]; rw [finrank_zmod_extension]; rw [pow_mul]

Depends on / 依赖: ZMod.algebra, algebra, finrank_zmod_extension, pow_finrank_eq_natCard, pow_mul
-/
theorem natCard_extension : Nat.card (Extension k p n) = Nat.card k ^ n := by
  let := ZMod.algebra k p
  rw [← pow_finrank_eq_natCard p]; rw [← pow_finrank_eq_natCard p]; rw [finrank_zmod_extension]; rw [pow_mul]

/--
theorem `finrank_extension` / 定理 `finrank_extension`

English:
theorem finrank_extension
  statement: Module.finrank k (Extension k p n) = n
  proof: by
  refine Nat.pow_right_injective (Finite.one_lt_card : 2 <= Nat.card k) ?_
  simp only [← Module.natCard_eq_pow_finrank, natCard_extension]

中文:
定理 finrank_extension
  结论: 模.finrank k (扩张 k p n) = n
  证明: by
  refine Nat.pow_right_injective (Finite.one_lt_card : 2 <= Nat.card k) ?_
  simp only [← Module.natCard_eq_pow_finrank, natCard_extension]

Depends on / 依赖: Finite, Finite.one_lt_card, Module, Module.natCard_eq_pow_finrank, Nat.card, Nat.pow_right_injective, natCard_eq_pow_finrank, natCard_extension, one_lt_card, pow_right_injective
-/
theorem finrank_extension : Module.finrank k (Extension k p n) = n := by
  refine Nat.pow_right_injective (Finite.one_lt_card : 2 <= Nat.card k) ?_
  simp only [← Module.natCard_eq_pow_finrank, natCard_extension]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsSplittingField k (Extension k p n) (X ^ Nat.card k ^ n - X)
  body: by
  have := Fintype.ofFinite (Extension k p n)
  convert! FiniteField.isSplittingField_sub (Extension k p n) k
  · rw [Fintype.card_eq_nat_card, natCard_extension]

example : IsGalois k (Extension k p n) :=
  inferInstance

example : IsCyclic Gal(Extension k p n / k) :=
  inferInstance

中文:
实例 :
  签名: 是分裂域 k (扩张 k p n) (X ^ 自然数.card k ^ n - X)
  定义体: by
  have := Fintype.ofFinite (Extension k p n)
  convert! FiniteField.isSplittingField_sub (Extension k p n) k
  · rw [Fintype.card_eq_nat_card, natCard_extension]

example : IsGalois k (Extension k p n) :=
  inferInstance

example : IsCyclic Gal(Extension k p n / k) :=
  inferInstance

Depends on / 依赖: Extension, FiniteField, FiniteField.isSplittingField_sub, Fintype, Fintype.card_eq_nat_card, Fintype.ofFinite, card_eq_nat_card, convert, isSplittingField_sub, natCard_extension, ofFinite
-/
instance : IsSplittingField k (Extension k p n) (X ^ Nat.card k ^ n - X) := by
  have := Fintype.ofFinite (Extension k p n)
  convert! FiniteField.isSplittingField_sub (Extension k p n) k
  · rw [Fintype.card_eq_nat_card, natCard_extension]

example : IsGalois k (Extension k p n) :=
  inferInstance

example : IsCyclic Gal(Extension k p n / k) :=
  inferInstance

/--
theorem `natCard_algEquiv_extension` / 定理 `natCard_algEquiv_extension`

English:
theorem natCard_algEquiv_extension
  statement: Nat.card Gal(Extension k p n / k) = n
  proof: (IsGalois.card_aut_eq_finrank _ _).trans finrank_extension k p n

中文:
定理 natCard_algEquiv_extension
  结论: 自然数.card Gal(扩张 k p n / k) = n
  证明: (IsGalois.card_aut_eq_finrank _ _).trans finrank_extension k p n

Depends on / 依赖: IsGalois, IsGalois.card_aut_eq_finrank, card_aut_eq_finrank, finrank_extension
-/
theorem natCard_algEquiv_extension : Nat.card Gal(Extension k p n / k) = n :=
(IsGalois.card_aut_eq_finrank _ _).trans finrank_extension k p n

/--
theorem `card_algEquiv_extension` / 定理 `card_algEquiv_extension`

English:
theorem card_algEquiv_extension
  statement: Fintype.card Gal(Extension k p n / k) = n
  proof: Fintype.card_eq_nat_card.trans natCard_algEquiv_extension k p n

中文:
定理 card_algEquiv_extension
  结论: 有限类型.card Gal(扩张 k p n / k) = n
  证明: Fintype.card_eq_nat_card.trans natCard_algEquiv_extension k p n

Depends on / 依赖: Fintype, Fintype.card_eq_nat_card.trans, card_eq_nat_card, natCard_algEquiv_extension
-/
theorem card_algEquiv_extension : Fintype.card Gal(Extension k p n / k) = n :=
Fintype.card_eq_nat_card.trans natCard_algEquiv_extension k p n

/--
Definition of `Extension.frob` / `Extension.frob` 的定义

English:
definition Extension.frob
  signature: :
  body: haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _

中文:
定义 扩张.frob
  签名: :
  定义体: haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _

Depends on / 依赖: FiniteField, FiniteField.frobeniusAlgEquivOfAlgebraic, Fintype, Fintype.ofFinite, frobeniusAlgEquivOfAlgebraic, ofFinite
-/
noncomputable def Extension.frob :
    Gal(Extension k p n / k) :=
  haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _

/--
lemma `Extension.frob_apply` / 引理 `Extension.frob_apply`

English:
lemma Extension.frob_apply
  given: {x : Extension k p n}
  proof: by
  simp [frob, ← Nat.card_eq_fintype_card]

@[simp]

中文:
引理 扩张.frob_apply
  条件: {x : 扩张 k p n}
  证明: by
  simp [frob, ← Nat.card_eq_fintype_card]

@[simp]
-/
@[simp] lemma Extension.frob_apply {x : Extension k p n} :
    frob k p n x = x ^ Nat.card k := by
  simp [frob, ← Nat.card_eq_fintype_card]

@[simp]
/--
theorem `Extension.frob_iterate_apply` / 定理 `Extension.frob_iterate_apply`

English:
theorem Extension.frob_iterate_apply
  given: (i : Nat) {x : Extension k p n}
  proof: by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [pow_add]; rw [pow_one]; rw [AlgEquiv.mul_apply]; rw [ih]; rw [frob_apply]; rw [← pow_mul]; rw [← Nat.pow_add_one']

中文:
定理 扩张.frob_iterate_apply
  条件: (i : 自然数) {x : 扩张 k p n}
  证明: by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [pow_add]; rw [pow_one]; rw [AlgEquiv.mul_apply]; rw [ih]; rw [frob_apply]; rw [← pow_mul]; rw [← Nat.pow_add_one']

Depends on / 依赖: AlgEquiv, AlgEquiv.mul_apply, Nat.pow_add_one, frob_apply, generalizing, mul_apply, pow_add, pow_add_one, pow_mul, pow_one
-/
theorem Extension.frob_iterate_apply (i : Nat) {x : Extension k p n} :
    (frob k p n ^ i) x = x ^ (Nat.card k ^ i) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [pow_add]; rw [pow_one]; rw [AlgEquiv.mul_apply]; rw [ih]; rw [frob_apply]; rw [← pow_mul]; rw [← Nat.pow_add_one']

/--
theorem `Extension.exists_frob_pow_eq` / 定理 `Extension.exists_frob_pow_eq`

English:
theorem Extension.exists_frob_pow_eq
  given: (g : Gal(Extension k p n/k))
  proof: by
  let := Fintype.ofFinite k
  obtain ⟨⟨i, hi⟩, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (Extension k p n)).2 g
  refine ⟨i, ?_, by ext; simp [frob]⟩
  rwa [finrank_extension] at hi

中文:
定理 扩张.存在_frob_pow_eq
  条件: (g : Gal(扩张 k p n/k))
  证明: by
  let := Fintype.ofFinite k
  obtain ⟨⟨i, hi⟩, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (Extension k p n)).2 g
  refine ⟨i, ?_, by ext; simp [frob]⟩
  rwa [finrank_extension] at hi

Depends on / 依赖: Extension, FiniteField, FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow, Fintype, Fintype.ofFinite, bijective_frobeniusAlgEquivOfAlgebraic_pow, finrank_extension, ofFinite
-/
theorem Extension.exists_frob_pow_eq (g : Gal(Extension k p n/k)) :
    exists i < n, Extension.frob k p n ^ i = g := by
  let := Fintype.ofFinite k
  obtain ⟨⟨i, hi⟩, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (Extension k p n)).2 g
  refine ⟨i, ?_, by ext; simp [frob]⟩
  rwa [finrank_extension] at hi

/--
Definition of `algEquivExtension` / `algEquivExtension` 的定义

English:
definition algEquivExtension
  signature: (l : Type*) [Field l] [Algebra k l]
  body: by
  refine Nonempty.some ?_
have : Module.Finite k l := Module.finite_of_finrank_pos h ▸ NeZero.pos n
  have : Finite l := Module.finite_of_finite k
  have : Fintype l := .ofFinite _
  have : IsSplittingField k l (X ^ Nat.card k ^ n - X) := by
    rw [← h]; rw [← Module.natCard_eq_pow_finrank]; rw [← Fintype.card_eq_nat_card]
    exact FiniteField.isSplittingField_sub l k
  refine ⟨(IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).trans ?_⟩
  exact (IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).symm

include p in

中文:
定义 algEquivExtension
  签名: (l : 类型) [域 l] [代数 k l]
  定义体: by
  refine Nonempty.some ?_
have : Module.Finite k l := Module.finite_of_finrank_pos h ▸ NeZero.pos n
  have : Finite l := Module.finite_of_finite k
  have : Fintype l := .ofFinite _
  have : IsSplittingField k l (X ^ Nat.card k ^ n - X) := by
    rw [← h]; rw [← Module.natCard_eq_pow_finrank]; rw [← Fintype.card_eq_nat_card]
    exact FiniteField.isSplittingField_sub l k
  refine ⟨(IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).trans ?_⟩
  exact (IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).symm

include p in

Depends on / 依赖: Finite, FiniteField, FiniteField.isSplittingField_sub, Fintype, Fintype.card_eq_nat_card, IsSplittingField, IsSplittingField.algEquiv, Module, Module.Finite, Module.finite_of_finite, Module.finite_of_finrank_pos, Module.natCard_eq_pow_finrank, Nat.card, NeZero, NeZero.pos, Nonempty, Nonempty.some, algEquiv, card_eq_nat_card, finite_of_finite
-/
noncomputable def algEquivExtension (l : Type*) [Field l] [Algebra k l]
    (h : Module.finrank k l = n) : l ≃ₐ[k] Extension k p n := by
  refine Nonempty.some ?_
have : Module.Finite k l := Module.finite_of_finrank_pos h ▸ NeZero.pos n
  have : Finite l := Module.finite_of_finite k
  have : Fintype l := .ofFinite _
  have : IsSplittingField k l (X ^ Nat.card k ^ n - X) := by
    rw [← h]; rw [← Module.natCard_eq_pow_finrank]; rw [← Fintype.card_eq_nat_card]
    exact FiniteField.isSplittingField_sub l k
  refine ⟨(IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).trans ?_⟩
  exact (IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).symm

include p in
/--
theorem `exists_forall_apply_eq_pow` / 定理 `exists_forall_apply_eq_pow`

English:
theorem exists_forall_apply_eq_pow
  given: (l : Type*) [Field l] [Algebra k l] [Finite l] (g : Gal(l/k))
  proof: by
  let n := Module.finrank k l
  have : NeZero n := NeZero.of_pos Module.finrank_pos
obtain ⟨i, _, hi⟩ := Extension.exists_frob_pow_eq k p n
    (algEquivExtension k p n l rfl).symm.trans (g.trans (algEquivExtension k p n l rfl))
  refine ⟨i, fun x => ?_⟩
  simpa using (AlgEquiv.congr_arg (f := (algEquivExtension k p n l rfl).symm) <|
    AlgEquiv.congr_fun hi (algEquivExtension k p n l rfl x)).symm

中文:
定理 存在_对任意_apply_eq_pow
  条件: (l : 类型) [域 l] [代数 k l] [有限 l] (g : Gal(l/k))
  证明: by
  let n := Module.finrank k l
  have : NeZero n := NeZero.of_pos Module.finrank_pos
obtain ⟨i, _, hi⟩ := Extension.exists_frob_pow_eq k p n
    (algEquivExtension k p n l rfl).symm.trans (g.trans (algEquivExtension k p n l rfl))
  refine ⟨i, fun x => ?_⟩
  simpa using (AlgEquiv.congr_arg (f := (algEquivExtension k p n l rfl).symm) <|
    AlgEquiv.congr_fun hi (algEquivExtension k p n l rfl x)).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.congr_arg, AlgEquiv.congr_fun, Extension, Extension.exists_frob_pow_eq, Module, Module.finrank, Module.finrank_pos, NeZero, NeZero.of_pos, algEquivExtension, congr_arg, congr_fun, exists_frob_pow_eq, finrank, finrank_pos, g.trans, of_pos, symm.trans
-/
theorem exists_forall_apply_eq_pow (l : Type*) [Field l] [Algebra k l] [Finite l] (g : Gal(l/k)) :
    exists i, forall x, g x = x ^ (Nat.card k ^ i) := by
  let n := Module.finrank k l
  have : NeZero n := NeZero.of_pos Module.finrank_pos
obtain ⟨i, _, hi⟩ := Extension.exists_frob_pow_eq k p n
    (algEquivExtension k p n l rfl).symm.trans (g.trans (algEquivExtension k p n l rfl))
  refine ⟨i, fun x => ?_⟩
  simpa using (AlgEquiv.congr_arg (f := (algEquivExtension k p n l rfl).symm) <|
    AlgEquiv.congr_fun hi (algEquivExtension k p n l rfl x)).symm

end FiniteField

namespace Irreducible

open FiniteField

variable {k}
variable {f : k[X]} (hi : Irreducible f)
include hi

omit [Finite k] in -- Junk for `Nat.card` allows us to omit the finiteness assumption here.
/--
theorem `natDegree_dvd_of_dvd_X_pow_card_pow_sub_X` / 定理 `natDegree_dvd_of_dvd_X_pow_card_pow_sub_X`

English:
theorem natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
  given: {n : Nat} (h : f ∣ X ^ (Nat.card k) ^ n - X)
  proof: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  cases finite_or_infinite k; swap
  · rw [Nat.card_eq_zero_of_infinite, zero_pow hn, pow_zero, ← dvd_neg, neg_sub] at h
    rw [((Splits.X_sub_C 1).of_dvd (X_sub_C_ne_zero 1) h).natDegree_eq_one_of_irreducible hi]
    exact one_dvd n
  let ⟨p, hp⟩ := CharP.exists k
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  have : NeZero n := ⟨hn⟩
  rw [← finrank_extension k p n]
  apply Irreducible.natDegree_dvd_finrank hi
  refine Splits.of_dvd ?_ ?_ (map_dvd (algebraMap _ (Extension _ p n)) h)
  · apply IsSplittingField.splits
  · exact map_ne_zero (X_pow_card_pow_sub_X_ne_zero _ hn Finite.one_lt_card)

中文:
定理 natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
  条件: {n : 自然数} (h : f ∣ X ^ (自然数.card k) ^ n - X)
  证明: by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  cases finite_or_infinite k; swap
  · rw [Nat.card_eq_zero_of_infinite, zero_pow hn, pow_zero, ← dvd_neg, neg_sub] at h
    rw [((Splits.X_sub_C 1).of_dvd (X_sub_C_ne_zero 1) h).natDegree_eq_one_of_irreducible hi]
    exact one_dvd n
  let ⟨p, hp⟩ := CharP.exists k
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  have : NeZero n := ⟨hn⟩
  rw [← finrank_extension k p n]
  apply Irreducible.natDegree_dvd_finrank hi
  refine Splits.of_dvd ?_ ?_ (map_dvd (algebraMap _ (Extension _ p n)) h)
  · apply IsSplittingField.splits
  · exact map_ne_zero (X_pow_card_pow_sub_X_ne_zero _ hn Finite.one_lt_card)

Depends on / 依赖: CharP.char_is_prime, CharP.exists, Irreducible, Irreducible.natDegree_dvd_finrank, Nat.Prime, Nat.card_eq_zero_of_infinite, NeZero, Splits, Splits.X_sub_C, Splits.of_dvd, X_sub_C, X_sub_C_ne_zero, algebraMap, card_eq_zero_of_infinite, char_is_prime, dvd_neg, eq_or_ne, finite_or_infinite, finrank_extension, map_dvd
-/
theorem natDegree_dvd_of_dvd_X_pow_card_pow_sub_X {n : Nat} (h : f ∣ X ^ (Nat.card k) ^ n - X) :
    f.natDegree ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  cases finite_or_infinite k; swap
  · rw [Nat.card_eq_zero_of_infinite, zero_pow hn, pow_zero, ← dvd_neg, neg_sub] at h
    rw [((Splits.X_sub_C 1).of_dvd (X_sub_C_ne_zero 1) h).natDegree_eq_one_of_irreducible hi]
    exact one_dvd n
  let ⟨p, hp⟩ := CharP.exists k
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  have : NeZero n := ⟨hn⟩
  rw [← finrank_extension k p n]
  apply Irreducible.natDegree_dvd_finrank hi
  refine Splits.of_dvd ?_ ?_ (map_dvd (algebraMap _ (Extension _ p n)) h)
  · apply IsSplittingField.splits
  · exact map_ne_zero (X_pow_card_pow_sub_X_ne_zero _ hn Finite.one_lt_card)

/--
theorem `natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X` / 定理 `natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X`

English:
theorem natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
  given: {n : Nat}
  proof: by
  refine ⟨fun hdvd => dvd_trans ?_ (dvd_pow_pow_sub_self_of_dvd hdvd),
    hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X⟩
  let a := AdjoinRoot.root f
  have : NeZero f.natDegree := NeZero.of_pos (Irreducible.natDegree_pos hi)
have : Fact Irreducible f := ⟨hi⟩
  rw [← hi.dvd_iff_aeval_eq_zero (b := a) (by aesop)]
  let ⟨p, hp⟩ := CharP.exists k
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  let e := FiniteField.algEquivExtension k p f.natDegree (AdjoinRoot f)
    (finrank_quotient_span_eq_natDegree (f := f))
  have hpeval : (e a) ^ (Nat.card k) ^ f.natDegree - (e a) = 0 := by
    have := Fintype.ofFinite (Extension k p f.natDegree)
    rw [← (natCard_extension k p f.natDegree)]; rw [← Fintype.card_eq_nat_card]; rw [pow_card (e a)]; rw [sub_self]
  apply_fun e.symm at hpeval
  simpa using hpeval

中文:
定理 natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X
  条件: {n : 自然数}
  证明: by
  refine ⟨fun hdvd => dvd_trans ?_ (dvd_pow_pow_sub_self_of_dvd hdvd),
    hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X⟩
  let a := AdjoinRoot.root f
  have : NeZero f.natDegree := NeZero.of_pos (Irreducible.natDegree_pos hi)
have : Fact Irreducible f := ⟨hi⟩
  rw [← hi.dvd_iff_aeval_eq_zero (b := a) (by aesop)]
  let ⟨p, hp⟩ := CharP.exists k
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  let e := FiniteField.algEquivExtension k p f.natDegree (AdjoinRoot f)
    (finrank_quotient_span_eq_natDegree (f := f))
  have hpeval : (e a) ^ (Nat.card k) ^ f.natDegree - (e a) = 0 := by
    have := Fintype.ofFinite (Extension k p f.natDegree)
    rw [← (natCard_extension k p f.natDegree)]; rw [← Fintype.card_eq_nat_card]; rw [pow_card (e a)]; rw [sub_self]
  apply_fun e.symm at hpeval
  simpa using hpeval

Depends on / 依赖: AdjoinRoot, AdjoinRoot.root, CharP.char_is_prime, CharP.exists, FiniteField, FiniteField.algEquivExtension, Irreducible, Irreducible.natDegree_pos, Nat.Prime, NeZero, NeZero.of_pos, algEquivExtension, char_is_prime, dvd_iff_aeval_eq_zero, dvd_pow_pow_sub_self_of_dvd, dvd_trans, f.natDegree, finrank_quotient_span_eq_natDegree, hi.dvd_iff_aeval_eq_zero, hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X
-/
theorem natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X {n : Nat} :
    f.natDegree ∣ n ↔ f ∣ X ^ (Nat.card k) ^ n - X := by
  refine ⟨fun hdvd => dvd_trans ?_ (dvd_pow_pow_sub_self_of_dvd hdvd),
    hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X⟩
  let a := AdjoinRoot.root f
  have : NeZero f.natDegree := NeZero.of_pos (Irreducible.natDegree_pos hi)
have : Fact Irreducible f := ⟨hi⟩
  rw [← hi.dvd_iff_aeval_eq_zero (b := a) (by aesop)]
  let ⟨p, hp⟩ := CharP.exists k
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  let e := FiniteField.algEquivExtension k p f.natDegree (AdjoinRoot f)
    (finrank_quotient_span_eq_natDegree (f := f))
  have hpeval : (e a) ^ (Nat.card k) ^ f.natDegree - (e a) = 0 := by
    have := Fintype.ofFinite (Extension k p f.natDegree)
    rw [← (natCard_extension k p f.natDegree)]; rw [← Fintype.card_eq_nat_card]; rw [pow_card (e a)]; rw [sub_self]
  apply_fun e.symm at hpeval
  simpa using hpeval

end Irreducible
