/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Combinatorics.Pigeonhole
public import Mathlib.Algebra.Order.AbsoluteValue.Euclidean

/-!
# Admissible absolute values

This file defines a structure `AbsoluteValue.IsAdmissible` which we use to show the class number
of the ring of integers of a global field is finite.

## Main definitions

* `AbsoluteValue.IsAdmissible abv` states the absolute value `abv : R → ℤ`
  respects the Euclidean domain structure on `R`, and that a large enough set
  of elements of `R^n` contains a pair of elements whose remainders are
  pointwise close together.

## Main results

* `AbsoluteValue.absIsAdmissible` shows the "standard" absolute value on `ℤ`,
  mapping negative `x` to `-x`, is admissible.
* `Polynomial.cardPowDegreeIsAdmissible` shows `cardPowDegree`,
  mapping `p : Polynomial 𝔽_q` to `q ^ degree p`, is admissible
-/

public section

local infixl:50 " ≺ " => EuclideanDomain.r

namespace AbsoluteValue

variable {R : Type*} [EuclideanDomain R]
variable (abv : AbsoluteValue R Int)

/--
Definition of `IsAdmissible` / `IsAdmissible` 的定义

English:
structure IsAdmissible
  parameters: extends IsEuclidean abv
  extends: IsEuclidean abv
  axioms and operations (2):
    - card : Real -> Nat
    - exists_partition' : forall (n : Nat) {ε : Real} (_ : 0 < ε) {b : R} (_ : b != 0) (A : Fin n -> R), exists t : Fin n -> Fin (card ε), forall i₀ i₁, t i₀ = t i₁ -> (abv (A i₁ % b - A i₀ % b) : Real) < abv b • ε

中文:
结构 是Admissible
  参数: extends 是Euclidean abv
  继承: 是Euclidean abv
  公理与运算 (2 个):
    - card : 实数 -> 自然数
    - exists_partition' : 对任意 (n : 自然数) {ε : 实数} (_ : 0 < ε) {b : R} (_ : b != 0) (A : 有限集 n -> R), 存在 t : 有限集 n -> 有限集 (card ε), 对任意 i₀ i₁, t i₀ = t i₁ -> (abv (A i₁ % b - A i₀ % b) : 实数) < abv b • ε
-/
structure IsAdmissible extends IsEuclidean abv where
  /-- The cardinality required for a given `ε`. -/
  protected card : Real -> Nat
  /-- For all `ε > 0` and finite families `A`, we can partition the remainders of `A` mod `b`
  into `abv.card ε` sets, such that all elements in each part of remainders are close together. -/
  exists_partition' :
    forall (n : Nat) {ε : Real} (_ : 0 < ε) {b : R} (_ : b != 0) (A : Fin n -> R),
      exists t : Fin n -> Fin (card ε), forall i₀ i₁, t i₀ = t i₁ -> (abv (A i₁ % b - A i₀ % b) : Real) < abv b • ε

namespace IsAdmissible

variable {abv}

/--
theorem `exists_partition` / 定理 `exists_partition`

English:
theorem exists_partition
  statement: {ι : Type*} [Finite ι] {ε : Real} (hε : 0 < ε) {b : R} (hb : b != 0)
  proof: by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  obtain ⟨t, ht⟩ := h.exists_partition' n hε hb (A ∘ e.symm)
  refine ⟨t ∘ e, fun i₀ i₁ h => ?_⟩
  convert! (config := { transparency := .default }) ht (e i₀) (e i₁) h <;>
    simp only [e.symm_apply_apply]

中文:
定理 存在_partition
  结论: {ι : 类型} [有限 ι] {ε : 实数} (hε : 0 < ε) {b : R} (hb : b != 0)
  证明: by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  obtain ⟨t, ht⟩ := h.exists_partition' n hε hb (A ∘ e.symm)
  refine ⟨t ∘ e, fun i₀ i₁ h => ?_⟩
  convert! (config := { transparency := .default }) ht (e i₀) (e i₁) h <;>
    simp only [e.symm_apply_apply]

Depends on / 依赖: Finite, Finite.exists_equiv_fin, config, convert, e.symm, e.symm_apply_apply, exists_equiv_fin, exists_partition, h.exists_partition, symm_apply_apply, transparency
-/
theorem exists_partition {ι : Type*} [Finite ι] {ε : Real} (hε : 0 < ε) {b : R} (hb : b != 0)
    (A : ι -> R) (h : abv.IsAdmissible) : exists t : ι -> Fin (h.card ε),
      forall i₀ i₁, t i₀ = t i₁ -> (abv (A i₁ % b - A i₀ % b) : Real) < abv b • ε := by
  rcases Finite.exists_equiv_fin ι with ⟨n, ⟨e⟩⟩
  obtain ⟨t, ht⟩ := h.exists_partition' n hε hb (A ∘ e.symm)
  refine ⟨t ∘ e, fun i₀ i₁ h => ?_⟩
  convert! (config := { transparency := .default }) ht (e i₀) (e i₁) h <;>
    simp only [e.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_approx_aux` / 定理 `exists_approx_aux`

English:
theorem exists_approx_aux
  given: (n : Nat) (h : abv.IsAdmissible)
  proof: by
  have := Classical.decEq R
  induction n with
  | zero =>
    intro ε _hε b _hb A
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    rintro ⟨i, ⟨⟩⟩
  | succ n ih =>
  intro ε hε b hb A
  let M := h.card ε
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M ^ n` remainders where the first components lie close together:
  obtain ⟨s, s_inj, hs⟩ :
    exists s : Fin (M ^ n).succ -> Fin (M ^ n.succ).succ,
      Function.Injective s ∧ forall i₀ i₁, (abv (A (s i₁) 0 % b - A (s i₀) 0 % b) : Real) < abv b • ε := by
    -- We can partition the `A`s into `M` subsets where
    -- the first components lie close together:
    obtain ⟨t, ht⟩ :
      exists t : Fin (M ^ n.succ).succ -> Fin M,
        forall i₀ i₁, t i₀ = t i₁ -> (abv (A i₁ 0 % b - A i₀ 0 % b) : Real) < abv b • ε :=
      h.exists_partition hε hb fun x => A x 0
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain ⟨s, hs⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := t)
        (by simpa only [Fintype.card_fin, pow_succ'] using Nat.lt_succ_self (M ^ n.succ))
    have : (M ^ n).succ <= (Finset.toList {x | t x = s}).length := by
      rwa [Finset.length_toList]
    refine ⟨fun i => (Finset.toList {x | t x = s})[i.castLE this], fun i j h => ?_,
      fun i₀ i₁ => ht _ _ ?_⟩
    · simpa [(Finset.nodup_toList _).getElem_inj_iff, Fin.val_inj] using h
    · have (i : Fin (M ^ n).succ) : t (Finset.toList {x | t x = s})[i.castLE this] = s :=
        (Finset.mem_filter.mp ((Finset.mem_toList (s := {x | t x = s})).mp (List.getElem_mem _))).2
      simp_rw [this]
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb fun x => Fin.tail (A (s x))
  refine ⟨s k₀, s k₁, fun h => hk (s_inj h), fun i => Fin.cases ?_ (fun i => ?_) i⟩
  · exact hs k₀ k₁
  · exact h i

中文:
定理 存在_approx_aux
  条件: (n : 自然数) (h : abv.是Admissible)
  证明: by
  have := Classical.decEq R
  induction n with
  | zero =>
    intro ε _hε b _hb A
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    rintro ⟨i, ⟨⟩⟩
  | succ n ih =>
  intro ε hε b hb A
  let M := h.card ε
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M ^ n` remainders where the first components lie close together:
  obtain ⟨s, s_inj, hs⟩ :
    exists s : Fin (M ^ n).succ -> Fin (M ^ n.succ).succ,
      Function.Injective s ∧ forall i₀ i₁, (abv (A (s i₁) 0 % b - A (s i₀) 0 % b) : Real) < abv b • ε := by
    -- We can partition the `A`s into `M` subsets where
    -- the first components lie close together:
    obtain ⟨t, ht⟩ :
      exists t : Fin (M ^ n.succ).succ -> Fin M,
        forall i₀ i₁, t i₀ = t i₁ -> (abv (A i₁ 0 % b - A i₀ 0 % b) : Real) < abv b • ε :=
      h.exists_partition hε hb fun x => A x 0
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain ⟨s, hs⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := t)
        (by simpa only [Fintype.card_fin, pow_succ'] using Nat.lt_succ_self (M ^ n.succ))
    have : (M ^ n).succ <= (Finset.toList {x | t x = s}).length := by
      rwa [Finset.length_toList]
    refine ⟨fun i => (Finset.toList {x | t x = s})[i.castLE this], fun i j h => ?_,
      fun i₀ i₁ => ht _ _ ?_⟩
    · simpa [(Finset.nodup_toList _).getElem_inj_iff, Fin.val_inj] using h
    · have (i : Fin (M ^ n).succ) : t (Finset.toList {x | t x = s})[i.castLE this] = s :=
        (Finset.mem_filter.mp ((Finset.mem_toList (s := {x | t x = s})).mp (List.getElem_mem _))).2
      simp_rw [this]
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb fun x => Fin.tail (A (s x))
  refine ⟨s k₀, s k₁, fun h => hk (s_inj h), fun i => Fin.cases ?_ (fun i => ?_) i⟩
  · exact hs k₀ k₁
  · exact h i

Depends on / 依赖: Classical, Classical.decEq, h.card
-/
theorem exists_approx_aux (n : Nat) (h : abv.IsAdmissible) :
    forall {ε : Real} (_hε : 0 < ε) {b : R} (_hb : b != 0) (A : Fin (h.card ε ^ n).succ -> Fin n -> R),
      exists i₀ i₁, i₀ != i₁ ∧ forall k, (abv (A i₁ k % b - A i₀ k % b) : Real) < abv b • ε := by
  have := Classical.decEq R
  induction n with
  | zero =>
    intro ε _hε b _hb A
    refine ⟨0, 1, ?_, ?_⟩
    · simp
    rintro ⟨i, ⟨⟩⟩
  | succ n ih =>
  intro ε hε b hb A
  let M := h.card ε
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M ^ n` remainders where the first components lie close together:
  obtain ⟨s, s_inj, hs⟩ :
    exists s : Fin (M ^ n).succ -> Fin (M ^ n.succ).succ,
      Function.Injective s ∧ forall i₀ i₁, (abv (A (s i₁) 0 % b - A (s i₀) 0 % b) : Real) < abv b • ε := by
    -- We can partition the `A`s into `M` subsets where
    -- the first components lie close together:
    obtain ⟨t, ht⟩ :
      exists t : Fin (M ^ n.succ).succ -> Fin M,
        forall i₀ i₁, t i₀ = t i₁ -> (abv (A i₁ 0 % b - A i₀ 0 % b) : Real) < abv b • ε :=
      h.exists_partition hε hb fun x => A x 0
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain ⟨s, hs⟩ :=
      Fintype.exists_lt_card_fiber_of_mul_lt_card (f := t)
        (by simpa only [Fintype.card_fin, pow_succ'] using Nat.lt_succ_self (M ^ n.succ))
    have : (M ^ n).succ <= (Finset.toList {x | t x = s}).length := by
      rwa [Finset.length_toList]
    refine ⟨fun i => (Finset.toList {x | t x = s})[i.castLE this], fun i j h => ?_,
      fun i₀ i₁ => ht _ _ ?_⟩
    · simpa [(Finset.nodup_toList _).getElem_inj_iff, Fin.val_inj] using h
    · have (i : Fin (M ^ n).succ) : t (Finset.toList {x | t x = s})[i.castLE this] = s :=
        (Finset.mem_filter.mp ((Finset.mem_toList (s := {x | t x = s})).mp (List.getElem_mem _))).2
      simp_rw [this]
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb fun x => Fin.tail (A (s x))
  refine ⟨s k₀, s k₁, fun h => hk (s_inj h), fun i => Fin.cases ?_ (fun i => ?_) i⟩
  · exact hs k₀ k₁
  · exact h i

/--
theorem `exists_approx` / 定理 `exists_approx`

English:
theorem exists_approx
  statement: {ι : Type*} [Fintype ι] {ε : Real} (hε : 0 < ε) {b : R} (hb : b != 0)
  proof: by
  let e := Fintype.equivFin ι
  obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (Fintype.card ι) hε hb fun x y => A x (e.symm y)
  refine ⟨i₀, i₁, ne, fun k => ?_⟩
  convert! h (e k) <;> simp only [e.symm_apply_apply]

中文:
定理 存在_approx
  结论: {ι : 类型} [有限类型 ι] {ε : 实数} (hε : 0 < ε) {b : R} (hb : b != 0)
  证明: by
  let e := Fintype.equivFin ι
  obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (Fintype.card ι) hε hb fun x y => A x (e.symm y)
  refine ⟨i₀, i₁, ne, fun k => ?_⟩
  convert! h (e k) <;> simp only [e.symm_apply_apply]

Depends on / 依赖: Fintype, Fintype.card, Fintype.equivFin, convert, e.symm, e.symm_apply_apply, equivFin, exists_approx_aux, h.exists_approx_aux, symm_apply_apply
-/
theorem exists_approx {ι : Type*} [Fintype ι] {ε : Real} (hε : 0 < ε) {b : R} (hb : b != 0)
    (h : abv.IsAdmissible) (A : Fin (h.card ε ^ Fintype.card ι).succ -> ι -> R) :
    exists i₀ i₁, i₀ != i₁ ∧ forall k, (abv (A i₁ k % b - A i₀ k % b) : Real) < abv b • ε := by
  let e := Fintype.equivFin ι
  obtain ⟨i₀, i₁, ne, h⟩ := h.exists_approx_aux (Fintype.card ι) hε hb fun x y => A x (e.symm y)
  refine ⟨i₀, i₁, ne, fun k => ?_⟩
  convert! h (e k) <;> simp only [e.symm_apply_apply]

end IsAdmissible

end AbsoluteValue
