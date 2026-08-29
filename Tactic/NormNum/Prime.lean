/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Prime.Basic
public meta import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Tactic.NormNum.Basic
public meta import Mathlib.Tactic.NormNum.Result

/-!
# `norm_num` extensions on natural numbers

This file provides a `norm_num` extension to prove that natural numbers are prime and compute
its minimal factor. Todo: compute the list of all factors.


## Implementation Notes

For numbers larger than 25 bits, the primality proof produced by `norm_num` is an expression
that is thousands of levels deep, and the Lean kernel seems to raise a stack overflow when
type-checking that proof. If we want an implementation that works for larger primes, we should
generate a proof that has a smaller depth.

Note: `evalMinFac.aux` does not raise a stack overflow, which can be checked by replacing the
`prf'` in the recursive call by something like `(.sort .zero)`
-/

public meta section

open Nat Qq Lean Meta

namespace Mathlib.Meta.NormNum

/--
theorem `not_prime_mul_of_ble` / 定理 `not_prime_mul_of_ble`

English:
theorem not_prime_mul_of_ble
  statement: (a b n : Nat) (h : a * b = n) (h₁ : a.ble 1 = false)
  proof: not_prime_of_mul_eq h (ble_eq_false.mp h₁).ne' (ble_eq_false.mp h₂).ne'

中文:
定理 not_prime_mul_of_ble
  结论: (a b n : 自然数) (h : a * b = n) (h₁ : a.ble 1 = false)
  证明: not_prime_of_mul_eq h (ble_eq_false.mp h₁).ne' (ble_eq_false.mp h₂).ne'

Depends on / 依赖: ble_eq_false, ble_eq_false.mp, not_prime_of_mul_eq
-/
theorem not_prime_mul_of_ble (a b n : Nat) (h : a * b = n) (h₁ : a.ble 1 = false)
    (h₂ : b.ble 1 = false) : ¬ n.Prime :=
  not_prime_of_mul_eq h (ble_eq_false.mp h₁).ne' (ble_eq_false.mp h₂).ne'

/--
Definition of `deriveNotPrime` / `deriveNotPrime` 的定义

English:
definition deriveNotPrime
  signature: (n d : Nat) (en : Q(Nat))
  body: Id.run do
  let d' : Nat := n / d
  let prf : Q($d * $d' = $en) := (q(Eq.refl $en) : Expr)
  let r : Q(Nat.ble $d 1 = false) := (q(Eq.refl false) : Expr)
  let r' : Q(Nat.ble $d' 1 = false) := (q(Eq.refl false) : Expr)
  return q(not_prime_mul_of_ble _ _ _ $prf $r $r')

中文:
定义 deriveNotPrime
  签名: (n d : 自然数) (en : Q(自然数))
  定义体: Id.run do
  let d' : Nat := n / d
  let prf : Q($d * $d' = $en) := (q(Eq.refl $en) : Expr)
  let r : Q(Nat.ble $d 1 = false) := (q(Eq.refl false) : Expr)
  let r' : Q(Nat.ble $d' 1 = false) := (q(Eq.refl false) : Expr)
  return q(not_prime_mul_of_ble _ _ _ $prf $r $r')

Depends on / 依赖: Id.run
-/
def deriveNotPrime (n d : Nat) (en : Q(Nat)) : Q(¬ Nat.Prime $en) := Id.run do
  let d' : Nat := n / d
  let prf : Q($d * $d' = $en) := (q(Eq.refl $en) : Expr)
  let r : Q(Nat.ble $d 1 = false) := (q(Eq.refl false) : Expr)
  let r' : Q(Nat.ble $d' 1 = false) := (q(Eq.refl false) : Expr)
  return q(not_prime_mul_of_ble _ _ _ $prf $r $r')

/--
Definition of `MinFacHelper` / `MinFacHelper` 的定义

English:
definition MinFacHelper
  signature: (n k : Nat)
  body: 2 < k ∧ k % 2 = 1 ∧ k <= minFac n

中文:
定义 MinFacHelper
  签名: (n k : 自然数)
  定义体: 2 < k ∧ k % 2 = 1 ∧ k <= minFac n

Depends on / 依赖: minFac
-/
def MinFacHelper (n k : Nat) : Prop :=
  2 < k ∧ k % 2 = 1 ∧ k <= minFac n

/--
theorem `MinFacHelper.one_lt` / 定理 `MinFacHelper.one_lt`

English:
theorem MinFacHelper.one_lt
  given: {n k : Nat} (h : MinFacHelper n k)
  statement: 1 < n
  proof: by
  have : 2 < minFac n := h.1.trans_le h.2.2
  obtain rfl | h := n.eq_zero_or_pos
  · contradiction
  rcases (succ_le_of_lt h).eq_or_lt with rfl | h
  · simp_all
  exact h

中文:
定理 MinFacHelper.one_lt
  条件: {n k : 自然数} (h : MinFacHelper n k)
  结论: 1 < n
  证明: by
  have : 2 < minFac n := h.1.trans_le h.2.2
  obtain rfl | h := n.eq_zero_or_pos
  · contradiction
  rcases (succ_le_of_lt h).eq_or_lt with rfl | h
  · simp_all
  exact h

Depends on / 依赖: eq_or_lt, eq_zero_or_pos, minFac, n.eq_zero_or_pos, succ_le_of_lt, trans_le
-/
theorem MinFacHelper.one_lt {n k : Nat} (h : MinFacHelper n k) : 1 < n := by
  have : 2 < minFac n := h.1.trans_le h.2.2
  obtain rfl | h := n.eq_zero_or_pos
  · contradiction
  rcases (succ_le_of_lt h).eq_or_lt with rfl | h
  · simp_all
  exact h

/--
theorem `minFacHelper_0` / 定理 `minFacHelper_0`

English:
theorem minFacHelper_0
  statement: (n : Nat)
  proof: by
  refine ⟨by simp, by simp, ?_⟩
  refine (le_minFac'.mpr fun p hp hpn => ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))
  rcases hp.eq_or_lt with rfl | h
  · simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2
  · exact h

中文:
定理 minFacHelper_0
  结论: (n : 自然数)
  证明: by
  refine ⟨by simp, by simp, ?_⟩
  refine (le_minFac'.mpr fun p hp hpn => ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))
  rcases hp.eq_or_lt with rfl | h
  · simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2
  · exact h

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero, Nat.le_of_ble_eq_true, Nat.ne_of_gt, dvd_iff_mod_eq_zero, eq_or_lt, hp.eq_or_lt, le_minFac, le_of_ble_eq_true, ne_of_gt, resolve_left
-/
theorem minFacHelper_0 (n : Nat)
    (h1 : Nat.ble (nat_lit 2) n = true) (h2 : nat_lit 1 = n % (nat_lit 2)) :
    MinFacHelper n (nat_lit 3) := by
  refine ⟨by simp, by simp, ?_⟩
  refine (le_minFac'.mpr fun p hp hpn => ?_).resolve_left (Nat.ne_of_gt (Nat.le_of_ble_eq_true h1))
  rcases hp.eq_or_lt with rfl | h
  · simp [(Nat.dvd_iff_mod_eq_zero ..).1 hpn] at h2
  · exact h

/--
theorem `minFacHelper_1` / 定理 `minFacHelper_1`

English:
theorem minFacHelper_1
  statement: {n k k' : Nat} (e : k + 2 = k') (h : MinFacHelper n k)
  proof: by
  rw [← e]
  refine ⟨Nat.lt_add_right _ h.1, ?_, ?_⟩
  · rw [add_mod, mod_self, add_zero, mod_mod]
    exact h.2.1
  rcases h.2.2.eq_or_lt with rfl | h2
  · exact (np rfl).elim
  rcases (succ_le_of_lt h2).eq_or_lt with h2|h2
  · refine ((h.1.trans_le h.2.2).ne ?_).elim
    have h3 : 2 ∣ minFac n 

中文:
定理 minFacHelper_1
  结论: {n k k' : 自然数} (e : k + 2 = k') (h : MinFacHelper n k)
  证明: by
  rw [← e]
  refine ⟨Nat.lt_add_right _ h.1, ?_, ?_⟩
  · rw [add_mod, mod_self, add_zero, mod_mod]
    exact h.2.1
  rcases h.2.2.eq_or_lt with rfl | h2
  · exact (np rfl).elim
  rcases (succ_le_of_lt h2).eq_or_lt with h2|h2
  · refine ((h.1.trans_le h.2.2).ne ?_).elim
    have h3 : 2 ∣ minFac n 

Depends on / 依赖: IsCompact, IsCompact.isClosed, IsCompact.of_isClosed_subset, K.isCompact, Monotone, Monotone.initial_functor_iff, Nat.dvd_iff_mod_eq_zero, Nat.lt_add_right, Subset, Subset.trans, U.property, U.val.isOpen, add_mod, add_zero, closure_minimal, dvd_iff_mod_eq_zero, dvd_prime, eq_or_lt, exists_compact_between, h.one_lt.ne
-/
theorem minFacHelper_1 {n k k' : Nat} (e : k + 2 = k') (h : MinFacHelper n k)
    (np : minFac n != k) : MinFacHelper n k' := by
  rw [← e]
  refine ⟨Nat.lt_add_right _ h.1, ?_, ?_⟩
  · rw [add_mod, mod_self, add_zero, mod_mod]
    exact h.2.1
  rcases h.2.2.eq_or_lt with rfl | h2
  · exact (np rfl).elim
  rcases (succ_le_of_lt h2).eq_or_lt with h2|h2
  · refine ((h.1.trans_le h.2.2).ne ?_).elim
    have h3 : 2 ∣ minFac n := by
      rw [Nat.dvd_iff_mod_eq_zero]; rw [← h2]; rw [succ_eq_add_one]; rw [add_mod]; rw [h.2.1]
    simpa [dvd_prime <| minFac_prime h.one_lt.ne'] using h3
  exact h2

/--
theorem `minFacHelper_2` / 定理 `minFacHelper_2`

English:
theorem minFacHelper_2
  statement: {n k k' : Nat} (e : k + 2 = k') (nk : ¬ Nat.Prime k)
  proof: by
  refine minFacHelper_1 e h fun h2 => ?_
  rw [← h2] at nk
exact nk minFac_prime h.one_lt.ne'

中文:
定理 minFacHelper_2
  结论: {n k k' : 自然数} (e : k + 2 = k') (nk : ¬ 自然数.Prime k)
  证明: by
  refine minFacHelper_1 e h fun h2 => ?_
  rw [← h2] at nk
exact nk minFac_prime h.one_lt.ne'

Depends on / 依赖: IsClosed, IsClosed.closure_subset_iff, IsCompact, IsCompact.isClosed, IsCompact.of_isClosed_subset, Monotone, Monotone.initial_functor_iff, closure, closure_subset_iff, exists_open_set_nhds_of_compactsNhds, h.one_lt.ne, initial_functor_iff, isClosed, isClosed_closure, isCompact, minFacHelper_1, minFac_prime, of_isClosed_subset, one_lt, subseteq
-/
theorem minFacHelper_2 {n k k' : Nat} (e : k + 2 = k') (nk : ¬ Nat.Prime k)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine minFacHelper_1 e h fun h2 => ?_
  rw [← h2] at nk
exact nk minFac_prime h.one_lt.ne'

/--
theorem `minFacHelper_3` / 定理 `minFacHelper_3`

English:
theorem minFacHelper_3
  statement: {n k k' : Nat} (e : k + 2 = k') (nk : (n % k).beq 0 = false)
  proof: by
  refine minFacHelper_1 e h fun h2 => ?_
  have nk := Nat.ne_of_beq_eq_false nk
  rw [← Nat.dvd_iff_mod_eq_zero]; rw [← h2] at nk
exact nk minFac_dvd n

中文:
定理 minFacHelper_3
  结论: {n k k' : 自然数} (e : k + 2 = k') (nk : (n % k).beq 0 = false)
  证明: by
  refine minFacHelper_1 e h fun h2 => ?_
  have nk := Nat.ne_of_beq_eq_false nk
  rw [← Nat.dvd_iff_mod_eq_zero]; rw [← h2] at nk
exact nk minFac_dvd n

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero, Nat.ne_of_beq_eq_false, dvd_iff_mod_eq_zero, minFacHelper_1, minFac_dvd, ne_of_beq_eq_false
-/
theorem minFacHelper_3 {n k k' : Nat} (e : k + 2 = k') (nk : (n % k).beq 0 = false)
    (h : MinFacHelper n k) : MinFacHelper n k' := by
  refine minFacHelper_1 e h fun h2 => ?_
  have nk := Nat.ne_of_beq_eq_false nk
  rw [← Nat.dvd_iff_mod_eq_zero]; rw [← h2] at nk
exact nk minFac_dvd n

/--
theorem `isNat_minFac_1` / 定理 `isNat_minFac_1`

English:
theorem isNat_minFac_1
  statement: {a : Nat} -> IsNat a (nat_lit 1) -> IsNat a.minFac 1

中文:
定理 isNat_minFac_1
  结论: {a : 自然数} -> Is自然数 a (nat_lit 1) -> Is自然数 a.minFac 1
-/
theorem isNat_minFac_1 : {a : Nat} -> IsNat a (nat_lit 1) -> IsNat a.minFac 1
  | _, ⟨rfl⟩ => ⟨minFac_one⟩

/--
theorem `isNat_minFac_2` / 定理 `isNat_minFac_2`

English:
theorem isNat_minFac_2
  statement: {a a' : Nat} -> IsNat a a' -> a' % 2 = 0 -> IsNat a.minFac 2

中文:
定理 isNat_minFac_2
  结论: {a a' : 自然数} -> Is自然数 a a' -> a' % 2 = 0 -> Is自然数 a.minFac 2
-/
theorem isNat_minFac_2 : {a a' : Nat} -> IsNat a a' -> a' % 2 = 0 -> IsNat a.minFac 2
  | a, _, ⟨rfl⟩, h => ⟨by rw [cast_ofNat, minFac_eq_two_iff, Nat.dvd_iff_mod_eq_zero, h]⟩

/--
theorem `isNat_minFac_3` / 定理 `isNat_minFac_3`

English:
theorem isNat_minFac_3
  statement: {n n' : Nat} -> (k : Nat) ->

中文:
定理 isNat_minFac_3
  结论: {n n' : 自然数} -> (k : 自然数) ->
-/
theorem isNat_minFac_3 : {n n' : Nat} -> (k : Nat) ->
    IsNat n n' -> MinFacHelper n' k -> nat_lit 0 = n' % k -> IsNat (minFac n) k
  | n, _, k, ⟨rfl⟩, h1, h2 => by
    rw [eq_comm]; rw [← Nat.dvd_iff_mod_eq_zero] at h2
    exact ⟨le_antisymm (minFac_le_of_dvd h1.1.le h2) h1.2.2⟩

/--
theorem `isNat_minFac_4` / 定理 `isNat_minFac_4`

English:
theorem isNat_minFac_4
  statement: {n n' k : Nat} ->
  proof: hmn
      _ < k := sqrt_lt.mpr (ble_eq_false.mp h2)
      _ <= n.minFac := h1.2.2
      _ <= m := Nat.minFac_le_of_dvd hm h2mn

中文:
定理 isNat_minFac_4
  结论: {n n' k : 自然数} ->
  证明: hmn
      _ < k := sqrt_lt.mpr (ble_eq_false.mp h2)
      _ <= n.minFac := h1.2.2
      _ <= m := Nat.minFac_le_of_dvd hm h2mn
-/
theorem isNat_minFac_4 : {n n' k : Nat} ->
    IsNat n n' -> MinFacHelper n' k -> (k * k).ble n' = false -> IsNat (minFac n) n'
  | n, _, k, ⟨rfl⟩, h1, h2 => by
    refine ⟨(Nat.prime_def_minFac.mp ?_).2⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨h1.one_lt, fun m hm hmn h2mn => ?_⟩
exact lt_irrefl m calc
      m <= sqrt n := hmn
      _ < k := sqrt_lt.mpr (ble_eq_false.mp h2)
      _ <= n.minFac := h1.2.2
      _ <= m := Nat.minFac_le_of_dvd hm h2mn

/--
Definition of `evalMinFac` / `evalMinFac` 的定义

English:
definition evalMinFac
  signature: : NormNumExt where eval {_ _} e
  body: do
  let .app (.const ``Nat.minFac _) (n : Q(Nat)) ← whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨nn, pn⟩ ← deriveNat n sNat
  let n' := nn.natLit!
  let rec aux (ek : Q(Nat)) (prf : Q(MinFacHelper $nn $ek)) :
      (c : Q(Nat)) × Q(IsNat (Nat.minFac $

中文:
定义 evalMinFac
  签名: : NormNumExt where eval {_ _} e
  定义体: do
  let .app (.const ``Nat.minFac _) (n : Q(Nat)) ← whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨nn, pn⟩ ← deriveNat n sNat
  let n' := nn.natLit!
  let rec aux (ek : Q(Nat)) (prf : Q(MinFacHelper $nn $ek)) :
      (c : Q(Nat)) × Q(IsNat (Nat.minFac $
-/
@[norm_num Nat.minFac _] partial def evalMinFac : NormNumExt where eval {_ _} e := do
  let .app (.const ``Nat.minFac _) (n : Q(Nat)) ← whnfR e | failure
  let sNat : Q(AddMonoidWithOne Nat) := q(Nat.instAddMonoidWithOne)
  let ⟨nn, pn⟩ ← deriveNat n sNat
  let n' := nn.natLit!
  let rec aux (ek : Q(Nat)) (prf : Q(MinFacHelper $nn $ek)) :
      (c : Q(Nat)) × Q(IsNat (Nat.minFac $n) $c) :=
    let k := ek.natLit!
    -- remark: `deriveBool q($nn < $ek * $ek)` is 2x slower than the following test.
    if n' < k * k then
      let r : Q(Nat.ble ($ek * $ek) $nn = false) := (q(Eq.refl false) : Expr)
      ⟨nn, q(isNat_minFac_4 $pn $prf $r)⟩
    else
      let d : Nat := k.minFac
      -- the following branch is not necessary for the correctness,
      -- but makes the algorithm 2x faster
      if d < k then
have ek' : Q(Nat) := mkRawNatLit k + 2
        let pk' : Q($ek + 2 = $ek') := (q(Eq.refl $ek') : Expr)
        let pd := deriveNotPrime k d ek
        aux ek' q(minFacHelper_2 $pk' $pd $prf)
      -- remark: `deriveBool q($nn % $ek = 0)` is 5x slower than the following test
      else if n' % k = 0 then
        let r : Q(nat_lit 0 = $nn % $ek) := (q(Eq.refl 0) : Expr)
        let r' : Q(IsNat (minFac $n) $ek) := q(isNat_minFac_3 _ $pn $prf $r)
        ⟨ek, r'⟩
      else
        let r : Q(Nat.beq ($nn % $ek) 0 = false) := (q(Eq.refl false) : Expr)
have ek' : Q(Nat) := mkRawNatLit k + 2
        let pk' : Q($ek + 2 = $ek') := (q(Eq.refl $ek') : Expr)
        aux ek' q(minFacHelper_3 $pk' $r $prf)
let rec core : MetaM Result q(Nat.minFac $n) := do
    if n' = 1 then
      let pn : Q(IsNat $n (nat_lit 1)) := pn
      return .isNat sNat q(nat_lit 1) q(isNat_minFac_1 $pn)
    if n' % 2 = 0 then
      let pq : Q($nn % 2 = 0) := (q(Eq.refl 0) : Expr)
      return .isNat sNat q(nat_lit 2) q(isNat_minFac_2 $pn $pq)
    let pp : Q(Nat.ble 2 $nn = true) := (q(Eq.refl true) : Expr)
    let pq : Q(1 = $nn % 2) := (q(Eq.refl (nat_lit 1)) : Expr)
    let ⟨c, pc⟩ := aux q(nat_lit 3) q(minFacHelper_0 $nn $pp $pq)
    return .isNat sNat c pc
  core

/--
theorem `isNat_prime_0` / 定理 `isNat_prime_0`

English:
theorem isNat_prime_0
  statement: {n : Nat} -> IsNat n (nat_lit 0) -> ¬ n.Prime

中文:
定理 isNat_prime_0
  结论: {n : 自然数} -> Is自然数 n (nat_lit 0) -> ¬ n.Prime
-/
theorem isNat_prime_0 : {n : Nat} -> IsNat n (nat_lit 0) -> ¬ n.Prime
  | _, ⟨rfl⟩ => not_prime_zero

/--
theorem `isNat_prime_1` / 定理 `isNat_prime_1`

English:
theorem isNat_prime_1
  statement: {n : Nat} -> IsNat n (nat_lit 1) -> ¬ n.Prime

中文:
定理 isNat_prime_1
  结论: {n : 自然数} -> Is自然数 n (nat_lit 1) -> ¬ n.Prime
-/
theorem isNat_prime_1 : {n : Nat} -> IsNat n (nat_lit 1) -> ¬ n.Prime
  | _, ⟨rfl⟩ => not_prime_one

/--
theorem `isNat_prime_2` / 定理 `isNat_prime_2`

English:
theorem isNat_prime_2
  statement: {n n' : Nat} ->

中文:
定理 isNat_prime_2
  结论: {n n' : 自然数} ->
-/
theorem isNat_prime_2 : {n n' : Nat} ->
    IsNat n n' -> Nat.ble 2 n' = true -> IsNat (minFac n') n' -> n.Prime
  | _, _, ⟨rfl⟩, h1, ⟨h2⟩ => prime_def_minFac.mpr ⟨ble_eq.mp h1, h2⟩

/--
theorem `isNat_not_prime` / 定理 `isNat_not_prime`

English:
theorem isNat_not_prime
  given: {n n' : Nat} (h : IsNat n n')
  statement: ¬n'.Prime -> ¬n.Prime
  proof: isNat.natElim h

中文:
定理 isNat_not_prime
  条件: {n n' : 自然数} (h : Is自然数 n n')
  结论: ¬n'.Prime -> ¬n.Prime
  证明: isNat.natElim h

Depends on / 依赖: isNat.natElim, natElim
-/
theorem isNat_not_prime {n n' : Nat} (h : IsNat n n') : ¬n'.Prime -> ¬n.Prime := isNat.natElim h

/--
Definition of `evalNatPrime` / `evalNatPrime` 的定义

English:
definition evalNatPrime
  signature: : NormNumExt where eval {_ _} e
  body: do
  let .app (.const `Nat.Prime _) (n : Q(Nat)) ← whnfR e | failure
  let ⟨nn, pn⟩ ← deriveNat n _
  let n' := nn.natLit!
  -- note: if `n` is not prime, we don't have to verify the calculation of `n.minFac`, we just have
  -- to compute it, which is a lot quicker
  let rec core : MetaM (Result q(N

中文:
定义 evalNatPrime
  签名: : NormNumExt where eval {_ _} e
  定义体: do
  let .app (.const `Nat.Prime _) (n : Q(Nat)) ← whnfR e | failure
  let ⟨nn, pn⟩ ← deriveNat n _
  let n' := nn.natLit!
  -- note: if `n` is not prime, we don't have to verify the calculation of `n.minFac`, we just have
  -- to compute it, which is a lot quicker
  let rec core : MetaM (Result q(N
-/
@[norm_num Nat.Prime _] def evalNatPrime : NormNumExt where eval {_ _} e := do
  let .app (.const `Nat.Prime _) (n : Q(Nat)) ← whnfR e | failure
  let ⟨nn, pn⟩ ← deriveNat n _
  let n' := nn.natLit!
  -- note: if `n` is not prime, we don't have to verify the calculation of `n.minFac`, we just have
  -- to compute it, which is a lot quicker
  let rec core : MetaM (Result q(Nat.Prime $n)) := do
    match n' with
| 0 => haveI' : nn =Q 0 := ⟨⟩; return .isFalse q(isNat_prime_0 $pn)
| 1 => haveI' : nn =Q 1 := ⟨⟩; return .isFalse q(isNat_prime_1 $pn)
    | _ =>
      let d := n'.minFac
      if d < n' then
        let prf : Q(¬ Nat.Prime $nn) := deriveNotPrime n' d nn
        return .isFalse q(isNat_not_prime $pn $prf)
      let r : Q(Nat.ble 2 $nn = true) := (q(Eq.refl true) : Expr)
      let .isNat _ _lit (p2n : Q(IsNat (minFac $nn) $nn)) ←
        evalMinFac.core nn _ nn q(.raw_refl _) nn.natLit! | failure
      return .isTrue q(isNat_prime_2 $pn $r $p2n)
  core


end NormNum

end Meta

end Mathlib
