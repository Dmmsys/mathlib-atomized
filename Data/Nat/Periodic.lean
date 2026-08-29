/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Data.Nat.Count

/-!
# Periodic Functions on ℕ

This file identifies a few functions on `ℕ` which are periodic, and also proves a lemma about
periodic predicates which helps determine their cardinality when filtering intervals over them.
-/

public section

assert_not_exists TwoSidedIdeal

namespace Nat

open Function

/--
theorem `periodic_gcd` / 定理 `periodic_gcd`

English:
theorem periodic_gcd
  given: (a : Nat)
  statement: Periodic (gcd a) a
  proof: a.gcd_add_self_right

中文:
定理 periodic_gcd
  条件: (a : 自然数)
  结论: 周期 (最大公约数 a) a
  证明: a.gcd_add_self_right

Depends on / 依赖: a.gcd_add_self_right, gcd_add_self_right
-/
theorem periodic_gcd (a : Nat) : Periodic (gcd a) a :=
  a.gcd_add_self_right

/--
theorem `periodic_coprime` / 定理 `periodic_coprime`

English:
theorem periodic_coprime
  given: (a : Nat)
  statement: Periodic (Coprime a) a
  proof: fun _ => eq_iff_iff.mpr coprime_add_self_right

中文:
定理 periodic_coprime
  条件: (a : 自然数)
  结论: 周期 (Coprime a) a
  证明: fun _ => eq_iff_iff.mpr coprime_add_self_right

Depends on / 依赖: coprime_add_self_right, eq_iff_iff, eq_iff_iff.mpr
-/
theorem periodic_coprime (a : Nat) : Periodic (Coprime a) a :=
  fun _ => eq_iff_iff.mpr coprime_add_self_right

/--
theorem `periodic_mod` / 定理 `periodic_mod`

English:
theorem periodic_mod
  given: (a : Nat)
  statement: Periodic (fun n => n % a) a
  proof: (add_mod_right · a)

中文:
定理 periodic_mod
  条件: (a : 自然数)
  结论: 周期 (fun n => n % a) a
  证明: (add_mod_right · a)

Depends on / 依赖: add_mod_right
-/
theorem periodic_mod (a : Nat) : Periodic (fun n => n % a) a :=
  (add_mod_right · a)

/--
theorem `_root_.Function.Periodic.map_mod_nat` / 定理 `_root_.Function.Periodic.map_mod_nat`

English:
theorem _root_.Function.Periodic.map_mod_nat
  given: {α : Type*} {f : Nat -> α} {a : Nat} (hf : Periodic f a)
  proof: fun n => by
  conv_rhs => rw [← n.mod_add_div a, mul_comm, ← Nat.nsmul_eq_mul, hf.nsmul]

中文:
定理 _root_.函数.周期.map_mod_nat
  条件: {α : 类型} {f : 自然数 -> α} {a : 自然数} (hf : 周期 f a)
  证明: fun n => by
  conv_rhs => rw [← n.mod_add_div a, mul_comm, ← Nat.nsmul_eq_mul, hf.nsmul]

Depends on / 依赖: Nat.nsmul_eq_mul, conv_rhs, hf.nsmul, mod_add_div, mul_comm, n.mod_add_div, nsmul_eq_mul
-/
theorem _root_.Function.Periodic.map_mod_nat {α : Type*} {f : Nat -> α} {a : Nat} (hf : Periodic f a) :
    forall n, f (n % a) = f n := fun n => by
  conv_rhs => rw [← n.mod_add_div a, mul_comm, ← Nat.nsmul_eq_mul, hf.nsmul]

section Multiset

open Multiset

/--
theorem `filter_multiset_Ico_card_eq_of_periodic` / 定理 `filter_multiset_Ico_card_eq_of_periodic`

English:
theorem filter_multiset_Ico_card_eq_of_periodic
  statement: (n a : Nat) (p : Nat -> Prop) [DecidablePred p]
  proof: by
  rw [count_eq_card_filter_range]; rw [Finset.card]; rw [Finset.filter_val]; rw [Finset.range_val]; rw [←
    multiset_Ico_map_mod n]; rw [← map_count_True_eq_filter_card]; rw [← map_count_True_eq_filter_card]; rw [map_map]
  congr; funext n
  exact (pp.map_mod_nat n).symm

中文:
定理 filter_multiset_Ico_card_eq_of_periodic
  结论: (n a : 自然数) (p : 自然数 -> 命题) [DecidablePred p]
  证明: by
  rw [count_eq_card_filter_range]; rw [Finset.card]; rw [Finset.filter_val]; rw [Finset.range_val]; rw [←
    multiset_Ico_map_mod n]; rw [← map_count_True_eq_filter_card]; rw [← map_count_True_eq_filter_card]; rw [map_map]
  congr; funext n
  exact (pp.map_mod_nat n).symm

Depends on / 依赖: Finset, Finset.card, Finset.filter_val, Finset.range_val, count_eq_card_filter_range, filter_val, map_count_True_eq_filter_card, map_map, map_mod_nat, multiset_Ico_map_mod, pp.map_mod_nat, range_val
-/
theorem filter_multiset_Ico_card_eq_of_periodic (n a : Nat) (p : Nat -> Prop) [DecidablePred p]
    (pp : Periodic p a) : card (filter p (Ico n (n + a))) = a.count p := by
  rw [count_eq_card_filter_range]; rw [Finset.card]; rw [Finset.filter_val]; rw [Finset.range_val]; rw [←
    multiset_Ico_map_mod n]; rw [← map_count_True_eq_filter_card]; rw [← map_count_True_eq_filter_card]; rw [map_map]
  congr; funext n
  exact (pp.map_mod_nat n).symm

end Multiset

section Finset

open Finset

/--
theorem `filter_Ico_card_eq_of_periodic` / 定理 `filter_Ico_card_eq_of_periodic`

English:
theorem filter_Ico_card_eq_of_periodic
  statement: (n a : Nat) (p : Nat -> Prop) [DecidablePred p]
  proof: n.filter_multiset_Ico_card_eq_of_periodic a p pp

中文:
定理 filter_Ico_card_eq_of_periodic
  结论: (n a : 自然数) (p : 自然数 -> 命题) [DecidablePred p]
  证明: n.filter_multiset_Ico_card_eq_of_periodic a p pp

Depends on / 依赖: filter_multiset_Ico_card_eq_of_periodic, n.filter_multiset_Ico_card_eq_of_periodic
-/
theorem filter_Ico_card_eq_of_periodic (n a : Nat) (p : Nat -> Prop) [DecidablePred p]
    (pp : Periodic p a) : ((Ico n (n + a)).filter p).card = a.count p :=
  n.filter_multiset_Ico_card_eq_of_periodic a p pp

end Finset

end Nat
