/-
Copyright (c) 2025 Concordance Inc. dba Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic

/-!
# Congruence modulo natural and integer numbers for big operators

In this file we prove various versions of the following theorem:
if `f i ≡ g i [MOD n]` for all `i ∈ s`, then `∏ i ∈ s, f i ≡ ∏ i ∈ s, g i [MOD n]`,
and similarly for sums.

We prove it for lists, multisets, and finsets, as well as for natural and integer numbers.
-/

public section

namespace Nat

variable {α : Type*} {n : Nat} {l : List α} {f g : α -> Nat}

namespace ModEq

/--
theorem `listProd_map` / 定理 `listProd_map`

English:
theorem listProd_map
  given: (h : forall x in l, f x ≡ g x [MOD n])
  proof: by
  induction l <;> aesop (add unsafe ModEq.mul)

中文:
定理 listProd_map
  条件: (h : 对任意 x in l, f x ≡ g x [MOD n])
  证明: by
  induction l <;> aesop (add unsafe ModEq.mul)

Depends on / 依赖: ModEq.mul, unsafe
-/
theorem listProd_map (h : forall x in l, f x ≡ g x [MOD n]) :
    (l.map f).prod ≡ (l.map g).prod [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)

/--
theorem `listProd_map_one` / 定理 `listProd_map_one`

English:
theorem listProd_map_one
  given: (h : forall x in l, f x ≡ 1 [MOD n])
  statement: (l.map f).prod ≡ 1 [MOD n]
  proof: (listProd_map h).trans by simp [ModEq.refl]

中文:
定理 listProd_map_one
  条件: (h : 对任意 x in l, f x ≡ 1 [MOD n])
  结论: (l.map f).prod ≡ 1 [MOD n]
  证明: (listProd_map h).trans by simp [ModEq.refl]

Depends on / 依赖: ModEq.refl, listProd_map
-/
theorem listProd_map_one (h : forall x in l, f x ≡ 1 [MOD n]) : (l.map f).prod ≡ 1 [MOD n] :=
(listProd_map h).trans by simp [ModEq.refl]

/--
theorem `listProd_one` / 定理 `listProd_one`

English:
theorem listProd_one
  given: {l : List Nat} (h : forall x in l, x ≡ 1 [MOD n])
  statement: l.prod ≡ 1 [MOD n]
  proof: by
  simpa using listProd_map_one h

中文:
定理 listProd_one
  条件: {l : List 自然数} (h : 对任意 x in l, x ≡ 1 [MOD n])
  结论: l.prod ≡ 1 [MOD n]
  证明: by
  simpa using listProd_map_one h

Depends on / 依赖: listProd_map_one
-/
theorem listProd_one {l : List Nat} (h : forall x in l, x ≡ 1 [MOD n]) : l.prod ≡ 1 [MOD n] := by
  simpa using listProd_map_one h

/--
theorem `listSum_map` / 定理 `listSum_map`

English:
theorem listSum_map
  given: (h : forall x in l, f x ≡ g x [MOD n])
  statement: (l.map f).sum ≡ (l.map g).sum [MOD n]
  proof: by
  induction l <;> aesop (add unsafe ModEq.add)

中文:
定理 listSum_map
  条件: (h : 对任意 x in l, f x ≡ g x [MOD n])
  结论: (l.map f).sum ≡ (l.map g).sum [MOD n]
  证明: by
  induction l <;> aesop (add unsafe ModEq.add)

Depends on / 依赖: ModEq.add, unsafe
-/
theorem listSum_map (h : forall x in l, f x ≡ g x [MOD n]) : (l.map f).sum ≡ (l.map g).sum [MOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)

/--
theorem `listSum_map_zero` / 定理 `listSum_map_zero`

English:
theorem listSum_map_zero
  given: (h : forall x in l, f x ≡ 0 [MOD n])
  statement: (l.map f).sum ≡ 0 [MOD n]
  proof: by
  simpa using listSum_map h

中文:
定理 listSum_map_zero
  条件: (h : 对任意 x in l, f x ≡ 0 [MOD n])
  结论: (l.map f).sum ≡ 0 [MOD n]
  证明: by
  simpa using listSum_map h

Depends on / 依赖: listSum_map
-/
theorem listSum_map_zero (h : forall x in l, f x ≡ 0 [MOD n]) : (l.map f).sum ≡ 0 [MOD n] := by
  simpa using listSum_map h

/--
theorem `listSum_zero` / 定理 `listSum_zero`

English:
theorem listSum_zero
  given: {l : List Nat} (h : forall x in l, x ≡ 0 [MOD n])
  statement: l.sum ≡ 0 [MOD n]
  proof: by
  simpa using listSum_map h

中文:
定理 listSum_zero
  条件: {l : List 自然数} (h : 对任意 x in l, x ≡ 0 [MOD n])
  结论: l.sum ≡ 0 [MOD n]
  证明: by
  simpa using listSum_map h

Depends on / 依赖: listSum_map
-/
theorem listSum_zero {l : List Nat} (h : forall x in l, x ≡ 0 [MOD n]) : l.sum ≡ 0 [MOD n] := by
  simpa using listSum_map h

/--
theorem `multisetProd_map` / 定理 `multisetProd_map`

English:
theorem multisetProd_map
  given: {s : Multiset α} (h : forall x in s, f x ≡ g x [MOD n])
  proof: by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

中文:
定理 multisetProd_map
  条件: {s : Multiset α} (h : 对任意 x in s, f x ≡ g x [MOD n])
  证明: by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

Depends on / 依赖: listProd_map
-/
theorem multisetProd_map {s : Multiset α} (h : forall x in s, f x ≡ g x [MOD n]) :
    (s.map f).prod ≡ (s.map g).prod [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

/--
theorem `multisetProd_map_one` / 定理 `multisetProd_map_one`

English:
theorem multisetProd_map_one
  given: {s : Multiset α} (h : forall x in s, f x ≡ 1 [MOD n])
  proof: by
  simpa using multisetProd_map h

中文:
定理 multisetProd_map_one
  条件: {s : Multiset α} (h : 对任意 x in s, f x ≡ 1 [MOD n])
  证明: by
  simpa using multisetProd_map h

Depends on / 依赖: multisetProd_map
-/
theorem multisetProd_map_one {s : Multiset α} (h : forall x in s, f x ≡ 1 [MOD n]) :
    (s.map f).prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map h

/--
theorem `multisetProd_one` / 定理 `multisetProd_one`

English:
theorem multisetProd_one
  given: {s : Multiset Nat} (h : forall x in s, x ≡ 1 [MOD n])
  statement: s.prod ≡ 1 [MOD n]
  proof: by
  simpa using multisetProd_map_one h

中文:
定理 multisetProd_one
  条件: {s : Multiset 自然数} (h : 对任意 x in s, x ≡ 1 [MOD n])
  结论: s.prod ≡ 1 [MOD n]
  证明: by
  simpa using multisetProd_map_one h

Depends on / 依赖: multisetProd_map_one
-/
theorem multisetProd_one {s : Multiset Nat} (h : forall x in s, x ≡ 1 [MOD n]) : s.prod ≡ 1 [MOD n] := by
  simpa using multisetProd_map_one h

/--
theorem `multisetSum_map` / 定理 `multisetSum_map`

English:
theorem multisetSum_map
  given: {s : Multiset α} (h : forall x in s, f x ≡ g x [MOD n])
  proof: by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

中文:
定理 multisetSum_map
  条件: {s : Multiset α} (h : 对任意 x in s, f x ≡ g x [MOD n])
  证明: by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

Depends on / 依赖: listSum_map
-/
theorem multisetSum_map {s : Multiset α} (h : forall x in s, f x ≡ g x [MOD n]) :
    (s.map f).sum ≡ (s.map g).sum [MOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

/--
theorem `multisetSum_map_zero` / 定理 `multisetSum_map_zero`

English:
theorem multisetSum_map_zero
  given: {s : Multiset α} (h : forall x in s, f x ≡ 0 [MOD n])
  proof: by
  simpa using multisetSum_map h

中文:
定理 multisetSum_map_zero
  条件: {s : Multiset α} (h : 对任意 x in s, f x ≡ 0 [MOD n])
  证明: by
  simpa using multisetSum_map h

Depends on / 依赖: multisetSum_map
-/
theorem multisetSum_map_zero {s : Multiset α} (h : forall x in s, f x ≡ 0 [MOD n]) :
    (s.map f).sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h

/--
theorem `multisetSum_zero` / 定理 `multisetSum_zero`

English:
theorem multisetSum_zero
  given: {s : Multiset Nat} (h : forall x in s, x ≡ 0 [MOD n])
  statement: s.sum ≡ 0 [MOD n]
  proof: by
  simpa using multisetSum_map h

@[gcongr]

中文:
定理 multisetSum_zero
  条件: {s : Multiset 自然数} (h : 对任意 x in s, x ≡ 0 [MOD n])
  结论: s.sum ≡ 0 [MOD n]
  证明: by
  simpa using multisetSum_map h

@[gcongr]

Depends on / 依赖: multisetSum_map
-/
theorem multisetSum_zero {s : Multiset Nat} (h : forall x in s, x ≡ 0 [MOD n]) : s.sum ≡ 0 [MOD n] := by
  simpa using multisetSum_map h

@[gcongr]
/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  given: {s : Finset α} (h : forall x in s, f x ≡ g x [MOD n])
  proof: .multisetProd_map (s := s.1) h

中文:
定理 prod
  条件: {s : Finset α} (h : 对任意 x in s, f x ≡ g x [MOD n])
  证明: .multisetProd_map (s := s.1) h
-/
protected theorem prod {s : Finset α} (h : forall x in s, f x ≡ g x [MOD n]) :
    (∏ x in s, f x) ≡ ∏ x in s, g x [MOD n] :=
  .multisetProd_map (s := s.1) h

/--
theorem `prod_one` / 定理 `prod_one`

English:
theorem prod_one
  given: {s : Finset α} (h : forall x in s, f x ≡ 1 [MOD n])
  statement: ∏ x in s, f x ≡ 1 [MOD n]
  proof: by
  simpa using ModEq.prod h

@[gcongr]

中文:
定理 prod_one
  条件: {s : Finset α} (h : 对任意 x in s, f x ≡ 1 [MOD n])
  结论: ∏ x in s, f x ≡ 1 [MOD n]
  证明: by
  simpa using ModEq.prod h

@[gcongr]

Depends on / 依赖: ModEq.prod
-/
theorem prod_one {s : Finset α} (h : forall x in s, f x ≡ 1 [MOD n]) : ∏ x in s, f x ≡ 1 [MOD n] := by
  simpa using ModEq.prod h

@[gcongr]
/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  given: {s : Finset α} (h : forall x in s, f x ≡ g x [MOD n])
  proof: .multisetSum_map (s := s.1) h

中文:
定理 sum
  条件: {s : Finset α} (h : 对任意 x in s, f x ≡ g x [MOD n])
  证明: .multisetSum_map (s := s.1) h
-/
protected theorem sum {s : Finset α} (h : forall x in s, f x ≡ g x [MOD n]) :
    (∑ x in s, f x) ≡ ∑ x in s, g x [MOD n] :=
  .multisetSum_map (s := s.1) h

/--
theorem `sum_zero` / 定理 `sum_zero`

English:
theorem sum_zero
  given: {s : Finset α} (h : forall x in s, f x ≡ 0 [MOD n])
  statement: ∑ x in s, f x ≡ 0 [MOD n]
  proof: by
  simpa using ModEq.sum h

中文:
定理 sum_zero
  条件: {s : Finset α} (h : 对任意 x in s, f x ≡ 0 [MOD n])
  结论: ∑ x in s, f x ≡ 0 [MOD n]
  证明: by
  simpa using ModEq.sum h

Depends on / 依赖: ModEq.sum
-/
theorem sum_zero {s : Finset α} (h : forall x in s, f x ≡ 0 [MOD n]) : ∑ x in s, f x ≡ 0 [MOD n] := by
  simpa using ModEq.sum h

end ModEq

/--
theorem `prod_modEq_ite` / 定理 `prod_modEq_ite`

English:
theorem prod_modEq_ite
  statement: [DecidableEq α] {s : Finset α} {a : α}
  proof: by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod, apply_ite Nat.cast] at *
  exact Finset.prod_eq_ite _ hf

中文:
定理 prod_modEq_ite
  结论: [DecidableEq α] {s : Finset α} {a : α}
  证明: by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod, apply_ite Nat.cast] at *
  exact Finset.prod_eq_ite _ hf

Depends on / 依赖: Finset, Finset.prod_eq_ite, Nat.cast, ZMod.natCast_eq_natCast_iff, apply_ite, cast_one, cast_prod, natCast_eq_natCast_iff, prod_eq_ite
-/
theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : forall x in s, x != a -> f x ≡ 1 [MOD n]) :
    (∏ x in s, f x) ≡ if a in s then f a else 1 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod, apply_ite Nat.cast] at *
  exact Finset.prod_eq_ite _ hf

/--
theorem `prod_modEq_single` / 定理 `prod_modEq_single`

English:
theorem prod_modEq_single
  statement: {s : Finset α} {a : α}
  proof: by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

中文:
定理 prod_modEq_single
  结论: {s : Finset α} {a : α}
  证明: by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

Depends on / 依赖: Finset, Finset.prod_eq_single, ZMod.natCast_eq_natCast_iff, cast_one, cast_prod, natCast_eq_natCast_iff, prod_eq_single
-/
theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s -> f a ≡ 1 [MOD n]) (hf : forall x in s, x != a -> f x ≡ 1 [MOD n]) :
    (∏ x in s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

/--
theorem `sum_modEq_ite` / 定理 `sum_modEq_ite`

English:
theorem sum_modEq_ite
  statement: [DecidableEq α] {s : Finset α} {a : α}
  proof: by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum, apply_ite Nat.cast] at *
  exact Finset.sum_eq_ite _ hf

中文:
定理 sum_modEq_ite
  结论: [DecidableEq α] {s : Finset α} {a : α}
  证明: by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum, apply_ite Nat.cast] at *
  exact Finset.sum_eq_ite _ hf

Depends on / 依赖: Finset, Finset.sum_eq_ite, Nat.cast, ZMod.natCast_eq_natCast_iff, apply_ite, cast_sum, cast_zero, natCast_eq_natCast_iff, sum_eq_ite
-/
theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : forall x in s, x != a -> f x ≡ 0 [MOD n]) :
    (∑ x in s, f x) ≡ if a in s then f a else 0 [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum, apply_ite Nat.cast] at *
  exact Finset.sum_eq_ite _ hf

/--
theorem `sum_modEq_single` / 定理 `sum_modEq_single`

English:
theorem sum_modEq_single
  statement: {s : Finset α} {a : α}
  proof: by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

中文:
定理 sum_modEq_single
  结论: {s : Finset α} {a : α}
  证明: by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

Depends on / 依赖: Finset, Finset.sum_eq_single, ZMod.natCast_eq_natCast_iff, cast_sum, cast_zero, natCast_eq_natCast_iff, sum_eq_single
-/
theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s -> f a ≡ 0 [MOD n]) (hf : forall x in s, x != a -> f x ≡ 0 [MOD n]) :
    (∑ x in s, f x) ≡ f a [MOD n] := by
  simp only [← ZMod.natCast_eq_natCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

end Nat

namespace Int

variable {α : Type*} {n : Int} {l : List α} {f g : α -> Int}

namespace ModEq

/--
theorem `listProd_map` / 定理 `listProd_map`

English:
theorem listProd_map
  given: (h : forall x in l, f x ≡ g x [ZMOD n])
  proof: by
  induction l <;> aesop (add unsafe ModEq.mul)

中文:
定理 listProd_map
  条件: (h : 对任意 x in l, f x ≡ g x [ZMOD n])
  证明: by
  induction l <;> aesop (add unsafe ModEq.mul)

Depends on / 依赖: ModEq.mul, unsafe
-/
theorem listProd_map (h : forall x in l, f x ≡ g x [ZMOD n]) :
    (l.map f).prod ≡ (l.map g).prod [ZMOD n] := by
  induction l <;> aesop (add unsafe ModEq.mul)

/--
theorem `listProd_map_one` / 定理 `listProd_map_one`

English:
theorem listProd_map_one
  given: (h : forall x in l, f x ≡ 1 [ZMOD n])
  statement: (l.map f).prod ≡ 1 [ZMOD n]
  proof: (listProd_map h).trans by simp

中文:
定理 listProd_map_one
  条件: (h : 对任意 x in l, f x ≡ 1 [ZMOD n])
  结论: (l.map f).prod ≡ 1 [ZMOD n]
  证明: (listProd_map h).trans by simp

Depends on / 依赖: listProd_map
-/
theorem listProd_map_one (h : forall x in l, f x ≡ 1 [ZMOD n]) : (l.map f).prod ≡ 1 [ZMOD n] :=
(listProd_map h).trans by simp

/--
theorem `listProd_one` / 定理 `listProd_one`

English:
theorem listProd_one
  given: {l : List Int} (h : forall x in l, x ≡ 1 [ZMOD n])
  statement: l.prod ≡ 1 [ZMOD n]
  proof: by
  simpa using listProd_map_one h

中文:
定理 listProd_one
  条件: {l : List 整数} (h : 对任意 x in l, x ≡ 1 [ZMOD n])
  结论: l.prod ≡ 1 [ZMOD n]
  证明: by
  simpa using listProd_map_one h

Depends on / 依赖: listProd_map_one
-/
theorem listProd_one {l : List Int} (h : forall x in l, x ≡ 1 [ZMOD n]) : l.prod ≡ 1 [ZMOD n] := by
  simpa using listProd_map_one h

/--
theorem `listSum_map` / 定理 `listSum_map`

English:
theorem listSum_map
  given: (h : forall x in l, f x ≡ g x [ZMOD n])
  statement: (l.map f).sum ≡ (l.map g).sum [ZMOD n]
  proof: by
  induction l <;> aesop (add unsafe ModEq.add)

中文:
定理 listSum_map
  条件: (h : 对任意 x in l, f x ≡ g x [ZMOD n])
  结论: (l.map f).sum ≡ (l.map g).sum [ZMOD n]
  证明: by
  induction l <;> aesop (add unsafe ModEq.add)

Depends on / 依赖: ModEq.add, unsafe
-/
theorem listSum_map (h : forall x in l, f x ≡ g x [ZMOD n]) : (l.map f).sum ≡ (l.map g).sum [ZMOD n] := by
  induction l <;> aesop (add unsafe ModEq.add)

/--
theorem `listSum_map_zero` / 定理 `listSum_map_zero`

English:
theorem listSum_map_zero
  given: (h : forall x in l, f x ≡ 0 [ZMOD n])
  statement: (l.map f).sum ≡ 0 [ZMOD n]
  proof: by
  simpa using listSum_map h

中文:
定理 listSum_map_zero
  条件: (h : 对任意 x in l, f x ≡ 0 [ZMOD n])
  结论: (l.map f).sum ≡ 0 [ZMOD n]
  证明: by
  simpa using listSum_map h

Depends on / 依赖: listSum_map
-/
theorem listSum_map_zero (h : forall x in l, f x ≡ 0 [ZMOD n]) : (l.map f).sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map h

/--
theorem `listSum_zero` / 定理 `listSum_zero`

English:
theorem listSum_zero
  given: {l : List Int} (h : forall x in l, x ≡ 0 [ZMOD n])
  statement: l.sum ≡ 0 [ZMOD n]
  proof: by
  simpa using listSum_map_zero h

中文:
定理 listSum_zero
  条件: {l : List 整数} (h : 对任意 x in l, x ≡ 0 [ZMOD n])
  结论: l.sum ≡ 0 [ZMOD n]
  证明: by
  simpa using listSum_map_zero h

Depends on / 依赖: listSum_map_zero
-/
theorem listSum_zero {l : List Int} (h : forall x in l, x ≡ 0 [ZMOD n]) : l.sum ≡ 0 [ZMOD n] := by
  simpa using listSum_map_zero h

/--
theorem `multisetProd_map` / 定理 `multisetProd_map`

English:
theorem multisetProd_map
  given: {s : Multiset α} (h : forall x in s, f x ≡ g x [ZMOD n])
  proof: by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

中文:
定理 multisetProd_map
  条件: {s : Multiset α} (h : 对任意 x in s, f x ≡ g x [ZMOD n])
  证明: by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

Depends on / 依赖: listProd_map
-/
theorem multisetProd_map {s : Multiset α} (h : forall x in s, f x ≡ g x [ZMOD n]) :
    (s.map f).prod ≡ (s.map g).prod [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using listProd_map (l := l) h

/--
theorem `multisetProd_map_one` / 定理 `multisetProd_map_one`

English:
theorem multisetProd_map_one
  given: {s : Multiset α} (h : forall x in s, f x ≡ 1 [ZMOD n])
  proof: by
  simpa using multisetProd_map h

中文:
定理 multisetProd_map_one
  条件: {s : Multiset α} (h : 对任意 x in s, f x ≡ 1 [ZMOD n])
  证明: by
  simpa using multisetProd_map h

Depends on / 依赖: multisetProd_map
-/
theorem multisetProd_map_one {s : Multiset α} (h : forall x in s, f x ≡ 1 [ZMOD n]) :
    (s.map f).prod ≡ 1 [ZMOD n] := by
  simpa using multisetProd_map h

/--
theorem `multisetProd_one` / 定理 `multisetProd_one`

English:
theorem multisetProd_one
  given: {s : Multiset Int} (h : forall x in s, x ≡ 1 [ZMOD n])
  statement: s.prod ≡ 1 [ZMOD n]
  proof: by
  simpa using multisetProd_map_one h

中文:
定理 multisetProd_one
  条件: {s : Multiset 整数} (h : 对任意 x in s, x ≡ 1 [ZMOD n])
  结论: s.prod ≡ 1 [ZMOD n]
  证明: by
  simpa using multisetProd_map_one h

Depends on / 依赖: multisetProd_map_one
-/
theorem multisetProd_one {s : Multiset Int} (h : forall x in s, x ≡ 1 [ZMOD n]) : s.prod ≡ 1 [ZMOD n] := by
  simpa using multisetProd_map_one h

/--
theorem `multisetSum_map` / 定理 `multisetSum_map`

English:
theorem multisetSum_map
  given: {s : Multiset α} (h : forall x in s, f x ≡ g x [ZMOD n])
  proof: by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

中文:
定理 multisetSum_map
  条件: {s : Multiset α} (h : 对任意 x in s, f x ≡ g x [ZMOD n])
  证明: by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

Depends on / 依赖: listSum_map
-/
theorem multisetSum_map {s : Multiset α} (h : forall x in s, f x ≡ g x [ZMOD n]) :
    (s.map f).sum ≡ (s.map g).sum [ZMOD n] := by
  rcases s with ⟨l⟩
  simpa using listSum_map (l := l) h

/--
theorem `multisetSum_map_zero` / 定理 `multisetSum_map_zero`

English:
theorem multisetSum_map_zero
  given: {s : Multiset α} (h : forall x in s, f x ≡ 0 [ZMOD n])
  proof: by
  simpa using multisetSum_map h

中文:
定理 multisetSum_map_zero
  条件: {s : Multiset α} (h : 对任意 x in s, f x ≡ 0 [ZMOD n])
  证明: by
  simpa using multisetSum_map h

Depends on / 依赖: multisetSum_map
-/
theorem multisetSum_map_zero {s : Multiset α} (h : forall x in s, f x ≡ 0 [ZMOD n]) :
    (s.map f).sum ≡ 0 [ZMOD n] := by
  simpa using multisetSum_map h

/--
theorem `multisetSum_zero` / 定理 `multisetSum_zero`

English:
theorem multisetSum_zero
  given: {s : Multiset Int} (h : forall x in s, x ≡ 0 [ZMOD n])
  statement: s.sum ≡ 0 [ZMOD n]
  proof: by
  simpa using multisetSum_map_zero h

@[gcongr]

中文:
定理 multisetSum_zero
  条件: {s : Multiset 整数} (h : 对任意 x in s, x ≡ 0 [ZMOD n])
  结论: s.sum ≡ 0 [ZMOD n]
  证明: by
  simpa using multisetSum_map_zero h

@[gcongr]

Depends on / 依赖: multisetSum_map_zero
-/
theorem multisetSum_zero {s : Multiset Int} (h : forall x in s, x ≡ 0 [ZMOD n]) : s.sum ≡ 0 [ZMOD n] := by
  simpa using multisetSum_map_zero h

@[gcongr]
/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  given: {s : Finset α} (h : forall x in s, f x ≡ g x [ZMOD n])
  proof: .multisetProd_map (s := s.1) h

中文:
定理 prod
  条件: {s : Finset α} (h : 对任意 x in s, f x ≡ g x [ZMOD n])
  证明: .multisetProd_map (s := s.1) h
-/
protected theorem prod {s : Finset α} (h : forall x in s, f x ≡ g x [ZMOD n]) :
    (∏ x in s, f x) ≡ ∏ x in s, g x [ZMOD n] :=
  .multisetProd_map (s := s.1) h

/--
theorem `prod_one` / 定理 `prod_one`

English:
theorem prod_one
  given: {s : Finset α} (h : forall x in s, f x ≡ 1 [ZMOD n])
  statement: ∏ x in s, f x ≡ 1 [ZMOD n]
  proof: by
  simpa using ModEq.prod h

@[gcongr]

中文:
定理 prod_one
  条件: {s : Finset α} (h : 对任意 x in s, f x ≡ 1 [ZMOD n])
  结论: ∏ x in s, f x ≡ 1 [ZMOD n]
  证明: by
  simpa using ModEq.prod h

@[gcongr]

Depends on / 依赖: ModEq.prod
-/
theorem prod_one {s : Finset α} (h : forall x in s, f x ≡ 1 [ZMOD n]) : ∏ x in s, f x ≡ 1 [ZMOD n] := by
  simpa using ModEq.prod h

@[gcongr]
/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  given: {s : Finset α} (h : forall x in s, f x ≡ g x [ZMOD n])
  proof: .multisetSum_map (s := s.1) h

中文:
定理 sum
  条件: {s : Finset α} (h : 对任意 x in s, f x ≡ g x [ZMOD n])
  证明: .multisetSum_map (s := s.1) h
-/
protected theorem sum {s : Finset α} (h : forall x in s, f x ≡ g x [ZMOD n]) :
    (∑ x in s, f x) ≡ ∑ x in s, g x [ZMOD n] :=
  .multisetSum_map (s := s.1) h

/--
theorem `sum_zero` / 定理 `sum_zero`

English:
theorem sum_zero
  given: {s : Finset α} (h : forall x in s, f x ≡ 0 [ZMOD n])
  proof: .multisetSum_map_zero (s := s.1) h

中文:
定理 sum_zero
  条件: {s : Finset α} (h : 对任意 x in s, f x ≡ 0 [ZMOD n])
  证明: .multisetSum_map_zero (s := s.1) h
-/
protected theorem sum_zero {s : Finset α} (h : forall x in s, f x ≡ 0 [ZMOD n]) :
    (∑ x in s, f x) ≡ 0 [ZMOD n] :=
  .multisetSum_map_zero (s := s.1) h

end ModEq

/--
theorem `prod_modEq_ite` / 定理 `prod_modEq_ite`

English:
theorem prod_modEq_ite
  statement: [DecidableEq α] {s : Finset α} {a : α}
  proof: by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod,
    apply_ite Int.cast] at *
  exact Finset.prod_eq_ite _ hf

中文:
定理 prod_modEq_ite
  结论: [DecidableEq α] {s : Finset α} {a : α}
  证明: by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod,
    apply_ite Int.cast] at *
  exact Finset.prod_eq_ite _ hf

Depends on / 依赖: Finset, Finset.prod_eq_ite, Int.cast, ZMod.intCast_eq_intCast_iff, apply_ite, cast_one, cast_prod, intCast_eq_intCast_iff, modEq_natAbs, prod_eq_ite
-/
theorem prod_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : forall x in s, x != a -> f x ≡ 1 [ZMOD n]) :
    (∏ x in s, f x) ≡ if a in s then f a else 1 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod,
    apply_ite Int.cast] at *
  exact Finset.prod_eq_ite _ hf

/--
theorem `prod_modEq_single` / 定理 `prod_modEq_single`

English:
theorem prod_modEq_single
  statement: {s : Finset α} {a : α}
  proof: by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

中文:
定理 prod_modEq_single
  结论: {s : Finset α} {a : α}
  证明: by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

Depends on / 依赖: Finset, Finset.prod_eq_single, ZMod.intCast_eq_intCast_iff, cast_one, cast_prod, intCast_eq_intCast_iff, modEq_natAbs, prod_eq_single
-/
theorem prod_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s -> f a ≡ 1 [ZMOD n]) (hf : forall x in s, x != a -> f x ≡ 1 [ZMOD n]) :
    (∏ x in s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_one, cast_prod] at *
  apply Finset.prod_eq_single <;> assumption

/--
theorem `sum_modEq_ite` / 定理 `sum_modEq_ite`

English:
theorem sum_modEq_ite
  statement: [DecidableEq α] {s : Finset α} {a : α}
  proof: by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum,
    apply_ite Int.cast] at *
  exact Finset.sum_eq_ite _ hf

中文:
定理 sum_modEq_ite
  结论: [DecidableEq α] {s : Finset α} {a : α}
  证明: by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum,
    apply_ite Int.cast] at *
  exact Finset.sum_eq_ite _ hf

Depends on / 依赖: Finset, Finset.sum_eq_ite, Int.cast, ZMod.intCast_eq_intCast_iff, apply_ite, cast_sum, cast_zero, intCast_eq_intCast_iff, modEq_natAbs, sum_eq_ite
-/
theorem sum_modEq_ite [DecidableEq α] {s : Finset α} {a : α}
    (hf : forall x in s, x != a -> f x ≡ 0 [ZMOD n]) :
    (∑ x in s, f x) ≡ if a in s then f a else 0 [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum,
    apply_ite Int.cast] at *
  exact Finset.sum_eq_ite _ hf

/--
theorem `sum_modEq_single` / 定理 `sum_modEq_single`

English:
theorem sum_modEq_single
  statement: {s : Finset α} {a : α}
  proof: by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

中文:
定理 sum_modEq_single
  结论: {s : Finset α} {a : α}
  证明: by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

Depends on / 依赖: Finset, Finset.sum_eq_single, ZMod.intCast_eq_intCast_iff, cast_sum, cast_zero, intCast_eq_intCast_iff, modEq_natAbs, sum_eq_single
-/
theorem sum_modEq_single {s : Finset α} {a : α}
    (ha : a ∉ s -> f a ≡ 0 [ZMOD n]) (hf : forall x in s, x != a -> f x ≡ 0 [ZMOD n]) :
    (∑ x in s, f x) ≡ f a [ZMOD n] := by
  simp only [← modEq_natAbs (n := n), ← ZMod.intCast_eq_intCast_iff, cast_zero, cast_sum] at *
  apply Finset.sum_eq_single <;> assumption

end Int
