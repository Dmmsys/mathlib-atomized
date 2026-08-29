/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Indicator
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-!
# Finitely supported product of finsets

This file defines the finitely supported product of finsets as a `Finset (ι →₀ α)`.

## Main declarations

* `Finset.finsupp`: Finitely supported product of finsets. `s.finset t` is the product of the `t i`
  over all `i ∈ s`.
* `Finsupp.pi`: `f.pi` is the finset of `Finsupp`s whose `i`-th value lies in `f i`. This is the
  special case of `Finset.finsupp` where we take the product of the `f i` over the support of `f`.

## Implementation notes

We make heavy use of the fact that `0 : Finset α` is `{0}`. This scalar actions convention turns out
to be precisely what we want here too.
-/

@[expose] public section


noncomputable section

open Finsupp

open scoped Pointwise

variable {ι α : Type*} [Zero α] {s : Finset ι} {f : ι ->₀ α}

namespace Finset

open scoped Classical in
/--
Definition of `finsupp` / `finsupp` 的定义

English:
definition finsupp
  signature: (s : Finset ι) (t : ι -> Finset α)
  body: (s.pi t).map ⟨indicator s, indicator_injective s⟩

中文:
定义 finsupp
  签名: (s : 有限集 ι) (t : ι -> 有限集 α)
  定义体: (s.pi t).map ⟨indicator s, indicator_injective s⟩
-/
protected def finsupp (s : Finset ι) (t : ι -> Finset α) : Finset (ι ->₀ α) :=
  (s.pi t).map ⟨indicator s, indicator_injective s⟩

/--
theorem `mem_finsupp_iff` / 定理 `mem_finsupp_iff`

English:
theorem mem_finsupp_iff
  given: {t : ι -> Finset α}
  proof: by
  classical
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨support_indicator_subset _ _, fun i hi => ?_⟩
    convert! mem_pi.1 hf i hi
    exact indicator_of_mem hi _
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    exact ite_eq_left_iff.2 fun hi => (notMe

中文:
定理 mem_finsupp_iff
  条件: {t : ι -> 有限集 α}
  证明: by
  classical
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨support_indicator_subset _ _, fun i hi => ?_⟩
    convert! mem_pi.1 hf i hi
    exact indicator_of_mem hi _
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    exact ite_eq_left_iff.2 fun hi => (notMe

Depends on / 依赖: classical, convert, indicator_of_mem, ite_eq_left_iff, mem_map, mem_map.trans, mem_pi, notMem_support_iff, support_indicator_subset
-/
theorem mem_finsupp_iff {t : ι -> Finset α} :
    f in s.finsupp t ↔ f.support subseteq s ∧ forall i in s, f i in t i := by
  classical
  refine mem_map.trans ⟨?_, ?_⟩
  · rintro ⟨f, hf, rfl⟩
    refine ⟨support_indicator_subset _ _, fun i hi => ?_⟩
    convert! mem_pi.1 hf i hi
    exact indicator_of_mem hi _
  · refine fun h => ⟨fun i _ => f i, mem_pi.2 h.2, ?_⟩
    ext i
    exact ite_eq_left_iff.2 fun hi => (notMem_support_iff.1 fun H => hi <| h.1 H).symm

/-- When `t` is supported on `s`, `f ∈ s.finsupp t` precisely means that `f` is pointwise in `t`. -/
@[simp]
/--
theorem `mem_finsupp_iff_of_support_subset` / 定理 `mem_finsupp_iff_of_support_subset`

English:
theorem mem_finsupp_iff_of_support_subset
  given: {t : ι ->₀ Finset α} (ht : t.support subseteq s)
  proof: by
  refine
    mem_finsupp_iff.trans
      (forall_and.symm.trans <|
        forall_congr' fun i =>
          ⟨fun h => ?_, fun h =>
⟨fun hi => ht mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i in s
    · exact h.2 hi
    · rw [notMem_support_iff.1 (mt h.1 hi)

中文:
定理 mem_finsupp_iff_of_support_subset
  条件: {t : ι ->₀ 有限集 α} (ht : t.support subseteq s)
  证明: by
  refine
    mem_finsupp_iff.trans
      (forall_and.symm.trans <|
        forall_congr' fun i =>
          ⟨fun h => ?_, fun h =>
⟨fun hi => ht mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i in s
    · exact h.2 hi
    · rw [notMem_support_iff.1 (mt h.1 hi)

Depends on / 依赖: forall_and, forall_and.symm.trans, forall_congr, mem_finsupp_iff, mem_finsupp_iff.trans, mem_support_iff, mem_zero, notMem_support_iff, zero_mem_zero
-/
theorem mem_finsupp_iff_of_support_subset {t : ι ->₀ Finset α} (ht : t.support subseteq s) :
    f in s.finsupp t ↔ forall i, f i in t i := by
  refine
    mem_finsupp_iff.trans
      (forall_and.symm.trans <|
        forall_congr' fun i =>
          ⟨fun h => ?_, fun h =>
⟨fun hi => ht mem_support_iff.2 fun H => mem_support_iff.1 hi ?_, fun _ => h⟩⟩)
  · by_cases hi : i in s
    · exact h.2 hi
    · rw [notMem_support_iff.1 (mt h.1 hi), notMem_support_iff.1 fun H => hi <| ht H]
      exact zero_mem_zero
  · rwa [H, mem_zero] at h

@[simp]
/--
theorem `card_finsupp` / 定理 `card_finsupp`

English:
theorem card_finsupp
  given: (s : Finset ι) (t : ι -> Finset α)
  statement: #(s.finsupp t) = ∏ i in s, #(t i)
  proof: by
classical exact (card_map _).trans card_pi _ _

中文:
定理 card_finsupp
  条件: (s : 有限集 ι) (t : ι -> 有限集 α)
  结论: #(s.finsupp t) = ∏ i in s, #(t i)
  证明: by
classical exact (card_map _).trans card_pi _ _

Depends on / 依赖: card_map, card_pi, classical
-/
theorem card_finsupp (s : Finset ι) (t : ι -> Finset α) : #(s.finsupp t) = ∏ i in s, #(t i) := by
classical exact (card_map _).trans card_pi _ _

end Finset

open Finset

namespace Finsupp

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: (f : ι ->₀ Finset α)
  body: f.support.finsupp f

@[simp]

中文:
定义 pi
  签名: (f : ι ->₀ 有限集 α)
  定义体: f.support.finsupp f

@[simp]

Depends on / 依赖: f.support.finsupp, finsupp, support
-/
def pi (f : ι ->₀ Finset α) : Finset (ι ->₀ α) :=
  f.support.finsupp f

@[simp]
/--
theorem `mem_pi` / 定理 `mem_pi`

English:
theorem mem_pi
  given: {f : ι ->₀ Finset α} {g : ι ->₀ α}
  statement: g in f.pi ↔ forall i, g i in f i
  proof: mem_finsupp_iff_of_support_subset Subset.refl _

@[simp]

中文:
定理 mem_pi
  条件: {f : ι ->₀ 有限集 α} {g : ι ->₀ α}
  结论: g in f.pi ↔ 对任意 i, g i in f i
  证明: mem_finsupp_iff_of_support_subset Subset.refl _

@[simp]

Depends on / 依赖: Subset, Subset.refl, mem_finsupp_iff_of_support_subset
-/
theorem mem_pi {f : ι ->₀ Finset α} {g : ι ->₀ α} : g in f.pi ↔ forall i, g i in f i :=
mem_finsupp_iff_of_support_subset Subset.refl _

@[simp]
/--
theorem `card_pi` / 定理 `card_pi`

English:
theorem card_pi
  given: (f : ι ->₀ Finset α)
  statement: #f.pi = f.prod fun i => #(f i)
  proof: by
  rw [pi]; rw [card_finsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]

中文:
定理 card_pi
  条件: (f : ι ->₀ 有限集 α)
  结论: #f.pi = f.乘积 fun i => #(f i)
  证明: by
  rw [pi]; rw [card_finsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]

Depends on / 依赖: Finset, Finset.prod_congr, Nat.cast_id, Pi.natCast_apply, card_finsupp, cast_id, natCast_apply, prod_congr
-/
theorem card_pi (f : ι ->₀ Finset α) : #f.pi = f.prod fun i => #(f i) := by
  rw [pi]; rw [card_finsupp]
  exact Finset.prod_congr rfl fun i _ => by simp only [Pi.natCast_apply, Nat.cast_id]

end Finsupp
