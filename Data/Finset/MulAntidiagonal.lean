/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Data.Set.MulAntidiagonal
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Multiplication antidiagonal as a `Finset`.

We construct the `Finset` of all pairs
of an element in `s` and an element in `t` that multiply to `a`,
given that `s` and `t` are well-ordered. -/

@[expose] public section


namespace Set

open scoped Pointwise

variable {α : Type*} {s t : Set α}

@[to_additive]
/--
theorem `IsPWO.mul` / 定理 `IsPWO.mul`

English:
theorem IsPWO.mul
  statement: [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
  proof: by
  rw [← image_mul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd)

中文:
定理 IsPWO.mul
  结论: [交换幺半群 α] [偏序 α] [是OrderedCancel幺半群 α]
  证明: by
  rw [← image_mul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd)

Depends on / 依赖: hs.prod, image_mul_prod, image_of_monotone, monotone_fst, monotone_fst.mul, monotone_snd
-/
theorem IsPWO.mul [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
    (hs : s.IsPWO) (ht : t.IsPWO) : IsPWO (s * t) := by
  rw [← image_mul_prod]
  exact (hs.prod ht).image_of_monotone (monotone_fst.mul' monotone_snd)

variable [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α]

@[to_additive]
/--
theorem `IsWF.mul` / 定理 `IsWF.mul`

English:
theorem IsWF.mul
  given: (hs : s.IsWF) (ht : t.IsWF)
  statement: IsWF (s * t)
  proof: (hs.isPWO.mul ht.isPWO).isWF

@[to_additive]

中文:
定理 IsWF.mul
  条件: (hs : s.IsWF) (ht : t.IsWF)
  结论: IsWF (s * t)
  证明: (hs.isPWO.mul ht.isPWO).isWF

@[to_additive]

Depends on / 依赖: hs.isPWO.mul, ht.isPWO
-/
theorem IsWF.mul (hs : s.IsWF) (ht : t.IsWF) : IsWF (s * t) :=
  (hs.isPWO.mul ht.isPWO).isWF

@[to_additive]
/--
theorem `IsWF.min_mul` / 定理 `IsWF.min_mul`

English:
theorem IsWF.min_mul
  given: (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty)
  proof: by
  refine le_antisymm (IsWF.min_le _ _ (mem_mul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)

中文:
定理 IsWF.min_mul
  条件: (hs : s.IsWF) (ht : t.IsWF) (hsn : s.非空) (htn : t.非空)
  证明: by
  refine le_antisymm (IsWF.min_le _ _ (mem_mul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)

Depends on / 依赖: IsWF.le_min_iff, IsWF.min_le, hs.min_le, hs.min_mem, ht.min_le, ht.min_mem, le_antisymm, le_min_iff, mem_mul, min_le, min_mem, mul_le_mul
-/
theorem IsWF.min_mul (hs : s.IsWF) (ht : t.IsWF) (hsn : s.Nonempty) (htn : t.Nonempty) :
    (hs.mul ht).min (hsn.mul htn) = hs.min hsn * ht.min htn := by
  refine le_antisymm (IsWF.min_le _ _ (mem_mul.2 ⟨_, hs.min_mem _, _, ht.min_mem _, rfl⟩)) ?_
  rw [IsWF.le_min_iff]
  rintro _ ⟨x, hx, y, hy, rfl⟩
  exact mul_le_mul' (hs.min_le _ hx) (ht.min_le _ hy)

end Set

namespace Finset

open scoped Pointwise

variable {α : Type*}
variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α]
  {s t : Set α} (hs : s.IsPWO) (ht : t.IsPWO) (a : α)

/-- `Finset.mulAntidiagonal hs ht a` is the set of all pairs of an element in `s` and an
element in `t` that multiply to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/
@[to_additive /-- `Finset.antidiagonal hs ht a` is the set of all pairs of an element in
`s` and an element in `t` that add to `a`, but its construction requires proofs that `s` and `t` are
well-ordered. -/]
/--
Definition of `mulAntidiagonal` / `mulAntidiagonal` 的定义

English:
definition mulAntidiagonal
  signature: : Finset (α × α)
  body: (Set.MulAntidiagonal.finite_of_isPWO hs ht a).toFinset

中文:
定义 mulAntidiagonal
  签名: : 有限集 (α × α)
  定义体: (Set.MulAntidiagonal.finite_of_isPWO hs ht a).toFinset

Depends on / 依赖: MulAntidiagonal, Set.MulAntidiagonal.finite_of_isPWO, finite_of_isPWO, toFinset
-/
noncomputable def mulAntidiagonal : Finset (α × α) :=
  (Set.MulAntidiagonal.finite_of_isPWO hs ht a).toFinset

variable {hs ht a} {u : Set α} {hu : u.IsPWO} {x : α × α}

@[to_additive (attr := simp)]
/--
theorem `mem_mulAntidiagonal` / 定理 `mem_mulAntidiagonal`

English:
theorem mem_mulAntidiagonal
  statement: x in mulAntidiagonal hs ht a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a
  proof: by
  simp only [mulAntidiagonal, Set.Finite.mem_toFinset, Set.mem_mulAntidiagonal]

@[to_additive]

中文:
定理 mem_mulAntidiagonal
  结论: x in mulAntidiagonal hs ht a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a
  证明: by
  simp only [mulAntidiagonal, Set.Finite.mem_toFinset, Set.mem_mulAntidiagonal]

@[to_additive]

Depends on / 依赖: Finite, Set.Finite.mem_toFinset, Set.mem_mulAntidiagonal, mem_mulAntidiagonal, mem_toFinset, mulAntidiagonal
-/
theorem mem_mulAntidiagonal : x in mulAntidiagonal hs ht a ↔ x.1 in s ∧ x.2 in t ∧ x.1 * x.2 = a := by
  simp only [mulAntidiagonal, Set.Finite.mem_toFinset, Set.mem_mulAntidiagonal]

@[to_additive]
/--
theorem `mulAntidiagonal_mono_left` / 定理 `mulAntidiagonal_mono_left`

English:
theorem mulAntidiagonal_mono_left
  given: (h : u subseteq s)
  statement: mulAntidiagonal hu ht a subseteq mulAntidiagonal hs ht a
  proof: Set.Finite.toFinset_mono Set.mulAntidiagonal_mono_left h

@[to_additive]

中文:
定理 mulAntidiagonal_mono_left
  条件: (h : u subseteq s)
  结论: mulAntidiagonal hu ht a subseteq mulAntidiagonal hs ht a
  证明: Set.Finite.toFinset_mono Set.mulAntidiagonal_mono_left h

@[to_additive]

Depends on / 依赖: Finite, Set.Finite.toFinset_mono, Set.mulAntidiagonal_mono_left, mulAntidiagonal_mono_left, toFinset_mono
-/
theorem mulAntidiagonal_mono_left (h : u subseteq s) : mulAntidiagonal hu ht a subseteq mulAntidiagonal hs ht a :=
Set.Finite.toFinset_mono Set.mulAntidiagonal_mono_left h

@[to_additive]
/--
theorem `mulAntidiagonal_mono_right` / 定理 `mulAntidiagonal_mono_right`

English:
theorem mulAntidiagonal_mono_right
  given: (h : u subseteq t)
  proof: Set.Finite.toFinset_mono Set.mulAntidiagonal_mono_right h

@[to_additive]

中文:
定理 mulAntidiagonal_mono_right
  条件: (h : u subseteq t)
  证明: Set.Finite.toFinset_mono Set.mulAntidiagonal_mono_right h

@[to_additive]

Depends on / 依赖: Finite, Set.Finite.toFinset_mono, Set.mulAntidiagonal_mono_right, mulAntidiagonal_mono_right, toFinset_mono
-/
theorem mulAntidiagonal_mono_right (h : u subseteq t) :
    mulAntidiagonal hs hu a subseteq mulAntidiagonal hs ht a :=
Set.Finite.toFinset_mono Set.mulAntidiagonal_mono_right h

@[to_additive]
/--
theorem `swap_mem_mulAntidiagonal` / 定理 `swap_mem_mulAntidiagonal`

English:
theorem swap_mem_mulAntidiagonal
  proof: by
  simp

@[to_additive]

中文:
定理 swap_mem_mulAntidiagonal
  证明: by
  simp

@[to_additive]
-/
theorem swap_mem_mulAntidiagonal :
    x.swap in Finset.mulAntidiagonal hs ht a ↔ x in Finset.mulAntidiagonal ht hs a := by
  simp

@[to_additive]
/--
theorem `support_mulAntidiagonal_subset_mul` / 定理 `support_mulAntidiagonal_subset_mul`

English:
theorem support_mulAntidiagonal_subset_mul
  statement: { a | (mulAntidiagonal hs ht a).Nonempty } subseteq s * t
  proof: fun a ⟨b, hb⟩ => by
  rw [mem_mulAntidiagonal] at hb
  exact ⟨b.1, hb.1, b.2, hb.2⟩

@[to_additive]

中文:
定理 support_mulAntidiagonal_subset_mul
  结论: { a | (mulAntidiagonal hs ht a).非空 } subseteq s * t
  证明: fun a ⟨b, hb⟩ => by
  rw [mem_mulAntidiagonal] at hb
  exact ⟨b.1, hb.1, b.2, hb.2⟩

@[to_additive]

Depends on / 依赖: mem_mulAntidiagonal
-/
theorem support_mulAntidiagonal_subset_mul : { a | (mulAntidiagonal hs ht a).Nonempty } subseteq s * t :=
  fun a ⟨b, hb⟩ => by
  rw [mem_mulAntidiagonal] at hb
  exact ⟨b.1, hb.1, b.2, hb.2⟩

@[to_additive]
/--
theorem `isPWO_support_mulAntidiagonal` / 定理 `isPWO_support_mulAntidiagonal`

English:
theorem isPWO_support_mulAntidiagonal
  statement: { a | (mulAntidiagonal hs ht a).Nonempty }.IsPWO
  proof: (hs.mul ht).mono support_mulAntidiagonal_subset_mul

@[to_additive]

中文:
定理 isPWO_support_mulAntidiagonal
  结论: { a | (mulAntidiagonal hs ht a).非空 }.IsPWO
  证明: (hs.mul ht).mono support_mulAntidiagonal_subset_mul

@[to_additive]

Depends on / 依赖: hs.mul, support_mulAntidiagonal_subset_mul
-/
theorem isPWO_support_mulAntidiagonal : { a | (mulAntidiagonal hs ht a).Nonempty }.IsPWO :=
  (hs.mul ht).mono support_mulAntidiagonal_subset_mul

@[to_additive]
/--
theorem `mulAntidiagonal_min_mul_min` / 定理 `mulAntidiagonal_min_mul_min`

English:
theorem mulAntidiagonal_min_mul_min
  statement: {α} [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α]
  proof: by
  ext ⟨a, b⟩
  simp only [mem_mulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (mul_lt_mul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, mul_left_cancel hst⟩
  · rintr

中文:
定理 mulAntidiagonal_min_mul_min
  结论: {α} [交换幺半群 α] [线性序 α] [是OrderedCancel幺半群 α]
  证明: by
  ext ⟨a, b⟩
  simp only [mem_mulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (mul_lt_mul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, mul_left_cancel hst⟩
  · rintr

Depends on / 依赖: Prod.ext_iff, eq_of_not_lt, ext_iff, hs.min_le, hs.min_mem, ht.min_le, ht.min_mem, mem_mulAntidiagonal, mem_singleton, min_le, min_mem, mul_left_cancel, mul_lt_mul_of_lt_of_le
-/
theorem mulAntidiagonal_min_mul_min {α} [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α]
    {s t : Set α} (hs : s.IsWF) (ht : t.IsWF) (hns : s.Nonempty) (hnt : t.Nonempty) :
    mulAntidiagonal hs.isPWO ht.isPWO (hs.min hns * ht.min hnt) = {(hs.min hns, ht.min hnt)} := by
  ext ⟨a, b⟩
  simp only [mem_mulAntidiagonal, mem_singleton, Prod.ext_iff]
  constructor
  · rintro ⟨has, hat, hst⟩
    obtain rfl :=
      (hs.min_le hns has).eq_of_not_lt fun hlt =>
        (mul_lt_mul_of_lt_of_le hlt <| ht.min_le hnt hat).ne' hst
    exact ⟨rfl, mul_left_cancel hst⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨hs.min_mem _, ht.min_mem _, rfl⟩

@[deprecated (since := "2026-06-08")] alias addAntidiagonal := antidiagonal
@[deprecated (since := "2026-06-08")] alias mem_addAntidiagonal := mem_antidiagonal
@[deprecated (since := "2026-06-08")] alias addAntidiagonal_mono_left := antidiagonal_mono_left
@[deprecated (since := "2026-06-08")] alias addAntidiagonal_mono_right := antidiagonal_mono_right
@[deprecated (since := "2026-06-08")] alias swap_mem_addAntidiagonal := swap_mem_antidiagonal
@[deprecated (since := "2026-06-08")]
alias support_addAntidiagonal_subset_add := support_antidiagonal_subset_add
@[deprecated (since := "2026-06-08")]
alias isPWO_support_addAntidiagonal := isPWO_support_antidiagonal
@[deprecated (since := "2026-06-08")] alias addAntidiagonal_min_mul_min := antidiagonal_min_add_min

end Finset
