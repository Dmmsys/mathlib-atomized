/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Notation.Indicator

/-!
# Indicator function

In this file, we prove basic results about the indicator of a set.

- `Set.indicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `Set.mulIndicator (s : Set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.


## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `fun _ ↦ 1`.

The indicator function is implemented non-computably, to avoid having to pass around `Decidable`
arguments. This is in contrast with the design of `Pi.single` or `Set.piecewise`.

## Tags
indicator, characteristic
-/

@[expose] public section

assert_not_exists MonoidWithZero

open Function

variable {α β γ M N : Type*}

namespace Set

section Monoid

variable [MulOneClass M] {s t : Set α} {a : α}

@[to_additive]
/--
theorem `mulIndicator_union_mul_inter_apply` / 定理 `mulIndicator_union_mul_inter_apply`

English:
theorem mulIndicator_union_mul_inter_apply
  given: (f : α -> M) (s t : Set α) (a : α)
  proof: by
  by_cases hs : a in s <;> by_cases ht : a in t <;> simp [*]

@[to_additive]

中文:
定理 mulIndicator_union_mul_inter_apply
  条件: (f : α -> M) (s t : 集合 α) (a : α)
  证明: by
  by_cases hs : a in s <;> by_cases ht : a in t <;> simp [*]

@[to_additive]
-/
theorem mulIndicator_union_mul_inter_apply (f : α -> M) (s t : Set α) (a : α) :
    mulIndicator (s union t) f a * mulIndicator (s inter t) f a
      = mulIndicator s f a * mulIndicator t f a := by
  by_cases hs : a in s <;> by_cases ht : a in t <;> simp [*]

@[to_additive]
/--
theorem `mulIndicator_union_mul_inter` / 定理 `mulIndicator_union_mul_inter`

English:
theorem mulIndicator_union_mul_inter
  given: (f : α -> M) (s t : Set α)
  proof: funext mulIndicator_union_mul_inter_apply f s t

@[to_additive]

中文:
定理 mulIndicator_union_mul_inter
  条件: (f : α -> M) (s t : 集合 α)
  证明: funext mulIndicator_union_mul_inter_apply f s t

@[to_additive]

Depends on / 依赖: mulIndicator_union_mul_inter_apply
-/
theorem mulIndicator_union_mul_inter (f : α -> M) (s t : Set α) :
    mulIndicator (s union t) f * mulIndicator (s inter t) f = mulIndicator s f * mulIndicator t f :=
funext mulIndicator_union_mul_inter_apply f s t

@[to_additive]
/--
theorem `mulIndicator_union_of_notMem_inter` / 定理 `mulIndicator_union_of_notMem_inter`

English:
theorem mulIndicator_union_of_notMem_inter
  given: (h : a ∉ s inter t) (f : α -> M)
  proof: by
  rw [← mulIndicator_union_mul_inter_apply f s t]; rw [mulIndicator_of_notMem h]; rw [mul_one]

@[to_additive]

中文:
定理 mulIndicator_union_of_notMem_inter
  条件: (h : a ∉ s inter t) (f : α -> M)
  证明: by
  rw [← mulIndicator_union_mul_inter_apply f s t]; rw [mulIndicator_of_notMem h]; rw [mul_one]

@[to_additive]

Depends on / 依赖: mulIndicator_of_notMem, mulIndicator_union_mul_inter_apply, mul_one
-/
theorem mulIndicator_union_of_notMem_inter (h : a ∉ s inter t) (f : α -> M) :
    mulIndicator (s union t) f a = mulIndicator s f a * mulIndicator t f a := by
  rw [← mulIndicator_union_mul_inter_apply f s t]; rw [mulIndicator_of_notMem h]; rw [mul_one]

@[to_additive]
/--
theorem `mulIndicator_union_of_disjoint` / 定理 `mulIndicator_union_of_disjoint`

English:
theorem mulIndicator_union_of_disjoint
  given: (h : Disjoint s t) (f : α -> M)
  proof: funext fun _ => mulIndicator_union_of_notMem_inter (fun ha => h.le_bot ha) _

中文:
定理 mulIndicator_union_of_disjoint
  条件: (h : Disjoint s t) (f : α -> M)
  证明: funext fun _ => mulIndicator_union_of_notMem_inter (fun ha => h.le_bot ha) _

Depends on / 依赖: h.le_bot, le_bot, mulIndicator_union_of_notMem_inter
-/
theorem mulIndicator_union_of_disjoint (h : Disjoint s t) (f : α -> M) :
    mulIndicator (s union t) f = fun a => mulIndicator s f a * mulIndicator t f a :=
  funext fun _ => mulIndicator_union_of_notMem_inter (fun ha => h.le_bot ha) _

open scoped symmDiff in
@[to_additive]
/--
theorem `mulIndicator_symmDiff` / 定理 `mulIndicator_symmDiff`

English:
theorem mulIndicator_symmDiff
  given: (s t : Set α) (f : α -> M)
  proof: mulIndicator_union_of_disjoint (disjoint_sdiff_self_right.mono_left sdiff_le) _

@[to_additive]

中文:
定理 mulIndicator_symmDiff
  条件: (s t : 集合 α) (f : α -> M)
  证明: mulIndicator_union_of_disjoint (disjoint_sdiff_self_right.mono_left sdiff_le) _

@[to_additive]

Depends on / 依赖: disjoint_sdiff_self_right, disjoint_sdiff_self_right.mono_left, mono_left, mulIndicator_union_of_disjoint, sdiff_le
-/
theorem mulIndicator_symmDiff (s t : Set α) (f : α -> M) :
    mulIndicator (s ∆ t) f = mulIndicator (s \ t) f * mulIndicator (t \ s) f :=
  mulIndicator_union_of_disjoint (disjoint_sdiff_self_right.mono_left sdiff_le) _

@[to_additive]
/--
theorem `mulIndicator_mul` / 定理 `mulIndicator_mul`

English:
theorem mulIndicator_mul
  given: (s : Set α) (f g : α -> M)
  proof: by
  funext
  simp only [mulIndicator]
  split_ifs
  · rfl
  rw [mul_one]

@[to_additive]

中文:
定理 mulIndicator_mul
  条件: (s : 集合 α) (f g : α -> M)
  证明: by
  funext
  simp only [mulIndicator]
  split_ifs
  · rfl
  rw [mul_one]

@[to_additive]

Depends on / 依赖: mulIndicator, mul_one, split_ifs
-/
theorem mulIndicator_mul (s : Set α) (f g : α -> M) :
    (mulIndicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g a := by
  funext
  simp only [mulIndicator]
  split_ifs
  · rfl
  rw [mul_one]

@[to_additive]
/--
theorem `mulIndicator_mul'` / 定理 `mulIndicator_mul'`

English:
theorem mulIndicator_mul'
  given: (s : Set α) (f g : α -> M)
  proof: mulIndicator_mul s f g

@[to_additive (attr := simp)]

中文:
定理 mulIndicator_mul'
  条件: (s : 集合 α) (f g : α -> M)
  证明: mulIndicator_mul s f g

@[to_additive (attr := simp)]

Depends on / 依赖: mulIndicator_mul
-/
theorem mulIndicator_mul' (s : Set α) (f g : α -> M) :
    mulIndicator s (f * g) = mulIndicator s f * mulIndicator s g :=
  mulIndicator_mul s f g

@[to_additive (attr := simp)]
/--
theorem `mulIndicator_compl_mul_self_apply` / 定理 `mulIndicator_compl_mul_self_apply`

English:
theorem mulIndicator_compl_mul_self_apply
  given: (s : Set α) (f : α -> M) (a : α)
  proof: by_cases (fun ha : a in s => by simp [ha]) fun ha => by simp [ha]

@[to_additive (attr := simp)]

中文:
定理 mulIndicator_compl_mul_self_apply
  条件: (s : 集合 α) (f : α -> M) (a : α)
  证明: by_cases (fun ha : a in s => by simp [ha]) fun ha => by simp [ha]

@[to_additive (attr := simp)]
-/
theorem mulIndicator_compl_mul_self_apply (s : Set α) (f : α -> M) (a : α) :
    mulIndicator sᶜ f a * mulIndicator s f a = f a :=
  by_cases (fun ha : a in s => by simp [ha]) fun ha => by simp [ha]

@[to_additive (attr := simp)]
/--
theorem `mulIndicator_compl_mul_self` / 定理 `mulIndicator_compl_mul_self`

English:
theorem mulIndicator_compl_mul_self
  given: (s : Set α) (f : α -> M)
  proof: funext mulIndicator_compl_mul_self_apply s f

@[to_additive (attr := simp)]

中文:
定理 mulIndicator_compl_mul_self
  条件: (s : 集合 α) (f : α -> M)
  证明: funext mulIndicator_compl_mul_self_apply s f

@[to_additive (attr := simp)]

Depends on / 依赖: mulIndicator_compl_mul_self_apply
-/
theorem mulIndicator_compl_mul_self (s : Set α) (f : α -> M) :
    mulIndicator sᶜ f * mulIndicator s f = f :=
funext mulIndicator_compl_mul_self_apply s f

@[to_additive (attr := simp)]
/--
theorem `mulIndicator_self_mul_compl_apply` / 定理 `mulIndicator_self_mul_compl_apply`

English:
theorem mulIndicator_self_mul_compl_apply
  given: (s : Set α) (f : α -> M) (a : α)
  proof: by_cases (fun ha : a in s => by simp [ha]) fun ha => by simp [ha]

@[to_additive (attr := simp)]

中文:
定理 mulIndicator_self_mul_compl_apply
  条件: (s : 集合 α) (f : α -> M) (a : α)
  证明: by_cases (fun ha : a in s => by simp [ha]) fun ha => by simp [ha]

@[to_additive (attr := simp)]
-/
theorem mulIndicator_self_mul_compl_apply (s : Set α) (f : α -> M) (a : α) :
    mulIndicator s f a * mulIndicator sᶜ f a = f a :=
  by_cases (fun ha : a in s => by simp [ha]) fun ha => by simp [ha]

@[to_additive (attr := simp)]
/--
theorem `mulIndicator_self_mul_compl` / 定理 `mulIndicator_self_mul_compl`

English:
theorem mulIndicator_self_mul_compl
  given: (s : Set α) (f : α -> M)
  proof: funext mulIndicator_self_mul_compl_apply s f

@[to_additive]

中文:
定理 mulIndicator_self_mul_compl
  条件: (s : 集合 α) (f : α -> M)
  证明: funext mulIndicator_self_mul_compl_apply s f

@[to_additive]

Depends on / 依赖: mulIndicator_self_mul_compl_apply
-/
theorem mulIndicator_self_mul_compl (s : Set α) (f : α -> M) :
    mulIndicator s f * mulIndicator sᶜ f = f :=
funext mulIndicator_self_mul_compl_apply s f

@[to_additive]
/--
theorem `mulIndicator_mul_eq_left` / 定理 `mulIndicator_mul_eq_left`

English:
theorem mulIndicator_mul_eq_left
  given: {f g : α -> M} (h : Disjoint (mulSupport f) (mulSupport g))
  proof: by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : g x = 1 := notMem_mulSupport.1 (disjoint_left.1 h hx)
  rw [Pi.mul_apply]; rw [this]; rw [mul_one]

@[to_additive]

中文:
定理 mulIndicator_mul_eq_left
  条件: {f g : α -> M} (h : Disjoint (mulSupport f) (mulSupport g))
  证明: by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : g x = 1 := notMem_mulSupport.1 (disjoint_left.1 h hx)
  rw [Pi.mul_apply]; rw [this]; rw [mul_one]

@[to_additive]

Depends on / 依赖: Pi.mul_apply, disjoint_left, mulIndicator_congr, mulIndicator_mulSupport, mul_apply, mul_one, notMem_mulSupport
-/
theorem mulIndicator_mul_eq_left {f g : α -> M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport f).mulIndicator (f * g) = f := by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : g x = 1 := notMem_mulSupport.1 (disjoint_left.1 h hx)
  rw [Pi.mul_apply]; rw [this]; rw [mul_one]

@[to_additive]
/--
theorem `mulIndicator_mul_eq_right` / 定理 `mulIndicator_mul_eq_right`

English:
theorem mulIndicator_mul_eq_right
  given: {f g : α -> M} (h : Disjoint (mulSupport f) (mulSupport g))
  proof: by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : f x = 1 := notMem_mulSupport.1 (disjoint_right.1 h hx)
  rw [Pi.mul_apply]; rw [this]; rw [one_mul]

@[to_additive]

中文:
定理 mulIndicator_mul_eq_right
  条件: {f g : α -> M} (h : Disjoint (mulSupport f) (mulSupport g))
  证明: by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : f x = 1 := notMem_mulSupport.1 (disjoint_right.1 h hx)
  rw [Pi.mul_apply]; rw [this]; rw [one_mul]

@[to_additive]

Depends on / 依赖: Pi.mul_apply, disjoint_right, mulIndicator_congr, mulIndicator_mulSupport, mul_apply, notMem_mulSupport, one_mul
-/
theorem mulIndicator_mul_eq_right {f g : α -> M} (h : Disjoint (mulSupport f) (mulSupport g)) :
    (mulSupport g).mulIndicator (f * g) = g := by
  refine (mulIndicator_congr fun x hx => ?_).trans mulIndicator_mulSupport
  have : f x = 1 := notMem_mulSupport.1 (disjoint_right.1 h hx)
  rw [Pi.mul_apply]; rw [this]; rw [one_mul]

@[to_additive]
/--
theorem `mulIndicator_mul_compl_eq_piecewise` / 定理 `mulIndicator_mul_compl_eq_piecewise`

English:
theorem mulIndicator_mul_compl_eq_piecewise
  given: [DecidablePred (· in s)] (f g : α -> M)
  proof: by
  ext x
  by_cases h : x in s
  · rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_mem h,
      Set.mulIndicator_of_notMem (Set.notMem_compl_iff.2 h), mul_one]
  · rw [piecewise_eq_of_notMem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_notMem h,
      Set.mulIndicator_of_mem (Set.

中文:
定理 mulIndicator_mul_compl_eq_piecewise
  条件: [DecidablePred (· in s)] (f g : α -> M)
  证明: by
  ext x
  by_cases h : x in s
  · rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_mem h,
      Set.mulIndicator_of_notMem (Set.notMem_compl_iff.2 h), mul_one]
  · rw [piecewise_eq_of_notMem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_notMem h,
      Set.mulIndicator_of_mem (Set.

Depends on / 依赖: Pi.mul_apply, Set.mem_compl, Set.mulIndicator_of_mem, Set.mulIndicator_of_notMem, Set.notMem_compl_iff, mem_compl, mulIndicator_of_mem, mulIndicator_of_notMem, mul_apply, mul_one, notMem_compl_iff, one_mul, piecewise_eq_of_mem, piecewise_eq_of_notMem
-/
theorem mulIndicator_mul_compl_eq_piecewise [DecidablePred (· in s)] (f g : α -> M) :
    s.mulIndicator f * sᶜ.mulIndicator g = s.piecewise f g := by
  ext x
  by_cases h : x in s
  · rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_mem h,
      Set.mulIndicator_of_notMem (Set.notMem_compl_iff.2 h), mul_one]
  · rw [piecewise_eq_of_notMem _ _ _ h, Pi.mul_apply, Set.mulIndicator_of_notMem h,
      Set.mulIndicator_of_mem (Set.mem_compl h), one_mul]

/-- `Set.mulIndicator` as a `monoidHom`. -/
@[to_additive /-- `Set.indicator` as an `addMonoidHom`. -/]
/--
Definition of `mulIndicatorHom` / `mulIndicatorHom` 的定义

English:
definition mulIndicatorHom
  signature: {α} (M) [MulOneClass M] (s : Set α)
  body: mulIndicator s
  map_one' := mulIndicator_one M s
  map_mul' := mulIndicator_mul s

中文:
定义 mulIndicatorHom
  签名: {α} (M) [MulOne类 M] (s : 集合 α)
  定义体: mulIndicator s
  map_one' := mulIndicator_one M s
  map_mul' := mulIndicator_mul s

Depends on / 依赖: mulIndicator
-/
noncomputable def mulIndicatorHom {α} (M) [MulOneClass M] (s : Set α) : (α -> M) ->* α -> M where
  toFun := mulIndicator s
  map_one' := mulIndicator_one M s
  map_mul' := mulIndicator_mul s

end Monoid

section Group

variable {G : Type*} [Group G] {s t : Set α}

@[to_additive]
/--
theorem `mulIndicator_inv'` / 定理 `mulIndicator_inv'`

English:
theorem mulIndicator_inv'
  given: (s : Set α) (f : α -> G)
  statement: mulIndicator s f⁻¹ = (mulIndicator s f)⁻¹
  proof: (mulIndicatorHom G s).map_inv f

@[to_additive]

中文:
定理 mulIndicator_inv'
  条件: (s : 集合 α) (f : α -> G)
  结论: mulIndicator s f⁻¹ = (mulIndicator s f)⁻¹
  证明: (mulIndicatorHom G s).map_inv f

@[to_additive]

Depends on / 依赖: map_inv, mulIndicatorHom
-/
theorem mulIndicator_inv' (s : Set α) (f : α -> G) : mulIndicator s f⁻¹ = (mulIndicator s f)⁻¹ :=
  (mulIndicatorHom G s).map_inv f

@[to_additive]
/--
theorem `mulIndicator_inv` / 定理 `mulIndicator_inv`

English:
theorem mulIndicator_inv
  given: (s : Set α) (f : α -> G)
  proof: mulIndicator_inv' s f

@[to_additive]

中文:
定理 mulIndicator_inv
  条件: (s : 集合 α) (f : α -> G)
  证明: mulIndicator_inv' s f

@[to_additive]

Depends on / 依赖: mulIndicator_inv
-/
theorem mulIndicator_inv (s : Set α) (f : α -> G) :
    (mulIndicator s fun a => (f a)⁻¹) = fun a => (mulIndicator s f a)⁻¹ :=
  mulIndicator_inv' s f

@[to_additive]
/--
theorem `mulIndicator_div` / 定理 `mulIndicator_div`

English:
theorem mulIndicator_div
  given: (s : Set α) (f g : α -> G)
  proof: (mulIndicatorHom G s).map_div f g

@[to_additive]

中文:
定理 mulIndicator_div
  条件: (s : 集合 α) (f g : α -> G)
  证明: (mulIndicatorHom G s).map_div f g

@[to_additive]

Depends on / 依赖: map_div, mulIndicatorHom
-/
theorem mulIndicator_div (s : Set α) (f g : α -> G) :
    (mulIndicator s fun a => f a / g a) = fun a => mulIndicator s f a / mulIndicator s g a :=
  (mulIndicatorHom G s).map_div f g

@[to_additive]
/--
theorem `mulIndicator_div'` / 定理 `mulIndicator_div'`

English:
theorem mulIndicator_div'
  given: (s : Set α) (f g : α -> G)
  proof: mulIndicator_div s f g

@[to_additive indicator_compl']

中文:
定理 mulIndicator_div'
  条件: (s : 集合 α) (f g : α -> G)
  证明: mulIndicator_div s f g

@[to_additive indicator_compl']

Depends on / 依赖: mulIndicator_div
-/
theorem mulIndicator_div' (s : Set α) (f g : α -> G) :
    mulIndicator s (f / g) = mulIndicator s f / mulIndicator s g :=
  mulIndicator_div s f g

@[to_additive indicator_compl']
/--
theorem `mulIndicator_compl` / 定理 `mulIndicator_compl`

English:
theorem mulIndicator_compl
  given: (s : Set α) (f : α -> G)
  proof: eq_mul_inv_of_mul_eq s.mulIndicator_compl_mul_self f

@[to_additive indicator_compl]

中文:
定理 mulIndicator_compl
  条件: (s : 集合 α) (f : α -> G)
  证明: eq_mul_inv_of_mul_eq s.mulIndicator_compl_mul_self f

@[to_additive indicator_compl]

Depends on / 依赖: eq_mul_inv_of_mul_eq, mulIndicator_compl_mul_self, s.mulIndicator_compl_mul_self
-/
theorem mulIndicator_compl (s : Set α) (f : α -> G) :
    mulIndicator sᶜ f = f * (mulIndicator s f)⁻¹ :=
eq_mul_inv_of_mul_eq s.mulIndicator_compl_mul_self f

@[to_additive indicator_compl]
/--
theorem `mulIndicator_compl'` / 定理 `mulIndicator_compl'`

English:
theorem mulIndicator_compl'
  given: (s : Set α) (f : α -> G)
  proof: by rw [div_eq_mul_inv, mulIndicator_compl]

@[to_additive indicator_sdiff']

中文:
定理 mulIndicator_compl'
  条件: (s : 集合 α) (f : α -> G)
  证明: by rw [div_eq_mul_inv, mulIndicator_compl]

@[to_additive indicator_sdiff']

Depends on / 依赖: div_eq_mul_inv, mulIndicator_compl
-/
theorem mulIndicator_compl' (s : Set α) (f : α -> G) :
    mulIndicator sᶜ f = f / mulIndicator s f := by rw [div_eq_mul_inv, mulIndicator_compl]

@[to_additive indicator_sdiff']
/--
theorem `mulIndicator_sdiff` / 定理 `mulIndicator_sdiff`

English:
theorem mulIndicator_sdiff
  given: (h : s subseteq t) (f : α -> G)
  proof: eq_mul_inv_of_mul_eq by
    rw [Pi.mul_def]; rw [← mulIndicator_union_of_disjoint]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right h]
    exact disjoint_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias mulIndicator_diff := mulIndicator_sdiff

@[to_additive indicator_sdiff]

中文:
定理 mulIndicator_sdiff
  条件: (h : s subseteq t) (f : α -> G)
  证明: eq_mul_inv_of_mul_eq by
    rw [Pi.mul_def]; rw [← mulIndicator_union_of_disjoint]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right h]
    exact disjoint_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias mulIndicator_diff := mulIndicator_sdiff

@[to_additive indicator_sdiff]

Depends on / 依赖: Pi.mul_def, disjoint_sdiff_self_left, eq_mul_inv_of_mul_eq, mulIndicator_union_of_disjoint, mul_def, sdiff_union_self, union_eq_self_of_subset_right
-/
theorem mulIndicator_sdiff (h : s subseteq t) (f : α -> G) :
    mulIndicator (t \ s) f = mulIndicator t f * (mulIndicator s f)⁻¹ :=
eq_mul_inv_of_mul_eq by
    rw [Pi.mul_def]; rw [← mulIndicator_union_of_disjoint]; rw [sdiff_union_self]; rw [union_eq_self_of_subset_right h]
    exact disjoint_sdiff_self_left

@[deprecated (since := "2026-06-03")] alias mulIndicator_diff := mulIndicator_sdiff

@[to_additive indicator_sdiff]
/--
theorem `mulIndicator_sdiff'` / 定理 `mulIndicator_sdiff'`

English:
theorem mulIndicator_sdiff'
  given: (h : s subseteq t) (f : α -> G)
  proof: by
  rw [mulIndicator_sdiff h]; rw [div_eq_mul_inv]

@[deprecated (since := "2026-06-03")] alias mulIndicator_diff' := mulIndicator_sdiff'

中文:
定理 mulIndicator_sdiff'
  条件: (h : s subseteq t) (f : α -> G)
  证明: by
  rw [mulIndicator_sdiff h]; rw [div_eq_mul_inv]

@[deprecated (since := "2026-06-03")] alias mulIndicator_diff' := mulIndicator_sdiff'

Depends on / 依赖: div_eq_mul_inv, mulIndicator_sdiff
-/
theorem mulIndicator_sdiff' (h : s subseteq t) (f : α -> G) :
    mulIndicator (t \ s) f = mulIndicator t f / mulIndicator s f := by
  rw [mulIndicator_sdiff h]; rw [div_eq_mul_inv]

@[deprecated (since := "2026-06-03")] alias mulIndicator_diff' := mulIndicator_sdiff'

open scoped symmDiff in
@[to_additive]
/--
theorem `apply_mulIndicator_symmDiff` / 定理 `apply_mulIndicator_symmDiff`

English:
theorem apply_mulIndicator_symmDiff
  statement: {g : G -> β} (hg : forall x, g x⁻¹ = g x)
  proof: by
  by_cases hs : x in s <;> by_cases ht : x in t <;> simp [mem_symmDiff, *]

中文:
定理 apply_mulIndicator_symmDiff
  结论: {g : G -> β} (hg : 对任意 x, g x⁻¹ = g x)
  证明: by
  by_cases hs : x in s <;> by_cases ht : x in t <;> simp [mem_symmDiff, *]

Depends on / 依赖: mem_symmDiff
-/
theorem apply_mulIndicator_symmDiff {g : G -> β} (hg : forall x, g x⁻¹ = g x)
    (s t : Set α) (f : α -> G) (x : α) :
    g (mulIndicator (s ∆ t) f x) = g (mulIndicator s f x / mulIndicator t f x) := by
  by_cases hs : x in s <;> by_cases ht : x in t <;> simp [mem_symmDiff, *]

end Group

section One

@[to_additive]
/--
lemma `mulSupport_subset_subsingleton_of_disjoint_on_mulSupport` / 引理 `mulSupport_subset_subsingleton_of_disjoint_on_mulSupport`

English:
lemma mulSupport_subset_subsingleton_of_disjoint_on_mulSupport
  statement: [One β] {s : γ -> Set α} (f : α -> β)
  proof: by
  suffices forall j', j' != j -> {i} subseteq s j -> {i} subseteq s j' -> {i} subseteq mulSupport f -> False by by_contra; aesop
  intro j' h hj hj' hi
  simp only [Pairwise, Disjoint, Set.subset_inter_iff] at hs
  simpa using hs h ⟨hj', hi⟩ ⟨hj, hi⟩

中文:
引理 mulSupport_subset_subsingleton_of_disjoint_on_mulSupport
  结论: [幺 β] {s : γ -> 集合 α} (f : α -> β)
  证明: by
  suffices forall j', j' != j -> {i} subseteq s j -> {i} subseteq s j' -> {i} subseteq mulSupport f -> False by by_contra; aesop
  intro j' h hj hj' hi
  simp only [Pairwise, Disjoint, Set.subset_inter_iff] at hs
  simpa using hs h ⟨hj', hi⟩ ⟨hj, hi⟩

Depends on / 依赖: Disjoint, Pairwise, Set.subset_inter_iff, mulSupport, subset_inter_iff, subseteq
-/
lemma mulSupport_subset_subsingleton_of_disjoint_on_mulSupport [One β] {s : γ -> Set α} (f : α -> β)
  (hs : Pairwise (Disjoint on (fun j => s j inter f.mulSupport))) (i : α) (j : γ) (hj : i in s j) :
    (fun d => (s d).mulIndicator f i).mulSupport subseteq {j} := by
  suffices forall j', j' != j -> {i} subseteq s j -> {i} subseteq s j' -> {i} subseteq mulSupport f -> False by by_contra; aesop
  intro j' h hj hj' hi
  simp only [Pairwise, Disjoint, Set.subset_inter_iff] at hs
  simpa using hs h ⟨hj', hi⟩ ⟨hj, hi⟩

end One

/-! ### Relationship with `Pi.mulSingle`/`Pi.single` -/

variable {ι : Type*} [DecidableEq ι] {M : Type*} [One M]

/-- On non-dependent functions, `Set.mulIndicator` on a singleton set equals `Pi.mulSingle`. -/
@[to_additive (attr := simp)
  /-- On non-dependent functions, `Set.indicator` on a singleton set equals `Pi.single`. -/]
/--
theorem `mulIndicator_singleton` / 定理 `mulIndicator_singleton`

English:
theorem mulIndicator_singleton
  given: (i : ι) (f : ι -> M)
  proof: by
  ext j
  simp only [Set.mulIndicator_apply, Pi.mulSingle_apply, Set.mem_singleton_iff]
  split_ifs with h <;> simp [h]

中文:
定理 mulIndicator_singleton
  条件: (i : ι) (f : ι -> M)
  证明: by
  ext j
  simp only [Set.mulIndicator_apply, Pi.mulSingle_apply, Set.mem_singleton_iff]
  split_ifs with h <;> simp [h]

Depends on / 依赖: Pi.mulSingle_apply, Set.mem_singleton_iff, Set.mulIndicator_apply, mem_singleton_iff, mulIndicator_apply, mulSingle_apply, split_ifs
-/
theorem mulIndicator_singleton (i : ι) (f : ι -> M) :
    Set.mulIndicator {i} f = Pi.mulSingle i (f i) := by
  ext j
  simp only [Set.mulIndicator_apply, Pi.mulSingle_apply, Set.mem_singleton_iff]
  split_ifs with h <;> simp [h]

end Set

@[to_additive]
/--
theorem `map_mulIndicator` / 定理 `map_mulIndicator`

English:
theorem map_mulIndicator
  statement: {M N F : Type*} [One M] [One N] [FunLike F M N] [OneHomClass F M N] (f : F)
  proof: by
  simp [Set.mulIndicator_comp_of_one]

中文:
定理 map_mulIndicator
  结论: {M N F : 类型} [幺 M] [幺 N] [函数状 F M N] [幺态射类 F M N] (f : F)
  证明: by
  simp [Set.mulIndicator_comp_of_one]

Depends on / 依赖: Set.mulIndicator_comp_of_one, mulIndicator_comp_of_one
-/
theorem map_mulIndicator {M N F : Type*} [One M] [One N] [FunLike F M N] [OneHomClass F M N] (f : F)
    (s : Set α) (g : α -> M) (x : α) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x := by
  simp [Set.mulIndicator_comp_of_one]
