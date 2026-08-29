/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Veblen hierarchy

We define the two-arguments Veblen function, which satisfies `veblen 0 a = ω ^ a` and that for
`o ≠ 0`, `veblen o` enumerates the common fixed points of `veblen o'` for `o' < o`.

We use this to define two important functions on ordinals: the epsilon function `ε_ o = veblen 1 o`,
and the gamma function `Γ_ o` enumerating the fixed points of `veblen · 0`.

## Main definitions

* `veblenWith`: The Veblen hierarchy with a specified initial function.
* `veblen`: The Veblen hierarchy starting with `ω ^ ·`.

## Notation

The following notation is scoped to the `Ordinal` namespace.

- `ε_ o` is notation for `veblen 1 o`. `ε₀` is notation for `ε_ 0`.
- `Γ_ o` is notation for `gamma o`. `Γ₀` is notation for `Γ_ 0`.

## TODO

- Prove that `ε₀` and `Γ₀` are countable.
- Prove that the ordinals principal under `veblen` are the gamma ordinals (and 0).

## References

* [Larry W. Miller, Normal functions and constructive ordinal notations][Miller_1976]
-/

@[expose] public section

noncomputable section

open Order Set

universe u

namespace Ordinal

variable {f : Ordinal.{u} -> Ordinal.{u}} {o o₁ o₂ a b x : Ordinal.{u}}

/-! ### Veblen function with a given starting function -/

section veblenWith

/-- `veblenWith f o` is the `o`-th function in the Veblen hierarchy starting with `f`. This is
defined so that

- `veblenWith f 0 = f`.
- `veblenWith f o` for `o ≠ 0` enumerates the common fixed points of `veblenWith f o'` over all
  `o' < o`.
-/
@[pp_nodot]
/--
Definition of `veblenWith` / `veblenWith` 的定义

English:
definition veblenWith
  signature: (f : Ordinal.{u} -> Ordinal.{u}) (o : Ordinal.{u})
  body: if o = 0 then f else derivFamily fun (⟨x, _⟩ : Iio o) => veblenWith f x
termination_by o

@[simp]

中文:
定义 veblenWith
  签名: (f : 序数.{u} -> 序数.{u}) (o : 序数.{u})
  定义体: if o = 0 then f else derivFamily fun (⟨x, _⟩ : Iio o) => veblenWith f x
termination_by o

@[simp]

Depends on / 依赖: derivFamily, termination_by, veblenWith
-/
def veblenWith (f : Ordinal.{u} -> Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} -> Ordinal.{u} :=
  if o = 0 then f else derivFamily fun (⟨x, _⟩ : Iio o) => veblenWith f x
termination_by o

@[simp]
/--
theorem `veblenWith_zero` / 定理 `veblenWith_zero`

English:
theorem veblenWith_zero
  given: (f : Ordinal -> Ordinal)
  statement: veblenWith f 0 = f
  proof: by
  rw [veblenWith]; rw [if_pos rfl]

中文:
定理 veblenWith_zero
  条件: (f : 序数 -> 序数)
  结论: veblenWith f 0 = f
  证明: by
  rw [veblenWith]; rw [if_pos rfl]

Depends on / 依赖: if_pos, veblenWith
-/
theorem veblenWith_zero (f : Ordinal -> Ordinal) : veblenWith f 0 = f := by
  rw [veblenWith]; rw [if_pos rfl]

/--
theorem `veblenWith_of_ne_zero` / 定理 `veblenWith_of_ne_zero`

English:
theorem veblenWith_of_ne_zero
  given: (f : Ordinal -> Ordinal) (h : o != 0)
  proof: by
  rw [veblenWith]; rw [if_neg h]

中文:
定理 veblenWith_of_ne_zero
  条件: (f : 序数 -> 序数) (h : o != 0)
  证明: by
  rw [veblenWith]; rw [if_neg h]

Depends on / 依赖: if_neg, veblenWith
-/
theorem veblenWith_of_ne_zero (f : Ordinal -> Ordinal) (h : o != 0) :
    veblenWith f o = derivFamily fun x : Iio o => veblenWith f x.1 := by
  rw [veblenWith]; rw [if_neg h]

/--
theorem `isNormal_veblenWith'` / 定理 `isNormal_veblenWith'`

English:
theorem isNormal_veblenWith'
  given: (f : Ordinal -> Ordinal) (h : o != 0)
  statement: IsNormal (veblenWith f o)
  proof: by
  rw [veblenWith_of_ne_zero f h]
  exact isNormal_derivFamily _

中文:
定理 isNormal_veblenWith'
  条件: (f : 序数 -> 序数) (h : o != 0)
  结论: 是正规 (veblenWith f o)
  证明: by
  rw [veblenWith_of_ne_zero f h]
  exact isNormal_derivFamily _

Depends on / 依赖: isNormal_derivFamily, veblenWith_of_ne_zero
-/
theorem isNormal_veblenWith' (f : Ordinal -> Ordinal) (h : o != 0) : IsNormal (veblenWith f o) := by
  rw [veblenWith_of_ne_zero f h]
  exact isNormal_derivFamily _

variable (hf : IsNormal f)
include hf

/--
theorem `isNormal_veblenWith` / 定理 `isNormal_veblenWith`

English:
theorem isNormal_veblenWith
  given: (o : Ordinal)
  statement: IsNormal (veblenWith f o)
  proof: by
  obtain rfl | h := eq_or_ne o 0
  · rwa [veblenWith_zero]
  · exact isNormal_veblenWith' f h

中文:
定理 isNormal_veblenWith
  条件: (o : 序数)
  结论: 是正规 (veblenWith f o)
  证明: by
  obtain rfl | h := eq_or_ne o 0
  · rwa [veblenWith_zero]
  · exact isNormal_veblenWith' f h

Depends on / 依赖: eq_or_ne, isNormal_veblenWith, veblenWith_zero
-/
theorem isNormal_veblenWith (o : Ordinal) : IsNormal (veblenWith f o) := by
  obtain rfl | h := eq_or_ne o 0
  · rwa [veblenWith_zero]
  · exact isNormal_veblenWith' f h

/--
theorem `mem_range_veblenWith` / 定理 `mem_range_veblenWith`

English:
theorem mem_range_veblenWith
  given: (h : o != 0)
  proof: by
  rw [veblenWith_of_ne_zero f h]; rw [mem_range_derivFamily (fun _ => isNormal_veblenWith hf _)]
  exact Subtype.forall

中文:
定理 mem_range_veblenWith
  条件: (h : o != 0)
  证明: by
  rw [veblenWith_of_ne_zero f h]; rw [mem_range_derivFamily (fun _ => isNormal_veblenWith hf _)]
  exact Subtype.forall

Depends on / 依赖: Subtype, Subtype.forall, isNormal_veblenWith, mem_range_derivFamily, veblenWith_of_ne_zero
-/
theorem mem_range_veblenWith (h : o != 0) :
    a in range (veblenWith f o) ↔ forall b < o, veblenWith f b a = a := by
  rw [veblenWith_of_ne_zero f h]; rw [mem_range_derivFamily (fun _ => isNormal_veblenWith hf _)]
  exact Subtype.forall

/--
theorem `veblenWith_veblenWith_of_lt` / 定理 `veblenWith_veblenWith_of_lt`

English:
theorem veblenWith_veblenWith_of_lt
  given: (h : o₁ < o₂) (a : Ordinal)
  proof: by
  apply (mem_range_veblenWith hf h.ne_bot).1 _ _ h
  simp

中文:
定理 veblenWith_veblenWith_of_lt
  条件: (h : o₁ < o₂) (a : 序数)
  证明: by
  apply (mem_range_veblenWith hf h.ne_bot).1 _ _ h
  simp

Depends on / 依赖: h.ne_bot, mem_range_veblenWith, ne_bot
-/
theorem veblenWith_veblenWith_of_lt (h : o₁ < o₂) (a : Ordinal) :
    veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a := by
  apply (mem_range_veblenWith hf h.ne_bot).1 _ _ h
  simp

/--
theorem `veblenWith_eq_self_of_le` / 定理 `veblenWith_eq_self_of_le`

English:
theorem veblenWith_eq_self_of_le
  given: (h : o₁ <= o₂) (h' : veblenWith f o₂ a = a)
  proof: by
  obtain rfl | h := h.eq_or_lt
  · assumption
  · rw [← h', veblenWith_veblenWith_of_lt hf h]

中文:
定理 veblenWith_eq_self_of_le
  条件: (h : o₁ <= o₂) (h' : veblenWith f o₂ a = a)
  证明: by
  obtain rfl | h := h.eq_or_lt
  · assumption
  · rw [← h', veblenWith_veblenWith_of_lt hf h]

Depends on / 依赖: eq_or_lt, h.eq_or_lt, veblenWith_veblenWith_of_lt
-/
theorem veblenWith_eq_self_of_le (h : o₁ <= o₂) (h' : veblenWith f o₂ a = a) :
    veblenWith f o₁ a = a := by
  obtain rfl | h := h.eq_or_lt
  · assumption
  · rw [← h', veblenWith_veblenWith_of_lt hf h]

/--
theorem `veblenWith_mem_range` / 定理 `veblenWith_mem_range`

English:
theorem veblenWith_mem_range
  statement: veblenWith f o a in range f
  proof: by
  obtain rfl | h := eq_zero_or_pos o
  · simp
  · rw [← veblenWith_veblenWith_of_lt hf h]
    simp

中文:
定理 veblenWith_mem_range
  结论: veblenWith f o a in range f
  证明: by
  obtain rfl | h := eq_zero_or_pos o
  · simp
  · rw [← veblenWith_veblenWith_of_lt hf h]
    simp

Depends on / 依赖: eq_zero_or_pos, veblenWith_veblenWith_of_lt
-/
theorem veblenWith_mem_range : veblenWith f o a in range f := by
  obtain rfl | h := eq_zero_or_pos o
  · simp
  · rw [← veblenWith_veblenWith_of_lt hf h]
    simp

/--
theorem `veblenWith_add_one` / 定理 `veblenWith_add_one`

English:
theorem veblenWith_add_one
  given: (o : Ordinal)
  statement: veblenWith f (o + 1) = deriv (veblenWith f o)
  proof: by
  rw [deriv_eq_enumOrd (isNormal_veblenWith hf o)]; rw [veblenWith_of_ne_zero f (add_pos_of_right zero_lt_one _).ne']; rw [derivFamily_eq_enumOrd]
  · apply congr_arg
    ext a
    rw [mem_iInter]
    use fun ha => ha ⟨o, lt_succ o⟩
    rintro (ha : _ = _) ⟨b, hb : b < _⟩
    obtain rfl | hb := lt_succ_iff_eq_or_lt.1 hb
    · rw [Function.mem_fixedPoints_iff, ha]
    · rw [← ha]
      exact veblenWith_veblenWith_of_lt hf hb _
  · exact fun o => isNormal_veblenWith hf o.1

@[simp]

中文:
定理 veblenWith_add_one
  条件: (o : 序数)
  结论: veblenWith f (o + 1) = deriv (veblenWith f o)
  证明: by
  rw [deriv_eq_enumOrd (isNormal_veblenWith hf o)]; rw [veblenWith_of_ne_zero f (add_pos_of_right zero_lt_one _).ne']; rw [derivFamily_eq_enumOrd]
  · apply congr_arg
    ext a
    rw [mem_iInter]
    use fun ha => ha ⟨o, lt_succ o⟩
    rintro (ha : _ = _) ⟨b, hb : b < _⟩
    obtain rfl | hb := lt_succ_iff_eq_or_lt.1 hb
    · rw [Function.mem_fixedPoints_iff, ha]
    · rw [← ha]
      exact veblenWith_veblenWith_of_lt hf hb _
  · exact fun o => isNormal_veblenWith hf o.1

@[simp]

Depends on / 依赖: Function, Function.mem_fixedPoints_iff, add_pos_of_right, congr_arg, derivFamily_eq_enumOrd, deriv_eq_enumOrd, isNormal_veblenWith, lt_succ, lt_succ_iff_eq_or_lt, mem_fixedPoints_iff, mem_iInter, veblenWith_of_ne_zero, veblenWith_veblenWith_of_lt, zero_lt_one
-/
theorem veblenWith_add_one (o : Ordinal) : veblenWith f (o + 1) = deriv (veblenWith f o) := by
  rw [deriv_eq_enumOrd (isNormal_veblenWith hf o)]; rw [veblenWith_of_ne_zero f (add_pos_of_right zero_lt_one _).ne']; rw [derivFamily_eq_enumOrd]
  · apply congr_arg
    ext a
    rw [mem_iInter]
    use fun ha => ha ⟨o, lt_succ o⟩
    rintro (ha : _ = _) ⟨b, hb : b < _⟩
    obtain rfl | hb := lt_succ_iff_eq_or_lt.1 hb
    · rw [Function.mem_fixedPoints_iff, ha]
    · rw [← ha]
      exact veblenWith_veblenWith_of_lt hf hb _
  · exact fun o => isNormal_veblenWith hf o.1

@[simp]
/--
theorem `veblenWith_one` / 定理 `veblenWith_one`

English:
theorem veblenWith_one
  statement: veblenWith f 1 = deriv f
  proof: by
  simpa using veblenWith_add_one hf 0

@[deprecated veblenWith_add_one (since := "2026-02-26")]

中文:
定理 veblenWith_one
  结论: veblenWith f 1 = deriv f
  证明: by
  simpa using veblenWith_add_one hf 0

@[deprecated veblenWith_add_one (since := "2026-02-26")]

Depends on / 依赖: veblenWith_add_one
-/
theorem veblenWith_one : veblenWith f 1 = deriv f := by
  simpa using veblenWith_add_one hf 0

@[deprecated veblenWith_add_one (since := "2026-02-26")]
/--
theorem `veblenWith_succ` / 定理 `veblenWith_succ`

English:
theorem veblenWith_succ
  given: (o : Ordinal)
  statement: veblenWith f (succ o) = deriv (veblenWith f o)
  proof: veblenWith_add_one hf o

中文:
定理 veblenWith_succ
  条件: (o : 序数)
  结论: veblenWith f (succ o) = deriv (veblenWith f o)
  证明: veblenWith_add_one hf o

Depends on / 依赖: veblenWith_add_one
-/
theorem veblenWith_succ (o : Ordinal) : veblenWith f (succ o) = deriv (veblenWith f o) :=
  veblenWith_add_one hf o

/--
theorem `veblenWith_right_strictMono` / 定理 `veblenWith_right_strictMono`

English:
theorem veblenWith_right_strictMono
  given: (o : Ordinal)
  statement: StrictMono (veblenWith f o)
  proof: (isNormal_veblenWith hf o).strictMono

@[simp]

中文:
定理 veblenWith_right_strictMono
  条件: (o : 序数)
  结论: 严格递增 (veblenWith f o)
  证明: (isNormal_veblenWith hf o).strictMono

@[simp]

Depends on / 依赖: isNormal_veblenWith, strictMono
-/
theorem veblenWith_right_strictMono (o : Ordinal) : StrictMono (veblenWith f o) :=
  (isNormal_veblenWith hf o).strictMono

@[simp]
/--
theorem `veblenWith_lt_veblenWith_iff_right` / 定理 `veblenWith_lt_veblenWith_iff_right`

English:
theorem veblenWith_lt_veblenWith_iff_right
  statement: veblenWith f o a < veblenWith f o b ↔ a < b
  proof: (veblenWith_right_strictMono hf o).lt_iff_lt

@[simp]

中文:
定理 veblenWith_lt_veblenWith_iff_right
  结论: veblenWith f o a < veblenWith f o b ↔ a < b
  证明: (veblenWith_right_strictMono hf o).lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, veblenWith_right_strictMono
-/
theorem veblenWith_lt_veblenWith_iff_right : veblenWith f o a < veblenWith f o b ↔ a < b :=
  (veblenWith_right_strictMono hf o).lt_iff_lt

@[simp]
/--
theorem `veblenWith_le_veblenWith_iff_right` / 定理 `veblenWith_le_veblenWith_iff_right`

English:
theorem veblenWith_le_veblenWith_iff_right
  statement: veblenWith f o a <= veblenWith f o b ↔ a <= b
  proof: (veblenWith_right_strictMono hf o).le_iff_le

中文:
定理 veblenWith_le_veblenWith_iff_right
  结论: veblenWith f o a <= veblenWith f o b ↔ a <= b
  证明: (veblenWith_right_strictMono hf o).le_iff_le

Depends on / 依赖: le_iff_le, veblenWith_right_strictMono
-/
theorem veblenWith_le_veblenWith_iff_right : veblenWith f o a <= veblenWith f o b ↔ a <= b :=
  (veblenWith_right_strictMono hf o).le_iff_le

/--
theorem `veblenWith_injective` / 定理 `veblenWith_injective`

English:
theorem veblenWith_injective
  given: (o : Ordinal)
  statement: Function.Injective (veblenWith f o)
  proof: (veblenWith_right_strictMono hf o).injective

@[simp]

中文:
定理 veblenWith_injective
  条件: (o : 序数)
  结论: 函数.单射 (veblenWith f o)
  证明: (veblenWith_right_strictMono hf o).injective

@[simp]

Depends on / 依赖: injective, veblenWith_right_strictMono
-/
theorem veblenWith_injective (o : Ordinal) : Function.Injective (veblenWith f o) :=
  (veblenWith_right_strictMono hf o).injective

@[simp]
/--
theorem `veblenWith_inj` / 定理 `veblenWith_inj`

English:
theorem veblenWith_inj
  statement: veblenWith f o a = veblenWith f o b ↔ a = b
  proof: (veblenWith_injective hf o).eq_iff

中文:
定理 veblenWith_inj
  结论: veblenWith f o a = veblenWith f o b ↔ a = b
  证明: (veblenWith_injective hf o).eq_iff

Depends on / 依赖: eq_iff, veblenWith_injective
-/
theorem veblenWith_inj : veblenWith f o a = veblenWith f o b ↔ a = b :=
  (veblenWith_injective hf o).eq_iff

/--
theorem `right_le_veblenWith` / 定理 `right_le_veblenWith`

English:
theorem right_le_veblenWith
  given: (o a : Ordinal)
  statement: a <= veblenWith f o a
  proof: (veblenWith_right_strictMono hf o).le_apply

中文:
定理 right_le_veblenWith
  条件: (o a : 序数)
  结论: a <= veblenWith f o a
  证明: (veblenWith_right_strictMono hf o).le_apply

Depends on / 依赖: le_apply, veblenWith_right_strictMono
-/
theorem right_le_veblenWith (o a : Ordinal) : a <= veblenWith f o a :=
  (veblenWith_right_strictMono hf o).le_apply

/--
theorem `veblenWith_left_monotone` / 定理 `veblenWith_left_monotone`

English:
theorem veblenWith_left_monotone
  given: (a : Ordinal)
  statement: Monotone (veblenWith f · a)
  proof: by
  rw [monotone_iff_forall_lt]
  intro o₁ o₂ h
  rw [← veblenWith_veblenWith_of_lt hf h]
  exact (veblenWith_right_strictMono hf o₁).monotone (right_le_veblenWith hf o₂ a)

中文:
定理 veblenWith_left_monotone
  条件: (a : 序数)
  结论: 递增 (veblenWith f · a)
  证明: by
  rw [monotone_iff_forall_lt]
  intro o₁ o₂ h
  rw [← veblenWith_veblenWith_of_lt hf h]
  exact (veblenWith_right_strictMono hf o₁).monotone (right_le_veblenWith hf o₂ a)

Depends on / 依赖: monotone, monotone_iff_forall_lt, right_le_veblenWith, veblenWith_right_strictMono, veblenWith_veblenWith_of_lt
-/
theorem veblenWith_left_monotone (a : Ordinal) : Monotone (veblenWith f · a) := by
  rw [monotone_iff_forall_lt]
  intro o₁ o₂ h
  rw [← veblenWith_veblenWith_of_lt hf h]
  exact (veblenWith_right_strictMono hf o₁).monotone (right_le_veblenWith hf o₂ a)

/--
theorem `veblenWith_pos` / 定理 `veblenWith_pos`

English:
theorem veblenWith_pos
  given: (hp : 0 < f 0)
  statement: 0 < veblenWith f o a
  proof: by
  have H (b) : 0 < veblenWith f 0 b := by
    rw [veblenWith_zero]
    exact hp.trans_le (hf.monotone zero_le)
  obtain rfl | h := eq_zero_or_pos o
  · exact H a
  · rw [← veblenWith_veblenWith_of_lt hf h]
    exact H _

中文:
定理 veblenWith_pos
  条件: (hp : 0 < f 0)
  结论: 0 < veblenWith f o a
  证明: by
  have H (b) : 0 < veblenWith f 0 b := by
    rw [veblenWith_zero]
    exact hp.trans_le (hf.monotone zero_le)
  obtain rfl | h := eq_zero_or_pos o
  · exact H a
  · rw [← veblenWith_veblenWith_of_lt hf h]
    exact H _

Depends on / 依赖: eq_zero_or_pos, hf.monotone, hp.trans_le, monotone, trans_le, veblenWith, veblenWith_veblenWith_of_lt, veblenWith_zero, zero_le
-/
theorem veblenWith_pos (hp : 0 < f 0) : 0 < veblenWith f o a := by
  have H (b) : 0 < veblenWith f 0 b := by
    rw [veblenWith_zero]
    exact hp.trans_le (hf.monotone zero_le)
  obtain rfl | h := eq_zero_or_pos o
  · exact H a
  · rw [← veblenWith_veblenWith_of_lt hf h]
    exact H _

/--
theorem `veblenWith_zero_strictMono` / 定理 `veblenWith_zero_strictMono`

English:
theorem veblenWith_zero_strictMono
  given: (hp : 0 < f 0)
  statement: StrictMono (veblenWith f · 0)
  proof: by
  intro o₁ o₂ h
  dsimp only
  rw [← veblenWith_veblenWith_of_lt hf h]; rw [veblenWith_lt_veblenWith_iff_right hf]
  exact veblenWith_pos hf hp

中文:
定理 veblenWith_zero_strictMono
  条件: (hp : 0 < f 0)
  结论: 严格递增 (veblenWith f · 0)
  证明: by
  intro o₁ o₂ h
  dsimp only
  rw [← veblenWith_veblenWith_of_lt hf h]; rw [veblenWith_lt_veblenWith_iff_right hf]
  exact veblenWith_pos hf hp

Depends on / 依赖: veblenWith_lt_veblenWith_iff_right, veblenWith_pos, veblenWith_veblenWith_of_lt
-/
theorem veblenWith_zero_strictMono (hp : 0 < f 0) : StrictMono (veblenWith f · 0) := by
  intro o₁ o₂ h
  dsimp only
  rw [← veblenWith_veblenWith_of_lt hf h]; rw [veblenWith_lt_veblenWith_iff_right hf]
  exact veblenWith_pos hf hp

/--
theorem `veblenWith_zero_lt_veblenWith_zero` / 定理 `veblenWith_zero_lt_veblenWith_zero`

English:
theorem veblenWith_zero_lt_veblenWith_zero
  given: (hp : 0 < f 0)
  proof: (veblenWith_zero_strictMono hf hp).lt_iff_lt

中文:
定理 veblenWith_zero_lt_veblenWith_zero
  条件: (hp : 0 < f 0)
  证明: (veblenWith_zero_strictMono hf hp).lt_iff_lt

Depends on / 依赖: lt_iff_lt, veblenWith_zero_strictMono
-/
theorem veblenWith_zero_lt_veblenWith_zero (hp : 0 < f 0) :
    veblenWith f o₁ 0 < veblenWith f o₂ 0 ↔ o₁ < o₂ :=
  (veblenWith_zero_strictMono hf hp).lt_iff_lt

/--
theorem `veblenWith_zero_le_veblenWith_zero` / 定理 `veblenWith_zero_le_veblenWith_zero`

English:
theorem veblenWith_zero_le_veblenWith_zero
  given: (hp : 0 < f 0)
  proof: (veblenWith_zero_strictMono hf hp).le_iff_le

中文:
定理 veblenWith_zero_le_veblenWith_zero
  条件: (hp : 0 < f 0)
  证明: (veblenWith_zero_strictMono hf hp).le_iff_le

Depends on / 依赖: le_iff_le, veblenWith_zero_strictMono
-/
theorem veblenWith_zero_le_veblenWith_zero (hp : 0 < f 0) :
    veblenWith f o₁ 0 <= veblenWith f o₂ 0 ↔ o₁ <= o₂ :=
  (veblenWith_zero_strictMono hf hp).le_iff_le

/--
theorem `veblenWith_zero_inj` / 定理 `veblenWith_zero_inj`

English:
theorem veblenWith_zero_inj
  given: (hp : 0 < f 0)
  statement: veblenWith f o₁ 0 = veblenWith f o₂ 0 ↔ o₁ = o₂
  proof: (veblenWith_zero_strictMono hf hp).injective.eq_iff

中文:
定理 veblenWith_zero_inj
  条件: (hp : 0 < f 0)
  结论: veblenWith f o₁ 0 = veblenWith f o₂ 0 ↔ o₁ = o₂
  证明: (veblenWith_zero_strictMono hf hp).injective.eq_iff

Depends on / 依赖: eq_iff, injective, injective.eq_iff, veblenWith_zero_strictMono
-/
theorem veblenWith_zero_inj (hp : 0 < f 0) : veblenWith f o₁ 0 = veblenWith f o₂ 0 ↔ o₁ = o₂ :=
  (veblenWith_zero_strictMono hf hp).injective.eq_iff

/--
theorem `left_le_veblenWith` / 定理 `left_le_veblenWith`

English:
theorem left_le_veblenWith
  given: (hp : 0 < f 0) (o a : Ordinal)
  statement: o <= veblenWith f o a
  proof: (veblenWith_zero_strictMono hf hp).le_apply.trans
    (veblenWith_right_strictMono hf _).monotone zero_le

中文:
定理 left_le_veblenWith
  条件: (hp : 0 < f 0) (o a : 序数)
  结论: o <= veblenWith f o a
  证明: (veblenWith_zero_strictMono hf hp).le_apply.trans
    (veblenWith_right_strictMono hf _).monotone zero_le

Depends on / 依赖: le_apply, le_apply.trans, monotone, veblenWith_right_strictMono, veblenWith_zero_strictMono, zero_le
-/
theorem left_le_veblenWith (hp : 0 < f 0) (o a : Ordinal) : o <= veblenWith f o a :=
(veblenWith_zero_strictMono hf hp).le_apply.trans
    (veblenWith_right_strictMono hf _).monotone zero_le

/--
theorem `isNormal_veblenWith_zero` / 定理 `isNormal_veblenWith_zero`

English:
theorem isNormal_veblenWith_zero
  given: (hp : 0 < f 0)
  statement: IsNormal (veblenWith f · 0)
  proof: by
  rw [isNormal_iff]
  refine ⟨veblenWith_zero_strictMono hf hp, fun o ho a IH => ?_⟩
  rw [veblenWith_of_ne_zero f ho.ne_bot]; rw [derivFamily_zero]
  apply nfpFamily_le fun l => ?_
  suffices exists b < o, List.foldr _ 0 l <= veblenWith f b 0 by
    obtain ⟨b, hb, hb'⟩ := this
    exact hb'.trans (IH b hb)
  induction l with
  | nil => use 0; simpa using ho.bot_lt
  | cons a l IH =>
    obtain ⟨b, hb, hb'⟩ := IH
    refine ⟨_, ho.succ_lt (max_lt a.2 hb), ((veblenWith_right_strictMono hf _).monotone <|
hb'.trans veblenWith_left_monotone hf _
        (le_max_right a.1 b).trans (le_succ _)).trans ?_⟩
    rw [veblenWith_veblenWith_of_lt hf]
    rw [lt_succ_iff]
    exact le_max_left _ b

中文:
定理 isNormal_veblenWith_zero
  条件: (hp : 0 < f 0)
  结论: 是正规 (veblenWith f · 0)
  证明: by
  rw [isNormal_iff]
  refine ⟨veblenWith_zero_strictMono hf hp, fun o ho a IH => ?_⟩
  rw [veblenWith_of_ne_zero f ho.ne_bot]; rw [derivFamily_zero]
  apply nfpFamily_le fun l => ?_
  suffices exists b < o, List.foldr _ 0 l <= veblenWith f b 0 by
    obtain ⟨b, hb, hb'⟩ := this
    exact hb'.trans (IH b hb)
  induction l with
  | nil => use 0; simpa using ho.bot_lt
  | cons a l IH =>
    obtain ⟨b, hb, hb'⟩ := IH
    refine ⟨_, ho.succ_lt (max_lt a.2 hb), ((veblenWith_right_strictMono hf _).monotone <|
hb'.trans veblenWith_left_monotone hf _
        (le_max_right a.1 b).trans (le_succ _)).trans ?_⟩
    rw [veblenWith_veblenWith_of_lt hf]
    rw [lt_succ_iff]
    exact le_max_left _ b

Depends on / 依赖: List.foldr, bot_lt, derivFamily_zero, ho.bot_lt, ho.ne_bot, ho.succ_lt, isNormal_iff, max_lt, monotone, ne_bot, nfpFamily_le, succ_lt, veblenWith, veblenWith_, veblenWith_of_ne_zero, veblenWith_right_strictMono, veblenWith_zero_strictMono
-/
theorem isNormal_veblenWith_zero (hp : 0 < f 0) : IsNormal (veblenWith f · 0) := by
  rw [isNormal_iff]
  refine ⟨veblenWith_zero_strictMono hf hp, fun o ho a IH => ?_⟩
  rw [veblenWith_of_ne_zero f ho.ne_bot]; rw [derivFamily_zero]
  apply nfpFamily_le fun l => ?_
  suffices exists b < o, List.foldr _ 0 l <= veblenWith f b 0 by
    obtain ⟨b, hb, hb'⟩ := this
    exact hb'.trans (IH b hb)
  induction l with
  | nil => use 0; simpa using ho.bot_lt
  | cons a l IH =>
    obtain ⟨b, hb, hb'⟩ := IH
    refine ⟨_, ho.succ_lt (max_lt a.2 hb), ((veblenWith_right_strictMono hf _).monotone <|
hb'.trans veblenWith_left_monotone hf _
        (le_max_right a.1 b).trans (le_succ _)).trans ?_⟩
    rw [veblenWith_veblenWith_of_lt hf]
    rw [lt_succ_iff]
    exact le_max_left _ b

/--
theorem `veblenWith_veblenWith_eq_veblenWith_iff` / 定理 `veblenWith_veblenWith_eq_veblenWith_iff`

English:
theorem veblenWith_veblenWith_eq_veblenWith_iff
  given: (h : o₂ <= o₁)
  proof: by
  grind [veblenWith_inj, -> veblenWith_eq_self_of_le]

中文:
定理 veblenWith_veblenWith_eq_veblenWith_iff
  条件: (h : o₂ <= o₁)
  证明: by
  grind [veblenWith_inj, -> veblenWith_eq_self_of_le]

Depends on / 依赖: veblenWith_eq_self_of_le, veblenWith_inj
-/
theorem veblenWith_veblenWith_eq_veblenWith_iff (h : o₂ <= o₁) :
    veblenWith f o₁ (veblenWith f o₂ a) = veblenWith f o₂ a ↔ veblenWith f o₁ a = a := by
  grind [veblenWith_inj, -> veblenWith_eq_self_of_le]

/--
theorem `veblenWith_lt_veblenWith_veblenWith_iff` / 定理 `veblenWith_lt_veblenWith_veblenWith_iff`

English:
theorem veblenWith_lt_veblenWith_veblenWith_iff
  given: (h : o₂ <= o₁)
  proof: by
  simp_rw [(right_le_veblenWith hf ..).lt_iff_ne', ne_eq,
    veblenWith_veblenWith_eq_veblenWith_iff hf h]

中文:
定理 veblenWith_lt_veblenWith_veblenWith_iff
  条件: (h : o₂ <= o₁)
  证明: by
  simp_rw [(right_le_veblenWith hf ..).lt_iff_ne', ne_eq,
    veblenWith_veblenWith_eq_veblenWith_iff hf h]

Depends on / 依赖: lt_iff_ne, ne_eq, right_le_veblenWith, simp_rw, veblenWith_veblenWith_eq_veblenWith_iff
-/
theorem veblenWith_lt_veblenWith_veblenWith_iff (h : o₂ <= o₁) :
    veblenWith f o₂ a < veblenWith f o₁ (veblenWith f o₂ a) ↔ a < veblenWith f o₁ a := by
  simp_rw [(right_le_veblenWith hf ..).lt_iff_ne', ne_eq,
    veblenWith_veblenWith_eq_veblenWith_iff hf h]

/--
theorem `veblenWith_apply_eq_apply_iff` / 定理 `veblenWith_apply_eq_apply_iff`

English:
theorem veblenWith_apply_eq_apply_iff
  statement: veblenWith f o (f a) = f a ↔ veblenWith f o a = a
  proof: by
  simpa using veblenWith_veblenWith_eq_veblenWith_iff hf zero_le

中文:
定理 veblenWith_apply_eq_apply_iff
  结论: veblenWith f o (f a) = f a ↔ veblenWith f o a = a
  证明: by
  simpa using veblenWith_veblenWith_eq_veblenWith_iff hf zero_le

Depends on / 依赖: veblenWith_veblenWith_eq_veblenWith_iff, zero_le
-/
theorem veblenWith_apply_eq_apply_iff : veblenWith f o (f a) = f a ↔ veblenWith f o a = a := by
  simpa using veblenWith_veblenWith_eq_veblenWith_iff hf zero_le

/--
theorem `apply_lt_veblenWith_apply_iff` / 定理 `apply_lt_veblenWith_apply_iff`

English:
theorem apply_lt_veblenWith_apply_iff
  statement: f a < veblenWith f o (f a) ↔ a < veblenWith f o a
  proof: by
  simpa using veblenWith_lt_veblenWith_veblenWith_iff hf zero_le

中文:
定理 apply_lt_veblenWith_apply_iff
  结论: f a < veblenWith f o (f a) ↔ a < veblenWith f o a
  证明: by
  simpa using veblenWith_lt_veblenWith_veblenWith_iff hf zero_le

Depends on / 依赖: veblenWith_lt_veblenWith_veblenWith_iff, zero_le
-/
theorem apply_lt_veblenWith_apply_iff : f a < veblenWith f o (f a) ↔ a < veblenWith f o a := by
  simpa using veblenWith_lt_veblenWith_veblenWith_iff hf zero_le

/--
theorem `cmp_veblenWith` / 定理 `cmp_veblenWith`

English:
theorem cmp_veblenWith
  proof: by
  obtain h | rfl | h := lt_trichotomy o₁ o₂
  on_goal 2 => simp [(veblenWith_right_strictMono hf _).cmp_map_eq]
  all_goals
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h]
    simp [h.cmp_eq_lt, h.cmp_eq_gt, (veblenWith_right_strictMono hf _).cmp_map_eq]

中文:
定理 cmp_veblenWith
  证明: by
  obtain h | rfl | h := lt_trichotomy o₁ o₂
  on_goal 2 => simp [(veblenWith_right_strictMono hf _).cmp_map_eq]
  all_goals
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h]
    simp [h.cmp_eq_lt, h.cmp_eq_gt, (veblenWith_right_strictMono hf _).cmp_map_eq]

Depends on / 依赖: all_goals, cmp_eq_gt, cmp_eq_lt, cmp_map_eq, conv_lhs, h.cmp_eq_gt, h.cmp_eq_lt, lt_trichotomy, on_goal, veblenWith_right_strictMono, veblenWith_veblenWith_of_lt
-/
theorem cmp_veblenWith :
    cmp (veblenWith f o₁ a) (veblenWith f o₂ b) =
    match cmp o₁ o₂ with
    | .eq => cmp a b
    | .lt => cmp a (veblenWith f o₂ b)
    | .gt => cmp (veblenWith f o₁ a) b := by
  obtain h | rfl | h := lt_trichotomy o₁ o₂
  on_goal 2 => simp [(veblenWith_right_strictMono hf _).cmp_map_eq]
  all_goals
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h]
    simp [h.cmp_eq_lt, h.cmp_eq_gt, (veblenWith_right_strictMono hf _).cmp_map_eq]

/--
theorem `veblenWith_lt_veblenWith_iff` / 定理 `veblenWith_lt_veblenWith_iff`

English:
theorem veblenWith_lt_veblenWith_iff
  proof: by
  rw [← cmp_eq_lt_iff]; rw [cmp_veblenWith hf]
  aesop (add simp lt_asymm)

中文:
定理 veblenWith_lt_veblenWith_iff
  证明: by
  rw [← cmp_eq_lt_iff]; rw [cmp_veblenWith hf]
  aesop (add simp lt_asymm)

Depends on / 依赖: cmp_eq_lt_iff, cmp_veblenWith, lt_asymm
-/
theorem veblenWith_lt_veblenWith_iff :
    veblenWith f o₁ a < veblenWith f o₂ b ↔
      o₁ = o₂ ∧ a < b ∨ o₁ < o₂ ∧ a < veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a < b := by
  rw [← cmp_eq_lt_iff]; rw [cmp_veblenWith hf]
  aesop (add simp lt_asymm)

/--
theorem `veblenWith_le_veblenWith_iff` / 定理 `veblenWith_le_veblenWith_iff`

English:
theorem veblenWith_le_veblenWith_iff
  proof: by
  rw [← not_lt]; rw [← cmp_eq_gt_iff]; rw [cmp_veblenWith hf]
  aesop (add simp [not_lt_of_ge, lt_asymm])

中文:
定理 veblenWith_le_veblenWith_iff
  证明: by
  rw [← not_lt]; rw [← cmp_eq_gt_iff]; rw [cmp_veblenWith hf]
  aesop (add simp [not_lt_of_ge, lt_asymm])

Depends on / 依赖: cmp_eq_gt_iff, cmp_veblenWith, lt_asymm, not_lt, not_lt_of_ge
-/
theorem veblenWith_le_veblenWith_iff :
    veblenWith f o₁ a <= veblenWith f o₂ b ↔
      o₁ = o₂ ∧ a <= b ∨ o₁ < o₂ ∧ a <= veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a <= b := by
  rw [← not_lt]; rw [← cmp_eq_gt_iff]; rw [cmp_veblenWith hf]
  aesop (add simp [not_lt_of_ge, lt_asymm])

/--
theorem `veblenWith_eq_veblenWith_iff` / 定理 `veblenWith_eq_veblenWith_iff`

English:
theorem veblenWith_eq_veblenWith_iff
  proof: by
  rw [← cmp_eq_eq_iff]; rw [cmp_veblenWith hf]
  aesop (add simp lt_asymm)

中文:
定理 veblenWith_eq_veblenWith_iff
  证明: by
  rw [← cmp_eq_eq_iff]; rw [cmp_veblenWith hf]
  aesop (add simp lt_asymm)

Depends on / 依赖: cmp_eq_eq_iff, cmp_veblenWith, lt_asymm
-/
theorem veblenWith_eq_veblenWith_iff :
    veblenWith f o₁ a = veblenWith f o₂ b ↔
      o₁ = o₂ ∧ a = b ∨ o₁ < o₂ ∧ a = veblenWith f o₂ b ∨ o₂ < o₁ ∧ veblenWith f o₁ a = b := by
  rw [← cmp_eq_eq_iff]; rw [cmp_veblenWith hf]
  aesop (add simp lt_asymm)

end veblenWith

/-! ### Veblen function -/

section veblen

/-- `veblen o` is the `o`-th function in the Veblen hierarchy starting with `ω ^ ·`. That is:

- `veblen 0 a = ω ^ a`.
- `veblen o` for `o ≠ 0` enumerates the fixed points of `veblen o'` for `o' < o`.
-/
@[pp_nodot]
/--
Definition of `veblen` / `veblen` 的定义

English:
definition veblen
  signature: : Ordinal.{u} -> Ordinal.{u} -> Ordinal.{u}
  body: veblenWith (ω ^ ·)

@[simp]

中文:
定义 veblen
  签名: : 序数.{u} -> 序数.{u} -> 序数.{u}
  定义体: veblenWith (ω ^ ·)

@[simp]

Depends on / 依赖: veblenWith
-/
def veblen : Ordinal.{u} -> Ordinal.{u} -> Ordinal.{u} :=
  veblenWith (ω ^ ·)

@[simp]
/--
theorem `veblen_zero` / 定理 `veblen_zero`

English:
theorem veblen_zero
  statement: veblen 0 = fun a => ω ^ a
  proof: by
  rw [veblen]; rw [veblenWith_zero]

中文:
定理 veblen_zero
  结论: veblen 0 = fun a => ω ^ a
  证明: by
  rw [veblen]; rw [veblenWith_zero]

Depends on / 依赖: veblen, veblenWith_zero
-/
theorem veblen_zero : veblen 0 = fun a => ω ^ a := by
  rw [veblen]; rw [veblenWith_zero]

/--
theorem `veblen_zero_apply` / 定理 `veblen_zero_apply`

English:
theorem veblen_zero_apply
  given: (a : Ordinal)
  statement: veblen 0 a = ω ^ a
  proof: by
  rw [veblen_zero]

中文:
定理 veblen_zero_apply
  条件: (a : 序数)
  结论: veblen 0 a = ω ^ a
  证明: by
  rw [veblen_zero]

Depends on / 依赖: veblen_zero
-/
theorem veblen_zero_apply (a : Ordinal) : veblen 0 a = ω ^ a := by
  rw [veblen_zero]

/--
theorem `veblen_of_ne_zero` / 定理 `veblen_of_ne_zero`

English:
theorem veblen_of_ne_zero
  given: (h : o != 0)
  statement: veblen o = derivFamily fun x : Iio o => veblen x.1
  proof: veblenWith_of_ne_zero _ h

中文:
定理 veblen_of_ne_zero
  条件: (h : o != 0)
  结论: veblen o = derivFamily fun x : 左无界右开区间 o => veblen x.1
  证明: veblenWith_of_ne_zero _ h

Depends on / 依赖: veblenWith_of_ne_zero
-/
theorem veblen_of_ne_zero (h : o != 0) : veblen o = derivFamily fun x : Iio o => veblen x.1 :=
  veblenWith_of_ne_zero _ h

/--
theorem `isNormal_veblen` / 定理 `isNormal_veblen`

English:
theorem isNormal_veblen
  given: (o : Ordinal)
  statement: IsNormal (veblen o)
  proof: isNormal_veblenWith (isNormal_opow one_lt_omega0) o

中文:
定理 isNormal_veblen
  条件: (o : 序数)
  结论: 是正规 (veblen o)
  证明: isNormal_veblenWith (isNormal_opow one_lt_omega0) o

Depends on / 依赖: isNormal_opow, isNormal_veblenWith, one_lt_omega0
-/
theorem isNormal_veblen (o : Ordinal) : IsNormal (veblen o) :=
  isNormal_veblenWith (isNormal_opow one_lt_omega0) o

/--
theorem `mem_range_veblen` / 定理 `mem_range_veblen`

English:
theorem mem_range_veblen
  given: (h : o != 0)
  statement: a in range (veblen o) ↔ forall b < o, veblen b a = a
  proof: mem_range_veblenWith (isNormal_opow one_lt_omega0) h

中文:
定理 mem_range_veblen
  条件: (h : o != 0)
  结论: a in range (veblen o) ↔ 对任意 b < o, veblen b a = a
  证明: mem_range_veblenWith (isNormal_opow one_lt_omega0) h

Depends on / 依赖: isNormal_opow, mem_range_veblenWith, one_lt_omega0
-/
theorem mem_range_veblen (h : o != 0) : a in range (veblen o) ↔ forall b < o, veblen b a = a :=
  mem_range_veblenWith (isNormal_opow one_lt_omega0) h

/--
theorem `veblen_veblen_of_lt` / 定理 `veblen_veblen_of_lt`

English:
theorem veblen_veblen_of_lt
  given: (h : o₁ < o₂) (a : Ordinal)
  statement: veblen o₁ (veblen o₂ a) = veblen o₂ a
  proof: veblenWith_veblenWith_of_lt (isNormal_opow one_lt_omega0) h a

中文:
定理 veblen_veblen_of_lt
  条件: (h : o₁ < o₂) (a : 序数)
  结论: veblen o₁ (veblen o₂ a) = veblen o₂ a
  证明: veblenWith_veblenWith_of_lt (isNormal_opow one_lt_omega0) h a

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_veblenWith_of_lt
-/
theorem veblen_veblen_of_lt (h : o₁ < o₂) (a : Ordinal) : veblen o₁ (veblen o₂ a) = veblen o₂ a :=
  veblenWith_veblenWith_of_lt (isNormal_opow one_lt_omega0) h a

/--
theorem `veblen_eq_self_of_le` / 定理 `veblen_eq_self_of_le`

English:
theorem veblen_eq_self_of_le
  given: (h : o₁ <= o₂) (h' : veblen o₂ a = a)
  statement: veblen o₁ a = a
  proof: veblenWith_eq_self_of_le (isNormal_opow one_lt_omega0) h h'

中文:
定理 veblen_eq_self_of_le
  条件: (h : o₁ <= o₂) (h' : veblen o₂ a = a)
  结论: veblen o₁ a = a
  证明: veblenWith_eq_self_of_le (isNormal_opow one_lt_omega0) h h'

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_eq_self_of_le
-/
theorem veblen_eq_self_of_le (h : o₁ <= o₂) (h' : veblen o₂ a = a) : veblen o₁ a = a :=
  veblenWith_eq_self_of_le (isNormal_opow one_lt_omega0) h h'

/--
theorem `veblen_mem_range_opow` / 定理 `veblen_mem_range_opow`

English:
theorem veblen_mem_range_opow
  given: (o a : Ordinal)
  statement: veblen o a in range (ω ^ · : Ordinal -> Ordinal)
  proof: veblenWith_mem_range (isNormal_opow one_lt_omega0)

中文:
定理 veblen_mem_range_opow
  条件: (o a : 序数)
  结论: veblen o a in range (ω ^ · : 序数 -> 序数)
  证明: veblenWith_mem_range (isNormal_opow one_lt_omega0)

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_mem_range
-/
theorem veblen_mem_range_opow (o a : Ordinal) : veblen o a in range (ω ^ · : Ordinal -> Ordinal) :=
  veblenWith_mem_range (isNormal_opow one_lt_omega0)

/--
theorem `veblen_add_one` / 定理 `veblen_add_one`

English:
theorem veblen_add_one
  given: (o : Ordinal)
  statement: veblen (o + 1) = deriv (veblen o)
  proof: veblenWith_add_one (isNormal_opow one_lt_omega0) o

@[deprecated veblen_add_one (since := "2026-02-26")]

中文:
定理 veblen_add_one
  条件: (o : 序数)
  结论: veblen (o + 1) = deriv (veblen o)
  证明: veblenWith_add_one (isNormal_opow one_lt_omega0) o

@[deprecated veblen_add_one (since := "2026-02-26")]

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_add_one
-/
theorem veblen_add_one (o : Ordinal) : veblen (o + 1) = deriv (veblen o) :=
  veblenWith_add_one (isNormal_opow one_lt_omega0) o

@[deprecated veblen_add_one (since := "2026-02-26")]
/--
theorem `veblen_succ` / 定理 `veblen_succ`

English:
theorem veblen_succ
  given: (o : Ordinal)
  statement: veblen (succ o) = deriv (veblen o)
  proof: veblen_add_one o

中文:
定理 veblen_succ
  条件: (o : 序数)
  结论: veblen (succ o) = deriv (veblen o)
  证明: veblen_add_one o

Depends on / 依赖: veblen_add_one
-/
theorem veblen_succ (o : Ordinal) : veblen (succ o) = deriv (veblen o) :=
  veblen_add_one o

/--
theorem `veblen_right_strictMono` / 定理 `veblen_right_strictMono`

English:
theorem veblen_right_strictMono
  given: (o : Ordinal)
  statement: StrictMono (veblen o)
  proof: veblenWith_right_strictMono (isNormal_opow one_lt_omega0) o

@[simp]

中文:
定理 veblen_right_strictMono
  条件: (o : 序数)
  结论: 严格递增 (veblen o)
  证明: veblenWith_right_strictMono (isNormal_opow one_lt_omega0) o

@[simp]

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_right_strictMono
-/
theorem veblen_right_strictMono (o : Ordinal) : StrictMono (veblen o) :=
  veblenWith_right_strictMono (isNormal_opow one_lt_omega0) o

@[simp]
/--
theorem `veblen_lt_veblen_iff_right` / 定理 `veblen_lt_veblen_iff_right`

English:
theorem veblen_lt_veblen_iff_right
  statement: veblen o a < veblen o b ↔ a < b
  proof: veblenWith_lt_veblenWith_iff_right (isNormal_opow one_lt_omega0)

@[simp]

中文:
定理 veblen_lt_veblen_iff_right
  结论: veblen o a < veblen o b ↔ a < b
  证明: veblenWith_lt_veblenWith_iff_right (isNormal_opow one_lt_omega0)

@[simp]

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_lt_veblenWith_iff_right
-/
theorem veblen_lt_veblen_iff_right : veblen o a < veblen o b ↔ a < b :=
  veblenWith_lt_veblenWith_iff_right (isNormal_opow one_lt_omega0)

@[simp]
/--
theorem `veblen_le_veblen_iff_right` / 定理 `veblen_le_veblen_iff_right`

English:
theorem veblen_le_veblen_iff_right
  statement: veblen o a <= veblen o b ↔ a <= b
  proof: veblenWith_le_veblenWith_iff_right (isNormal_opow one_lt_omega0)

中文:
定理 veblen_le_veblen_iff_right
  结论: veblen o a <= veblen o b ↔ a <= b
  证明: veblenWith_le_veblenWith_iff_right (isNormal_opow one_lt_omega0)

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_le_veblenWith_iff_right
-/
theorem veblen_le_veblen_iff_right : veblen o a <= veblen o b ↔ a <= b :=
  veblenWith_le_veblenWith_iff_right (isNormal_opow one_lt_omega0)

/--
theorem `veblen_injective` / 定理 `veblen_injective`

English:
theorem veblen_injective
  given: (o : Ordinal)
  statement: Function.Injective (veblen o)
  proof: veblenWith_injective (isNormal_opow one_lt_omega0) o

@[simp]

中文:
定理 veblen_injective
  条件: (o : 序数)
  结论: 函数.单射 (veblen o)
  证明: veblenWith_injective (isNormal_opow one_lt_omega0) o

@[simp]

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_injective
-/
theorem veblen_injective (o : Ordinal) : Function.Injective (veblen o) :=
  veblenWith_injective (isNormal_opow one_lt_omega0) o

@[simp]
/--
theorem `veblen_inj` / 定理 `veblen_inj`

English:
theorem veblen_inj
  statement: veblen o a = veblen o b ↔ a = b
  proof: (veblen_injective o).eq_iff

中文:
定理 veblen_inj
  结论: veblen o a = veblen o b ↔ a = b
  证明: (veblen_injective o).eq_iff

Depends on / 依赖: eq_iff, veblen_injective
-/
theorem veblen_inj : veblen o a = veblen o b ↔ a = b :=
  (veblen_injective o).eq_iff

/--
theorem `right_le_veblen` / 定理 `right_le_veblen`

English:
theorem right_le_veblen
  given: (o a : Ordinal)
  statement: a <= veblen o a
  proof: right_le_veblenWith (isNormal_opow one_lt_omega0) o a

中文:
定理 right_le_veblen
  条件: (o a : 序数)
  结论: a <= veblen o a
  证明: right_le_veblenWith (isNormal_opow one_lt_omega0) o a

Depends on / 依赖: isNormal_opow, one_lt_omega0, right_le_veblenWith
-/
theorem right_le_veblen (o a : Ordinal) : a <= veblen o a :=
  right_le_veblenWith (isNormal_opow one_lt_omega0) o a

/--
theorem `veblen_left_monotone` / 定理 `veblen_left_monotone`

English:
theorem veblen_left_monotone
  given: (o : Ordinal)
  statement: Monotone (veblen · o)
  proof: veblenWith_left_monotone (isNormal_opow one_lt_omega0) o

@[simp]

中文:
定理 veblen_left_monotone
  条件: (o : 序数)
  结论: 递增 (veblen · o)
  证明: veblenWith_left_monotone (isNormal_opow one_lt_omega0) o

@[simp]

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_left_monotone
-/
theorem veblen_left_monotone (o : Ordinal) : Monotone (veblen · o) :=
  veblenWith_left_monotone (isNormal_opow one_lt_omega0) o

@[simp]
/--
theorem `veblen_pos` / 定理 `veblen_pos`

English:
theorem veblen_pos
  statement: 0 < veblen o a
  proof: veblenWith_pos (isNormal_opow one_lt_omega0) (by simp)

中文:
定理 veblen_pos
  结论: 0 < veblen o a
  证明: veblenWith_pos (isNormal_opow one_lt_omega0) (by simp)

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_pos
-/
theorem veblen_pos : 0 < veblen o a :=
  veblenWith_pos (isNormal_opow one_lt_omega0) (by simp)

/--
theorem `veblen_zero_strictMono` / 定理 `veblen_zero_strictMono`

English:
theorem veblen_zero_strictMono
  statement: StrictMono (veblen · 0)
  proof: veblenWith_zero_strictMono (isNormal_opow one_lt_omega0) (by simp)

@[simp]

中文:
定理 veblen_zero_strictMono
  结论: 严格递增 (veblen · 0)
  证明: veblenWith_zero_strictMono (isNormal_opow one_lt_omega0) (by simp)

@[simp]

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_zero_strictMono
-/
theorem veblen_zero_strictMono : StrictMono (veblen · 0) :=
  veblenWith_zero_strictMono (isNormal_opow one_lt_omega0) (by simp)

@[simp]
/--
theorem `veblen_zero_lt_veblen_zero` / 定理 `veblen_zero_lt_veblen_zero`

English:
theorem veblen_zero_lt_veblen_zero
  statement: veblen o₁ 0 < veblen o₂ 0 ↔ o₁ < o₂
  proof: veblen_zero_strictMono.lt_iff_lt

@[simp]

中文:
定理 veblen_zero_lt_veblen_zero
  结论: veblen o₁ 0 < veblen o₂ 0 ↔ o₁ < o₂
  证明: veblen_zero_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, veblen_zero_strictMono, veblen_zero_strictMono.lt_iff_lt
-/
theorem veblen_zero_lt_veblen_zero : veblen o₁ 0 < veblen o₂ 0 ↔ o₁ < o₂ :=
  veblen_zero_strictMono.lt_iff_lt

@[simp]
/--
theorem `veblen_zero_le_veblen_zero` / 定理 `veblen_zero_le_veblen_zero`

English:
theorem veblen_zero_le_veblen_zero
  statement: veblen o₁ 0 <= veblen o₂ 0 ↔ o₁ <= o₂
  proof: veblen_zero_strictMono.le_iff_le

@[simp]

中文:
定理 veblen_zero_le_veblen_zero
  结论: veblen o₁ 0 <= veblen o₂ 0 ↔ o₁ <= o₂
  证明: veblen_zero_strictMono.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, veblen_zero_strictMono, veblen_zero_strictMono.le_iff_le
-/
theorem veblen_zero_le_veblen_zero : veblen o₁ 0 <= veblen o₂ 0 ↔ o₁ <= o₂ :=
  veblen_zero_strictMono.le_iff_le

@[simp]
/--
theorem `veblen_zero_inj` / 定理 `veblen_zero_inj`

English:
theorem veblen_zero_inj
  statement: veblen o₁ 0 = veblen o₂ 0 ↔ o₁ = o₂
  proof: veblen_zero_strictMono.injective.eq_iff

中文:
定理 veblen_zero_inj
  结论: veblen o₁ 0 = veblen o₂ 0 ↔ o₁ = o₂
  证明: veblen_zero_strictMono.injective.eq_iff

Depends on / 依赖: eq_iff, injective, veblen_zero_strictMono, veblen_zero_strictMono.injective.eq_iff
-/
theorem veblen_zero_inj : veblen o₁ 0 = veblen o₂ 0 ↔ o₁ = o₂ :=
  veblen_zero_strictMono.injective.eq_iff

/--
theorem `left_le_veblen` / 定理 `left_le_veblen`

English:
theorem left_le_veblen
  given: (o a : Ordinal)
  statement: o <= veblen o a
  proof: left_le_veblenWith (isNormal_opow one_lt_omega0) (by simp) o a

中文:
定理 left_le_veblen
  条件: (o a : 序数)
  结论: o <= veblen o a
  证明: left_le_veblenWith (isNormal_opow one_lt_omega0) (by simp) o a

Depends on / 依赖: isNormal_opow, left_le_veblenWith, one_lt_omega0
-/
theorem left_le_veblen (o a : Ordinal) : o <= veblen o a :=
  left_le_veblenWith (isNormal_opow one_lt_omega0) (by simp) o a

/--
theorem `isNormal_veblen_zero` / 定理 `isNormal_veblen_zero`

English:
theorem isNormal_veblen_zero
  statement: IsNormal (veblen · 0)
  proof: isNormal_veblenWith_zero (isNormal_opow one_lt_omega0) (by simp)

中文:
定理 isNormal_veblen_zero
  结论: 是正规 (veblen · 0)
  证明: isNormal_veblenWith_zero (isNormal_opow one_lt_omega0) (by simp)

Depends on / 依赖: isNormal_opow, isNormal_veblenWith_zero, one_lt_omega0
-/
theorem isNormal_veblen_zero : IsNormal (veblen · 0) :=
  isNormal_veblenWith_zero (isNormal_opow one_lt_omega0) (by simp)

/--
theorem `veblen_veblen_eq_veblen_iff` / 定理 `veblen_veblen_eq_veblen_iff`

English:
theorem veblen_veblen_eq_veblen_iff
  given: (h : o₂ <= o₁)
  proof: veblenWith_veblenWith_eq_veblenWith_iff (isNormal_opow one_lt_omega0) h

中文:
定理 veblen_veblen_eq_veblen_iff
  条件: (h : o₂ <= o₁)
  证明: veblenWith_veblenWith_eq_veblenWith_iff (isNormal_opow one_lt_omega0) h

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_veblenWith_eq_veblenWith_iff
-/
theorem veblen_veblen_eq_veblen_iff (h : o₂ <= o₁) :
    veblen o₁ (veblen o₂ a) = veblen o₂ a ↔ veblen o₁ a = a :=
  veblenWith_veblenWith_eq_veblenWith_iff (isNormal_opow one_lt_omega0) h

/--
theorem `veblen_lt_veblen_veblen_iff` / 定理 `veblen_lt_veblen_veblen_iff`

English:
theorem veblen_lt_veblen_veblen_iff
  given: (h : o₂ <= o₁)
  proof: veblenWith_lt_veblenWith_veblenWith_iff (isNormal_opow one_lt_omega0) h

中文:
定理 veblen_lt_veblen_veblen_iff
  条件: (h : o₂ <= o₁)
  证明: veblenWith_lt_veblenWith_veblenWith_iff (isNormal_opow one_lt_omega0) h

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_lt_veblenWith_veblenWith_iff
-/
theorem veblen_lt_veblen_veblen_iff (h : o₂ <= o₁) :
    veblen o₂ a < veblen o₁ (veblen o₂ a) ↔ a < veblen o₁ a :=
  veblenWith_lt_veblenWith_veblenWith_iff (isNormal_opow one_lt_omega0) h

/--
theorem `veblen_opow_eq_opow_iff` / 定理 `veblen_opow_eq_opow_iff`

English:
theorem veblen_opow_eq_opow_iff
  statement: veblen o (ω ^ a) = ω ^ a ↔ veblen o a = a
  proof: veblenWith_apply_eq_apply_iff (isNormal_opow one_lt_omega0)

中文:
定理 veblen_opow_eq_opow_iff
  结论: veblen o (ω ^ a) = ω ^ a ↔ veblen o a = a
  证明: veblenWith_apply_eq_apply_iff (isNormal_opow one_lt_omega0)

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_apply_eq_apply_iff
-/
theorem veblen_opow_eq_opow_iff : veblen o (ω ^ a) = ω ^ a ↔ veblen o a = a :=
  veblenWith_apply_eq_apply_iff (isNormal_opow one_lt_omega0)

/--
theorem `opow_lt_veblen_opow_iff` / 定理 `opow_lt_veblen_opow_iff`

English:
theorem opow_lt_veblen_opow_iff
  statement: ω ^ a < veblen o (ω ^ a) ↔ a < veblen o a
  proof: apply_lt_veblenWith_apply_iff (isNormal_opow one_lt_omega0)

中文:
定理 opow_lt_veblen_opow_iff
  结论: ω ^ a < veblen o (ω ^ a) ↔ a < veblen o a
  证明: apply_lt_veblenWith_apply_iff (isNormal_opow one_lt_omega0)

Depends on / 依赖: apply_lt_veblenWith_apply_iff, isNormal_opow, one_lt_omega0
-/
theorem opow_lt_veblen_opow_iff : ω ^ a < veblen o (ω ^ a) ↔ a < veblen o a :=
  apply_lt_veblenWith_apply_iff (isNormal_opow one_lt_omega0)

/--
theorem `lt_veblen` / 定理 `lt_veblen`

English:
theorem lt_veblen
  given: (a : Ordinal)
  statement: a < veblen a a
  proof: by
  obtain rfl | h := eq_zero_or_pos a
  · simp
  · apply (left_le_veblen a 0).trans_lt
    simpa

中文:
定理 lt_veblen
  条件: (a : 序数)
  结论: a < veblen a a
  证明: by
  obtain rfl | h := eq_zero_or_pos a
  · simp
  · apply (left_le_veblen a 0).trans_lt
    simpa

Depends on / 依赖: eq_zero_or_pos, left_le_veblen, trans_lt
-/
theorem lt_veblen (a : Ordinal) : a < veblen a a := by
  obtain rfl | h := eq_zero_or_pos a
  · simp
  · apply (left_le_veblen a 0).trans_lt
    simpa

/--
theorem `cmp_veblen` / 定理 `cmp_veblen`

English:
theorem cmp_veblen
  statement: cmp (veblen o₁ a) (veblen o₂ b) =
  proof: cmp_veblenWith (isNormal_opow one_lt_omega0)

中文:
定理 cmp_veblen
  结论: cmp (veblen o₁ a) (veblen o₂ b) =
  证明: cmp_veblenWith (isNormal_opow one_lt_omega0)

Depends on / 依赖: cmp_veblenWith, isNormal_opow, one_lt_omega0
-/
theorem cmp_veblen : cmp (veblen o₁ a) (veblen o₂ b) =
    match cmp o₁ o₂ with
    | .eq => cmp a b
    | .lt => cmp a (veblen o₂ b)
    | .gt => cmp (veblen o₁ a) b :=
  cmp_veblenWith (isNormal_opow one_lt_omega0)

/--
theorem `veblen_lt_veblen_iff` / 定理 `veblen_lt_veblen_iff`

English:
theorem veblen_lt_veblen_iff
  proof: veblenWith_lt_veblenWith_iff (isNormal_opow one_lt_omega0)

中文:
定理 veblen_lt_veblen_iff
  证明: veblenWith_lt_veblenWith_iff (isNormal_opow one_lt_omega0)

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_lt_veblenWith_iff
-/
theorem veblen_lt_veblen_iff :
    veblen o₁ a < veblen o₂ b ↔
      o₁ = o₂ ∧ a < b ∨ o₁ < o₂ ∧ a < veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a < b :=
  veblenWith_lt_veblenWith_iff (isNormal_opow one_lt_omega0)

/--
theorem `veblen_le_veblen_iff` / 定理 `veblen_le_veblen_iff`

English:
theorem veblen_le_veblen_iff
  proof: veblenWith_le_veblenWith_iff (isNormal_opow one_lt_omega0)

中文:
定理 veblen_le_veblen_iff
  证明: veblenWith_le_veblenWith_iff (isNormal_opow one_lt_omega0)

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_le_veblenWith_iff
-/
theorem veblen_le_veblen_iff :
    veblen o₁ a <= veblen o₂ b ↔
      o₁ = o₂ ∧ a <= b ∨ o₁ < o₂ ∧ a <= veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a <= b :=
  veblenWith_le_veblenWith_iff (isNormal_opow one_lt_omega0)

/--
theorem `veblen_eq_veblen_iff` / 定理 `veblen_eq_veblen_iff`

English:
theorem veblen_eq_veblen_iff
  proof: veblenWith_eq_veblenWith_iff (isNormal_opow one_lt_omega0)

中文:
定理 veblen_eq_veblen_iff
  证明: veblenWith_eq_veblenWith_iff (isNormal_opow one_lt_omega0)

Depends on / 依赖: isNormal_opow, one_lt_omega0, veblenWith_eq_veblenWith_iff
-/
theorem veblen_eq_veblen_iff :
    veblen o₁ a = veblen o₂ b ↔
      o₁ = o₂ ∧ a = b ∨ o₁ < o₂ ∧ a = veblen o₂ b ∨ o₂ < o₁ ∧ veblen o₁ a = b :=
  veblenWith_eq_veblenWith_iff (isNormal_opow one_lt_omega0)

end veblen

/-! ### Inverse Veblen function -/

/--
Definition of `invVeblen₁` / `invVeblen₁` 的定义

English:
definition invVeblen₁
  signature: (x : Ordinal)
  body: sInf {y | veblen y x != x}

中文:
定义 invVeblen₁
  签名: (x : 序数)
  定义体: sInf {y | veblen y x != x}

Depends on / 依赖: veblen
-/
def invVeblen₁ (x : Ordinal) : Ordinal :=
  sInf {y | veblen y x != x}

/--
theorem `veblen_eq_of_lt_invVeblen₁` / 定理 `veblen_eq_of_lt_invVeblen₁`

English:
theorem veblen_eq_of_lt_invVeblen₁
  given: (h : o < invVeblen₁ x)
  statement: veblen o x = x
  proof: by
  simpa using notMem_of_lt_csInf' h

中文:
定理 veblen_eq_of_lt_invVeblen₁
  条件: (h : o < invVeblen₁ x)
  结论: veblen o x = x
  证明: by
  simpa using notMem_of_lt_csInf' h

Depends on / 依赖: notMem_of_lt_csInf
-/
theorem veblen_eq_of_lt_invVeblen₁ (h : o < invVeblen₁ x) : veblen o x = x := by
  simpa using notMem_of_lt_csInf' h

/--
theorem `invVeblen₁_le` / 定理 `invVeblen₁_le`

English:
theorem invVeblen₁_le
  given: (x : Ordinal)
  statement: invVeblen₁ x <= x
  proof: csInf_le' (lt_veblen x).ne'

中文:
定理 invVeblen₁_le
  条件: (x : 序数)
  结论: invVeblen₁ x <= x
  证明: csInf_le' (lt_veblen x).ne'

Depends on / 依赖: csInf_le, lt_veblen
-/
theorem invVeblen₁_le (x : Ordinal) : invVeblen₁ x <= x :=
  csInf_le' (lt_veblen x).ne'

/--
theorem `lt_veblen_invVeblen₁` / 定理 `lt_veblen_invVeblen₁`

English:
theorem lt_veblen_invVeblen₁
  given: (x : Ordinal)
  statement: x < veblen (invVeblen₁ x) x
  proof: (right_le_veblen ..).lt_of_ne' (csInf_mem (s := {y | veblen y x != x}) ⟨x, (lt_veblen x).ne'⟩)

中文:
定理 lt_veblen_invVeblen₁
  条件: (x : 序数)
  结论: x < veblen (invVeblen₁ x) x
  证明: (right_le_veblen ..).lt_of_ne' (csInf_mem (s := {y | veblen y x != x}) ⟨x, (lt_veblen x).ne'⟩)

Depends on / 依赖: csInf_mem, lt_of_ne, lt_veblen, right_le_veblen, veblen
-/
theorem lt_veblen_invVeblen₁ (x : Ordinal) : x < veblen (invVeblen₁ x) x :=
  (right_le_veblen ..).lt_of_ne' (csInf_mem (s := {y | veblen y x != x}) ⟨x, (lt_veblen x).ne'⟩)

/--
theorem `lt_veblen_iff_invVeblen₁_le` / 定理 `lt_veblen_iff_invVeblen₁_le`

English:
theorem lt_veblen_iff_invVeblen₁_le
  statement: a < veblen o a ↔ invVeblen₁ a <= o
  proof: by
  obtain h | h := lt_or_ge o (invVeblen₁ a)
  · rw [veblen_eq_of_lt_invVeblen₁ h]
    simpa
  · simpa [(lt_veblen_invVeblen₁ a).trans_le (veblen_left_monotone _ h)]

中文:
定理 lt_veblen_iff_invVeblen₁_le
  结论: a < veblen o a ↔ invVeblen₁ a <= o
  证明: by
  obtain h | h := lt_or_ge o (invVeblen₁ a)
  · rw [veblen_eq_of_lt_invVeblen₁ h]
    simpa
  · simpa [(lt_veblen_invVeblen₁ a).trans_le (veblen_left_monotone _ h)]

Depends on / 依赖: lt_or_ge, trans_le, veblen_left_monotone
-/
theorem lt_veblen_iff_invVeblen₁_le : a < veblen o a ↔ invVeblen₁ a <= o := by
  obtain h | h := lt_or_ge o (invVeblen₁ a)
  · rw [veblen_eq_of_lt_invVeblen₁ h]
    simpa
  · simpa [(lt_veblen_invVeblen₁ a).trans_le (veblen_left_monotone _ h)]

/--
theorem `mem_range_veblen_iff_le_invVeblen₁` / 定理 `mem_range_veblen_iff_le_invVeblen₁`

English:
theorem mem_range_veblen_iff_le_invVeblen₁
  statement: ω ^ x in range (veblen o) ↔ o <= invVeblen₁ x
  proof: by
  obtain h | rfl | h := lt_trichotomy o (invVeblen₁ x)
· exact iff_of_true ⟨_, veblen_opow_eq_opow_iff.2 veblen_eq_of_lt_invVeblen₁ h⟩ h.le
  · apply iff_of_true _ le_rfl
    by_cases h : invVeblen₁ x = 0
    · simp [h]
    · simp_rw [mem_range_veblen h, veblen_opow_eq_opow_iff]
      exact fun o => veblen_eq_of_lt_invVeblen₁
  · apply iff_of_false _ h.not_ge
    rintro ⟨z, hz⟩
    have hz' := hz
    rw [← veblen_veblen_of_lt h]; rw [hz']; rw [veblen_opow_eq_opow_iff] at hz
    exact (lt_veblen_invVeblen₁ x).ne' hz

中文:
定理 mem_range_veblen_iff_le_invVeblen₁
  结论: ω ^ x in range (veblen o) ↔ o <= invVeblen₁ x
  证明: by
  obtain h | rfl | h := lt_trichotomy o (invVeblen₁ x)
· exact iff_of_true ⟨_, veblen_opow_eq_opow_iff.2 veblen_eq_of_lt_invVeblen₁ h⟩ h.le
  · apply iff_of_true _ le_rfl
    by_cases h : invVeblen₁ x = 0
    · simp [h]
    · simp_rw [mem_range_veblen h, veblen_opow_eq_opow_iff]
      exact fun o => veblen_eq_of_lt_invVeblen₁
  · apply iff_of_false _ h.not_ge
    rintro ⟨z, hz⟩
    have hz' := hz
    rw [← veblen_veblen_of_lt h]; rw [hz']; rw [veblen_opow_eq_opow_iff] at hz
    exact (lt_veblen_invVeblen₁ x).ne' hz

Depends on / 依赖: h.le, h.not_ge, iff_of_false, iff_of_true, le_rfl, lt_trichotomy, mem_range_veblen, not_ge, simp_rw, veblen_opow_eq_opow_iff, veblen_veblen_of_lt
-/
theorem mem_range_veblen_iff_le_invVeblen₁ : ω ^ x in range (veblen o) ↔ o <= invVeblen₁ x := by
  obtain h | rfl | h := lt_trichotomy o (invVeblen₁ x)
· exact iff_of_true ⟨_, veblen_opow_eq_opow_iff.2 veblen_eq_of_lt_invVeblen₁ h⟩ h.le
  · apply iff_of_true _ le_rfl
    by_cases h : invVeblen₁ x = 0
    · simp [h]
    · simp_rw [mem_range_veblen h, veblen_opow_eq_opow_iff]
      exact fun o => veblen_eq_of_lt_invVeblen₁
  · apply iff_of_false _ h.not_ge
    rintro ⟨z, hz⟩
    have hz' := hz
    rw [← veblen_veblen_of_lt h]; rw [hz']; rw [veblen_opow_eq_opow_iff] at hz
    exact (lt_veblen_invVeblen₁ x).ne' hz

/--
theorem `invVeblen₁_veblen` / 定理 `invVeblen₁_veblen`

English:
theorem invVeblen₁_veblen
  given: (h : a < veblen o a)
  statement: invVeblen₁ (veblen o a) = o
  proof: by
  apply le_antisymm
  · rwa [← lt_veblen_iff_invVeblen₁_le, veblen_lt_veblen_iff_right]
  · rw [← mem_range_veblen_iff_le_invVeblen₁]
    obtain rfl | ho := eq_zero_or_pos o
    · simp
    · rw [← veblen_zero_apply, veblen_veblen_of_lt ho]
      simp

中文:
定理 invVeblen₁_veblen
  条件: (h : a < veblen o a)
  结论: invVeblen₁ (veblen o a) = o
  证明: by
  apply le_antisymm
  · rwa [← lt_veblen_iff_invVeblen₁_le, veblen_lt_veblen_iff_right]
  · rw [← mem_range_veblen_iff_le_invVeblen₁]
    obtain rfl | ho := eq_zero_or_pos o
    · simp
    · rw [← veblen_zero_apply, veblen_veblen_of_lt ho]
      simp

Depends on / 依赖: eq_zero_or_pos, le_antisymm, veblen_lt_veblen_iff_right, veblen_veblen_of_lt, veblen_zero_apply
-/
theorem invVeblen₁_veblen (h : a < veblen o a) : invVeblen₁ (veblen o a) = o := by
  apply le_antisymm
  · rwa [← lt_veblen_iff_invVeblen₁_le, veblen_lt_veblen_iff_right]
  · rw [← mem_range_veblen_iff_le_invVeblen₁]
    obtain rfl | ho := eq_zero_or_pos o
    · simp
    · rw [← veblen_zero_apply, veblen_veblen_of_lt ho]
      simp

/--
theorem `invVeblen₁_of_lt_opow` / 定理 `invVeblen₁_of_lt_opow`

English:
theorem invVeblen₁_of_lt_opow
  given: (h : a < ω ^ a)
  statement: invVeblen₁ a = 0
  proof: by
  rwa [← nonpos_iff_eq_zero, ← lt_veblen_iff_invVeblen₁_le, veblen_zero]

@[simp]

中文:
定理 invVeblen₁_of_lt_opow
  条件: (h : a < ω ^ a)
  结论: invVeblen₁ a = 0
  证明: by
  rwa [← nonpos_iff_eq_zero, ← lt_veblen_iff_invVeblen₁_le, veblen_zero]

@[simp]

Depends on / 依赖: nonpos_iff_eq_zero, veblen_zero
-/
theorem invVeblen₁_of_lt_opow (h : a < ω ^ a) : invVeblen₁ a = 0 := by
  rwa [← nonpos_iff_eq_zero, ← lt_veblen_iff_invVeblen₁_le, veblen_zero]

@[simp]
/--
theorem `invVeblen₁_zero` / 定理 `invVeblen₁_zero`

English:
theorem invVeblen₁_zero
  statement: invVeblen₁ 0 = 0
  proof: invVeblen₁_of_lt_opow by simp

@[inherit_doc invVeblen₁]

中文:
定理 invVeblen₁_zero
  结论: invVeblen₁ 0 = 0
  证明: invVeblen₁_of_lt_opow by simp

@[inherit_doc invVeblen₁]
-/
theorem invVeblen₁_zero : invVeblen₁ 0 = 0 :=
invVeblen₁_of_lt_opow by simp

@[inherit_doc invVeblen₁]
/--
Definition of `invVeblen₂` / `invVeblen₂` 的定义

English:
definition invVeblen₂
  signature: (x : Ordinal)
  body: Classical.choose ((mem_range_veblen_iff_le_invVeblen₁ (x := x)).2 le_rfl)

@[simp]

中文:
定义 invVeblen₂
  签名: (x : 序数)
  定义体: Classical.choose ((mem_range_veblen_iff_le_invVeblen₁ (x := x)).2 le_rfl)

@[simp]

Depends on / 依赖: Classical, Classical.choose, le_rfl
-/
def invVeblen₂ (x : Ordinal) : Ordinal :=
  Classical.choose ((mem_range_veblen_iff_le_invVeblen₁ (x := x)).2 le_rfl)

@[simp]
/--
theorem `veblen_invVeblen₁_invVeblen₂` / 定理 `veblen_invVeblen₁_invVeblen₂`

English:
theorem veblen_invVeblen₁_invVeblen₂
  given: (x : Ordinal)
  statement: veblen (invVeblen₁ x) (invVeblen₂ x) = ω ^ x
  proof: Classical.choose_spec (mem_range_veblen_iff_le_invVeblen₁.2 le_rfl)

中文:
定理 veblen_invVeblen₁_invVeblen₂
  条件: (x : 序数)
  结论: veblen (invVeblen₁ x) (invVeblen₂ x) = ω ^ x
  证明: Classical.choose_spec (mem_range_veblen_iff_le_invVeblen₁.2 le_rfl)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, le_rfl
-/
theorem veblen_invVeblen₁_invVeblen₂ (x : Ordinal) : veblen (invVeblen₁ x) (invVeblen₂ x) = ω ^ x :=
  Classical.choose_spec (mem_range_veblen_iff_le_invVeblen₁.2 le_rfl)

/--
theorem `invVeblen₂_eq_iff` / 定理 `invVeblen₂_eq_iff`

English:
theorem invVeblen₂_eq_iff
  statement: invVeblen₂ x = a ↔ ω ^ x = veblen (invVeblen₁ x) a
  proof: by
  rw [← veblen_inj (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

中文:
定理 invVeblen₂_eq_iff
  结论: invVeblen₂ x = a ↔ ω ^ x = veblen (invVeblen₁ x) a
  证明: by
  rw [← veblen_inj (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

Depends on / 依赖: veblen_inj, x.invVeblen
-/
theorem invVeblen₂_eq_iff : invVeblen₂ x = a ↔ ω ^ x = veblen (invVeblen₁ x) a := by
  rw [← veblen_inj (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

/--
theorem `invVeblen₂_lt_iff` / 定理 `invVeblen₂_lt_iff`

English:
theorem invVeblen₂_lt_iff
  statement: invVeblen₂ x < a ↔ ω ^ x < veblen (invVeblen₁ x) a
  proof: by
  rw [← veblen_lt_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

中文:
定理 invVeblen₂_lt_iff
  结论: invVeblen₂ x < a ↔ ω ^ x < veblen (invVeblen₁ x) a
  证明: by
  rw [← veblen_lt_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

Depends on / 依赖: veblen_lt_veblen_iff_right, x.invVeblen
-/
theorem invVeblen₂_lt_iff : invVeblen₂ x < a ↔ ω ^ x < veblen (invVeblen₁ x) a := by
  rw [← veblen_lt_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

/--
theorem `invVeblen₂_le_iff` / 定理 `invVeblen₂_le_iff`

English:
theorem invVeblen₂_le_iff
  statement: invVeblen₂ x <= a ↔ ω ^ x <= veblen (invVeblen₁ x) a
  proof: by
  rw [← veblen_le_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

中文:
定理 invVeblen₂_le_iff
  结论: invVeblen₂ x <= a ↔ ω ^ x <= veblen (invVeblen₁ x) a
  证明: by
  rw [← veblen_le_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

Depends on / 依赖: veblen_le_veblen_iff_right, x.invVeblen
-/
theorem invVeblen₂_le_iff : invVeblen₂ x <= a ↔ ω ^ x <= veblen (invVeblen₁ x) a := by
  rw [← veblen_le_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

/--
theorem `lt_invVeblen₂_iff` / 定理 `lt_invVeblen₂_iff`

English:
theorem lt_invVeblen₂_iff
  statement: a < invVeblen₂ x ↔ veblen (invVeblen₁ x) a < ω ^ x
  proof: by
  rw [← veblen_lt_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

中文:
定理 lt_invVeblen₂_iff
  结论: a < invVeblen₂ x ↔ veblen (invVeblen₁ x) a < ω ^ x
  证明: by
  rw [← veblen_lt_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

Depends on / 依赖: veblen_lt_veblen_iff_right, x.invVeblen
-/
theorem lt_invVeblen₂_iff : a < invVeblen₂ x ↔ veblen (invVeblen₁ x) a < ω ^ x := by
  rw [← veblen_lt_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

/--
theorem `le_invVeblen₂_iff` / 定理 `le_invVeblen₂_iff`

English:
theorem le_invVeblen₂_iff
  statement: a <= invVeblen₂ x ↔ veblen (invVeblen₁ x) a <= ω ^ x
  proof: by
  rw [← veblen_le_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

中文:
定理 le_invVeblen₂_iff
  结论: a <= invVeblen₂ x ↔ veblen (invVeblen₁ x) a <= ω ^ x
  证明: by
  rw [← veblen_le_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

Depends on / 依赖: veblen_le_veblen_iff_right, x.invVeblen
-/
theorem le_invVeblen₂_iff : a <= invVeblen₂ x ↔ veblen (invVeblen₁ x) a <= ω ^ x := by
  rw [← veblen_le_veblen_iff_right (o := x.invVeblen₁)]; rw [veblen_invVeblen₁_invVeblen₂]

/--
theorem `invVeblen₂_lt` / 定理 `invVeblen₂_lt`

English:
theorem invVeblen₂_lt
  given: (x : Ordinal)
  statement: invVeblen₂ x < ω ^ x
  proof: by
  rw [invVeblen₂_lt_iff]; rw [opow_lt_veblen_opow_iff]
  exact lt_veblen_invVeblen₁ x

中文:
定理 invVeblen₂_lt
  条件: (x : 序数)
  结论: invVeblen₂ x < ω ^ x
  证明: by
  rw [invVeblen₂_lt_iff]; rw [opow_lt_veblen_opow_iff]
  exact lt_veblen_invVeblen₁ x

Depends on / 依赖: opow_lt_veblen_opow_iff
-/
theorem invVeblen₂_lt (x : Ordinal) : invVeblen₂ x < ω ^ x := by
  rw [invVeblen₂_lt_iff]; rw [opow_lt_veblen_opow_iff]
  exact lt_veblen_invVeblen₁ x

/--
theorem `invVeblen₂_le` / 定理 `invVeblen₂_le`

English:
theorem invVeblen₂_le
  given: (x : Ordinal)
  statement: invVeblen₂ x <= x
  proof: by
  obtain h | h := eq_zero_or_pos (invVeblen₁ x)
  · rw [invVeblen₂_le_iff, h, veblen_zero]
  · convert! (invVeblen₂_lt x).le
    rw [← veblen_zero_apply]; rw [veblen_eq_of_lt_invVeblen₁ h]

中文:
定理 invVeblen₂_le
  条件: (x : 序数)
  结论: invVeblen₂ x <= x
  证明: by
  obtain h | h := eq_zero_or_pos (invVeblen₁ x)
  · rw [invVeblen₂_le_iff, h, veblen_zero]
  · convert! (invVeblen₂_lt x).le
    rw [← veblen_zero_apply]; rw [veblen_eq_of_lt_invVeblen₁ h]

Depends on / 依赖: convert, eq_zero_or_pos, veblen_zero, veblen_zero_apply
-/
theorem invVeblen₂_le (x : Ordinal) : invVeblen₂ x <= x := by
  obtain h | h := eq_zero_or_pos (invVeblen₁ x)
  · rw [invVeblen₂_le_iff, h, veblen_zero]
  · convert! (invVeblen₂_lt x).le
    rw [← veblen_zero_apply]; rw [veblen_eq_of_lt_invVeblen₁ h]

/--
theorem `invVeblen₂_of_lt_opow` / 定理 `invVeblen₂_of_lt_opow`

English:
theorem invVeblen₂_of_lt_opow
  given: (h : a < ω ^ a)
  statement: invVeblen₂ a = a
  proof: by
  rw [invVeblen₂_eq_iff]; rw [invVeblen₁_of_lt_opow h]; rw [veblen_zero_apply]

@[simp]

中文:
定理 invVeblen₂_of_lt_opow
  条件: (h : a < ω ^ a)
  结论: invVeblen₂ a = a
  证明: by
  rw [invVeblen₂_eq_iff]; rw [invVeblen₁_of_lt_opow h]; rw [veblen_zero_apply]

@[simp]

Depends on / 依赖: veblen_zero_apply
-/
theorem invVeblen₂_of_lt_opow (h : a < ω ^ a) : invVeblen₂ a = a := by
  rw [invVeblen₂_eq_iff]; rw [invVeblen₁_of_lt_opow h]; rw [veblen_zero_apply]

@[simp]
/--
theorem `invVeblen₂_zero` / 定理 `invVeblen₂_zero`

English:
theorem invVeblen₂_zero
  statement: invVeblen₂ 0 = 0
  proof: by
  apply invVeblen₂_of_lt_opow
  simp

中文:
定理 invVeblen₂_zero
  结论: invVeblen₂ 0 = 0
  证明: by
  apply invVeblen₂_of_lt_opow
  simp
-/
theorem invVeblen₂_zero : invVeblen₂ 0 = 0 := by
  apply invVeblen₂_of_lt_opow
  simp

/--
theorem `invVeblen₂_veblen` / 定理 `invVeblen₂_veblen`

English:
theorem invVeblen₂_veblen
  given: (ho : o != 0) (h : a < veblen o a)
  statement: invVeblen₂ (veblen o a) = a
  proof: by
  rw [invVeblen₂_eq_iff]; rw [invVeblen₁_veblen h]; rw [← veblen_zero_apply]; rw [veblen_veblen_of_lt]
  exact ho.bot_lt

中文:
定理 invVeblen₂_veblen
  条件: (ho : o != 0) (h : a < veblen o a)
  结论: invVeblen₂ (veblen o a) = a
  证明: by
  rw [invVeblen₂_eq_iff]; rw [invVeblen₁_veblen h]; rw [← veblen_zero_apply]; rw [veblen_veblen_of_lt]
  exact ho.bot_lt

Depends on / 依赖: bot_lt, ho.bot_lt, veblen_veblen_of_lt, veblen_zero_apply
-/
theorem invVeblen₂_veblen (ho : o != 0) (h : a < veblen o a) : invVeblen₂ (veblen o a) = a := by
  rw [invVeblen₂_eq_iff]; rw [invVeblen₁_veblen h]; rw [← veblen_zero_apply]; rw [veblen_veblen_of_lt]
  exact ho.bot_lt

/--
theorem `veblen_eq_opow_iff` / 定理 `veblen_eq_opow_iff`

English:
theorem veblen_eq_opow_iff
  given: (h : a < veblen o a)
  proof: by
  refine ⟨?_, fun ⟨hx, ha⟩ => ?_⟩
  · obtain rfl | ho := eq_zero_or_pos o
    · rw [veblen_zero] at h
      have := invVeblen₁_of_lt_opow h
      have := invVeblen₂_of_lt_opow h
      aesop
    · rw [← veblen_veblen_of_lt ho, veblen_zero_apply, opow_right_inj one_lt_omega0]
      rintro rfl
      simp [invVeblen₁_veblen h, invVeblen₂_veblen ho.ne' h]
  · convert! ← veblen_invVeblen₁_invVeblen₂ x

中文:
定理 veblen_eq_opow_iff
  条件: (h : a < veblen o a)
  证明: by
  refine ⟨?_, fun ⟨hx, ha⟩ => ?_⟩
  · obtain rfl | ho := eq_zero_or_pos o
    · rw [veblen_zero] at h
      have := invVeblen₁_of_lt_opow h
      have := invVeblen₂_of_lt_opow h
      aesop
    · rw [← veblen_veblen_of_lt ho, veblen_zero_apply, opow_right_inj one_lt_omega0]
      rintro rfl
      simp [invVeblen₁_veblen h, invVeblen₂_veblen ho.ne' h]
  · convert! ← veblen_invVeblen₁_invVeblen₂ x

Depends on / 依赖: convert, eq_zero_or_pos, ho.ne, one_lt_omega0, opow_right_inj, veblen_veblen_of_lt, veblen_zero, veblen_zero_apply
-/
theorem veblen_eq_opow_iff (h : a < veblen o a) :
    veblen o a = ω ^ x ↔ invVeblen₁ x = o ∧ invVeblen₂ x = a := by
  refine ⟨?_, fun ⟨hx, ha⟩ => ?_⟩
  · obtain rfl | ho := eq_zero_or_pos o
    · rw [veblen_zero] at h
      have := invVeblen₁_of_lt_opow h
      have := invVeblen₂_of_lt_opow h
      aesop
    · rw [← veblen_veblen_of_lt ho, veblen_zero_apply, opow_right_inj one_lt_omega0]
      rintro rfl
      simp [invVeblen₁_veblen h, invVeblen₂_veblen ho.ne' h]
  · convert! ← veblen_invVeblen₁_invVeblen₂ x

/-! ### Epsilon function -/

/--
Definition of `epsilon` / `epsilon` 的定义

English:
abbreviation epsilon
  body: veblen 1

@[inherit_doc] scoped notation "ε_ " => epsilon
recommended_spelling "epsilon" for "ε_ " in [epsilon, «termε_»]

中文:
缩写 epsilon
  定义体: veblen 1

@[inherit_doc] scoped notation "ε_ " => epsilon
recommended_spelling "epsilon" for "ε_ " in [epsilon, «termε_»]

Depends on / 依赖: veblen
-/
abbrev epsilon := veblen 1

@[inherit_doc] scoped notation "ε_ " => epsilon
recommended_spelling "epsilon" for "ε_ " in [epsilon, «termε_»]

/-- `ε₀` is the first fixed point of `ω ^ ⬝`, i.e. the supremum of `ω`, `ω ^ ω`, `ω ^ ω ^ ω`, … -/
scoped notation "ε₀" => ε_ 0
recommended_spelling "epsilon_zero" for "ε₀" in [«termε₀»]

/--
theorem `epsilon_eq_deriv` / 定理 `epsilon_eq_deriv`

English:
theorem epsilon_eq_deriv
  given: (o : Ordinal)
  statement: ε_ o = deriv (fun a => ω ^ a) o
  proof: by
  simpa [epsilon] using congrFun (veblen_add_one 0) o

中文:
定理 epsilon_eq_deriv
  条件: (o : 序数)
  结论: ε_ o = deriv (fun a => ω ^ a) o
  证明: by
  simpa [epsilon] using congrFun (veblen_add_one 0) o

Depends on / 依赖: epsilon, veblen_add_one
-/
theorem epsilon_eq_deriv (o : Ordinal) : ε_ o = deriv (fun a => ω ^ a) o := by
  simpa [epsilon] using congrFun (veblen_add_one 0) o

/--
theorem `epsilon_zero_eq_nfp` / 定理 `epsilon_zero_eq_nfp`

English:
theorem epsilon_zero_eq_nfp
  statement: ε₀ = nfp (fun a => ω ^ a) 0
  proof: by
  rw [epsilon_eq_deriv]; rw [deriv_zero_right]

@[deprecated (since := "2026-02-02")]
alias epsilon0_eq_nfp := epsilon_zero_eq_nfp

中文:
定理 epsilon_zero_eq_nfp
  结论: ε₀ = nfp (fun a => ω ^ a) 0
  证明: by
  rw [epsilon_eq_deriv]; rw [deriv_zero_right]

@[deprecated (since := "2026-02-02")]
alias epsilon0_eq_nfp := epsilon_zero_eq_nfp

Depends on / 依赖: deriv_zero_right, epsilon_eq_deriv
-/
theorem epsilon_zero_eq_nfp : ε₀ = nfp (fun a => ω ^ a) 0 := by
  rw [epsilon_eq_deriv]; rw [deriv_zero_right]

@[deprecated (since := "2026-02-02")]
alias epsilon0_eq_nfp := epsilon_zero_eq_nfp

/--
theorem `epsilon_succ_eq_nfp` / 定理 `epsilon_succ_eq_nfp`

English:
theorem epsilon_succ_eq_nfp
  given: (o : Ordinal)
  statement: ε_ (succ o) = nfp (fun a => ω ^ a) (succ (ε_ o))
  proof: by
  rw [epsilon_eq_deriv]; rw [epsilon_eq_deriv]; rw [deriv_succ]

中文:
定理 epsilon_succ_eq_nfp
  条件: (o : 序数)
  结论: ε_ (succ o) = nfp (fun a => ω ^ a) (succ (ε_ o))
  证明: by
  rw [epsilon_eq_deriv]; rw [epsilon_eq_deriv]; rw [deriv_succ]

Depends on / 依赖: deriv_succ, epsilon_eq_deriv
-/
theorem epsilon_succ_eq_nfp (o : Ordinal) : ε_ (succ o) = nfp (fun a => ω ^ a) (succ (ε_ o)) := by
  rw [epsilon_eq_deriv]; rw [epsilon_eq_deriv]; rw [deriv_succ]

/--
theorem `epsilon_zero_le_of_omega0_opow_le` / 定理 `epsilon_zero_le_of_omega0_opow_le`

English:
theorem epsilon_zero_le_of_omega0_opow_le
  given: (h : ω ^ o <= o)
  statement: ε₀ <= o
  proof: by
  rw [epsilon_zero_eq_nfp]
  exact nfp_le_fp (fun _ _ => (opow_le_opow_iff_right one_lt_omega0).2) zero_le h

@[deprecated (since := "2026-02-02")]
alias epsilon0_le_of_omega0_opow_le := epsilon_zero_le_of_omega0_opow_le

@[simp]

中文:
定理 epsilon_zero_le_of_omega0_opow_le
  条件: (h : ω ^ o <= o)
  结论: ε₀ <= o
  证明: by
  rw [epsilon_zero_eq_nfp]
  exact nfp_le_fp (fun _ _ => (opow_le_opow_iff_right one_lt_omega0).2) zero_le h

@[deprecated (since := "2026-02-02")]
alias epsilon0_le_of_omega0_opow_le := epsilon_zero_le_of_omega0_opow_le

@[simp]

Depends on / 依赖: epsilon_zero_eq_nfp, nfp_le_fp, one_lt_omega0, opow_le_opow_iff_right, zero_le
-/
theorem epsilon_zero_le_of_omega0_opow_le (h : ω ^ o <= o) : ε₀ <= o := by
  rw [epsilon_zero_eq_nfp]
  exact nfp_le_fp (fun _ _ => (opow_le_opow_iff_right one_lt_omega0).2) zero_le h

@[deprecated (since := "2026-02-02")]
alias epsilon0_le_of_omega0_opow_le := epsilon_zero_le_of_omega0_opow_le

@[simp]
/--
theorem `omega0_opow_epsilon` / 定理 `omega0_opow_epsilon`

English:
theorem omega0_opow_epsilon
  given: (o : Ordinal)
  statement: ω ^ ε_ o = ε_ o
  proof: by
  rw [epsilon_eq_deriv]; rw [deriv_fp (isNormal_opow one_lt_omega0)]

中文:
定理 omega0_opow_epsilon
  条件: (o : 序数)
  结论: ω ^ ε_ o = ε_ o
  证明: by
  rw [epsilon_eq_deriv]; rw [deriv_fp (isNormal_opow one_lt_omega0)]

Depends on / 依赖: deriv_fp, epsilon_eq_deriv, isNormal_opow, one_lt_omega0
-/
theorem omega0_opow_epsilon (o : Ordinal) : ω ^ ε_ o = ε_ o := by
  rw [epsilon_eq_deriv]; rw [deriv_fp (isNormal_opow one_lt_omega0)]

/--
theorem `lt_epsilon_zero` / 定理 `lt_epsilon_zero`

English:
theorem lt_epsilon_zero
  statement: o < ε₀ ↔ exists n : Nat, o < (fun a => ω ^ a)^[n] 0
  proof: by
  rw [epsilon_zero_eq_nfp]; rw [lt_nfp_iff]

@[deprecated (since := "2026-02-02")]
alias lt_epsilon0 := lt_epsilon_zero

中文:
定理 lt_epsilon_zero
  结论: o < ε₀ ↔ 存在 n : 自然数, o < (fun a => ω ^ a)^[n] 0
  证明: by
  rw [epsilon_zero_eq_nfp]; rw [lt_nfp_iff]

@[deprecated (since := "2026-02-02")]
alias lt_epsilon0 := lt_epsilon_zero

Depends on / 依赖: epsilon_zero_eq_nfp, lt_nfp_iff
-/
theorem lt_epsilon_zero : o < ε₀ ↔ exists n : Nat, o < (fun a => ω ^ a)^[n] 0 := by
  rw [epsilon_zero_eq_nfp]; rw [lt_nfp_iff]

@[deprecated (since := "2026-02-02")]
alias lt_epsilon0 := lt_epsilon_zero

/--
theorem `iterate_omega0_opow_lt_epsilon_zero` / 定理 `iterate_omega0_opow_lt_epsilon_zero`

English:
theorem iterate_omega0_opow_lt_epsilon_zero
  given: (n : Nat)
  statement: (fun a => ω ^ a)^[n] 0 < ε₀
  proof: by
  rw [epsilon_zero_eq_nfp]
  apply iterate_lt_nfp (isNormal_opow one_lt_omega0).strictMono
  simp

@[deprecated (since := "2026-02-02")]
alias iterate_omega0_opow_lt_epsilon0 := iterate_omega0_opow_lt_epsilon_zero

中文:
定理 iterate_omega0_opow_lt_epsilon_zero
  条件: (n : 自然数)
  结论: (fun a => ω ^ a)^[n] 0 < ε₀
  证明: by
  rw [epsilon_zero_eq_nfp]
  apply iterate_lt_nfp (isNormal_opow one_lt_omega0).strictMono
  simp

@[deprecated (since := "2026-02-02")]
alias iterate_omega0_opow_lt_epsilon0 := iterate_omega0_opow_lt_epsilon_zero

Depends on / 依赖: epsilon_zero_eq_nfp, isNormal_opow, iterate_lt_nfp, one_lt_omega0, strictMono
-/
theorem iterate_omega0_opow_lt_epsilon_zero (n : Nat) : (fun a => ω ^ a)^[n] 0 < ε₀ := by
  rw [epsilon_zero_eq_nfp]
  apply iterate_lt_nfp (isNormal_opow one_lt_omega0).strictMono
  simp

@[deprecated (since := "2026-02-02")]
alias iterate_omega0_opow_lt_epsilon0 := iterate_omega0_opow_lt_epsilon_zero

/--
theorem `omega0_lt_epsilon` / 定理 `omega0_lt_epsilon`

English:
theorem omega0_lt_epsilon
  given: (o : Ordinal)
  statement: ω < ε_ o
  proof: by
apply lt_of_lt_of_le _ (veblen_right_strictMono _).monotone zero_le
  simpa using iterate_omega0_opow_lt_epsilon_zero 2

中文:
定理 omega0_lt_epsilon
  条件: (o : 序数)
  结论: ω < ε_ o
  证明: by
apply lt_of_lt_of_le _ (veblen_right_strictMono _).monotone zero_le
  simpa using iterate_omega0_opow_lt_epsilon_zero 2

Depends on / 依赖: iterate_omega0_opow_lt_epsilon_zero, lt_of_lt_of_le, monotone, veblen_right_strictMono, zero_le
-/
theorem omega0_lt_epsilon (o : Ordinal) : ω < ε_ o := by
apply lt_of_lt_of_le _ (veblen_right_strictMono _).monotone zero_le
  simpa using iterate_omega0_opow_lt_epsilon_zero 2

/--
theorem `natCast_lt_epsilon` / 定理 `natCast_lt_epsilon`

English:
theorem natCast_lt_epsilon
  given: (n : Nat) (o : Ordinal)
  statement: n < ε_ o
  proof: (natCast_lt_omega0 n).trans omega0_lt_epsilon o

中文:
定理 natCast_lt_epsilon
  条件: (n : 自然数) (o : 序数)
  结论: n < ε_ o
  证明: (natCast_lt_omega0 n).trans omega0_lt_epsilon o

Depends on / 依赖: natCast_lt_omega0, omega0_lt_epsilon
-/
theorem natCast_lt_epsilon (n : Nat) (o : Ordinal) : n < ε_ o :=
(natCast_lt_omega0 n).trans omega0_lt_epsilon o

/--
theorem `epsilon_pos` / 定理 `epsilon_pos`

English:
theorem epsilon_pos
  given: (o : Ordinal)
  statement: 0 < ε_ o
  proof: veblen_pos

中文:
定理 epsilon_pos
  条件: (o : 序数)
  结论: 0 < ε_ o
  证明: veblen_pos

Depends on / 依赖: veblen_pos
-/
theorem epsilon_pos (o : Ordinal) : 0 < ε_ o :=
  veblen_pos

/--
theorem `invVeblen₁_epsilon` / 定理 `invVeblen₁_epsilon`

English:
theorem invVeblen₁_epsilon
  given: (h : o < ε_ o)
  statement: invVeblen₁ (ε_ o) = 1
  proof: invVeblen₁_veblen h

中文:
定理 invVeblen₁_epsilon
  条件: (h : o < ε_ o)
  结论: invVeblen₁ (ε_ o) = 1
  证明: invVeblen₁_veblen h
-/
theorem invVeblen₁_epsilon (h : o < ε_ o) : invVeblen₁ (ε_ o) = 1 :=
  invVeblen₁_veblen h

/--
theorem `invVeblen₂_epsilon` / 定理 `invVeblen₂_epsilon`

English:
theorem invVeblen₂_epsilon
  given: (h : o < ε_ o)
  statement: invVeblen₂ (ε_ o) = o
  proof: invVeblen₂_veblen one_ne_zero h

中文:
定理 invVeblen₂_epsilon
  条件: (h : o < ε_ o)
  结论: invVeblen₂ (ε_ o) = o
  证明: invVeblen₂_veblen one_ne_zero h

Depends on / 依赖: one_ne_zero
-/
theorem invVeblen₂_epsilon (h : o < ε_ o) : invVeblen₂ (ε_ o) = o :=
  invVeblen₂_veblen one_ne_zero h

/-! ### Gamma function -/

/--
Definition of `gamma` / `gamma` 的定义

English:
definition gamma
  signature: : Ordinal -> Ordinal
  body: deriv (veblen · 0)

@[inherit_doc] scoped notation "Γ_ " => gamma
recommended_spelling "gamma" for "Γ_ " in [gamma, «termΓ_»]

中文:
定义 gamma
  签名: : 序数 -> 序数
  定义体: deriv (veblen · 0)

@[inherit_doc] scoped notation "Γ_ " => gamma
recommended_spelling "gamma" for "Γ_ " in [gamma, «termΓ_»]

Depends on / 依赖: veblen
-/
def gamma : Ordinal -> Ordinal :=
  deriv (veblen · 0)

@[inherit_doc] scoped notation "Γ_ " => gamma
recommended_spelling "gamma" for "Γ_ " in [gamma, «termΓ_»]

/-- The Feferman-Schütte ordinal `Γ₀` is the smallest fixed point of `veblen · 0`, i.e. the supremum
of `veblen ε₀ 0`, `veblen (veblen ε₀ 0) 0`, etc. -/
scoped notation "Γ₀" => Γ_ 0
recommended_spelling "gamma_zero" for "Γ₀" in [«termΓ₀»]

/--
theorem `isNormal_gamma` / 定理 `isNormal_gamma`

English:
theorem isNormal_gamma
  statement: IsNormal gamma
  proof: isNormal_deriv _

中文:
定理 isNormal_gamma
  结论: 是正规 gamma
  证明: isNormal_deriv _

Depends on / 依赖: isNormal_deriv
-/
theorem isNormal_gamma : IsNormal gamma :=
  isNormal_deriv _

/--
theorem `mem_range_gamma` / 定理 `mem_range_gamma`

English:
theorem mem_range_gamma
  statement: o in range Γ_ ↔ veblen o 0 = o
  proof: mem_range_deriv isNormal_veblen_zero

中文:
定理 mem_range_gamma
  结论: o in range Γ_ ↔ veblen o 0 = o
  证明: mem_range_deriv isNormal_veblen_zero

Depends on / 依赖: isNormal_veblen_zero, mem_range_deriv
-/
theorem mem_range_gamma : o in range Γ_ ↔ veblen o 0 = o :=
  mem_range_deriv isNormal_veblen_zero

/--
theorem `strictMono_gamma` / 定理 `strictMono_gamma`

English:
theorem strictMono_gamma
  statement: StrictMono gamma
  proof: isNormal_gamma.strictMono

中文:
定理 strictMono_gamma
  结论: 严格递增 gamma
  证明: isNormal_gamma.strictMono

Depends on / 依赖: isNormal_gamma, isNormal_gamma.strictMono, strictMono
-/
theorem strictMono_gamma : StrictMono gamma :=
  isNormal_gamma.strictMono

/--
theorem `monotone_gamma` / 定理 `monotone_gamma`

English:
theorem monotone_gamma
  statement: Monotone gamma
  proof: isNormal_gamma.monotone

@[simp]

中文:
定理 monotone_gamma
  结论: 递增 gamma
  证明: isNormal_gamma.monotone

@[simp]

Depends on / 依赖: isNormal_gamma, isNormal_gamma.monotone, monotone
-/
theorem monotone_gamma : Monotone gamma :=
  isNormal_gamma.monotone

@[simp]
/--
theorem `gamma_lt_gamma` / 定理 `gamma_lt_gamma`

English:
theorem gamma_lt_gamma
  statement: Γ_ a < Γ_ b ↔ a < b
  proof: strictMono_gamma.lt_iff_lt

@[simp]

中文:
定理 gamma_lt_gamma
  结论: Γ_ a < Γ_ b ↔ a < b
  证明: strictMono_gamma.lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, strictMono_gamma, strictMono_gamma.lt_iff_lt
-/
theorem gamma_lt_gamma : Γ_ a < Γ_ b ↔ a < b :=
  strictMono_gamma.lt_iff_lt

@[simp]
/--
theorem `gamma_le_gamma` / 定理 `gamma_le_gamma`

English:
theorem gamma_le_gamma
  statement: Γ_ a <= Γ_ b ↔ a <= b
  proof: strictMono_gamma.le_iff_le

@[simp]

中文:
定理 gamma_le_gamma
  结论: Γ_ a <= Γ_ b ↔ a <= b
  证明: strictMono_gamma.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, strictMono_gamma, strictMono_gamma.le_iff_le
-/
theorem gamma_le_gamma : Γ_ a <= Γ_ b ↔ a <= b :=
  strictMono_gamma.le_iff_le

@[simp]
/--
theorem `gamma_inj` / 定理 `gamma_inj`

English:
theorem gamma_inj
  statement: Γ_ a = Γ_ b ↔ a = b
  proof: strictMono_gamma.injective.eq_iff

@[simp]

中文:
定理 gamma_inj
  结论: Γ_ a = Γ_ b ↔ a = b
  证明: strictMono_gamma.injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, injective, strictMono_gamma, strictMono_gamma.injective.eq_iff
-/
theorem gamma_inj : Γ_ a = Γ_ b ↔ a = b :=
  strictMono_gamma.injective.eq_iff

@[simp]
/--
theorem `veblen_gamma_zero` / 定理 `veblen_gamma_zero`

English:
theorem veblen_gamma_zero
  given: (o : Ordinal)
  statement: veblen (Γ_ o) 0 = Γ_ o
  proof: deriv_fp isNormal_veblen_zero o

中文:
定理 veblen_gamma_zero
  条件: (o : 序数)
  结论: veblen (Γ_ o) 0 = Γ_ o
  证明: deriv_fp isNormal_veblen_zero o

Depends on / 依赖: deriv_fp, isNormal_veblen_zero
-/
theorem veblen_gamma_zero (o : Ordinal) : veblen (Γ_ o) 0 = Γ_ o :=
  deriv_fp isNormal_veblen_zero o

/--
theorem `gamma_zero_eq_nfp` / 定理 `gamma_zero_eq_nfp`

English:
theorem gamma_zero_eq_nfp
  statement: Γ₀ = nfp (veblen · 0) 0
  proof: deriv_zero_right _

@[deprecated (since := "2026-02-02")]
alias gamma0_eq_nfp := gamma_zero_eq_nfp

中文:
定理 gamma_zero_eq_nfp
  结论: Γ₀ = nfp (veblen · 0) 0
  证明: deriv_zero_right _

@[deprecated (since := "2026-02-02")]
alias gamma0_eq_nfp := gamma_zero_eq_nfp

Depends on / 依赖: deriv_zero_right
-/
theorem gamma_zero_eq_nfp : Γ₀ = nfp (veblen · 0) 0 :=
  deriv_zero_right _

@[deprecated (since := "2026-02-02")]
alias gamma0_eq_nfp := gamma_zero_eq_nfp

/--
theorem `gamma_succ_eq_nfp` / 定理 `gamma_succ_eq_nfp`

English:
theorem gamma_succ_eq_nfp
  given: (o : Ordinal)
  statement: Γ_ (succ o) = nfp (veblen · 0) (succ (Γ_ o))
  proof: deriv_succ _ _

中文:
定理 gamma_succ_eq_nfp
  条件: (o : 序数)
  结论: Γ_ (succ o) = nfp (veblen · 0) (succ (Γ_ o))
  证明: deriv_succ _ _

Depends on / 依赖: deriv_succ
-/
theorem gamma_succ_eq_nfp (o : Ordinal) : Γ_ (succ o) = nfp (veblen · 0) (succ (Γ_ o)) :=
  deriv_succ _ _

/--
theorem `gamma_zero_le_of_veblen_le` / 定理 `gamma_zero_le_of_veblen_le`

English:
theorem gamma_zero_le_of_veblen_le
  given: (h : veblen o 0 <= o)
  statement: Γ₀ <= o
  proof: by
  rw [gamma_zero_eq_nfp]
  exact nfp_le_fp (veblen_left_monotone 0) zero_le h

@[deprecated (since := "2026-02-02")]
alias gamma0_le_of_veblen_le := gamma_zero_le_of_veblen_le

中文:
定理 gamma_zero_le_of_veblen_le
  条件: (h : veblen o 0 <= o)
  结论: Γ₀ <= o
  证明: by
  rw [gamma_zero_eq_nfp]
  exact nfp_le_fp (veblen_left_monotone 0) zero_le h

@[deprecated (since := "2026-02-02")]
alias gamma0_le_of_veblen_le := gamma_zero_le_of_veblen_le

Depends on / 依赖: gamma_zero_eq_nfp, nfp_le_fp, veblen_left_monotone, zero_le
-/
theorem gamma_zero_le_of_veblen_le (h : veblen o 0 <= o) : Γ₀ <= o := by
  rw [gamma_zero_eq_nfp]
  exact nfp_le_fp (veblen_left_monotone 0) zero_le h

@[deprecated (since := "2026-02-02")]
alias gamma0_le_of_veblen_le := gamma_zero_le_of_veblen_le

/--
theorem `lt_gamma_zero` / 定理 `lt_gamma_zero`

English:
theorem lt_gamma_zero
  statement: o < Γ₀ ↔ exists n : Nat, o < (fun a => veblen a 0)^[n] 0
  proof: by
  rw [gamma_zero_eq_nfp]; rw [lt_nfp_iff]

@[deprecated (since := "2026-02-02")]
alias lt_gamma0 := lt_gamma_zero

中文:
定理 lt_gamma_zero
  结论: o < Γ₀ ↔ 存在 n : 自然数, o < (fun a => veblen a 0)^[n] 0
  证明: by
  rw [gamma_zero_eq_nfp]; rw [lt_nfp_iff]

@[deprecated (since := "2026-02-02")]
alias lt_gamma0 := lt_gamma_zero

Depends on / 依赖: gamma_zero_eq_nfp, lt_nfp_iff
-/
theorem lt_gamma_zero : o < Γ₀ ↔ exists n : Nat, o < (fun a => veblen a 0)^[n] 0 := by
  rw [gamma_zero_eq_nfp]; rw [lt_nfp_iff]

@[deprecated (since := "2026-02-02")]
alias lt_gamma0 := lt_gamma_zero

/--
theorem `iterate_veblen_lt_gamma_zero` / 定理 `iterate_veblen_lt_gamma_zero`

English:
theorem iterate_veblen_lt_gamma_zero
  given: (n : Nat)
  statement: (fun a => veblen a 0)^[n] 0 < Γ₀
  proof: by
  rw [gamma_zero_eq_nfp]
  apply iterate_lt_nfp veblen_zero_strictMono
  simp

@[deprecated (since := "2026-02-02")]
alias iterate_veblen_lt_gamma0 := iterate_veblen_lt_gamma_zero

中文:
定理 iterate_veblen_lt_gamma_zero
  条件: (n : 自然数)
  结论: (fun a => veblen a 0)^[n] 0 < Γ₀
  证明: by
  rw [gamma_zero_eq_nfp]
  apply iterate_lt_nfp veblen_zero_strictMono
  simp

@[deprecated (since := "2026-02-02")]
alias iterate_veblen_lt_gamma0 := iterate_veblen_lt_gamma_zero

Depends on / 依赖: gamma_zero_eq_nfp, iterate_lt_nfp, veblen_zero_strictMono
-/
theorem iterate_veblen_lt_gamma_zero (n : Nat) : (fun a => veblen a 0)^[n] 0 < Γ₀ := by
  rw [gamma_zero_eq_nfp]
  apply iterate_lt_nfp veblen_zero_strictMono
  simp

@[deprecated (since := "2026-02-02")]
alias iterate_veblen_lt_gamma0 := iterate_veblen_lt_gamma_zero

/--
theorem `epsilon_zero_lt_gamma` / 定理 `epsilon_zero_lt_gamma`

English:
theorem epsilon_zero_lt_gamma
  given: (o : Ordinal)
  statement: ε₀ < Γ_ o
  proof: by
  apply (gamma_le_gamma.2 zero_le).trans_lt'
  simpa using iterate_veblen_lt_gamma_zero 2

@[deprecated (since := "2026-02-02")]
alias epsilon0_lt_gamma := epsilon_zero_lt_gamma

中文:
定理 epsilon_zero_lt_gamma
  条件: (o : 序数)
  结论: ε₀ < Γ_ o
  证明: by
  apply (gamma_le_gamma.2 zero_le).trans_lt'
  simpa using iterate_veblen_lt_gamma_zero 2

@[deprecated (since := "2026-02-02")]
alias epsilon0_lt_gamma := epsilon_zero_lt_gamma

Depends on / 依赖: gamma_le_gamma, iterate_veblen_lt_gamma_zero, trans_lt, zero_le
-/
theorem epsilon_zero_lt_gamma (o : Ordinal) : ε₀ < Γ_ o := by
  apply (gamma_le_gamma.2 zero_le).trans_lt'
  simpa using iterate_veblen_lt_gamma_zero 2

@[deprecated (since := "2026-02-02")]
alias epsilon0_lt_gamma := epsilon_zero_lt_gamma

/--
theorem `omega0_lt_gamma` / 定理 `omega0_lt_gamma`

English:
theorem omega0_lt_gamma
  given: (o : Ordinal)
  statement: ω < Γ_ o
  proof: (omega0_lt_epsilon 0).trans (epsilon_zero_lt_gamma o)

中文:
定理 omega0_lt_gamma
  条件: (o : 序数)
  结论: ω < Γ_ o
  证明: (omega0_lt_epsilon 0).trans (epsilon_zero_lt_gamma o)

Depends on / 依赖: epsilon_zero_lt_gamma, omega0_lt_epsilon
-/
theorem omega0_lt_gamma (o : Ordinal) : ω < Γ_ o :=
  (omega0_lt_epsilon 0).trans (epsilon_zero_lt_gamma o)

/--
theorem `natCast_lt_gamma` / 定理 `natCast_lt_gamma`

English:
theorem natCast_lt_gamma
  given: (n : Nat)
  statement: n < Γ_ o
  proof: (natCast_lt_omega0 n).trans (omega0_lt_gamma o)

@[simp]

中文:
定理 natCast_lt_gamma
  条件: (n : 自然数)
  结论: n < Γ_ o
  证明: (natCast_lt_omega0 n).trans (omega0_lt_gamma o)

@[simp]

Depends on / 依赖: natCast_lt_omega0, omega0_lt_gamma
-/
theorem natCast_lt_gamma (n : Nat) : n < Γ_ o :=
  (natCast_lt_omega0 n).trans (omega0_lt_gamma o)

@[simp]
/--
theorem `gamma_pos` / 定理 `gamma_pos`

English:
theorem gamma_pos
  statement: 0 < Γ_ o
  proof: natCast_lt_gamma 0

@[simp]

中文:
定理 gamma_pos
  结论: 0 < Γ_ o
  证明: natCast_lt_gamma 0

@[simp]

Depends on / 依赖: natCast_lt_gamma
-/
theorem gamma_pos : 0 < Γ_ o :=
  natCast_lt_gamma 0

@[simp]
/--
theorem `gamma_ne_zero` / 定理 `gamma_ne_zero`

English:
theorem gamma_ne_zero
  statement: Γ_ o != 0
  proof: gamma_pos.ne'

@[simp]

中文:
定理 gamma_ne_zero
  结论: Γ_ o != 0
  证明: gamma_pos.ne'

@[simp]

Depends on / 依赖: gamma_pos, gamma_pos.ne
-/
theorem gamma_ne_zero : Γ_ o != 0 :=
  gamma_pos.ne'

@[simp]
/--
theorem `invVeblen₁_gamma` / 定理 `invVeblen₁_gamma`

English:
theorem invVeblen₁_gamma
  given: (o : Ordinal)
  statement: invVeblen₁ (Γ_ o) = Γ_ o
  proof: by
  rw [← veblen_gamma_zero]; rw [invVeblen₁_veblen veblen_pos]; rw [veblen_gamma_zero]

@[simp]

中文:
定理 invVeblen₁_gamma
  条件: (o : 序数)
  结论: invVeblen₁ (Γ_ o) = Γ_ o
  证明: by
  rw [← veblen_gamma_zero]; rw [invVeblen₁_veblen veblen_pos]; rw [veblen_gamma_zero]

@[simp]

Depends on / 依赖: veblen_gamma_zero, veblen_pos
-/
theorem invVeblen₁_gamma (o : Ordinal) : invVeblen₁ (Γ_ o) = Γ_ o := by
  rw [← veblen_gamma_zero]; rw [invVeblen₁_veblen veblen_pos]; rw [veblen_gamma_zero]

@[simp]
/--
theorem `invVeblen₂_gamma` / 定理 `invVeblen₂_gamma`

English:
theorem invVeblen₂_gamma
  given: (o : Ordinal)
  statement: invVeblen₂ (Γ_ o) = 0
  proof: by
  rw [← veblen_gamma_zero]; rw [invVeblen₂_veblen gamma_ne_zero veblen_pos]

中文:
定理 invVeblen₂_gamma
  条件: (o : 序数)
  结论: invVeblen₂ (Γ_ o) = 0
  证明: by
  rw [← veblen_gamma_zero]; rw [invVeblen₂_veblen gamma_ne_zero veblen_pos]

Depends on / 依赖: gamma_ne_zero, veblen_gamma_zero, veblen_pos
-/
theorem invVeblen₂_gamma (o : Ordinal) : invVeblen₂ (Γ_ o) = 0 := by
  rw [← veblen_gamma_zero]; rw [invVeblen₂_veblen gamma_ne_zero veblen_pos]

/--
theorem `invVeblen₁_eq_iff` / 定理 `invVeblen₁_eq_iff`

English:
theorem invVeblen₁_eq_iff
  statement: invVeblen₁ o = o ↔ o = 0 ∨ o in range Γ_
  proof: by
  constructor
  · rw [mem_range_gamma, or_iff_not_imp_left]
    refine fun h ho => (left_le_veblen ..).antisymm' ?_
    conv_rhs => rw [← veblen_eq_of_lt_invVeblen₁ (h.trans_ne ho).bot_lt, bot_eq_zero,
      veblen_zero_apply, ← veblen_invVeblen₁_invVeblen₂, h]
    simp
  · aesop

中文:
定理 invVeblen₁_eq_iff
  结论: invVeblen₁ o = o ↔ o = 0 ∨ o in range Γ_
  证明: by
  constructor
  · rw [mem_range_gamma, or_iff_not_imp_left]
    refine fun h ho => (left_le_veblen ..).antisymm' ?_
    conv_rhs => rw [← veblen_eq_of_lt_invVeblen₁ (h.trans_ne ho).bot_lt, bot_eq_zero,
      veblen_zero_apply, ← veblen_invVeblen₁_invVeblen₂, h]
    simp
  · aesop

Depends on / 依赖: antisymm, bot_eq_zero, bot_lt, conv_rhs, h.trans_ne, left_le_veblen, mem_range_gamma, or_iff_not_imp_left, trans_ne, veblen_zero_apply
-/
theorem invVeblen₁_eq_iff : invVeblen₁ o = o ↔ o = 0 ∨ o in range Γ_ := by
  constructor
  · rw [mem_range_gamma, or_iff_not_imp_left]
    refine fun h ho => (left_le_veblen ..).antisymm' ?_
    conv_rhs => rw [← veblen_eq_of_lt_invVeblen₁ (h.trans_ne ho).bot_lt, bot_eq_zero,
      veblen_zero_apply, ← veblen_invVeblen₁_invVeblen₂, h]
    simp
  · aesop

/--
theorem `invVeblen₁_lt_iff` / 定理 `invVeblen₁_lt_iff`

English:
theorem invVeblen₁_lt_iff
  statement: invVeblen₁ o < o ↔ o != 0 ∧ o ∉ range Γ_
  proof: by
  rw [(invVeblen₁_le o).lt_iff_ne]; rw [ne_eq]; rw [invVeblen₁_eq_iff]; rw [not_or]

中文:
定理 invVeblen₁_lt_iff
  结论: invVeblen₁ o < o ↔ o != 0 ∧ o ∉ range Γ_
  证明: by
  rw [(invVeblen₁_le o).lt_iff_ne]; rw [ne_eq]; rw [invVeblen₁_eq_iff]; rw [not_or]

Depends on / 依赖: lt_iff_ne, ne_eq, not_or
-/
theorem invVeblen₁_lt_iff : invVeblen₁ o < o ↔ o != 0 ∧ o ∉ range Γ_ := by
  rw [(invVeblen₁_le o).lt_iff_ne]; rw [ne_eq]; rw [invVeblen₁_eq_iff]; rw [not_or]

end Ordinal
