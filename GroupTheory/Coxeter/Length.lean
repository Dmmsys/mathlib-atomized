/-
Copyright (c) 2024 Mitchell Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Lee
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Zify

/-!
# The length function, reduced words, and descents

Throughout this file, `B` is a type and `M : CoxeterMatrix B` is a Coxeter matrix.
`cs : CoxeterSystem M W` is a Coxeter system; that is, `W` is a group, and `cs` holds the data
of a group isomorphism `W ≃* M.group`, where `M.group` refers to the quotient of the free group on
`B` by the Coxeter relations given by the matrix `M`. See `Mathlib/GroupTheory/Coxeter/Basic.lean`
for more details.

Given any element $w \in W$, its *length* (`CoxeterSystem.length`), denoted $\ell(w)$, is the
minimum number $\ell$ such that $w$ can be written as a product of a sequence of $\ell$ simple
reflections:
$$w = s_{i_1} \cdots s_{i_\ell}.$$
We prove for all $w_1, w_2 \in W$ that $\ell (w_1 w_2) \leq \ell (w_1) + \ell (w_2)$
and that $\ell (w_1 w_2)$ has the same parity as $\ell (w_1) + \ell (w_2)$.

We define a *reduced word* (`CoxeterSystem.IsReduced`) for an element $w \in W$ to be a way of
writing $w$ as a product of exactly $\ell(w)$ simple reflections. Every element of $W$ has a reduced
word.

We say that $i \in B$ is a *left descent* (`CoxeterSystem.IsLeftDescent`) of $w \in W$ if
$\ell(s_i w) < \ell(w)$. We show that if $i$ is a left descent of $w$, then
$\ell(s_i w) + 1 = \ell(w)$. On the other hand, if $i$ is not a left descent of $w$, then
$\ell(s_i w) = \ell(w) + 1$. We similarly define right descents (`CoxeterSystem.IsRightDescent`) and
prove analogous results.

## Main definitions

* `cs.length`
* `cs.IsReduced`
* `cs.IsLeftDescent`
* `cs.IsRightDescent`

## References

* [A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005)

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CoxeterSystem

open List Matrix Function

variable {B W : Type*} [Group W]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple
local prefix:100 "π " => cs.wordProd


/--
theorem `exists_word_with_prod` / 定理 `exists_word_with_prod`

English:
theorem exists_word_with_prod
  given: (w : W)
  statement: exists n ω, n = ω.length ∧ π ω = w
  proof: by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω

中文:
定理 存在_word_with_prod
  条件: (w : W)
  结论: 存在 n ω, n = ω.length ∧ π ω = w
  证明: by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω
-/
private theorem exists_word_with_prod (w : W) : exists n ω, n = ω.length ∧ π ω = w := by
  rcases cs.wordProd_surjective w with ⟨ω, rfl⟩
  use ω.length, ω

open scoped Classical in
/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: (w : W)
  body: Nat.find (cs.exists_word_with_prod w)

local prefix:100 "ℓ " => cs.length

中文:
定义 length
  签名: (w : W)
  定义体: Nat.find (cs.exists_word_with_prod w)

local prefix:100 "ℓ " => cs.length
-/
@[no_expose] noncomputable def length (w : W) : Nat := Nat.find (cs.exists_word_with_prod w)

local prefix:100 "ℓ " => cs.length

/--
Definition of `IsReduced` / `IsReduced` 的定义

English:
definition IsReduced
  signature: (ω : List B)
  body: ℓ (π ω) = ω.length

中文:
定义 是既约
  签名: (ω : 列表 B)
  定义体: ℓ (π ω) = ω.length

Depends on / 依赖: length
-/
def IsReduced (ω : List B) : Prop := ℓ (π ω) = ω.length

/--
theorem `IsReduced.eq` / 定理 `IsReduced.eq`

English:
theorem IsReduced.eq
  given: {ω : List B} (hω : cs.IsReduced ω)
  statement: ℓ (π ω) = ω.length
  proof: hω

中文:
定理 是既约.eq
  条件: {ω : 列表 B} (hω : cs.是既约 ω)
  结论: ℓ (π ω) = ω.length
  证明: hω
-/
theorem IsReduced.eq {ω : List B} (hω : cs.IsReduced ω) : ℓ (π ω) = ω.length := hω

/--
theorem `exists_isReduced` / 定理 `exists_isReduced`

English:
theorem exists_isReduced
  given: (w : W)
  statement: exists ω : List B, cs.IsReduced ω ∧ w = π ω
  proof: by
  classical
  obtain ⟨ω, hω, rfl⟩ := Nat.find_spec (cs.exists_word_with_prod w)
  exact ⟨ω, hω, rfl⟩

@[deprecated (since := "2026-03-25")] alias exists_reduced_word := exists_isReduced
@[deprecated (since := "2026-03-25")] alias exists_reduced_word' := exists_isReduced

中文:
定理 存在_isReduced
  条件: (w : W)
  结论: 存在 ω : 列表 B, cs.是既约 ω ∧ w = π ω
  证明: by
  classical
  obtain ⟨ω, hω, rfl⟩ := Nat.find_spec (cs.exists_word_with_prod w)
  exact ⟨ω, hω, rfl⟩

@[deprecated (since := "2026-03-25")] alias exists_reduced_word := exists_isReduced
@[deprecated (since := "2026-03-25")] alias exists_reduced_word' := exists_isReduced

Depends on / 依赖: Nat.find_spec, classical, cs.exists_word_with_prod, exists_word_with_prod, find_spec
-/
theorem exists_isReduced (w : W) : exists ω : List B, cs.IsReduced ω ∧ w = π ω := by
  classical
  obtain ⟨ω, hω, rfl⟩ := Nat.find_spec (cs.exists_word_with_prod w)
  exact ⟨ω, hω, rfl⟩

@[deprecated (since := "2026-03-25")] alias exists_reduced_word := exists_isReduced
@[deprecated (since := "2026-03-25")] alias exists_reduced_word' := exists_isReduced

/--
theorem `length_wordProd_le` / 定理 `length_wordProd_le`

English:
theorem length_wordProd_le
  given: (ω : List B)
  statement: ℓ (π ω) <= ω.length
  proof: by
  classical
  exact Nat.find_min' (cs.exists_word_with_prod (π ω)) ⟨ω, rfl, rfl⟩

中文:
定理 length_wordProd_le
  条件: (ω : 列表 B)
  结论: ℓ (π ω) <= ω.length
  证明: by
  classical
  exact Nat.find_min' (cs.exists_word_with_prod (π ω)) ⟨ω, rfl, rfl⟩

Depends on / 依赖: Nat.find_min, classical, cs.exists_word_with_prod, exists_word_with_prod, find_min
-/
theorem length_wordProd_le (ω : List B) : ℓ (π ω) <= ω.length := by
  classical
  exact Nat.find_min' (cs.exists_word_with_prod (π ω)) ⟨ω, rfl, rfl⟩

/--
theorem `length_one` / 定理 `length_one`

English:
theorem length_one
  statement: ℓ (1 : W) = 0
  proof: Nat.eq_zero_of_le_zero (cs.length_wordProd_le [])

@[simp]

中文:
定理 length_one
  结论: ℓ (1 : W) = 0
  证明: Nat.eq_zero_of_le_zero (cs.length_wordProd_le [])

@[simp]
-/
@[simp] theorem length_one : ℓ (1 : W) = 0 := Nat.eq_zero_of_le_zero (cs.length_wordProd_le [])

@[simp]
/--
theorem `length_eq_zero_iff` / 定理 `length_eq_zero_iff`

English:
theorem length_eq_zero_iff
  given: {w : W}
  statement: ℓ w = 0 ↔ w = 1
  proof: by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have : ω = [] := eq_nil_of_length_eq_zero (hω.symm.trans h)
    rw [this]; rw [wordProd_nil]
  · rintro rfl
    exact cs.length_one

@[simp]

中文:
定理 length_eq_zero_iff
  条件: {w : W}
  结论: ℓ w = 0 ↔ w = 1
  证明: by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have : ω = [] := eq_nil_of_length_eq_zero (hω.symm.trans h)
    rw [this]; rw [wordProd_nil]
  · rintro rfl
    exact cs.length_one

@[simp]

Depends on / 依赖: cs.exists_isReduced, cs.length_one, eq_nil_of_length_eq_zero, exists_isReduced, length_one, symm.trans, wordProd_nil
-/
theorem length_eq_zero_iff {w : W} : ℓ w = 0 ↔ w = 1 := by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have : ω = [] := eq_nil_of_length_eq_zero (hω.symm.trans h)
    rw [this]; rw [wordProd_nil]
  · rintro rfl
    exact cs.length_one

@[simp]
/--
theorem `length_inv` / 定理 `length_inv`

English:
theorem length_inv
  given: (w : W)
  statement: ℓ (w⁻¹) = ℓ w
  proof: by
  apply Nat.le_antisymm
  · rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← hω] at this
  · rcases cs.exists_isReduced w⁻¹ with ⟨ω, hω, h'ω⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← h'ω, ← hω, inv_inv, ← h'ω] at this

中文:
定理 length_inv
  条件: (w : W)
  结论: ℓ (w⁻¹) = ℓ w
  证明: by
  apply Nat.le_antisymm
  · rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← hω] at this
  · rcases cs.exists_isReduced w⁻¹ with ⟨ω, hω, h'ω⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← h'ω, ← hω, inv_inv, ← h'ω] at this

Depends on / 依赖: Nat.le_antisymm, cs.exists_isReduced, cs.length_wordProd_le, exists_isReduced, inv_inv, le_antisymm, length_reverse, length_wordProd_le, reverse, wordProd_reverse
-/
theorem length_inv (w : W) : ℓ (w⁻¹) = ℓ w := by
  apply Nat.le_antisymm
  · rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← hω] at this
  · rcases cs.exists_isReduced w⁻¹ with ⟨ω, hω, h'ω⟩
    have := cs.length_wordProd_le ω.reverse
    rwa [wordProd_reverse, length_reverse, ← h'ω, ← hω, inv_inv, ← h'ω] at this

/--
theorem `length_mul_le` / 定理 `length_mul_le`

English:
theorem length_mul_le
  given: (w₁ w₂ : W)
  statement: ℓ (w₁ * w₂) <= ℓ w₁ + ℓ w₂
  proof: by
  rcases cs.exists_isReduced w₁ with ⟨ω₁, hω₁, rfl⟩
  rcases cs.exists_isReduced w₂ with ⟨ω₂, hω₂, rfl⟩
  have := cs.length_wordProd_le (ω₁ ++ ω₂)
  simpa [hω₁.eq, hω₂.eq, wordProd_append] using this

中文:
定理 length_mul_le
  条件: (w₁ w₂ : W)
  结论: ℓ (w₁ * w₂) <= ℓ w₁ + ℓ w₂
  证明: by
  rcases cs.exists_isReduced w₁ with ⟨ω₁, hω₁, rfl⟩
  rcases cs.exists_isReduced w₂ with ⟨ω₂, hω₂, rfl⟩
  have := cs.length_wordProd_le (ω₁ ++ ω₂)
  simpa [hω₁.eq, hω₂.eq, wordProd_append] using this

Depends on / 依赖: cs.exists_isReduced, cs.length_wordProd_le, exists_isReduced, length_wordProd_le, wordProd_append
-/
theorem length_mul_le (w₁ w₂ : W) : ℓ (w₁ * w₂) <= ℓ w₁ + ℓ w₂ := by
  rcases cs.exists_isReduced w₁ with ⟨ω₁, hω₁, rfl⟩
  rcases cs.exists_isReduced w₂ with ⟨ω₂, hω₂, rfl⟩
  have := cs.length_wordProd_le (ω₁ ++ ω₂)
  simpa [hω₁.eq, hω₂.eq, wordProd_append] using this

/--
theorem `length_le_length_mul_add_left` / 定理 `length_le_length_mul_add_left`

English:
theorem length_le_length_mul_add_left
  given: (w₁ w₂ : W)
  statement: ℓ w₂ <= ℓ (w₁ * w₂) + ℓ w₁
  proof: by
  simpa [add_comm] using cs.length_mul_le w₁⁻¹ (w₁ * w₂)

中文:
定理 length_le_length_mul_add_left
  条件: (w₁ w₂ : W)
  结论: ℓ w₂ <= ℓ (w₁ * w₂) + ℓ w₁
  证明: by
  simpa [add_comm] using cs.length_mul_le w₁⁻¹ (w₁ * w₂)

Depends on / 依赖: add_comm, cs.length_mul_le, length_mul_le
-/
theorem length_le_length_mul_add_left (w₁ w₂ : W) : ℓ w₂ <= ℓ (w₁ * w₂) + ℓ w₁ := by
  simpa [add_comm] using cs.length_mul_le w₁⁻¹ (w₁ * w₂)

/--
theorem `length_le_length_mul_add_right` / 定理 `length_le_length_mul_add_right`

English:
theorem length_le_length_mul_add_right
  given: (w₁ w₂ : W)
  statement: ℓ w₁ <= ℓ (w₁ * w₂) + ℓ w₂
  proof: by
  simpa using cs.length_mul_le (w₁ * w₂) w₂⁻¹

@[deprecated length_le_length_mul_add_right (since := "2026-03-25")]

中文:
定理 length_le_length_mul_add_right
  条件: (w₁ w₂ : W)
  结论: ℓ w₁ <= ℓ (w₁ * w₂) + ℓ w₂
  证明: by
  simpa using cs.length_mul_le (w₁ * w₂) w₂⁻¹

@[deprecated length_le_length_mul_add_right (since := "2026-03-25")]

Depends on / 依赖: cs.length_mul_le, length_mul_le
-/
theorem length_le_length_mul_add_right (w₁ w₂ : W) : ℓ w₁ <= ℓ (w₁ * w₂) + ℓ w₂ := by
  simpa using cs.length_mul_le (w₁ * w₂) w₂⁻¹

@[deprecated length_le_length_mul_add_right (since := "2026-03-25")]
/--
theorem `length_mul_ge_length_sub_length` / 定理 `length_mul_ge_length_sub_length`

English:
theorem length_mul_ge_length_sub_length
  given: (w₁ w₂ : W)
  statement: ℓ w₁ - ℓ w₂ <= ℓ (w₁ * w₂)
  proof: by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_right ..

@[deprecated length_le_length_mul_add_left (since := "2026-03-25")]

中文:
定理 length_mul_ge_length_sub_length
  条件: (w₁ w₂ : W)
  结论: ℓ w₁ - ℓ w₂ <= ℓ (w₁ * w₂)
  证明: by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_right ..

@[deprecated length_le_length_mul_add_left (since := "2026-03-25")]

Depends on / 依赖: Nat.sub_le_iff_le_add, length_le_length_mul_add_right, sub_le_iff_le_add
-/
theorem length_mul_ge_length_sub_length (w₁ w₂ : W) : ℓ w₁ - ℓ w₂ <= ℓ (w₁ * w₂) := by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_right ..

@[deprecated length_le_length_mul_add_left (since := "2026-03-25")]
/--
theorem `length_mul_ge_length_sub_length'` / 定理 `length_mul_ge_length_sub_length'`

English:
theorem length_mul_ge_length_sub_length'
  given: (w₁ w₂ : W)
  statement: ℓ w₂ - ℓ w₁ <= ℓ (w₁ * w₂)
  proof: by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_left ..

@[deprecated "use `length_le_length_mul_add_left` and `length_le_length_mul_add_right"
(since := "2026-03-25")]

中文:
定理 length_mul_ge_length_sub_length'
  条件: (w₁ w₂ : W)
  结论: ℓ w₂ - ℓ w₁ <= ℓ (w₁ * w₂)
  证明: by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_left ..

@[deprecated "use `length_le_length_mul_add_left` and `length_le_length_mul_add_right"
(since := "2026-03-25")]

Depends on / 依赖: Nat.sub_le_iff_le_add, length_le_length_mul_add_left, sub_le_iff_le_add
-/
theorem length_mul_ge_length_sub_length' (w₁ w₂ : W) : ℓ w₂ - ℓ w₁ <= ℓ (w₁ * w₂) := by
  rw [Nat.sub_le_iff_le_add]; exact length_le_length_mul_add_left ..

@[deprecated "use `length_le_length_mul_add_left` and `length_le_length_mul_add_right"
(since := "2026-03-25")]
/--
theorem `length_mul_ge_max` / 定理 `length_mul_ge_max`

English:
theorem length_mul_ge_max
  given: (w₁ w₂ : W)
  statement: max (ℓ w₁ - ℓ w₂) (ℓ w₂ - ℓ w₁) <= ℓ (w₁ * w₂)
  proof: max_le (length_mul_ge_length_sub_length ..) (length_mul_ge_length_sub_length' ..)

中文:
定理 length_mul_ge_max
  条件: (w₁ w₂ : W)
  结论: 最大值 (ℓ w₁ - ℓ w₂) (ℓ w₂ - ℓ w₁) <= ℓ (w₁ * w₂)
  证明: max_le (length_mul_ge_length_sub_length ..) (length_mul_ge_length_sub_length' ..)

Depends on / 依赖: length_mul_ge_length_sub_length, max_le
-/
theorem length_mul_ge_max (w₁ w₂ : W) : max (ℓ w₁ - ℓ w₂) (ℓ w₂ - ℓ w₁) <= ℓ (w₁ * w₂) :=
  max_le (length_mul_ge_length_sub_length ..) (length_mul_ge_length_sub_length' ..)

/--
Definition of `lengthParity` / `lengthParity` 的定义

English:
definition lengthParity
  signature: : W ->* Multiplicative (ZMod 2)
  body: cs.lift ⟨fun _ => Multiplicative.ofAdd 1, by
  simp_rw [CoxeterMatrix.IsLiftable, ← ofAdd_add, (by decide : (1 + 1 : ZMod 2) = 0)]
  simp⟩

中文:
定义 lengthParity
  签名: : W ->* Multiplicative (ZMod 2)
  定义体: cs.lift ⟨fun _ => Multiplicative.ofAdd 1, by
  simp_rw [CoxeterMatrix.IsLiftable, ← ofAdd_add, (by decide : (1 + 1 : ZMod 2) = 0)]
  simp⟩

Depends on / 依赖: CoxeterMatrix, CoxeterMatrix.IsLiftable, IsLiftable, Multiplicative, Multiplicative.ofAdd, cs.lift, ofAdd_add, simp_rw
-/
def lengthParity : W ->* Multiplicative (ZMod 2) := cs.lift ⟨fun _ => Multiplicative.ofAdd 1, by
  simp_rw [CoxeterMatrix.IsLiftable, ← ofAdd_add, (by decide : (1 + 1 : ZMod 2) = 0)]
  simp⟩

/--
theorem `lengthParity_simple` / 定理 `lengthParity_simple`

English:
theorem lengthParity_simple
  given: (i : B)
  proof: cs.lift_apply_simple _ _

中文:
定理 lengthParity_simple
  条件: (i : B)
  证明: cs.lift_apply_simple _ _

Depends on / 依赖: cs.lift_apply_simple, lift_apply_simple
-/
theorem lengthParity_simple (i : B) :
    cs.lengthParity (s i) = Multiplicative.ofAdd 1 := cs.lift_apply_simple _ _

/--
theorem `lengthParity_comp_simple` / 定理 `lengthParity_comp_simple`

English:
theorem lengthParity_comp_simple
  proof: funext cs.lengthParity_simple

中文:
定理 lengthParity_comp_simple
  证明: funext cs.lengthParity_simple

Depends on / 依赖: cs.lengthParity_simple, lengthParity_simple
-/
theorem lengthParity_comp_simple :
    cs.lengthParity ∘ cs.simple = fun _ => Multiplicative.ofAdd 1 := funext cs.lengthParity_simple

/--
theorem `lengthParity_eq_ofAdd_length` / 定理 `lengthParity_eq_ofAdd_length`

English:
theorem lengthParity_eq_ofAdd_length
  given: (w : W)
  proof: by
  rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
  rw [hω]; rw [wordProd]; rw [map_list_prod]; rw [List.map_map]; rw [lengthParity_comp_simple]; rw [map_const']; rw [prod_replicate]; rw [← ofAdd_nsmul]; rw [nsmul_one]

中文:
定理 lengthParity_eq_ofAdd_length
  条件: (w : W)
  证明: by
  rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
  rw [hω]; rw [wordProd]; rw [map_list_prod]; rw [List.map_map]; rw [lengthParity_comp_simple]; rw [map_const']; rw [prod_replicate]; rw [← ofAdd_nsmul]; rw [nsmul_one]

Depends on / 依赖: List.map_map, cs.exists_isReduced, exists_isReduced, lengthParity_comp_simple, map_const, map_list_prod, map_map, nsmul_one, ofAdd_nsmul, prod_replicate, wordProd
-/
theorem lengthParity_eq_ofAdd_length (w : W) :
    cs.lengthParity w = Multiplicative.ofAdd (↑(ℓ w)) := by
  rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
  rw [hω]; rw [wordProd]; rw [map_list_prod]; rw [List.map_map]; rw [lengthParity_comp_simple]; rw [map_const']; rw [prod_replicate]; rw [← ofAdd_nsmul]; rw [nsmul_one]

/--
theorem `length_mul_mod_two` / 定理 `length_mul_mod_two`

English:
theorem length_mul_mod_two
  given: (w₁ w₂ : W)
  statement: ℓ (w₁ * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2
  proof: by
  rw [← ZMod.natCast_eq_natCast_iff']; rw [Nat.cast_add]
  simpa only [lengthParity_eq_ofAdd_length, ofAdd_add] using! map_mul cs.lengthParity w₁ w₂

@[simp]

中文:
定理 length_mul_mod_two
  条件: (w₁ w₂ : W)
  结论: ℓ (w₁ * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2
  证明: by
  rw [← ZMod.natCast_eq_natCast_iff']; rw [Nat.cast_add]
  simpa only [lengthParity_eq_ofAdd_length, ofAdd_add] using! map_mul cs.lengthParity w₁ w₂

@[simp]

Depends on / 依赖: Nat.cast_add, ZMod.natCast_eq_natCast_iff, cast_add, cs.lengthParity, lengthParity, lengthParity_eq_ofAdd_length, map_mul, natCast_eq_natCast_iff, ofAdd_add
-/
theorem length_mul_mod_two (w₁ w₂ : W) : ℓ (w₁ * w₂) % 2 = (ℓ w₁ + ℓ w₂) % 2 := by
  rw [← ZMod.natCast_eq_natCast_iff']; rw [Nat.cast_add]
  simpa only [lengthParity_eq_ofAdd_length, ofAdd_add] using! map_mul cs.lengthParity w₁ w₂

@[simp]
/--
theorem `length_simple` / 定理 `length_simple`

English:
theorem length_simple
  given: (i : B)
  statement: ℓ (s i) = 1
  proof: by
  apply Nat.le_antisymm
  · simpa using cs.length_wordProd_le [i]
  · by_contra! length_lt_one
    have : cs.lengthParity (s i) = Multiplicative.ofAdd 0 := by
      rw [lengthParity_eq_ofAdd_length]; rw [Nat.lt_one_iff.mp length_lt_one]; rw [Nat.cast_zero]
    have : Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd 1 :=
      this.symm.trans (cs.lengthParity_simple i)
    contradiction

中文:
定理 length_simple
  条件: (i : B)
  结论: ℓ (s i) = 1
  证明: by
  apply Nat.le_antisymm
  · simpa using cs.length_wordProd_le [i]
  · by_contra! length_lt_one
    have : cs.lengthParity (s i) = Multiplicative.ofAdd 0 := by
      rw [lengthParity_eq_ofAdd_length]; rw [Nat.lt_one_iff.mp length_lt_one]; rw [Nat.cast_zero]
    have : Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd 1 :=
      this.symm.trans (cs.lengthParity_simple i)
    contradiction

Depends on / 依赖: Multiplicative, Multiplicative.ofAdd, Nat.cast_zero, Nat.le_antisymm, Nat.lt_one_iff.mp, cast_zero, cs.lengthParity, cs.lengthParity_simple, cs.length_wordProd_le, le_antisymm, lengthParity, lengthParity_eq_ofAdd_length, lengthParity_simple, length_lt_one, length_wordProd_le, lt_one_iff, this.symm.trans
-/
theorem length_simple (i : B) : ℓ (s i) = 1 := by
  apply Nat.le_antisymm
  · simpa using cs.length_wordProd_le [i]
  · by_contra! length_lt_one
    have : cs.lengthParity (s i) = Multiplicative.ofAdd 0 := by
      rw [lengthParity_eq_ofAdd_length]; rw [Nat.lt_one_iff.mp length_lt_one]; rw [Nat.cast_zero]
    have : Multiplicative.ofAdd (0 : ZMod 2) = Multiplicative.ofAdd 1 :=
      this.symm.trans (cs.lengthParity_simple i)
    contradiction

/--
theorem `length_eq_one_iff` / 定理 `length_eq_one_iff`

English:
theorem length_eq_one_iff
  given: {w : W}
  statement: ℓ w = 1 ↔ exists i : B, w = s i
  proof: by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    rcases List.length_eq_one_iff.mp (hω.symm.trans h) with ⟨i, rfl⟩
    exact ⟨i, cs.wordProd_singleton i⟩
  · rintro ⟨i, rfl⟩
    exact cs.length_simple i

中文:
定理 length_eq_one_iff
  条件: {w : W}
  结论: ℓ w = 1 ↔ 存在 i : B, w = s i
  证明: by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    rcases List.length_eq_one_iff.mp (hω.symm.trans h) with ⟨i, rfl⟩
    exact ⟨i, cs.wordProd_singleton i⟩
  · rintro ⟨i, rfl⟩
    exact cs.length_simple i

Depends on / 依赖: List.length_eq_one_iff.mp, cs.exists_isReduced, cs.length_simple, cs.wordProd_singleton, exists_isReduced, length_eq_one_iff, length_simple, symm.trans, wordProd_singleton
-/
theorem length_eq_one_iff {w : W} : ℓ w = 1 ↔ exists i : B, w = s i := by
  constructor
  · intro h
    rcases cs.exists_isReduced w with ⟨ω, hω, rfl⟩
    rcases List.length_eq_one_iff.mp (hω.symm.trans h) with ⟨i, rfl⟩
    exact ⟨i, cs.wordProd_singleton i⟩
  · rintro ⟨i, rfl⟩
    exact cs.length_simple i

/--
theorem `length_mul_simple_ne` / 定理 `length_mul_simple_ne`

English:
theorem length_mul_simple_ne
  given: (w : W) (i : B)
  statement: ℓ (w * s i) != ℓ w
  proof: by
  intro eq
  have length_mod_two := cs.length_mul_mod_two w (s i)
  rw [eq]; rw [length_simple] at length_mod_two
  lia

中文:
定理 length_mul_simple_ne
  条件: (w : W) (i : B)
  结论: ℓ (w * s i) != ℓ w
  证明: by
  intro eq
  have length_mod_two := cs.length_mul_mod_two w (s i)
  rw [eq]; rw [length_simple] at length_mod_two
  lia

Depends on / 依赖: cs.length_mul_mod_two, length_mod_two, length_mul_mod_two, length_simple
-/
theorem length_mul_simple_ne (w : W) (i : B) : ℓ (w * s i) != ℓ w := by
  intro eq
  have length_mod_two := cs.length_mul_mod_two w (s i)
  rw [eq]; rw [length_simple] at length_mod_two
  lia

/--
theorem `length_simple_mul_ne` / 定理 `length_simple_mul_ne`

English:
theorem length_simple_mul_ne
  given: (w : W) (i : B)
  statement: ℓ (s i * w) != ℓ w
  proof: by
  rw [← length_inv]
  simpa using cs.length_mul_simple_ne w⁻¹ i

中文:
定理 length_simple_mul_ne
  条件: (w : W) (i : B)
  结论: ℓ (s i * w) != ℓ w
  证明: by
  rw [← length_inv]
  simpa using cs.length_mul_simple_ne w⁻¹ i

Depends on / 依赖: cs.length_mul_simple_ne, length_inv, length_mul_simple_ne
-/
theorem length_simple_mul_ne (w : W) (i : B) : ℓ (s i * w) != ℓ w := by
  rw [← length_inv]
  simpa using cs.length_mul_simple_ne w⁻¹ i

/--
theorem `length_mul_simple` / 定理 `length_mul_simple`

English:
theorem length_mul_simple
  given: (w : W) (i : B)
  statement: ℓ (w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w
  proof: by
  rcases (cs.length_mul_simple_ne w i).lt_or_gt with h | h <;> rw [← Nat.add_one_le_iff] at h
  · refine .inr (h.antisymm ?_)
    simpa using cs.length_le_length_mul_add_right w (s i)
  · refine .inl (h.antisymm' ?_)
    simpa using cs.length_mul_le w (s i)

中文:
定理 length_mul_simple
  条件: (w : W) (i : B)
  结论: ℓ (w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w
  证明: by
  rcases (cs.length_mul_simple_ne w i).lt_or_gt with h | h <;> rw [← Nat.add_one_le_iff] at h
  · refine .inr (h.antisymm ?_)
    simpa using cs.length_le_length_mul_add_right w (s i)
  · refine .inl (h.antisymm' ?_)
    simpa using cs.length_mul_le w (s i)

Depends on / 依赖: Nat.add_one_le_iff, add_one_le_iff, antisymm, cs.length_le_length_mul_add_right, cs.length_mul_le, cs.length_mul_simple_ne, h.antisymm, length_le_length_mul_add_right, length_mul_le, length_mul_simple_ne, lt_or_gt
-/
theorem length_mul_simple (w : W) (i : B) : ℓ (w * s i) = ℓ w + 1 ∨ ℓ (w * s i) + 1 = ℓ w := by
  rcases (cs.length_mul_simple_ne w i).lt_or_gt with h | h <;> rw [← Nat.add_one_le_iff] at h
  · refine .inr (h.antisymm ?_)
    simpa using cs.length_le_length_mul_add_right w (s i)
  · refine .inl (h.antisymm' ?_)
    simpa using cs.length_mul_le w (s i)

/--
theorem `length_simple_mul` / 定理 `length_simple_mul`

English:
theorem length_simple_mul
  given: (w : W) (i : B)
  statement: ℓ (s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w
  proof: by
  have := cs.length_mul_simple w⁻¹ i
  rwa [(by simp : w⁻¹ * (s i) = ((s i) * w)⁻¹), length_inv, length_inv] at this

中文:
定理 length_simple_mul
  条件: (w : W) (i : B)
  结论: ℓ (s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w
  证明: by
  have := cs.length_mul_simple w⁻¹ i
  rwa [(by simp : w⁻¹ * (s i) = ((s i) * w)⁻¹), length_inv, length_inv] at this

Depends on / 依赖: cs.length_mul_simple, length_inv, length_mul_simple
-/
theorem length_simple_mul (w : W) (i : B) : ℓ (s i * w) = ℓ w + 1 ∨ ℓ (s i * w) + 1 = ℓ w := by
  have := cs.length_mul_simple w⁻¹ i
  rwa [(by simp : w⁻¹ * (s i) = ((s i) * w)⁻¹), length_inv, length_inv] at this

/-! ### Reduced words -/

@[simp]
/--
theorem `isReduced_reverse_iff` / 定理 `isReduced_reverse_iff`

English:
theorem isReduced_reverse_iff
  given: (ω : List B)
  statement: cs.IsReduced (ω.reverse) ↔ cs.IsReduced ω
  proof: by
  simp [IsReduced]

中文:
定理 isReduced_reverse_iff
  条件: (ω : 列表 B)
  结论: cs.是既约 (ω.reverse) ↔ cs.是既约 ω
  证明: by
  simp [IsReduced]

Depends on / 依赖: IsReduced
-/
theorem isReduced_reverse_iff (ω : List B) : cs.IsReduced (ω.reverse) ↔ cs.IsReduced ω := by
  simp [IsReduced]

/--
theorem `IsReduced.reverse` / 定理 `IsReduced.reverse`

English:
theorem IsReduced.reverse
  statement: {cs : CoxeterSystem M W} {ω : List B}
  proof: (cs.isReduced_reverse_iff ω).mpr hω

中文:
定理 是既约.reverse
  结论: {cs : 余xeterSystem M W} {ω : 列表 B}
  证明: (cs.isReduced_reverse_iff ω).mpr hω

Depends on / 依赖: cs.isReduced_reverse_iff, isReduced_reverse_iff
-/
theorem IsReduced.reverse {cs : CoxeterSystem M W} {ω : List B}
    (hω : cs.IsReduced ω) : cs.IsReduced (ω.reverse) :=
  (cs.isReduced_reverse_iff ω).mpr hω


/--
theorem `isReduced_take_and_drop` / 定理 `isReduced_take_and_drop`

English:
theorem isReduced_take_and_drop
  given: {ω : List B} (hω : cs.IsReduced ω) (j : Nat)
  proof: by
  have h₁ : ℓ (π (ω.take j)) <= (ω.take j).length := cs.length_wordProd_le (ω.take j)
  have h₂ : ℓ (π (ω.drop j)) <= (ω.drop j).length := cs.length_wordProd_le (ω.drop j)
  have h₃ := calc
    (ω.take j).length + (ω.drop j).length
    _ = ω.length := by rw [← List.length_append, ω.take_append_drop j]
    _ = ℓ (π ω) := hω.symm
    _ = ℓ (π (ω.take j) * π (ω.drop j)) := by rw [← cs.wordProd_append, ω.take_append_drop j]
    _ <= ℓ (π (ω.take j)) + ℓ (π (ω.drop j)) := cs.length_mul_le _ _
  unfold IsReduced
  lia

中文:
定理 isReduced_take_and_drop
  条件: {ω : 列表 B} (hω : cs.是既约 ω) (j : 自然数)
  证明: by
  have h₁ : ℓ (π (ω.take j)) <= (ω.take j).length := cs.length_wordProd_le (ω.take j)
  have h₂ : ℓ (π (ω.drop j)) <= (ω.drop j).length := cs.length_wordProd_le (ω.drop j)
  have h₃ := calc
    (ω.take j).length + (ω.drop j).length
    _ = ω.length := by rw [← List.length_append, ω.take_append_drop j]
    _ = ℓ (π ω) := hω.symm
    _ = ℓ (π (ω.take j) * π (ω.drop j)) := by rw [← cs.wordProd_append, ω.take_append_drop j]
    _ <= ℓ (π (ω.take j)) + ℓ (π (ω.drop j)) := cs.length_mul_le _ _
  unfold IsReduced
  lia
-/
private theorem isReduced_take_and_drop {ω : List B} (hω : cs.IsReduced ω) (j : Nat) :
    cs.IsReduced (ω.take j) ∧ cs.IsReduced (ω.drop j) := by
  have h₁ : ℓ (π (ω.take j)) <= (ω.take j).length := cs.length_wordProd_le (ω.take j)
  have h₂ : ℓ (π (ω.drop j)) <= (ω.drop j).length := cs.length_wordProd_le (ω.drop j)
  have h₃ := calc
    (ω.take j).length + (ω.drop j).length
    _ = ω.length := by rw [← List.length_append, ω.take_append_drop j]
    _ = ℓ (π ω) := hω.symm
    _ = ℓ (π (ω.take j) * π (ω.drop j)) := by rw [← cs.wordProd_append, ω.take_append_drop j]
    _ <= ℓ (π (ω.take j)) + ℓ (π (ω.drop j)) := cs.length_mul_le _ _
  unfold IsReduced
  lia

/--
theorem `IsReduced.take` / 定理 `IsReduced.take`

English:
theorem IsReduced.take
  given: {cs : CoxeterSystem M W} {ω : List B} (hω : cs.IsReduced ω) (j : Nat)
  proof: (isReduced_take_and_drop _ hω _).1

中文:
定理 是既约.take
  条件: {cs : 余xeterSystem M W} {ω : 列表 B} (hω : cs.是既约 ω) (j : 自然数)
  证明: (isReduced_take_and_drop _ hω _).1

Depends on / 依赖: isReduced_take_and_drop
-/
theorem IsReduced.take {cs : CoxeterSystem M W} {ω : List B} (hω : cs.IsReduced ω) (j : Nat) :
    cs.IsReduced (ω.take j) :=
  (isReduced_take_and_drop _ hω _).1

/--
theorem `IsReduced.drop` / 定理 `IsReduced.drop`

English:
theorem IsReduced.drop
  given: {cs : CoxeterSystem M W} {ω : List B} (hω : cs.IsReduced ω) (j : Nat)
  proof: (isReduced_take_and_drop _ hω _).2

中文:
定理 是既约.drop
  条件: {cs : 余xeterSystem M W} {ω : 列表 B} (hω : cs.是既约 ω) (j : 自然数)
  证明: (isReduced_take_and_drop _ hω _).2

Depends on / 依赖: isReduced_take_and_drop
-/
theorem IsReduced.drop {cs : CoxeterSystem M W} {ω : List B} (hω : cs.IsReduced ω) (j : Nat) :
    cs.IsReduced (ω.drop j) :=
  (isReduced_take_and_drop _ hω _).2

/--
theorem `not_isReduced_alternatingWord` / 定理 `not_isReduced_alternatingWord`

English:
theorem not_isReduced_alternatingWord
  given: (i i' : B) {m : Nat} (hM : M i i' != 0) (hm : m > M i i')
  proof: by
  induction hm with
  | refl => -- Base case; m = M i i' + 1
    suffices h : ℓ (π (alternatingWord i i' (M i i' + 1))) < M i i' + 1 by
      unfold IsReduced
      rw [Nat.succ_eq_add_one]; rw [length_alternatingWord]
      lia
    have : M i i' + 1 <= M i i' * 2 := by linarith [Nat.one_le_iff_ne_zero.mpr hM]
    rw [cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' _ this]
    have : M i i' * 2 - (M i i' + 1) = M i i' - 1 := by lia
    rw [this]
    calc
      ℓ (π (alternatingWord i' i (M i i' - 1)))
      _ <= (alternatingWord i' i (M i i' - 1)).length := cs.length_wordProd_le _
      _ = M i i' - 1 := length_alternatingWord _ _ _
      _ <= M i i' := Nat.sub_le _ _
      _ < M i i' + 1 := Nat.lt_succ_self _
  | step m ih => -- Inductive step
    contrapose ih
    rw [alternatingWord_succ'] at ih
    apply IsReduced.drop (j := 1) at ih
    simpa using ih

中文:
定理 not_isReduced_alternatingWord
  条件: (i i' : B) {m : 自然数} (hM : M i i' != 0) (hm : m > M i i')
  证明: by
  induction hm with
  | refl => -- Base case; m = M i i' + 1
    suffices h : ℓ (π (alternatingWord i i' (M i i' + 1))) < M i i' + 1 by
      unfold IsReduced
      rw [Nat.succ_eq_add_one]; rw [length_alternatingWord]
      lia
    have : M i i' + 1 <= M i i' * 2 := by linarith [Nat.one_le_iff_ne_zero.mpr hM]
    rw [cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' _ this]
    have : M i i' * 2 - (M i i' + 1) = M i i' - 1 := by lia
    rw [this]
    calc
      ℓ (π (alternatingWord i' i (M i i' - 1)))
      _ <= (alternatingWord i' i (M i i' - 1)).length := cs.length_wordProd_le _
      _ = M i i' - 1 := length_alternatingWord _ _ _
      _ <= M i i' := Nat.sub_le _ _
      _ < M i i' + 1 := Nat.lt_succ_self _
  | step m ih => -- Inductive step
    contrapose ih
    rw [alternatingWord_succ'] at ih
    apply IsReduced.drop (j := 1) at ih
    simpa using ih

Depends on / 依赖: IsReduced, Nat.one_le_iff_ne_zero.mpr, Nat.succ_eq_add_one, alternatingWord, cs.prod_alternatingWord_eq_prod_alternatingWord_sub, length_alternatingWord, one_le_iff_ne_zero, prod_alternatingWord_eq_prod_alternatingWord_sub, succ_eq_add_one
-/
theorem not_isReduced_alternatingWord (i i' : B) {m : Nat} (hM : M i i' != 0) (hm : m > M i i') :
    ¬cs.IsReduced (alternatingWord i i' m) := by
  induction hm with
  | refl => -- Base case; m = M i i' + 1
    suffices h : ℓ (π (alternatingWord i i' (M i i' + 1))) < M i i' + 1 by
      unfold IsReduced
      rw [Nat.succ_eq_add_one]; rw [length_alternatingWord]
      lia
    have : M i i' + 1 <= M i i' * 2 := by linarith [Nat.one_le_iff_ne_zero.mpr hM]
    rw [cs.prod_alternatingWord_eq_prod_alternatingWord_sub i i' _ this]
    have : M i i' * 2 - (M i i' + 1) = M i i' - 1 := by lia
    rw [this]
    calc
      ℓ (π (alternatingWord i' i (M i i' - 1)))
      _ <= (alternatingWord i' i (M i i' - 1)).length := cs.length_wordProd_le _
      _ = M i i' - 1 := length_alternatingWord _ _ _
      _ <= M i i' := Nat.sub_le _ _
      _ < M i i' + 1 := Nat.lt_succ_self _
  | step m ih => -- Inductive step
    contrapose ih
    rw [alternatingWord_succ'] at ih
    apply IsReduced.drop (j := 1) at ih
    simpa using ih

/-! ### Descents -/

/--
Definition of `IsLeftDescent` / `IsLeftDescent` 的定义

English:
definition IsLeftDescent
  signature: (w : W) (i : B)
  body: ℓ (s i * w) < ℓ w

中文:
定义 IsLeftDescent
  签名: (w : W) (i : B)
  定义体: ℓ (s i * w) < ℓ w
-/
def IsLeftDescent (w : W) (i : B) : Prop := ℓ (s i * w) < ℓ w

/--
Definition of `IsRightDescent` / `IsRightDescent` 的定义

English:
definition IsRightDescent
  signature: (w : W) (i : B)
  body: ℓ (w * s i) < ℓ w

中文:
定义 IsRightDescent
  签名: (w : W) (i : B)
  定义体: ℓ (w * s i) < ℓ w
-/
def IsRightDescent (w : W) (i : B) : Prop := ℓ (w * s i) < ℓ w

/--
theorem `not_isLeftDescent_one` / 定理 `not_isLeftDescent_one`

English:
theorem not_isLeftDescent_one
  given: (i : B)
  statement: ¬cs.IsLeftDescent 1 i
  proof: by simp [IsLeftDescent]

中文:
定理 not_isLeftDescent_one
  条件: (i : B)
  结论: ¬cs.IsLeftDescent 1 i
  证明: by simp [IsLeftDescent]

Depends on / 依赖: IsLeftDescent
-/
theorem not_isLeftDescent_one (i : B) : ¬cs.IsLeftDescent 1 i := by simp [IsLeftDescent]

/--
theorem `not_isRightDescent_one` / 定理 `not_isRightDescent_one`

English:
theorem not_isRightDescent_one
  given: (i : B)
  statement: ¬cs.IsRightDescent 1 i
  proof: by simp [IsRightDescent]

中文:
定理 not_isRightDescent_one
  条件: (i : B)
  结论: ¬cs.IsRightDescent 1 i
  证明: by simp [IsRightDescent]

Depends on / 依赖: IsRightDescent
-/
theorem not_isRightDescent_one (i : B) : ¬cs.IsRightDescent 1 i := by simp [IsRightDescent]

/--
theorem `isLeftDescent_inv_iff` / 定理 `isLeftDescent_inv_iff`

English:
theorem isLeftDescent_inv_iff
  given: {w : W} {i : B}
  proof: by
  unfold IsLeftDescent IsRightDescent
  nth_rw 1 [← length_inv]
  simp

中文:
定理 isLeftDescent_inv_iff
  条件: {w : W} {i : B}
  证明: by
  unfold IsLeftDescent IsRightDescent
  nth_rw 1 [← length_inv]
  simp

Depends on / 依赖: IsLeftDescent, IsRightDescent, length_inv, nth_rw
-/
theorem isLeftDescent_inv_iff {w : W} {i : B} :
    cs.IsLeftDescent w⁻¹ i ↔ cs.IsRightDescent w i := by
  unfold IsLeftDescent IsRightDescent
  nth_rw 1 [← length_inv]
  simp

/--
theorem `isRightDescent_inv_iff` / 定理 `isRightDescent_inv_iff`

English:
theorem isRightDescent_inv_iff
  given: {w : W} {i : B}
  proof: by
  simpa using (cs.isLeftDescent_inv_iff (w := w⁻¹)).symm

中文:
定理 isRightDescent_inv_iff
  条件: {w : W} {i : B}
  证明: by
  simpa using (cs.isLeftDescent_inv_iff (w := w⁻¹)).symm

Depends on / 依赖: cs.isLeftDescent_inv_iff, isLeftDescent_inv_iff
-/
theorem isRightDescent_inv_iff {w : W} {i : B} :
    cs.IsRightDescent w⁻¹ i ↔ cs.IsLeftDescent w i := by
  simpa using (cs.isLeftDescent_inv_iff (w := w⁻¹)).symm

/--
theorem `exists_leftDescent_of_ne_one` / 定理 `exists_leftDescent_of_ne_one`

English:
theorem exists_leftDescent_of_ne_one
  given: {w : W} (hw : w != 1)
  statement: exists i : B, cs.IsLeftDescent w i
  proof: by
  rcases cs.exists_isReduced w with ⟨ω, h, rfl⟩
  have h₁ : ω != [] := by rintro rfl; simp at hw
  rcases List.exists_cons_of_ne_nil h₁ with ⟨i, ω', rfl⟩
  use i
  rw [IsLeftDescent]; rw [h]; rw [wordProd_cons]; rw [simple_mul_simple_cancel_left]
  calc
    ℓ (π ω') <= ω'.length := cs.length_wordProd_le ω'
    _ < (i :: ω').length := by simp

中文:
定理 存在_leftDescent_of_ne_one
  条件: {w : W} (hw : w != 1)
  结论: 存在 i : B, cs.IsLeftDescent w i
  证明: by
  rcases cs.exists_isReduced w with ⟨ω, h, rfl⟩
  have h₁ : ω != [] := by rintro rfl; simp at hw
  rcases List.exists_cons_of_ne_nil h₁ with ⟨i, ω', rfl⟩
  use i
  rw [IsLeftDescent]; rw [h]; rw [wordProd_cons]; rw [simple_mul_simple_cancel_left]
  calc
    ℓ (π ω') <= ω'.length := cs.length_wordProd_le ω'
    _ < (i :: ω').length := by simp

Depends on / 依赖: IsLeftDescent, List.exists_cons_of_ne_nil, cs.exists_isReduced, cs.length_wordProd_le, exists_cons_of_ne_nil, exists_isReduced, length, length_wordProd_le, simple_mul_simple_cancel_left, wordProd_cons
-/
theorem exists_leftDescent_of_ne_one {w : W} (hw : w != 1) : exists i : B, cs.IsLeftDescent w i := by
  rcases cs.exists_isReduced w with ⟨ω, h, rfl⟩
  have h₁ : ω != [] := by rintro rfl; simp at hw
  rcases List.exists_cons_of_ne_nil h₁ with ⟨i, ω', rfl⟩
  use i
  rw [IsLeftDescent]; rw [h]; rw [wordProd_cons]; rw [simple_mul_simple_cancel_left]
  calc
    ℓ (π ω') <= ω'.length := cs.length_wordProd_le ω'
    _ < (i :: ω').length := by simp

/--
theorem `exists_rightDescent_of_ne_one` / 定理 `exists_rightDescent_of_ne_one`

English:
theorem exists_rightDescent_of_ne_one
  given: {w : W} (hw : w != 1)
  statement: exists i : B, cs.IsRightDescent w i
  proof: by
  simp only [← isLeftDescent_inv_iff]
  apply exists_leftDescent_of_ne_one
  simpa

中文:
定理 存在_rightDescent_of_ne_one
  条件: {w : W} (hw : w != 1)
  结论: 存在 i : B, cs.IsRightDescent w i
  证明: by
  simp only [← isLeftDescent_inv_iff]
  apply exists_leftDescent_of_ne_one
  simpa

Depends on / 依赖: exists_leftDescent_of_ne_one, isLeftDescent_inv_iff
-/
theorem exists_rightDescent_of_ne_one {w : W} (hw : w != 1) : exists i : B, cs.IsRightDescent w i := by
  simp only [← isLeftDescent_inv_iff]
  apply exists_leftDescent_of_ne_one
  simpa

/--
theorem `isLeftDescent_iff` / 定理 `isLeftDescent_iff`

English:
theorem isLeftDescent_iff
  given: {w : W} {i : B}
  proof: by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_left (by lia)
  · lia

中文:
定理 isLeftDescent_iff
  条件: {w : W} {i : B}
  证明: by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_left (by lia)
  · lia

Depends on / 依赖: IsLeftDescent, cs.length_simple_mul, length_simple_mul, resolve_left
-/
theorem isLeftDescent_iff {w : W} {i : B} :
    cs.IsLeftDescent w i ↔ ℓ (s i * w) + 1 = ℓ w := by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_left (by lia)
  · lia

/--
theorem `not_isLeftDescent_iff` / 定理 `not_isLeftDescent_iff`

English:
theorem not_isLeftDescent_iff
  given: {w : W} {i : B}
  proof: by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_right (by lia)
  · lia

中文:
定理 not_isLeftDescent_iff
  条件: {w : W} {i : B}
  证明: by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_right (by lia)
  · lia

Depends on / 依赖: IsLeftDescent, cs.length_simple_mul, length_simple_mul, resolve_right
-/
theorem not_isLeftDescent_iff {w : W} {i : B} :
    ¬cs.IsLeftDescent w i ↔ ℓ (s i * w) = ℓ w + 1 := by
  unfold IsLeftDescent
  constructor
  · intro _
    exact (cs.length_simple_mul w i).resolve_right (by lia)
  · lia

/--
theorem `isRightDescent_iff` / 定理 `isRightDescent_iff`

English:
theorem isRightDescent_iff
  given: {w : W} {i : B}
  proof: by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_left (by lia)
  · lia

中文:
定理 isRightDescent_iff
  条件: {w : W} {i : B}
  证明: by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_left (by lia)
  · lia

Depends on / 依赖: IsRightDescent, cs.length_mul_simple, length_mul_simple, resolve_left
-/
theorem isRightDescent_iff {w : W} {i : B} :
    cs.IsRightDescent w i ↔ ℓ (w * s i) + 1 = ℓ w := by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_left (by lia)
  · lia

/--
theorem `not_isRightDescent_iff` / 定理 `not_isRightDescent_iff`

English:
theorem not_isRightDescent_iff
  given: {w : W} {i : B}
  proof: by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_right (by lia)
  · lia

中文:
定理 not_isRightDescent_iff
  条件: {w : W} {i : B}
  证明: by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_right (by lia)
  · lia

Depends on / 依赖: IsRightDescent, cs.length_mul_simple, length_mul_simple, resolve_right
-/
theorem not_isRightDescent_iff {w : W} {i : B} :
    ¬cs.IsRightDescent w i ↔ ℓ (w * s i) = ℓ w + 1 := by
  unfold IsRightDescent
  constructor
  · intro _
    exact (cs.length_mul_simple w i).resolve_right (by lia)
  · lia

/--
theorem `isLeftDescent_iff_not_isLeftDescent_mul` / 定理 `isLeftDescent_iff_not_isLeftDescent_mul`

English:
theorem isLeftDescent_iff_not_isLeftDescent_mul
  given: {w : W} {i : B}
  proof: by
  rw [isLeftDescent_iff]; rw [not_isLeftDescent_iff]; rw [simple_mul_simple_cancel_left]
  tauto

中文:
定理 isLeftDescent_iff_not_isLeftDescent_mul
  条件: {w : W} {i : B}
  证明: by
  rw [isLeftDescent_iff]; rw [not_isLeftDescent_iff]; rw [simple_mul_simple_cancel_left]
  tauto

Depends on / 依赖: isLeftDescent_iff, not_isLeftDescent_iff, simple_mul_simple_cancel_left
-/
theorem isLeftDescent_iff_not_isLeftDescent_mul {w : W} {i : B} :
    cs.IsLeftDescent w i ↔ ¬cs.IsLeftDescent (s i * w) i := by
  rw [isLeftDescent_iff]; rw [not_isLeftDescent_iff]; rw [simple_mul_simple_cancel_left]
  tauto

/--
theorem `isRightDescent_iff_not_isRightDescent_mul` / 定理 `isRightDescent_iff_not_isRightDescent_mul`

English:
theorem isRightDescent_iff_not_isRightDescent_mul
  given: {w : W} {i : B}
  proof: by
  rw [isRightDescent_iff]; rw [not_isRightDescent_iff]; rw [simple_mul_simple_cancel_right]
  tauto

中文:
定理 isRightDescent_iff_not_isRightDescent_mul
  条件: {w : W} {i : B}
  证明: by
  rw [isRightDescent_iff]; rw [not_isRightDescent_iff]; rw [simple_mul_simple_cancel_right]
  tauto

Depends on / 依赖: isRightDescent_iff, not_isRightDescent_iff, simple_mul_simple_cancel_right
-/
theorem isRightDescent_iff_not_isRightDescent_mul {w : W} {i : B} :
    cs.IsRightDescent w i ↔ ¬cs.IsRightDescent (w * s i) i := by
  rw [isRightDescent_iff]; rw [not_isRightDescent_iff]; rw [simple_mul_simple_cancel_right]
  tauto

end CoxeterSystem
