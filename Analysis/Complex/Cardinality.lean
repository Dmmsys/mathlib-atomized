/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.Complex.Basic

/-!
# The cardinality of the complex numbers

This file shows that the complex numbers have cardinality continuum, i.e. `#ℂ = 𝔠`.
-/

public section

open Cardinal Set

open Cardinal

/-- The cardinality of the complex numbers, as a type. -/
@[simp]
/--
theorem `Cardinal.mk_complex` / 定理 `Cardinal.mk_complex`

English:
theorem Cardinal.mk_complex
  statement: #Complex = 𝔠
  proof: by
  rw [mk_congr Complex.equivRealProd]; rw [mk_prod]; rw [lift_id]; rw [mk_real]; rw [continuum_mul_self]

中文:
定理 Cardinal.mk_complex
  结论: #Complex = 𝔠
  证明: by
  rw [mk_congr Complex.equivRealProd]; rw [mk_prod]; rw [lift_id]; rw [mk_real]; rw [continuum_mul_self]

Depends on / 依赖: Complex.equivRealProd, continuum_mul_self, equivRealProd, lift_id, mk_congr, mk_prod, mk_real
-/
theorem Cardinal.mk_complex : #Complex = 𝔠 := by
  rw [mk_congr Complex.equivRealProd]; rw [mk_prod]; rw [lift_id]; rw [mk_real]; rw [continuum_mul_self]

/--
theorem `Cardinal.mk_univ_complex` / 定理 `Cardinal.mk_univ_complex`

English:
theorem Cardinal.mk_univ_complex
  statement: #(Set.univ : Set Complex) = 𝔠
  proof: by rw [mk_univ, mk_complex]

中文:
定理 Cardinal.mk_univ_complex
  结论: #(Set.univ : Set Complex) = 𝔠
  证明: by rw [mk_univ, mk_complex]

Depends on / 依赖: mk_complex, mk_univ
-/
theorem Cardinal.mk_univ_complex : #(Set.univ : Set Complex) = 𝔠 := by rw [mk_univ, mk_complex]

/--
theorem `not_countable_complex` / 定理 `not_countable_complex`

English:
theorem not_countable_complex
  statement: ¬(Set.univ : Set Complex).Countable
  proof: by
  rw [← le_aleph0_iff_set_countable]; rw [not_le]; rw [Cardinal.mk_univ_complex]
  apply cantor

中文:
定理 not_countable_complex
  结论: ¬(Set.univ : Set Complex).Countable
  证明: by
  rw [← le_aleph0_iff_set_countable]; rw [not_le]; rw [Cardinal.mk_univ_complex]
  apply cantor

Depends on / 依赖: Cardinal, Cardinal.mk_univ_complex, cantor, le_aleph0_iff_set_countable, mk_univ_complex, not_le
-/
theorem not_countable_complex : ¬(Set.univ : Set Complex).Countable := by
  rw [← le_aleph0_iff_set_countable]; rw [not_le]; rw [Cardinal.mk_univ_complex]
  apply cantor
