/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Lemma
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Basic
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Counting
public import Mathlib.Data.Finset.CastCard

/-!
# Triangle removal lemma

In this file, we prove the triangle removal lemma.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section

open Finset Fintype Nat SzemerediRegularity

variable {α : Type*} [DecidableEq α] [Fintype α] {G : SimpleGraph α} [DecidableRel G.Adj]
  {s t : Finset α} {P : Finpartition (univ : Finset α)} {ε : Real}

namespace SimpleGraph

/--
Definition of `triangleRemovalBound` / `triangleRemovalBound` 的定义

English:
definition triangleRemovalBound
  signature: (ε : Real)
  body: min (2 * ⌈4 / ε⌉₊ ^ 3)⁻¹ ((1 - min 1 ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3)

中文:
定义 triangleRemovalBound
  签名: (ε : 实数)
  定义体: min (2 * ⌈4 / ε⌉₊ ^ 3)⁻¹ ((1 - min 1 ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3)
-/
noncomputable def triangleRemovalBound (ε : Real) : Real :=
  min (2 * ⌈4 / ε⌉₊ ^ 3)⁻¹ ((1 - min 1 ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3)

/--
lemma `triangleRemovalBound_pos` / 引理 `triangleRemovalBound_pos`

English:
lemma triangleRemovalBound_pos
  given: (hε : 0 < ε)
  statement: 0 < triangleRemovalBound ε
  proof: by
  have : 0 < 1 - min 1 ε / 4 := by have := min_le_left 1 ε; linarith
  unfold triangleRemovalBound
  positivity

中文:
引理 triangleRemovalBound_pos
  条件: (hε : 0 < ε)
  结论: 0 < triangleRemovalBound ε
  证明: by
  have : 0 < 1 - min 1 ε / 4 := by have := min_le_left 1 ε; linarith
  unfold triangleRemovalBound
  positivity

Depends on / 依赖: min_le_left, triangleRemovalBound
-/
lemma triangleRemovalBound_pos (hε : 0 < ε) : 0 < triangleRemovalBound ε := by
  have : 0 < 1 - min 1 ε / 4 := by have := min_le_left 1 ε; linarith
  unfold triangleRemovalBound
  positivity

/--
lemma `triangleRemovalBound_nonpos` / 引理 `triangleRemovalBound_nonpos`

English:
lemma triangleRemovalBound_nonpos
  given: (hε : ε <= 0)
  statement: triangleRemovalBound ε <= 0
  proof: by
  rw [triangleRemovalBound]; rw [ceil_eq_zero.2 (div_nonpos_of_nonneg_of_nonpos _ hε)] <;> simp

中文:
引理 triangleRemovalBound_nonpos
  条件: (hε : ε <= 0)
  结论: triangleRemovalBound ε <= 0
  证明: by
  rw [triangleRemovalBound]; rw [ceil_eq_zero.2 (div_nonpos_of_nonneg_of_nonpos _ hε)] <;> simp

Depends on / 依赖: ceil_eq_zero, div_nonpos_of_nonneg_of_nonpos, triangleRemovalBound
-/
lemma triangleRemovalBound_nonpos (hε : ε <= 0) : triangleRemovalBound ε <= 0 := by
  rw [triangleRemovalBound]; rw [ceil_eq_zero.2 (div_nonpos_of_nonneg_of_nonpos _ hε)] <;> simp

/--
lemma `triangleRemovalBound_mul_cube_lt` / 引理 `triangleRemovalBound_mul_cube_lt`

English:
lemma triangleRemovalBound_mul_cube_lt
  given: (hε : 0 < ε)
  proof: by
  calc
    _ <= (2 * ⌈4 / ε⌉₊ ^ 3 : Real)⁻¹ * ↑⌈4 / ε⌉₊ ^ 3 := by gcongr; exact min_le_left _ _
    _ = 2⁻¹ := by rw [mul_inv, inv_mul_cancel_right₀]; positivity
    _ < 1 := by norm_num

中文:
引理 triangleRemovalBound_mul_cube_lt
  条件: (hε : 0 < ε)
  证明: by
  calc
    _ <= (2 * ⌈4 / ε⌉₊ ^ 3 : Real)⁻¹ * ↑⌈4 / ε⌉₊ ^ 3 := by gcongr; exact min_le_left _ _
    _ = 2⁻¹ := by rw [mul_inv, inv_mul_cancel_right₀]; positivity
    _ < 1 := by norm_num

Depends on / 依赖: min_le_left, mul_inv
-/
lemma triangleRemovalBound_mul_cube_lt (hε : 0 < ε) :
    triangleRemovalBound ε * ⌈4 / ε⌉₊ ^ 3 < 1 := by
  calc
    _ <= (2 * ⌈4 / ε⌉₊ ^ 3 : Real)⁻¹ * ↑⌈4 / ε⌉₊ ^ 3 := by gcongr; exact min_le_left _ _
    _ = 2⁻¹ := by rw [mul_inv, inv_mul_cancel_right₀]; positivity
    _ < 1 := by norm_num

/--
lemma `triangleRemovalBound_le` / 引理 `triangleRemovalBound_le`

English:
lemma triangleRemovalBound_le
  given: (hε₁ : ε <= 1)
  proof: by
  simp [triangleRemovalBound, hε₁]

中文:
引理 triangleRemovalBound_le
  条件: (hε₁ : ε <= 1)
  证明: by
  simp [triangleRemovalBound, hε₁]

Depends on / 依赖: triangleRemovalBound
-/
lemma triangleRemovalBound_le (hε₁ : ε <= 1) :
    triangleRemovalBound ε <= (1 - ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 := by
  simp [triangleRemovalBound, hε₁]

/--
lemma `aux` / 引理 `aux`

English:
lemma aux
  given: {n k : Nat} (hk : 0 < k) (hn : k <= n)
  statement: n < 2 * k * (n / k)
  proof: by
  rw [mul_assoc]; rw [two_mul]; rw [← add_lt_add_iff_right (n % k)]; rw [add_right_comm]; rw [add_assoc]; rw [mod_add_div n k]; rw [add_comm]; rw [add_lt_add_iff_right]
  apply (mod_lt n hk).trans_le
  simpa using Nat.mul_le_mul_left k ((Nat.one_le_div_iff hk).2 hn)

中文:
引理 aux
  条件: {n k : 自然数} (hk : 0 < k) (hn : k <= n)
  结论: n < 2 * k * (n / k)
  证明: by
  rw [mul_assoc]; rw [two_mul]; rw [← add_lt_add_iff_right (n % k)]; rw [add_right_comm]; rw [add_assoc]; rw [mod_add_div n k]; rw [add_comm]; rw [add_lt_add_iff_right]
  apply (mod_lt n hk).trans_le
  simpa using Nat.mul_le_mul_left k ((Nat.one_le_div_iff hk).2 hn)
-/
private lemma aux {n k : Nat} (hk : 0 < k) (hn : k <= n) : n < 2 * k * (n / k) := by
  rw [mul_assoc]; rw [two_mul]; rw [← add_lt_add_iff_right (n % k)]; rw [add_right_comm]; rw [add_assoc]; rw [mod_add_div n k]; rw [add_comm]; rw [add_lt_add_iff_right]
  apply (mod_lt n hk).trans_le
  simpa using Nat.mul_le_mul_left k ((Nat.one_le_div_iff hk).2 hn)

/--
lemma `card_bound` / 引理 `card_bound`

English:
lemma card_bound
  statement: (hP₁ : P.IsEquipartition) (hP₃ : #P.parts <= bound (ε / 8) ⌈4 / ε⌉₊)
  proof: by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  have := Finset.Nonempty.card_pos ⟨_, hX⟩
  calc
    _ <= card α / (2 * #P.parts : Real) := by gcongr
    _ <= ↑(card α / #P.parts) :=
(div_le_iff₀' (by positivity)).2 mod_cast (aux ‹_› P.card_parts_le_card).le
    _ <= (#s : Real) := mod_cast hP₁.average_le_card_part hX

中文:
引理 card_bound
  结论: (hP₁ : P.IsEquipartition) (hP₃ : #P.parts <= bound (ε / 8) ⌈4 / ε⌉₊)
  证明: by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  have := Finset.Nonempty.card_pos ⟨_, hX⟩
  calc
    _ <= card α / (2 * #P.parts : Real) := by gcongr
    _ <= ↑(card α / #P.parts) :=
(div_le_iff₀' (by positivity)).2 mod_cast (aux ‹_› P.card_parts_le_card).le
    _ <= (#s : Real) := mod_cast hP₁.average_le_card_part hX
-/
private lemma card_bound (hP₁ : P.IsEquipartition) (hP₃ : #P.parts <= bound (ε / 8) ⌈4 / ε⌉₊)
    (hX : s in P.parts) : card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊ : Real) <= #s := by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  have := Finset.Nonempty.card_pos ⟨_, hX⟩
  calc
    _ <= card α / (2 * #P.parts : Real) := by gcongr
    _ <= ↑(card α / #P.parts) :=
(div_le_iff₀' (by positivity)).2 mod_cast (aux ‹_› P.card_parts_le_card).le
    _ <= (#s : Real) := mod_cast hP₁.average_le_card_part hX

/--
lemma `triangle_removal_aux` / 引理 `triangle_removal_aux`

English:
lemma triangle_removal_aux
  statement: (hε : 0 < ε) (hε₁ : ε <= 1) (hP₁ : P.IsEquipartition)
  proof: by
  rw [mem_cliqueFinset_iff]; rw [is3Clique_iff] at ht
  obtain ⟨x, y, z, ⟨-, s, hX, Y, hY, xX, yY, nXY, uXY, dXY⟩,
                   ⟨-, X', hX', Z, hZ, xX', zZ, nXZ, uXZ, dXZ⟩,
                   ⟨-, Y', hY', Z', hZ', yY', zZ', nYZ, uYZ, dYZ⟩, rfl⟩ := ht
  cases P.disjoint.elim hX hX' (not_disjoint_iff.2 ⟨x, xX, xX'⟩)
  cases P.disjoint.elim hY hY' (not_disjoint_iff.2 ⟨y, yY, yY'⟩)
  cases P.disjoint.elim hZ hZ' (not_disjoint_iff.2 ⟨z, zZ, zZ'⟩)
  have dXY := P.disjoint hX hY nXY
  have dXZ := P.disjoint hX hZ nXZ
  have dYZ := P.disjoint hY hZ nYZ
  have that : 2 * (ε / 8) = ε / 4 := by ring
  have : 0 <= 1 - 2 * (ε / 8) := by
    have : ε / 4 <= 1 := ‹ε / 4 <= _›.trans (by exact mod_cast G.edgeDensity_le_one _ _); linarith
  calc
    _ <= (1 - ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 * card α ^ 3 := by
      gcongr; exact triangleRemovalBound_le hε₁
    _ = (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) *
          (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) := by
      ring
    _ <= (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * #s * #Y * #Z := by
      gcongr <;> exact card_bound hP₁ hP₃ ‹_›
    _ <= _ :=
      triangle_counting G (by rwa [that]) uXY dXY (by rwa [that]) uXZ dXZ (by rwa [that]) uYZ dYZ

中文:
引理 triangle_removal_aux
  结论: (hε : 0 < ε) (hε₁ : ε <= 1) (hP₁ : P.IsEquipartition)
  证明: by
  rw [mem_cliqueFinset_iff]; rw [is3Clique_iff] at ht
  obtain ⟨x, y, z, ⟨-, s, hX, Y, hY, xX, yY, nXY, uXY, dXY⟩,
                   ⟨-, X', hX', Z, hZ, xX', zZ, nXZ, uXZ, dXZ⟩,
                   ⟨-, Y', hY', Z', hZ', yY', zZ', nYZ, uYZ, dYZ⟩, rfl⟩ := ht
  cases P.disjoint.elim hX hX' (not_disjoint_iff.2 ⟨x, xX, xX'⟩)
  cases P.disjoint.elim hY hY' (not_disjoint_iff.2 ⟨y, yY, yY'⟩)
  cases P.disjoint.elim hZ hZ' (not_disjoint_iff.2 ⟨z, zZ, zZ'⟩)
  have dXY := P.disjoint hX hY nXY
  have dXZ := P.disjoint hX hZ nXZ
  have dYZ := P.disjoint hY hZ nYZ
  have that : 2 * (ε / 8) = ε / 4 := by ring
  have : 0 <= 1 - 2 * (ε / 8) := by
    have : ε / 4 <= 1 := ‹ε / 4 <= _›.trans (by exact mod_cast G.edgeDensity_le_one _ _); linarith
  calc
    _ <= (1 - ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 * card α ^ 3 := by
      gcongr; exact triangleRemovalBound_le hε₁
    _ = (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) *
          (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) := by
      ring
    _ <= (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * #s * #Y * #Z := by
      gcongr <;> exact card_bound hP₁ hP₃ ‹_›
    _ <= _ :=
      triangle_counting G (by rwa [that]) uXY dXY (by rwa [that]) uXZ dXZ (by rwa [that]) uYZ dYZ
-/
private lemma triangle_removal_aux (hε : 0 < ε) (hε₁ : ε <= 1) (hP₁ : P.IsEquipartition)
    (hP₃ : #P.parts <= bound (ε / 8) ⌈4 / ε⌉₊)
    (ht : t in (G.regularityReduced P (ε / 8) (ε / 4)).cliqueFinset 3) :
    triangleRemovalBound ε * card α ^ 3 <= #(G.cliqueFinset 3) := by
  rw [mem_cliqueFinset_iff]; rw [is3Clique_iff] at ht
  obtain ⟨x, y, z, ⟨-, s, hX, Y, hY, xX, yY, nXY, uXY, dXY⟩,
                   ⟨-, X', hX', Z, hZ, xX', zZ, nXZ, uXZ, dXZ⟩,
                   ⟨-, Y', hY', Z', hZ', yY', zZ', nYZ, uYZ, dYZ⟩, rfl⟩ := ht
  cases P.disjoint.elim hX hX' (not_disjoint_iff.2 ⟨x, xX, xX'⟩)
  cases P.disjoint.elim hY hY' (not_disjoint_iff.2 ⟨y, yY, yY'⟩)
  cases P.disjoint.elim hZ hZ' (not_disjoint_iff.2 ⟨z, zZ, zZ'⟩)
  have dXY := P.disjoint hX hY nXY
  have dXZ := P.disjoint hX hZ nXZ
  have dYZ := P.disjoint hY hZ nYZ
  have that : 2 * (ε / 8) = ε / 4 := by ring
  have : 0 <= 1 - 2 * (ε / 8) := by
    have : ε / 4 <= 1 := ‹ε / 4 <= _›.trans (by exact mod_cast G.edgeDensity_le_one _ _); linarith
  calc
    _ <= (1 - ε / 4) * (ε / (16 * bound (ε / 8) ⌈4 / ε⌉₊)) ^ 3 * card α ^ 3 := by
      gcongr; exact triangleRemovalBound_le hε₁
    _ = (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) *
          (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) * (card α / (2 * bound (ε / 8) ⌈4 / ε⌉₊)) := by
      ring
    _ <= (1 - 2 * (ε / 8)) * (ε / 8) ^ 3 * #s * #Y * #Z := by
      gcongr <;> exact card_bound hP₁ hP₃ ‹_›
    _ <= _ :=
      triangle_counting G (by rwa [that]) uXY dXY (by rwa [that]) uXZ dXZ (by rwa [that]) uYZ dYZ

/--
lemma `regularityReduced_edges_card_aux` / 引理 `regularityReduced_edges_card_aux`

English:
lemma regularityReduced_edges_card_aux
  statement: [Nonempty α] (hε : 0 < ε) (hP : P.IsEquipartition)
  proof: by
  let A := (P.nonUniforms G (ε / 8)).biUnion fun (U, V) => U ×ˢ V
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G (ε / 4)).biUnion fun (U, V) => G.interedges U V
  calc
    _ = (#((univ ×ˢ univ).filter fun (x, y) =>
          G.Adj x y ∧ ¬(G.regularityReduced P (ε / 8) (ε / 4)).Adj x y) : Real) := by
      rw [univ_product_univ]; rw [mul_sub]; rw [filter_and_not]; rw [cast_card_sdiff]
      · norm_cast
        rw [two_mul_card_edgeFinset]; rw [two_mul_card_edgeFinset]
      · gcongr with xy _
        exact fun hxy => regularityReduced_le hxy
    _ <= #(A union B union C) := by gcongr; exact unreduced_edges_subset
    _ <= #(A union B) + #C := mod_cast (card_union_le _ _)
    _ <= #A + #B + #C := by gcongr; exact mod_cast card_union_le _ _
    _ < 4 * (ε / 8) * card α ^ 2 + _ + _ := by
      gcongr; exact hP.sum_nonUniforms_lt univ_nonempty (by positivity) hPε
    _ <= _ + ε / 2 * card α ^ 2 + 4 * (ε / 4) * card α ^ 2 := by
      gcongr
      · exact hP.card_biUnion_offDiag_le hε hP'
      · exact hP.card_interedges_sparsePairs_le (G := G) (ε := ε / 4) (by positivity)
    _ = 2 * ε * (card α ^ 2 : Nat) := by norm_cast; ring

中文:
引理 regularityReduced_edges_card_aux
  结论: [非空 α] (hε : 0 < ε) (hP : P.IsEquipartition)
  证明: by
  let A := (P.nonUniforms G (ε / 8)).biUnion fun (U, V) => U ×ˢ V
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G (ε / 4)).biUnion fun (U, V) => G.interedges U V
  calc
    _ = (#((univ ×ˢ univ).filter fun (x, y) =>
          G.Adj x y ∧ ¬(G.regularityReduced P (ε / 8) (ε / 4)).Adj x y) : Real) := by
      rw [univ_product_univ]; rw [mul_sub]; rw [filter_and_not]; rw [cast_card_sdiff]
      · norm_cast
        rw [two_mul_card_edgeFinset]; rw [two_mul_card_edgeFinset]
      · gcongr with xy _
        exact fun hxy => regularityReduced_le hxy
    _ <= #(A union B union C) := by gcongr; exact unreduced_edges_subset
    _ <= #(A union B) + #C := mod_cast (card_union_le _ _)
    _ <= #A + #B + #C := by gcongr; exact mod_cast card_union_le _ _
    _ < 4 * (ε / 8) * card α ^ 2 + _ + _ := by
      gcongr; exact hP.sum_nonUniforms_lt univ_nonempty (by positivity) hPε
    _ <= _ + ε / 2 * card α ^ 2 + 4 * (ε / 4) * card α ^ 2 := by
      gcongr
      · exact hP.card_biUnion_offDiag_le hε hP'
      · exact hP.card_interedges_sparsePairs_le (G := G) (ε := ε / 4) (by positivity)
    _ = 2 * ε * (card α ^ 2 : Nat) := by norm_cast; ring

Depends on / 依赖: G.Adj, G.interedges, G.regularityReduced, P.nonUniforms, P.parts.biUnion, P.sparsePairs, biUnion, cast_card_sdiff, filter, filter_and_not, interedges, mul_sub, nonUniforms, offDiag, regularityReduc, regularityReduced, sparsePairs, two_mul_card_edgeFinset, univ_product_univ
-/
lemma regularityReduced_edges_card_aux [Nonempty α] (hε : 0 < ε) (hP : P.IsEquipartition)
    (hPε : P.IsUniform G (ε / 8)) (hP' : 4 / ε <= #P.parts) :
    2 * (#G.edgeFinset - #(G.regularityReduced P (ε / 8) (ε / 4)).edgeFinset : Real)
      < 2 * ε * (card α ^ 2 : Nat) := by
  let A := (P.nonUniforms G (ε / 8)).biUnion fun (U, V) => U ×ˢ V
  let B := P.parts.biUnion offDiag
  let C := (P.sparsePairs G (ε / 4)).biUnion fun (U, V) => G.interedges U V
  calc
    _ = (#((univ ×ˢ univ).filter fun (x, y) =>
          G.Adj x y ∧ ¬(G.regularityReduced P (ε / 8) (ε / 4)).Adj x y) : Real) := by
      rw [univ_product_univ]; rw [mul_sub]; rw [filter_and_not]; rw [cast_card_sdiff]
      · norm_cast
        rw [two_mul_card_edgeFinset]; rw [two_mul_card_edgeFinset]
      · gcongr with xy _
        exact fun hxy => regularityReduced_le hxy
    _ <= #(A union B union C) := by gcongr; exact unreduced_edges_subset
    _ <= #(A union B) + #C := mod_cast (card_union_le _ _)
    _ <= #A + #B + #C := by gcongr; exact mod_cast card_union_le _ _
    _ < 4 * (ε / 8) * card α ^ 2 + _ + _ := by
      gcongr; exact hP.sum_nonUniforms_lt univ_nonempty (by positivity) hPε
    _ <= _ + ε / 2 * card α ^ 2 + 4 * (ε / 4) * card α ^ 2 := by
      gcongr
      · exact hP.card_biUnion_offDiag_le hε hP'
      · exact hP.card_interedges_sparsePairs_le (G := G) (ε := ε / 4) (by positivity)
    _ = 2 * ε * (card α ^ 2 : Nat) := by norm_cast; ring

/--
lemma `FarFromTriangleFree.le_card_cliqueFinset` / 引理 `FarFromTriangleFree.le_card_cliqueFinset`

English:
lemma FarFromTriangleFree.le_card_cliqueFinset
  given: (hG : G.FarFromTriangleFree ε)
  proof: by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  obtain hε | hε := le_or_gt ε 0
  · apply (mul_nonpos_of_nonpos_of_nonneg (triangleRemovalBound_nonpos hε) _).trans <;> positivity
  let l : Nat := ⌈4 / ε⌉₊
  have hl : 4 / ε <= l := le_ceil (4 / ε)
  rcases le_total (card α) l with hl' | hl'
  · calc
      _ <= triangleRemovalBound ε * ↑l ^ 3 := by
        gcongr; exact (triangleRemovalBound_pos hε).le
      _ <= (1 : Real) := (triangleRemovalBound_mul_cube_lt hε).le
      _ <= _ := by simpa [one_le_iff_ne_zero] using (hG.cliqueFinset_nonempty hε).card_pos.ne'
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G (by positivity : 0 < ε / 8) hl'
  have : 4 / ε <= #P.parts := hl.trans (cast_le.2 hP₂)
  have k := regularityReduced_edges_card_aux hε hP₁ hP₄ this
  rw [mul_assoc] at k
  replace k := lt_of_mul_lt_mul_left k zero_le_two
  obtain ⟨t, ht⟩ := hG.cliqueFinset_nonempty' regularityReduced_le k
  exact triangle_removal_aux hε hG.lt_one.le hP₁ hP₃ ht

中文:
引理 FarFromTriangleFree.le_card_cliqueFinset
  条件: (hG : G.FarFromTriangleFree ε)
  证明: by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  obtain hε | hε := le_or_gt ε 0
  · apply (mul_nonpos_of_nonpos_of_nonneg (triangleRemovalBound_nonpos hε) _).trans <;> positivity
  let l : Nat := ⌈4 / ε⌉₊
  have hl : 4 / ε <= l := le_ceil (4 / ε)
  rcases le_total (card α) l with hl' | hl'
  · calc
      _ <= triangleRemovalBound ε * ↑l ^ 3 := by
        gcongr; exact (triangleRemovalBound_pos hε).le
      _ <= (1 : Real) := (triangleRemovalBound_mul_cube_lt hε).le
      _ <= _ := by simpa [one_le_iff_ne_zero] using (hG.cliqueFinset_nonempty hε).card_pos.ne'
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G (by positivity : 0 < ε / 8) hl'
  have : 4 / ε <= #P.parts := hl.trans (cast_le.2 hP₂)
  have k := regularityReduced_edges_card_aux hε hP₁ hP₄ this
  rw [mul_assoc] at k
  replace k := lt_of_mul_lt_mul_left k zero_le_two
  obtain ⟨t, ht⟩ := hG.cliqueFinset_nonempty' regularityReduced_le k
  exact triangle_removal_aux hε hG.lt_one.le hP₁ hP₃ ht

Depends on / 依赖: Fintype, Fintype.card_eq_zero, card_eq_zero, isEmpty_or_nonempty, le_ceil, le_or_gt, le_total, mul_nonpos_of_nonpos_of_nonneg, one_le_iff_ne_zero, triangleRemovalBound, triangleRemovalBound_mul_cube_lt, triangleRemovalBound_nonpos, triangleRemovalBound_pos
-/
lemma FarFromTriangleFree.le_card_cliqueFinset (hG : G.FarFromTriangleFree ε) :
    triangleRemovalBound ε * card α ^ 3 <= #(G.cliqueFinset 3) := by
  cases isEmpty_or_nonempty α
  · simp [Fintype.card_eq_zero]
  obtain hε | hε := le_or_gt ε 0
  · apply (mul_nonpos_of_nonpos_of_nonneg (triangleRemovalBound_nonpos hε) _).trans <;> positivity
  let l : Nat := ⌈4 / ε⌉₊
  have hl : 4 / ε <= l := le_ceil (4 / ε)
  rcases le_total (card α) l with hl' | hl'
  · calc
      _ <= triangleRemovalBound ε * ↑l ^ 3 := by
        gcongr; exact (triangleRemovalBound_pos hε).le
      _ <= (1 : Real) := (triangleRemovalBound_mul_cube_lt hε).le
      _ <= _ := by simpa [one_le_iff_ne_zero] using (hG.cliqueFinset_nonempty hε).card_pos.ne'
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G (by positivity : 0 < ε / 8) hl'
  have : 4 / ε <= #P.parts := hl.trans (cast_le.2 hP₂)
  have k := regularityReduced_edges_card_aux hε hP₁ hP₄ this
  rw [mul_assoc] at k
  replace k := lt_of_mul_lt_mul_left k zero_le_two
  obtain ⟨t, ht⟩ := hG.cliqueFinset_nonempty' regularityReduced_le k
  exact triangle_removal_aux hε hG.lt_one.le hP₁ hP₃ ht

/--
lemma `triangle_removal` / 引理 `triangle_removal`

English:
lemma triangle_removal
  given: (hG : #(G.cliqueFinset 3) < triangleRemovalBound ε * card α ^ 3)
  proof: by
  by_contra! h
  refine hG.not_ge (farFromTriangleFree_iff.2 ?_).le_card_cliqueFinset
  intro G' _ hG hG'
  exact le_of_not_gt fun i => h G' hG _ i hG'

中文:
引理 triangle_removal
  条件: (hG : #(G.cliqueFinset 3) < triangleRemovalBound ε * card α ^ 3)
  证明: by
  by_contra! h
  refine hG.not_ge (farFromTriangleFree_iff.2 ?_).le_card_cliqueFinset
  intro G' _ hG hG'
  exact le_of_not_gt fun i => h G' hG _ i hG'

Depends on / 依赖: farFromTriangleFree_iff, hG.not_ge, le_card_cliqueFinset, le_of_not_gt, not_ge
-/
lemma triangle_removal (hG : #(G.cliqueFinset 3) < triangleRemovalBound ε * card α ^ 3) :
    exists G' <= G, exists _ : DecidableRel G'.Adj,
      (#G.edgeFinset - #G'.edgeFinset : Real) < ε * (card α ^ 2 : Nat) ∧ G'.CliqueFree 3 := by
  by_contra! h
  refine hG.not_ge (farFromTriangleFree_iff.2 ?_).le_card_cliqueFinset
  intro G' _ hG hG'
  exact le_of_not_gt fun i => h G' hG _ i hG'

end SimpleGraph

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq SimpleGraph

/-- Extension for the `positivity` tactic: `SimpleGraph.triangleRemovalBound ε` is positive
if `ε` is.

This exploits the positivity of the junk value of `triangleRemovalBound ε` for `ε ≥ 1`. -/
@[positivity triangleRemovalBound _]
meta def evalTriangleRemovalBound : PositivityExt where eval {u α} _zα pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(Real), ~q(triangleRemovalBound $ε) =>
    let .positive hε ← core q(inferInstance) (some q(inferInstance)) ε | failure
    assertInstancesCommute
    pure (.positive q(triangleRemovalBound_pos $hε))
  | _, _, _ => throwError "failed to match on Int.ceil application"

example (ε : Real) (hε : 0 < ε) : 0 < triangleRemovalBound ε := by positivity

end Mathlib.Meta.Positivity
