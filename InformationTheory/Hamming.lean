/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions
* `hammingDist x y`: the Hamming distance between `x` and `y`, the number of entries which differ.
* `hammingNorm x`: the Hamming norm of `x`, the number of non-zero entries.
* `Hamming β`: a type synonym for `Π i, β i` with `dist` and `norm` provided by the above.
* `Hamming.toHamming`, `Hamming.ofHamming`: functions for casting between `Hamming β` and
  `Π i, β i`.
* the Hamming norm forms a normed group on `Hamming β`.
-/

@[expose] public section


section HammingDistNorm

open Finset Function

variable {α ι : Type*} {β : ι -> Type*} [Fintype ι] [forall i, DecidableEq (β i)]
variable {γ : ι -> Type*} [forall i, DecidableEq (γ i)]

/--
Definition of `hammingDist` / `hammingDist` 的定义

English:
definition hammingDist
  signature: (x y : forall i, β i)
  body: #{i | x i != y i}

中文:
定义 hammingDist
  签名: (x y : 对任意 i, β i)
  定义体: #{i | x i != y i}
-/
def hammingDist (x y : forall i, β i) : Nat := #{i | x i != y i}

/-- Corresponds to `dist_self`. -/
@[simp]
/--
theorem `hammingDist_self` / 定理 `hammingDist_self`

English:
theorem hammingDist_self
  given: (x : forall i, β i)
  statement: hammingDist x x = 0
  proof: by
  rw [hammingDist]; rw [card_eq_zero]; rw [filter_eq_empty_iff]
  exact fun _ _ H => H rfl

中文:
定理 hammingDist_self
  条件: (x : 对任意 i, β i)
  结论: hammingDist x x = 0
  证明: by
  rw [hammingDist]; rw [card_eq_zero]; rw [filter_eq_empty_iff]
  exact fun _ _ H => H rfl

Depends on / 依赖: card_eq_zero, filter_eq_empty_iff, hammingDist
-/
theorem hammingDist_self (x : forall i, β i) : hammingDist x x = 0 := by
  rw [hammingDist]; rw [card_eq_zero]; rw [filter_eq_empty_iff]
  exact fun _ _ H => H rfl

-- TODO: this seems unnecessary.
/--
theorem `hammingDist_nonneg` / 定理 `hammingDist_nonneg`

English:
theorem hammingDist_nonneg
  given: {x y : forall i, β i}
  statement: 0 <= hammingDist x y
  proof: zero_le

中文:
定理 hammingDist_nonneg
  条件: {x y : 对任意 i, β i}
  结论: 0 <= hammingDist x y
  证明: zero_le

Depends on / 依赖: zero_le
-/
theorem hammingDist_nonneg {x y : forall i, β i} : 0 <= hammingDist x y :=
  zero_le

/--
theorem `hammingDist_comm` / 定理 `hammingDist_comm`

English:
theorem hammingDist_comm
  given: (x y : forall i, β i)
  statement: hammingDist x y = hammingDist y x
  proof: by
  simp_rw [hammingDist, ne_comm]

中文:
定理 hammingDist_comm
  条件: (x y : 对任意 i, β i)
  结论: hammingDist x y = hammingDist y x
  证明: by
  simp_rw [hammingDist, ne_comm]

Depends on / 依赖: hammingDist, ne_comm, simp_rw
-/
theorem hammingDist_comm (x y : forall i, β i) : hammingDist x y = hammingDist y x := by
  simp_rw [hammingDist, ne_comm]

/--
theorem `hammingDist_triangle` / 定理 `hammingDist_triangle`

English:
theorem hammingDist_triangle
  given: (x y z : forall i, β i)
  proof: by
  classical
    unfold hammingDist
    refine le_trans (card_mono ?_) (card_union_le _ _)
    rw [← filter_or]
    exact monotone_filter_right _ fun i _ h => (h.ne_or_ne _).imp_right Ne.symm

中文:
定理 hammingDist_triangle
  条件: (x y z : 对任意 i, β i)
  证明: by
  classical
    unfold hammingDist
    refine le_trans (card_mono ?_) (card_union_le _ _)
    rw [← filter_or]
    exact monotone_filter_right _ fun i _ h => (h.ne_or_ne _).imp_right Ne.symm

Depends on / 依赖: Ne.symm, card_mono, card_union_le, classical, filter_or, h.ne_or_ne, hammingDist, imp_right, le_trans, monotone_filter_right, ne_or_ne
-/
theorem hammingDist_triangle (x y z : forall i, β i) :
    hammingDist x z <= hammingDist x y + hammingDist y z := by
  classical
    unfold hammingDist
    refine le_trans (card_mono ?_) (card_union_le _ _)
    rw [← filter_or]
    exact monotone_filter_right _ fun i _ h => (h.ne_or_ne _).imp_right Ne.symm

/--
theorem `hammingDist_triangle_left` / 定理 `hammingDist_triangle_left`

English:
theorem hammingDist_triangle_left
  given: (x y z : forall i, β i)
  proof: by
  rw [hammingDist_comm z]
  exact hammingDist_triangle _ _ _

中文:
定理 hammingDist_triangle_left
  条件: (x y z : 对任意 i, β i)
  证明: by
  rw [hammingDist_comm z]
  exact hammingDist_triangle _ _ _

Depends on / 依赖: hammingDist_comm, hammingDist_triangle, isChain_cons_raise
-/
theorem hammingDist_triangle_left (x y z : forall i, β i) :
    hammingDist x y <= hammingDist z x + hammingDist z y := by
  rw [hammingDist_comm z]
  exact hammingDist_triangle _ _ _

/--
theorem `hammingDist_triangle_right` / 定理 `hammingDist_triangle_right`

English:
theorem hammingDist_triangle_right
  given: (x y z : forall i, β i)
  proof: by
  rw [hammingDist_comm y]
  exact hammingDist_triangle _ _ _

中文:
定理 hammingDist_triangle_right
  条件: (x y z : 对任意 i, β i)
  证明: by
  rw [hammingDist_comm y]
  exact hammingDist_triangle _ _ _

Depends on / 依赖: hammingDist_comm, hammingDist_triangle
-/
theorem hammingDist_triangle_right (x y z : forall i, β i) :
    hammingDist x y <= hammingDist x z + hammingDist y z := by
  rw [hammingDist_comm y]
  exact hammingDist_triangle _ _ _

/--
theorem `swap_hammingDist` / 定理 `swap_hammingDist`

English:
theorem swap_hammingDist
  statement: swap (@hammingDist _ β _ _) = hammingDist
  proof: by
  funext x y
  exact hammingDist_comm _ _

中文:
定理 swap_hammingDist
  结论: swap (@hammingDist _ β _ _) = hammingDist
  证明: by
  funext x y
  exact hammingDist_comm _ _

Depends on / 依赖: _sorted, hammingDist_comm
-/
theorem swap_hammingDist : swap (@hammingDist _ β _ _) = hammingDist := by
  funext x y
  exact hammingDist_comm _ _

/--
theorem `eq_of_hammingDist_eq_zero` / 定理 `eq_of_hammingDist_eq_zero`

English:
theorem eq_of_hammingDist_eq_zero
  given: {x y : forall i, β i}
  statement: hammingDist x y = 0 -> x = y
  proof: by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, Classical.not_not, funext_iff, mem_univ,
    forall_true_left, imp_self]

中文:
定理 eq_of_hammingDist_eq_zero
  条件: {x y : 对任意 i, β i}
  结论: hammingDist x y = 0 -> x = y
  证明: by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, Classical.not_not, funext_iff, mem_univ,
    forall_true_left, imp_self]

Depends on / 依赖: Classical, Classical.not_not, card_eq_zero, filter_eq_empty_iff, forall_true_left, funext_iff, hammingDist, imp_self, mem_univ, not_not, simp_rw
-/
theorem eq_of_hammingDist_eq_zero {x y : forall i, β i} : hammingDist x y = 0 -> x = y := by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, Classical.not_not, funext_iff, mem_univ,
    forall_true_left, imp_self]

/-- Corresponds to `dist_eq_zero`. -/
@[simp]
/--
theorem `hammingDist_eq_zero` / 定理 `hammingDist_eq_zero`

English:
theorem hammingDist_eq_zero
  given: {x y : forall i, β i}
  statement: hammingDist x y = 0 ↔ x = y
  proof: ⟨eq_of_hammingDist_eq_zero, fun H => by
    rw [H]
    exact hammingDist_self _⟩

中文:
定理 hammingDist_eq_zero
  条件: {x y : 对任意 i, β i}
  结论: hammingDist x y = 0 ↔ x = y
  证明: ⟨eq_of_hammingDist_eq_zero, fun H => by
    rw [H]
    exact hammingDist_self _⟩

Depends on / 依赖: eq_of_hammingDist_eq_zero, hammingDist_self
-/
theorem hammingDist_eq_zero {x y : forall i, β i} : hammingDist x y = 0 ↔ x = y :=
  ⟨eq_of_hammingDist_eq_zero, fun H => by
    rw [H]
    exact hammingDist_self _⟩

/-- Corresponds to `zero_eq_dist`. -/
@[simp]
/--
theorem `hamming_zero_eq_dist` / 定理 `hamming_zero_eq_dist`

English:
theorem hamming_zero_eq_dist
  given: {x y : forall i, β i}
  statement: 0 = hammingDist x y ↔ x = y
  proof: by
  rw [eq_comm]; rw [hammingDist_eq_zero]

中文:
定理 hamming_zero_eq_dist
  条件: {x y : 对任意 i, β i}
  结论: 0 = hammingDist x y ↔ x = y
  证明: by
  rw [eq_comm]; rw [hammingDist_eq_zero]

Depends on / 依赖: eq_comm, hammingDist_eq_zero
-/
theorem hamming_zero_eq_dist {x y : forall i, β i} : 0 = hammingDist x y ↔ x = y := by
  rw [eq_comm]; rw [hammingDist_eq_zero]

/--
theorem `hammingDist_ne_zero` / 定理 `hammingDist_ne_zero`

English:
theorem hammingDist_ne_zero
  given: {x y : forall i, β i}
  statement: hammingDist x y != 0 ↔ x != y
  proof: hammingDist_eq_zero.not

中文:
定理 hammingDist_ne_zero
  条件: {x y : 对任意 i, β i}
  结论: hammingDist x y != 0 ↔ x != y
  证明: hammingDist_eq_zero.not

Depends on / 依赖: hammingDist_eq_zero, hammingDist_eq_zero.not
-/
theorem hammingDist_ne_zero {x y : forall i, β i} : hammingDist x y != 0 ↔ x != y :=
  hammingDist_eq_zero.not

/-- Corresponds to `dist_pos`. -/
@[simp]
/--
theorem `hammingDist_pos` / 定理 `hammingDist_pos`

English:
theorem hammingDist_pos
  given: {x y : forall i, β i}
  statement: 0 < hammingDist x y ↔ x != y
  proof: by
  rw [← hammingDist_ne_zero]; rw [iff_not_comm]; rw [not_lt]; rw [Nat.le_zero]

中文:
定理 hammingDist_pos
  条件: {x y : 对任意 i, β i}
  结论: 0 < hammingDist x y ↔ x != y
  证明: by
  rw [← hammingDist_ne_zero]; rw [iff_not_comm]; rw [not_lt]; rw [Nat.le_zero]

Depends on / 依赖: Nat.le_zero, hammingDist_ne_zero, iff_not_comm, le_zero, not_lt
-/
theorem hammingDist_pos {x y : forall i, β i} : 0 < hammingDist x y ↔ x != y := by
  rw [← hammingDist_ne_zero]; rw [iff_not_comm]; rw [not_lt]; rw [Nat.le_zero]

/--
theorem `hammingDist_lt_one` / 定理 `hammingDist_lt_one`

English:
theorem hammingDist_lt_one
  given: {x y : forall i, β i}
  statement: hammingDist x y < 1 ↔ x = y
  proof: by
  rw [Nat.lt_one_iff]; rw [hammingDist_eq_zero]

中文:
定理 hammingDist_lt_one
  条件: {x y : 对任意 i, β i}
  结论: hammingDist x y < 1 ↔ x = y
  证明: by
  rw [Nat.lt_one_iff]; rw [hammingDist_eq_zero]

Depends on / 依赖: Nat.lt_one_iff, hammingDist_eq_zero, lt_one_iff
-/
theorem hammingDist_lt_one {x y : forall i, β i} : hammingDist x y < 1 ↔ x = y := by
  rw [Nat.lt_one_iff]; rw [hammingDist_eq_zero]

/--
theorem `hammingDist_le_card_fintype` / 定理 `hammingDist_le_card_fintype`

English:
theorem hammingDist_le_card_fintype
  given: {x y : forall i, β i}
  statement: hammingDist x y <= Fintype.card ι
  proof: card_le_univ _

中文:
定理 hammingDist_le_card_fintype
  条件: {x y : 对任意 i, β i}
  结论: hammingDist x y <= 有限类型.card ι
  证明: card_le_univ _

Depends on / 依赖: card_le_univ
-/
theorem hammingDist_le_card_fintype {x y : forall i, β i} : hammingDist x y <= Fintype.card ι :=
  card_le_univ _

/--
theorem `hammingDist_comp_le_hammingDist` / 定理 `hammingDist_comp_le_hammingDist`

English:
theorem hammingDist_comp_le_hammingDist
  given: (f : forall i, γ i -> β i) {x y : forall i, γ i}
  proof: by
  dsimp [hammingDist]; gcongr; simp +contextual

中文:
定理 hammingDist_comp_le_hammingDist
  条件: (f : 对任意 i, γ i -> β i) {x y : 对任意 i, γ i}
  证明: by
  dsimp [hammingDist]; gcongr; simp +contextual

Depends on / 依赖: contextual, hammingDist
-/
theorem hammingDist_comp_le_hammingDist (f : forall i, γ i -> β i) {x y : forall i, γ i} :
    hammingDist (fun i => f i (x i)) (fun i => f i (y i)) <= hammingDist x y := by
  dsimp [hammingDist]; gcongr; simp +contextual

/--
theorem `hammingDist_comp` / 定理 `hammingDist_comp`

English:
theorem hammingDist_comp
  given: (f : forall i, γ i -> β i) {x y : forall i, γ i} (hf : forall i, Injective (f i))
  proof: le_antisymm (hammingDist_comp_le_hammingDist _) by dsimp [hammingDist]; gcongr; exact @hf _ _ _

中文:
定理 hammingDist_comp
  条件: (f : 对任意 i, γ i -> β i) {x y : 对任意 i, γ i} (hf : 对任意 i, 单射 (f i))
  证明: le_antisymm (hammingDist_comp_le_hammingDist _) by dsimp [hammingDist]; gcongr; exact @hf _ _ _

Depends on / 依赖: hammingDist, hammingDist_comp_le_hammingDist, le_antisymm
-/
theorem hammingDist_comp (f : forall i, γ i -> β i) {x y : forall i, γ i} (hf : forall i, Injective (f i)) :
    hammingDist (fun i => f i (x i)) (fun i => f i (y i)) = hammingDist x y :=
le_antisymm (hammingDist_comp_le_hammingDist _) by dsimp [hammingDist]; gcongr; exact @hf _ _ _

/--
theorem `hammingDist_smul_le_hammingDist` / 定理 `hammingDist_smul_le_hammingDist`

English:
theorem hammingDist_smul_le_hammingDist
  given: [forall i, SMul α (β i)] {k : α} {x y : forall i, β i}
  proof: hammingDist_comp_le_hammingDist fun i => (k • · : β i -> β i)

中文:
定理 hammingDist_smul_le_hammingDist
  条件: [对任意 i, 标量乘法 α (β i)] {k : α} {x y : 对任意 i, β i}
  证明: hammingDist_comp_le_hammingDist fun i => (k • · : β i -> β i)

Depends on / 依赖: hammingDist_comp_le_hammingDist
-/
theorem hammingDist_smul_le_hammingDist [forall i, SMul α (β i)] {k : α} {x y : forall i, β i} :
    hammingDist (k • x) (k • y) <= hammingDist x y :=
  hammingDist_comp_le_hammingDist fun i => (k • · : β i -> β i)

/--
theorem `hammingDist_smul` / 定理 `hammingDist_smul`

English:
theorem hammingDist_smul
  statement: [forall i, SMul α (β i)] {k : α} {x y : forall i, β i}
  proof: hammingDist_comp (fun i => (k • · : β i -> β i)) hk

中文:
定理 hammingDist_smul
  结论: [对任意 i, 标量乘法 α (β i)] {k : α} {x y : 对任意 i, β i}
  证明: hammingDist_comp (fun i => (k • · : β i -> β i)) hk

Depends on / 依赖: hammingDist_comp
-/
theorem hammingDist_smul [forall i, SMul α (β i)] {k : α} {x y : forall i, β i}
    (hk : forall i, IsSMulRegular (β i) k) : hammingDist (k • x) (k • y) = hammingDist x y :=
  hammingDist_comp (fun i => (k • · : β i -> β i)) hk

section Zero

variable [forall i, Zero (β i)] [forall i, Zero (γ i)]

/--
Definition of `hammingNorm` / `hammingNorm` 的定义

English:
definition hammingNorm
  signature: (x : forall i, β i)
  body: #{i | x i != 0}

中文:
定义 hammingNorm
  签名: (x : 对任意 i, β i)
  定义体: #{i | x i != 0}
-/
def hammingNorm (x : forall i, β i) : Nat := #{i | x i != 0}

/-- Corresponds to `dist_zero_right`. -/
@[simp]
/--
theorem `hammingDist_zero_right` / 定理 `hammingDist_zero_right`

English:
theorem hammingDist_zero_right
  given: (x : forall i, β i)
  statement: hammingDist x 0 = hammingNorm x
  proof: rfl

中文:
定理 hammingDist_zero_right
  条件: (x : 对任意 i, β i)
  结论: hammingDist x 0 = hammingNorm x
  证明: rfl
-/
theorem hammingDist_zero_right (x : forall i, β i) : hammingDist x 0 = hammingNorm x :=
  rfl

/-- Corresponds to `dist_zero_left`. -/
@[simp]
/--
theorem `hammingDist_zero_left` / 定理 `hammingDist_zero_left`

English:
theorem hammingDist_zero_left
  statement: hammingDist (0 : forall i, β i) = hammingNorm
  proof: funext fun x => by rw [hammingDist_comm, hammingDist_zero_right]

中文:
定理 hammingDist_zero_left
  结论: hammingDist (0 : 对任意 i, β i) = hammingNorm
  证明: funext fun x => by rw [hammingDist_comm, hammingDist_zero_right]

Depends on / 依赖: hammingDist_comm, hammingDist_zero_right
-/
theorem hammingDist_zero_left : hammingDist (0 : forall i, β i) = hammingNorm :=
  funext fun x => by rw [hammingDist_comm, hammingDist_zero_right]

-- TODO: this seems unnecessary.
/--
theorem `hammingNorm_nonneg` / 定理 `hammingNorm_nonneg`

English:
theorem hammingNorm_nonneg
  given: {x : forall i, β i}
  statement: 0 <= hammingNorm x
  proof: zero_le

中文:
定理 hammingNorm_nonneg
  条件: {x : 对任意 i, β i}
  结论: 0 <= hammingNorm x
  证明: zero_le

Depends on / 依赖: zero_le
-/
theorem hammingNorm_nonneg {x : forall i, β i} : 0 <= hammingNorm x :=
  zero_le

/-- Corresponds to `norm_zero`. -/
@[simp]
/--
theorem `hammingNorm_zero` / 定理 `hammingNorm_zero`

English:
theorem hammingNorm_zero
  statement: hammingNorm (0 : forall i, β i) = 0
  proof: hammingDist_self _

中文:
定理 hammingNorm_zero
  结论: hammingNorm (0 : 对任意 i, β i) = 0
  证明: hammingDist_self _

Depends on / 依赖: hammingDist_self
-/
theorem hammingNorm_zero : hammingNorm (0 : forall i, β i) = 0 :=
  hammingDist_self _

/-- Corresponds to `norm_eq_zero`. -/
@[simp]
/--
theorem `hammingNorm_eq_zero` / 定理 `hammingNorm_eq_zero`

English:
theorem hammingNorm_eq_zero
  given: {x : forall i, β i}
  statement: hammingNorm x = 0 ↔ x = 0
  proof: hammingDist_eq_zero

中文:
定理 hammingNorm_eq_zero
  条件: {x : 对任意 i, β i}
  结论: hammingNorm x = 0 ↔ x = 0
  证明: hammingDist_eq_zero

Depends on / 依赖: hammingDist_eq_zero
-/
theorem hammingNorm_eq_zero {x : forall i, β i} : hammingNorm x = 0 ↔ x = 0 :=
  hammingDist_eq_zero

/--
theorem `hammingNorm_ne_zero_iff` / 定理 `hammingNorm_ne_zero_iff`

English:
theorem hammingNorm_ne_zero_iff
  given: {x : forall i, β i}
  statement: hammingNorm x != 0 ↔ x != 0
  proof: hammingNorm_eq_zero.not

中文:
定理 hammingNorm_ne_zero_iff
  条件: {x : 对任意 i, β i}
  结论: hammingNorm x != 0 ↔ x != 0
  证明: hammingNorm_eq_zero.not

Depends on / 依赖: hammingNorm_eq_zero, hammingNorm_eq_zero.not
-/
theorem hammingNorm_ne_zero_iff {x : forall i, β i} : hammingNorm x != 0 ↔ x != 0 :=
  hammingNorm_eq_zero.not

/-- Corresponds to `norm_pos_iff`. -/
@[simp]
/--
theorem `hammingNorm_pos_iff` / 定理 `hammingNorm_pos_iff`

English:
theorem hammingNorm_pos_iff
  given: {x : forall i, β i}
  statement: 0 < hammingNorm x ↔ x != 0
  proof: hammingDist_pos

中文:
定理 hammingNorm_pos_iff
  条件: {x : 对任意 i, β i}
  结论: 0 < hammingNorm x ↔ x != 0
  证明: hammingDist_pos

Depends on / 依赖: hammingDist_pos
-/
theorem hammingNorm_pos_iff {x : forall i, β i} : 0 < hammingNorm x ↔ x != 0 :=
  hammingDist_pos

/--
theorem `hammingNorm_lt_one` / 定理 `hammingNorm_lt_one`

English:
theorem hammingNorm_lt_one
  given: {x : forall i, β i}
  statement: hammingNorm x < 1 ↔ x = 0
  proof: hammingDist_lt_one

中文:
定理 hammingNorm_lt_one
  条件: {x : 对任意 i, β i}
  结论: hammingNorm x < 1 ↔ x = 0
  证明: hammingDist_lt_one

Depends on / 依赖: hammingDist_lt_one
-/
theorem hammingNorm_lt_one {x : forall i, β i} : hammingNorm x < 1 ↔ x = 0 :=
  hammingDist_lt_one

/--
theorem `hammingNorm_le_card_fintype` / 定理 `hammingNorm_le_card_fintype`

English:
theorem hammingNorm_le_card_fintype
  given: {x : forall i, β i}
  statement: hammingNorm x <= Fintype.card ι
  proof: hammingDist_le_card_fintype

中文:
定理 hammingNorm_le_card_fintype
  条件: {x : 对任意 i, β i}
  结论: hammingNorm x <= 有限类型.card ι
  证明: hammingDist_le_card_fintype

Depends on / 依赖: hammingDist_le_card_fintype
-/
theorem hammingNorm_le_card_fintype {x : forall i, β i} : hammingNorm x <= Fintype.card ι :=
  hammingDist_le_card_fintype

/--
theorem `hammingNorm_comp_le_hammingNorm` / 定理 `hammingNorm_comp_le_hammingNorm`

English:
theorem hammingNorm_comp_le_hammingNorm
  given: (f : forall i, γ i -> β i) {x : forall i, γ i} (hf : forall i, f i 0 = 0)
  proof: by
  simpa only [← hammingDist_zero_right, hf]
    using! hammingDist_comp_le_hammingDist f (y := fun _ => 0)

中文:
定理 hammingNorm_comp_le_hammingNorm
  条件: (f : 对任意 i, γ i -> β i) {x : 对任意 i, γ i} (hf : 对任意 i, f i 0 = 0)
  证明: by
  simpa only [← hammingDist_zero_right, hf]
    using! hammingDist_comp_le_hammingDist f (y := fun _ => 0)

Depends on / 依赖: hammingDist_comp_le_hammingDist, hammingDist_zero_right
-/
theorem hammingNorm_comp_le_hammingNorm (f : forall i, γ i -> β i) {x : forall i, γ i} (hf : forall i, f i 0 = 0) :
    (hammingNorm fun i => f i (x i)) <= hammingNorm x := by
  simpa only [← hammingDist_zero_right, hf]
    using! hammingDist_comp_le_hammingDist f (y := fun _ => 0)

/--
theorem `hammingNorm_comp` / 定理 `hammingNorm_comp`

English:
theorem hammingNorm_comp
  statement: (f : forall i, γ i -> β i) {x : forall i, γ i} (hf₁ : forall i, Injective (f i))
  proof: by
  simpa only [← hammingDist_zero_right, hf₂] using! hammingDist_comp f hf₁ (y := fun _ => 0)

中文:
定理 hammingNorm_comp
  结论: (f : 对任意 i, γ i -> β i) {x : 对任意 i, γ i} (hf₁ : 对任意 i, 单射 (f i))
  证明: by
  simpa only [← hammingDist_zero_right, hf₂] using! hammingDist_comp f hf₁ (y := fun _ => 0)

Depends on / 依赖: hammingDist_comp, hammingDist_zero_right
-/
theorem hammingNorm_comp (f : forall i, γ i -> β i) {x : forall i, γ i} (hf₁ : forall i, Injective (f i))
    (hf₂ : forall i, f i 0 = 0) : (hammingNorm fun i => f i (x i)) = hammingNorm x := by
  simpa only [← hammingDist_zero_right, hf₂] using! hammingDist_comp f hf₁ (y := fun _ => 0)

/--
theorem `hammingNorm_smul_le_hammingNorm` / 定理 `hammingNorm_smul_le_hammingNorm`

English:
theorem hammingNorm_smul_le_hammingNorm
  statement: [Zero α] [forall i, SMulWithZero α (β i)] {k : α}
  proof: hammingNorm_comp_le_hammingNorm (fun i (c : β i) => k • c) fun i => by simp_rw [smul_zero]

中文:
定理 hammingNorm_smul_le_hammingNorm
  结论: [零 α] [对任意 i, 带零标量乘法 α (β i)] {k : α}
  证明: hammingNorm_comp_le_hammingNorm (fun i (c : β i) => k • c) fun i => by simp_rw [smul_zero]

Depends on / 依赖: hammingNorm_comp_le_hammingNorm, simp_rw, smul_zero
-/
theorem hammingNorm_smul_le_hammingNorm [Zero α] [forall i, SMulWithZero α (β i)] {k : α}
    {x : forall i, β i} : hammingNorm (k • x) <= hammingNorm x :=
  hammingNorm_comp_le_hammingNorm (fun i (c : β i) => k • c) fun i => by simp_rw [smul_zero]

/--
theorem `hammingNorm_smul` / 定理 `hammingNorm_smul`

English:
theorem hammingNorm_smul
  statement: [Zero α] [forall i, SMulWithZero α (β i)] {k : α}
  proof: hammingNorm_comp (fun i (c : β i) => k • c) hk fun i => by simp_rw [smul_zero]

中文:
定理 hammingNorm_smul
  结论: [零 α] [对任意 i, 带零标量乘法 α (β i)] {k : α}
  证明: hammingNorm_comp (fun i (c : β i) => k • c) hk fun i => by simp_rw [smul_zero]

Depends on / 依赖: hammingNorm_comp, simp_rw, smul_zero
-/
theorem hammingNorm_smul [Zero α] [forall i, SMulWithZero α (β i)] {k : α}
    (hk : forall i, IsSMulRegular (β i) k) (x : forall i, β i) : hammingNorm (k • x) = hammingNorm x :=
  hammingNorm_comp (fun i (c : β i) => k • c) hk fun i => by simp_rw [smul_zero]

end Zero

/--
theorem `hammingDist_eq_hammingNorm` / 定理 `hammingDist_eq_hammingNorm`

English:
theorem hammingDist_eq_hammingNorm
  given: [forall i, AddGroup (β i)] (x y : forall i, β i)
  proof: by
  simp_rw [hammingNorm, hammingDist, Pi.add_apply, Pi.neg_apply, ne_eq, neg_add_eq_zero]

中文:
定理 hammingDist_eq_hammingNorm
  条件: [对任意 i, 加法群 (β i)] (x y : 对任意 i, β i)
  证明: by
  simp_rw [hammingNorm, hammingDist, Pi.add_apply, Pi.neg_apply, ne_eq, neg_add_eq_zero]

Depends on / 依赖: Pi.add_apply, Pi.neg_apply, add_apply, hammingDist, hammingNorm, ne_eq, neg_add_eq_zero, neg_apply, simp_rw
-/
theorem hammingDist_eq_hammingNorm [forall i, AddGroup (β i)] (x y : forall i, β i) :
    hammingDist x y = hammingNorm (-x + y) := by
  simp_rw [hammingNorm, hammingDist, Pi.add_apply, Pi.neg_apply, ne_eq, neg_add_eq_zero]

end HammingDistNorm

/-! ### The `Hamming` type synonym -/

/--
Definition of `Hamming` / `Hamming` 的定义

English:
definition Hamming
  signature: {ι : Type*} (β : ι -> Type*)
  body: forall i, β i

中文:
定义 Hamming
  签名: {ι : 类型} (β : ι -> 类型)
  定义体: forall i, β i
-/
def Hamming {ι : Type*} (β : ι -> Type*) : Type _ :=
  forall i, β i

namespace Hamming

variable {α ι : Type*} {β : ι -> Type*}


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Inhabited (β i)] : Inhabited (Hamming β)
  body: inferInstanceAs Inhabited (forall i, β i)

中文:
实例 [对任意
  签名: i, 可居 (β i)] : 可居 (Hamming β)
  定义体: inferInstanceAs Inhabited (forall i, β i)

Depends on / 依赖: Inhabited
-/
instance [forall i, Inhabited (β i)] : Inhabited (Hamming β) :=
inferInstanceAs Inhabited (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: ι] [Fintype ι] [forall i, Fintype (β i)] : Fintype (Hamming β)
  body: inferInstanceAs Fintype (forall i, β i)

中文:
实例 [DecidableEq
  签名: ι] [有限类型 ι] [对任意 i, 有限类型 (β i)] : 有限类型 (Hamming β)
  定义体: inferInstanceAs Fintype (forall i, β i)

Depends on / 依赖: Fintype
-/
instance [DecidableEq ι] [Fintype ι] [forall i, Fintype (β i)] : Fintype (Hamming β) :=
inferInstanceAs Fintype (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: ι] [forall i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (Hamming β)
  body: inferInstanceAs Nontrivial (forall i, β i)

中文:
实例 [可居
  签名: ι] [对任意 i, 非空 (β i)] [非平凡 (β default)] : 非平凡 (Hamming β)
  定义体: inferInstanceAs Nontrivial (forall i, β i)

Depends on / 依赖: Nontrivial
-/
instance [Inhabited ι] [forall i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (Hamming β) :=
inferInstanceAs Nontrivial (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: ι] [forall i, DecidableEq (β i)] : DecidableEq (Hamming β)
  body: inferInstanceAs DecidableEq (forall i, β i)

中文:
实例 [有限类型
  签名: ι] [对任意 i, DecidableEq (β i)] : DecidableEq (Hamming β)
  定义体: inferInstanceAs DecidableEq (forall i, β i)

Depends on / 依赖: DecidableEq
-/
instance [Fintype ι] [forall i, DecidableEq (β i)] : DecidableEq (Hamming β) :=
inferInstanceAs DecidableEq (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Zero (β i)] : Zero (Hamming β)
  body: inferInstanceAs Zero (forall i, β i)

中文:
实例 [对任意
  签名: i, 零 (β i)] : 零 (Hamming β)
  定义体: inferInstanceAs Zero (forall i, β i)
-/
instance [forall i, Zero (β i)] : Zero (Hamming β) :=
inferInstanceAs Zero (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Neg (β i)] : Neg (Hamming β)
  body: inferInstanceAs Neg (forall i, β i)

中文:
实例 [对任意
  签名: i, 取负 (β i)] : 取负 (Hamming β)
  定义体: inferInstanceAs Neg (forall i, β i)
-/
instance [forall i, Neg (β i)] : Neg (Hamming β) :=
inferInstanceAs Neg (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Add (β i)] : Add (Hamming β)
  body: inferInstanceAs Add (forall i, β i)

中文:
实例 [对任意
  签名: i, 加法 (β i)] : 加法 (Hamming β)
  定义体: inferInstanceAs Add (forall i, β i)
-/
instance [forall i, Add (β i)] : Add (Hamming β) :=
inferInstanceAs Add (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Sub (β i)] : Sub (Hamming β)
  body: inferInstanceAs Sub (forall i, β i)

中文:
实例 [对任意
  签名: i, 减法 (β i)] : 减法 (Hamming β)
  定义体: inferInstanceAs Sub (forall i, β i)
-/
instance [forall i, Sub (β i)] : Sub (Hamming β) :=
inferInstanceAs Sub (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, SMul α (β i)] : SMul α (Hamming β)
  body: inferInstanceAs SMul α (forall i, β i)

中文:
实例 [对任意
  签名: i, 标量乘法 α (β i)] : 标量乘法 α (Hamming β)
  定义体: inferInstanceAs SMul α (forall i, β i)
-/
instance [forall i, SMul α (β i)] : SMul α (Hamming β) :=
inferInstanceAs SMul α (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: α] [forall i, Zero (β i)] [forall i, SMulWithZero α (β i)] : SMulWithZero α (Hamming β)
  body: inferInstanceAs SMulWithZero α (forall i, β i)

中文:
实例 [零
  签名: α] [对任意 i, 零 (β i)] [对任意 i, 带零标量乘法 α (β i)] : 带零标量乘法 α (Hamming β)
  定义体: inferInstanceAs SMulWithZero α (forall i, β i)

Depends on / 依赖: SMulWithZero
-/
instance [Zero α] [forall i, Zero (β i)] [forall i, SMulWithZero α (β i)] : SMulWithZero α (Hamming β) :=
inferInstanceAs SMulWithZero α (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddMonoid (β i)] : AddMonoid (Hamming β)
  body: inferInstanceAs AddMonoid (forall i, β i)

中文:
实例 [对任意
  签名: i, 加法幺半群 (β i)] : 加法幺半群 (Hamming β)
  定义体: inferInstanceAs AddMonoid (forall i, β i)

Depends on / 依赖: AddMonoid
-/
instance [forall i, AddMonoid (β i)] : AddMonoid (Hamming β) :=
inferInstanceAs AddMonoid (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddGroup (β i)] : AddGroup (Hamming β)
  body: inferInstanceAs AddGroup (forall i, β i)

中文:
实例 [对任意
  签名: i, 加法群 (β i)] : 加法群 (Hamming β)
  定义体: inferInstanceAs AddGroup (forall i, β i)

Depends on / 依赖: AddGroup
-/
instance [forall i, AddGroup (β i)] : AddGroup (Hamming β) :=
inferInstanceAs AddGroup (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddCommMonoid (β i)] : AddCommMonoid (Hamming β)
  body: inferInstanceAs AddCommMonoid (forall i, β i)

中文:
实例 [对任意
  签名: i, 加法交换幺半群 (β i)] : 加法交换幺半群 (Hamming β)
  定义体: inferInstanceAs AddCommMonoid (forall i, β i)

Depends on / 依赖: AddCommMonoid
-/
instance [forall i, AddCommMonoid (β i)] : AddCommMonoid (Hamming β) :=
inferInstanceAs AddCommMonoid (forall i, β i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddCommGroup (β i)] : AddCommGroup (Hamming β)
  body: inferInstanceAs AddCommGroup (forall i, β i)

中文:
实例 [对任意
  签名: i, 加法交换群 (β i)] : 加法交换群 (Hamming β)
  定义体: inferInstanceAs AddCommGroup (forall i, β i)

Depends on / 依赖: AddCommGroup
-/
instance [forall i, AddCommGroup (β i)] : AddCommGroup (Hamming β) :=
inferInstanceAs AddCommGroup (forall i, β i)

instance (α) [Semiring α] (β : ι -> Type*) [forall i, AddCommMonoid (β i)] [forall i, Module α (β i)] :
    Module α (Hamming β) :=
inferInstanceAs Module α (forall i, β i)

/-! API to/from the type synonym. -/


/-- `Hamming.toHamming` is the identity function to the `Hamming` of a type. -/
@[match_pattern]
/--
Definition of `toHamming` / `toHamming` 的定义

English:
definition toHamming
  signature: : (forall i, β i) ≃ Hamming β
  body: Equiv.refl _

中文:
定义 toHamming
  签名: : (对任意 i, β i) ≃ Hamming β
  定义体: Equiv.refl _

Depends on / 依赖: Equiv.refl
-/
def toHamming : (forall i, β i) ≃ Hamming β :=
  Equiv.refl _

/-- `Hamming.ofHamming` is the identity function from the `Hamming` of a type. -/
@[match_pattern]
/--
Definition of `ofHamming` / `ofHamming` 的定义

English:
definition ofHamming
  signature: : Hamming β ≃ forall i, β i
  body: Equiv.refl _

@[simp]

中文:
定义 ofHamming
  签名: : Hamming β ≃ 对任意 i, β i
  定义体: Equiv.refl _

@[simp]

Depends on / 依赖: Equiv.refl
-/
def ofHamming : Hamming β ≃ forall i, β i :=
  Equiv.refl _

@[simp]
/--
theorem `toHamming_symm_eq` / 定理 `toHamming_symm_eq`

English:
theorem toHamming_symm_eq
  statement: (@toHamming _ β).symm = ofHamming
  proof: rfl

@[simp]

中文:
定理 toHamming_symm_eq
  结论: (@toHamming _ β).symm = ofHamming
  证明: rfl

@[simp]
-/
theorem toHamming_symm_eq : (@toHamming _ β).symm = ofHamming :=
  rfl

@[simp]
/--
theorem `ofHamming_symm_eq` / 定理 `ofHamming_symm_eq`

English:
theorem ofHamming_symm_eq
  statement: (@ofHamming _ β).symm = toHamming
  proof: rfl

@[simp]

中文:
定理 ofHamming_symm_eq
  结论: (@ofHamming _ β).symm = toHamming
  证明: rfl

@[simp]
-/
theorem ofHamming_symm_eq : (@ofHamming _ β).symm = toHamming :=
  rfl

@[simp]
/--
theorem `toHamming_ofHamming` / 定理 `toHamming_ofHamming`

English:
theorem toHamming_ofHamming
  given: (x : Hamming β)
  statement: toHamming (ofHamming x) = x
  proof: rfl

@[simp]

中文:
定理 toHamming_ofHamming
  条件: (x : Hamming β)
  结论: toHamming (ofHamming x) = x
  证明: rfl

@[simp]
-/
theorem toHamming_ofHamming (x : Hamming β) : toHamming (ofHamming x) = x :=
  rfl

@[simp]
/--
theorem `ofHamming_toHamming` / 定理 `ofHamming_toHamming`

English:
theorem ofHamming_toHamming
  given: (x : forall i, β i)
  statement: ofHamming (toHamming x) = x
  proof: rfl

中文:
定理 ofHamming_toHamming
  条件: (x : 对任意 i, β i)
  结论: ofHamming (toHamming x) = x
  证明: rfl
-/
theorem ofHamming_toHamming (x : forall i, β i) : ofHamming (toHamming x) = x :=
  rfl

/--
theorem `toHamming_inj` / 定理 `toHamming_inj`

English:
theorem toHamming_inj
  given: {x y : forall i, β i}
  statement: toHamming x = toHamming y ↔ x = y
  proof: Iff.rfl

中文:
定理 toHamming_inj
  条件: {x y : 对任意 i, β i}
  结论: toHamming x = toHamming y ↔ x = y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toHamming_inj {x y : forall i, β i} : toHamming x = toHamming y ↔ x = y :=
  Iff.rfl

/--
theorem `ofHamming_inj` / 定理 `ofHamming_inj`

English:
theorem ofHamming_inj
  given: {x y : Hamming β}
  statement: ofHamming x = ofHamming y ↔ x = y
  proof: Iff.rfl

@[simp]

中文:
定理 ofHamming_inj
  条件: {x y : Hamming β}
  结论: ofHamming x = ofHamming y ↔ x = y
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem ofHamming_inj {x y : Hamming β} : ofHamming x = ofHamming y ↔ x = y :=
  Iff.rfl

@[simp]
/--
theorem `toHamming_zero` / 定理 `toHamming_zero`

English:
theorem toHamming_zero
  given: [forall i, Zero (β i)]
  statement: toHamming (0 : forall i, β i) = 0
  proof: rfl

@[simp]

中文:
定理 toHamming_zero
  条件: [对任意 i, 零 (β i)]
  结论: toHamming (0 : 对任意 i, β i) = 0
  证明: rfl

@[simp]
-/
theorem toHamming_zero [forall i, Zero (β i)] : toHamming (0 : forall i, β i) = 0 :=
  rfl

@[simp]
/--
theorem `ofHamming_zero` / 定理 `ofHamming_zero`

English:
theorem ofHamming_zero
  given: [forall i, Zero (β i)]
  statement: ofHamming (0 : Hamming β) = 0
  proof: rfl

@[simp]

中文:
定理 ofHamming_zero
  条件: [对任意 i, 零 (β i)]
  结论: ofHamming (0 : Hamming β) = 0
  证明: rfl

@[simp]
-/
theorem ofHamming_zero [forall i, Zero (β i)] : ofHamming (0 : Hamming β) = 0 :=
  rfl

@[simp]
/--
theorem `toHamming_neg` / 定理 `toHamming_neg`

English:
theorem toHamming_neg
  given: [forall i, Neg (β i)] {x : forall i, β i}
  statement: toHamming (-x) = -toHamming x
  proof: rfl

@[simp]

中文:
定理 toHamming_neg
  条件: [对任意 i, 取负 (β i)] {x : 对任意 i, β i}
  结论: toHamming (-x) = -toHamming x
  证明: rfl

@[simp]
-/
theorem toHamming_neg [forall i, Neg (β i)] {x : forall i, β i} : toHamming (-x) = -toHamming x :=
  rfl

@[simp]
/--
theorem `ofHamming_neg` / 定理 `ofHamming_neg`

English:
theorem ofHamming_neg
  given: [forall i, Neg (β i)] {x : Hamming β}
  statement: ofHamming (-x) = -ofHamming x
  proof: rfl

@[simp]

中文:
定理 ofHamming_neg
  条件: [对任意 i, 取负 (β i)] {x : Hamming β}
  结论: ofHamming (-x) = -ofHamming x
  证明: rfl

@[simp]
-/
theorem ofHamming_neg [forall i, Neg (β i)] {x : Hamming β} : ofHamming (-x) = -ofHamming x :=
  rfl

@[simp]
/--
theorem `toHamming_add` / 定理 `toHamming_add`

English:
theorem toHamming_add
  given: [forall i, Add (β i)] {x y : forall i, β i}
  proof: rfl

@[simp]

中文:
定理 toHamming_add
  条件: [对任意 i, 加法 (β i)] {x y : 对任意 i, β i}
  证明: rfl

@[simp]
-/
theorem toHamming_add [forall i, Add (β i)] {x y : forall i, β i} :
    toHamming (x + y) = toHamming x + toHamming y :=
  rfl

@[simp]
/--
theorem `ofHamming_add` / 定理 `ofHamming_add`

English:
theorem ofHamming_add
  given: [forall i, Add (β i)] {x y : Hamming β}
  proof: rfl

@[simp]

中文:
定理 ofHamming_add
  条件: [对任意 i, 加法 (β i)] {x y : Hamming β}
  证明: rfl

@[simp]
-/
theorem ofHamming_add [forall i, Add (β i)] {x y : Hamming β} :
    ofHamming (x + y) = ofHamming x + ofHamming y :=
  rfl

@[simp]
/--
theorem `toHamming_sub` / 定理 `toHamming_sub`

English:
theorem toHamming_sub
  given: [forall i, Sub (β i)] {x y : forall i, β i}
  proof: rfl

@[simp]

中文:
定理 toHamming_sub
  条件: [对任意 i, 减法 (β i)] {x y : 对任意 i, β i}
  证明: rfl

@[simp]
-/
theorem toHamming_sub [forall i, Sub (β i)] {x y : forall i, β i} :
    toHamming (x - y) = toHamming x - toHamming y :=
  rfl

@[simp]
/--
theorem `ofHamming_sub` / 定理 `ofHamming_sub`

English:
theorem ofHamming_sub
  given: [forall i, Sub (β i)] {x y : Hamming β}
  proof: rfl

@[simp]

中文:
定理 ofHamming_sub
  条件: [对任意 i, 减法 (β i)] {x y : Hamming β}
  证明: rfl

@[simp]
-/
theorem ofHamming_sub [forall i, Sub (β i)] {x y : Hamming β} :
    ofHamming (x - y) = ofHamming x - ofHamming y :=
  rfl

@[simp]
/--
theorem `toHamming_smul` / 定理 `toHamming_smul`

English:
theorem toHamming_smul
  given: [forall i, SMul α (β i)] {r : α} {x : forall i, β i}
  proof: rfl

@[simp]

中文:
定理 toHamming_smul
  条件: [对任意 i, 标量乘法 α (β i)] {r : α} {x : 对任意 i, β i}
  证明: rfl

@[simp]
-/
theorem toHamming_smul [forall i, SMul α (β i)] {r : α} {x : forall i, β i} :
    toHamming (r • x) = r • toHamming x :=
  rfl

@[simp]
/--
theorem `ofHamming_smul` / 定理 `ofHamming_smul`

English:
theorem ofHamming_smul
  given: [forall i, SMul α (β i)] {r : α} {x : Hamming β}
  proof: rfl

中文:
定理 ofHamming_smul
  条件: [对任意 i, 标量乘法 α (β i)] {r : α} {x : Hamming β}
  证明: rfl
-/
theorem ofHamming_smul [forall i, SMul α (β i)] {r : α} {x : Hamming β} :
    ofHamming (r • x) = r • ofHamming x :=
  rfl

section

/-! Instances equipping `Hamming` with `hammingNorm` and `hammingDist`. -/

variable [Fintype ι] [forall i, DecidableEq (β i)]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Dist (Hamming β)
  body: ⟨fun x y => hammingDist (ofHamming x) (ofHamming y)⟩

@[simp, push_cast]

中文:
实例 :
  签名: Dist (Hamming β)
  定义体: ⟨fun x y => hammingDist (ofHamming x) (ofHamming y)⟩

@[simp, push_cast]

Depends on / 依赖: hammingDist, ofHamming
-/
instance : Dist (Hamming β) :=
  ⟨fun x y => hammingDist (ofHamming x) (ofHamming y)⟩

@[simp, push_cast]
/--
theorem `dist_eq_hammingDist` / 定理 `dist_eq_hammingDist`

English:
theorem dist_eq_hammingDist
  given: (x y : Hamming β)
  proof: rfl

中文:
定理 dist_eq_hammingDist
  条件: (x y : Hamming β)
  证明: rfl
-/
theorem dist_eq_hammingDist (x y : Hamming β) :
    dist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PseudoMetricSpace (Hamming β)
  body: by
    push_cast
    exact mod_cast hammingDist_self
  dist_comm := by
    push_cast
    exact mod_cast hammingDist_comm
  dist_triangle := by
    push_cast
    exact mod_cast hammingDist_triangle
  toUniformSpace := ⊥
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ fun s => by
    push_cast
    constructor
· refine fun hs => ⟨1, zero_lt_one, fun hab => hs by simpa using hab⟩
    · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ rfl
      refine hs (lt_of_eq_of_lt ?_ hε)
      exact mod_cast hammingDist_self _
  toBornology := ⟨⊥, bot_le⟩
  cobounded_sets := by
    ext
    push_cast
    refine iff_of_true (Filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => ?_⟩
    exact mod_cast hammingDist_le_card_fintype

@[simp, push_cast]

中文:
实例 :
  签名: 伪度量空间 (Hamming β)
  定义体: by
    push_cast
    exact mod_cast hammingDist_self
  dist_comm := by
    push_cast
    exact mod_cast hammingDist_comm
  dist_triangle := by
    push_cast
    exact mod_cast hammingDist_triangle
  toUniformSpace := ⊥
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ fun s => by
    push_cast
    constructor
· refine fun hs => ⟨1, zero_lt_one, fun hab => hs by simpa using hab⟩
    · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ rfl
      refine hs (lt_of_eq_of_lt ?_ hε)
      exact mod_cast hammingDist_self _
  toBornology := ⟨⊥, bot_le⟩
  cobounded_sets := by
    ext
    push_cast
    refine iff_of_true (Filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => ?_⟩
    exact mod_cast hammingDist_le_card_fintype

@[simp, push_cast]

Depends on / 依赖: bot_le, cobounded_sets, dist_comm, dist_triangle, hammingDist_comm, hammingDist_self, hammingDist_triangle, lt_of_eq_of_lt, mod_cast, toBornology, toUniformSpace, uniformity_dist, uniformity_dist_of_mem_uniformity, zero_lt_one
-/
instance : PseudoMetricSpace (Hamming β) where
  dist_self := by
    push_cast
    exact mod_cast hammingDist_self
  dist_comm := by
    push_cast
    exact mod_cast hammingDist_comm
  dist_triangle := by
    push_cast
    exact mod_cast hammingDist_triangle
  toUniformSpace := ⊥
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ fun s => by
    push_cast
    constructor
· refine fun hs => ⟨1, zero_lt_one, fun hab => hs by simpa using hab⟩
    · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ rfl
      refine hs (lt_of_eq_of_lt ?_ hε)
      exact mod_cast hammingDist_self _
  toBornology := ⟨⊥, bot_le⟩
  cobounded_sets := by
    ext
    push_cast
    refine iff_of_true (Filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => ?_⟩
    exact mod_cast hammingDist_le_card_fintype

@[simp, push_cast]
/--
theorem `nndist_eq_hammingDist` / 定理 `nndist_eq_hammingDist`

English:
theorem nndist_eq_hammingDist
  given: (x y : Hamming β)
  proof: rfl

中文:
定理 nndist_eq_hammingDist
  条件: (x y : Hamming β)
  证明: rfl
-/
theorem nndist_eq_hammingDist (x y : Hamming β) :
    nndist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DiscreteTopology (Hamming β)
  body: ⟨rfl⟩

中文:
实例 :
  签名: 离散拓扑 (Hamming β)
  定义体: ⟨rfl⟩
-/
instance : DiscreteTopology (Hamming β) := ⟨rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MetricSpace (Hamming β)
  body: .ofT0PseudoMetricSpace _

中文:
实例 :
  签名: 度量空间 (Hamming β)
  定义体: .ofT0PseudoMetricSpace _

Depends on / 依赖: ofT0PseudoMetricSpace
-/
instance : MetricSpace (Hamming β) := .ofT0PseudoMetricSpace _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, Zero (β i)] : Norm (Hamming β)
  body: ⟨fun x => hammingNorm (ofHamming x)⟩

@[simp, push_cast]

中文:
实例 [对任意
  签名: i, 零 (β i)] : 范数 (Hamming β)
  定义体: ⟨fun x => hammingNorm (ofHamming x)⟩

@[simp, push_cast]

Depends on / 依赖: hammingNorm, ofHamming
-/
instance [forall i, Zero (β i)] : Norm (Hamming β) :=
  ⟨fun x => hammingNorm (ofHamming x)⟩

@[simp, push_cast]
/--
theorem `norm_eq_hammingNorm` / 定理 `norm_eq_hammingNorm`

English:
theorem norm_eq_hammingNorm
  given: [forall i, Zero (β i)] (x : Hamming β)
  statement: ‖x‖ = hammingNorm (ofHamming x)
  proof: rfl

中文:
定理 norm_eq_hammingNorm
  条件: [对任意 i, 零 (β i)] (x : Hamming β)
  结论: ‖x‖ = hammingNorm (ofHamming x)
  证明: rfl
-/
theorem norm_eq_hammingNorm [forall i, Zero (β i)] (x : Hamming β) : ‖x‖ = hammingNorm (ofHamming x) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddGroup (β i)] : NormedAddGroup (Hamming β) where
  body: by push_cast; exact mod_cast hammingDist_eq_hammingNorm

中文:
实例 [对任意
  签名: i, 加法群 (β i)] : 赋范加群 (Hamming β) where
  定义体: by push_cast; exact mod_cast hammingDist_eq_hammingNorm

Depends on / 依赖: hammingDist_eq_hammingNorm, mod_cast
-/
instance [forall i, AddGroup (β i)] : NormedAddGroup (Hamming β) where
  dist_eq := by push_cast; exact mod_cast hammingDist_eq_hammingNorm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [forall
  signature: i, AddCommGroup (β i)] : NormedAddCommGroup (Hamming β) where
  body: fun x y => NormedAddGroup.dist_eq x y

@[simp, push_cast]

中文:
实例 [对任意
  签名: i, 加法交换群 (β i)] : 赋范交换加群 (Hamming β) where
  定义体: fun x y => NormedAddGroup.dist_eq x y

@[simp, push_cast]

Depends on / 依赖: NormedAddGroup, NormedAddGroup.dist_eq, dist_eq
-/
instance [forall i, AddCommGroup (β i)] : NormedAddCommGroup (Hamming β) where
  dist_eq := fun x y => NormedAddGroup.dist_eq x y

@[simp, push_cast]
/--
theorem `nnnorm_eq_hammingNorm` / 定理 `nnnorm_eq_hammingNorm`

English:
theorem nnnorm_eq_hammingNorm
  given: [forall i, AddGroup (β i)] (x : Hamming β)
  proof: rfl

中文:
定理 nnnorm_eq_hammingNorm
  条件: [对任意 i, 加法群 (β i)] (x : Hamming β)
  证明: rfl
-/
theorem nnnorm_eq_hammingNorm [forall i, AddGroup (β i)] (x : Hamming β) :
    ‖x‖₊ = hammingNorm (ofHamming x) := rfl

end

end Hamming
