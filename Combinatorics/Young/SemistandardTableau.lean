/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
module

public import Mathlib.Combinatorics.Young.YoungDiagram

/-!
# Semistandard Young tableaux

A semistandard Young tableau is a filling of a Young diagram by natural numbers, such that
the entries are weakly increasing left-to-right along rows (i.e. for fixed `i`), and
strictly-increasing top-to-bottom along columns (i.e. for fixed `j`).

An example of an SSYT of shape `μ = [4, 2, 1]` is:

```text
0 0 0 2
1 1
2
```

We represent a semistandard Young tableau as a function `ℕ → ℕ → ℕ`, which is required to be zero
for all pairs `(i, j) ∉ μ` and to satisfy the row-weak and column-strict conditions on `μ`.


## Main definitions

- `SemistandardYoungTableau (μ : YoungDiagram)`: semistandard Young tableaux of shape `μ`. There is
  a `coe` instance such that `T i j` is value of the `(i, j)` entry of the semistandard Young
  tableau `T`.
- `SemistandardYoungTableau.highestWeight (μ : YoungDiagram)`: the semistandard Young tableau whose
  `i`th row consists entirely of `i`s, for each `i`.

## Tags

Semistandard Young tableau

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/

@[expose] public section


/--
Definition of `SemistandardYoungTableau` / `SemistandardYoungTableau` 的定义

English:
structure SemistandardYoungTableau
  parameters: (μ : YoungDiagram)
  axioms and operations (4):
    - entry : Nat -> Nat -> Nat
    - row_weak' : forall {i j1 j2 : Nat}, j1 < j2 -> (i, j2) in μ -> entry i j1 <= entry i j2
    - col_strict' : forall {i1 i2 j : Nat}, i1 < i2 -> (i2, j) in μ -> entry i1 j < entry i2 j
    - zeros' : forall {i j}, (i, j) ∉ μ -> entry i j = 0

中文:
结构 半标准Young表
  参数: (μ : Young图)
  公理与运算 (4 个):
    - entry : 自然数 -> 自然数 -> 自然数
    - row_weak' : 对任意 {i j1 j2 : 自然数}, j1 < j2 -> (i, j2) in μ -> entry i j1 <= entry i j2
    - col_strict' : 对任意 {i1 i2 j : 自然数}, i1 < i2 -> (i2, j) in μ -> entry i1 j < entry i2 j
    - zeros' : 对任意 {i j}, (i, j) ∉ μ -> entry i j = 0
-/
structure SemistandardYoungTableau (μ : YoungDiagram) where
  /-- `entry i j` is value of the `(i, j)` entry of the SSYT `μ`. -/
  entry : Nat -> Nat -> Nat
  /-- The entries in each row are weakly increasing (left to right). -/
  row_weak' : forall {i j1 j2 : Nat}, j1 < j2 -> (i, j2) in μ -> entry i j1 <= entry i j2
  /-- The entries in each column are strictly increasing (top to bottom). -/
  col_strict' : forall {i1 i2 j : Nat}, i1 < i2 -> (i2, j) in μ -> entry i1 j < entry i2 j
  /-- `entry` is required to be zero for all pairs `(i, j) ∉ μ`. -/
  zeros' : forall {i j}, (i, j) ∉ μ -> entry i j = 0

namespace SemistandardYoungTableau

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: {μ : YoungDiagram}
  body: SemistandardYoungTableau.entry
  coe_injective T T' h := by
    cases T
    cases T'
    congr

@[simp]

中文:
实例 instFunLike
  签名: {μ : Young图}
  定义体: SemistandardYoungTableau.entry
  coe_injective T T' h := by
    cases T
    cases T'
    congr

@[simp]

Depends on / 依赖: SemistandardYoungTableau, SemistandardYoungTableau.entry
-/
instance instFunLike {μ : YoungDiagram} : FunLike (SemistandardYoungTableau μ) Nat (Nat -> Nat) where
  coe := SemistandardYoungTableau.entry
  coe_injective T T' h := by
    cases T
    cases T'
    congr

@[simp]
/--
theorem `to_fun_eq_coe` / 定理 `to_fun_eq_coe`

English:
theorem to_fun_eq_coe
  given: {μ : YoungDiagram} {T : SemistandardYoungTableau μ}
  proof: rfl

@[ext]

中文:
定理 to_fun_eq_coe
  条件: {μ : Young图} {T : 半标准Young表 μ}
  证明: rfl

@[ext]
-/
theorem to_fun_eq_coe {μ : YoungDiagram} {T : SemistandardYoungTableau μ} :
    T.entry = (T : Nat -> Nat -> Nat) :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {μ : YoungDiagram} {T T' : SemistandardYoungTableau μ} (h : forall i j, T i j = T' i j)
  proof: DFunLike.ext T T' fun _ => by
    funext
    apply h

中文:
定理 ext
  条件: {μ : Young图} {T T' : 半标准Young表 μ} (h : 对任意 i j, T i j = T' i j)
  证明: DFunLike.ext T T' fun _ => by
    funext
    apply h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {μ : YoungDiagram} {T T' : SemistandardYoungTableau μ} (h : forall i j, T i j = T' i j) :
    T = T' :=
  DFunLike.ext T T' fun _ => by
    funext
    apply h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : Nat -> Nat -> Nat)
  body: entry'
  row_weak' := h.symm ▸ T.row_weak'
  col_strict' := h.symm ▸ T.col_strict'
  zeros' := h.symm ▸ T.zeros'

@[simp]

中文:
定义 copy
  签名: {μ : Young图} (T : 半标准Young表 μ) (entry' : 自然数 -> 自然数 -> 自然数)
  定义体: entry'
  row_weak' := h.symm ▸ T.row_weak'
  col_strict' := h.symm ▸ T.col_strict'
  zeros' := h.symm ▸ T.zeros'

@[simp]
-/
protected def copy {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : Nat -> Nat -> Nat)
    (h : entry' = T) : SemistandardYoungTableau μ where
  entry := entry'
  row_weak' := h.symm ▸ T.row_weak'
  col_strict' := h.symm ▸ T.col_strict'
  zeros' := h.symm ▸ T.zeros'

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  statement: {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : Nat -> Nat -> Nat)
  proof: rfl

中文:
定理 coe_copy
  结论: {μ : Young图} (T : 半标准Young表 μ) (entry' : 自然数 -> 自然数 -> 自然数)
  证明: rfl
-/
theorem coe_copy {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : Nat -> Nat -> Nat)
    (h : entry' = T) : ⇑(T.copy entry' h) = entry' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  statement: {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : Nat -> Nat -> Nat)
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  结论: {μ : Young图} (T : 半标准Young表 μ) (entry' : 自然数 -> 自然数 -> 自然数)
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : Nat -> Nat -> Nat)
    (h : entry' = T) : T.copy entry' h = T :=
  DFunLike.ext' h

/--
theorem `row_weak` / 定理 `row_weak`

English:
theorem row_weak
  statement: {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : Nat} (hj : j1 < j2)
  proof: T.row_weak' hj hcell

中文:
定理 row_weak
  结论: {μ : Young图} (T : 半标准Young表 μ) {i j1 j2 : 自然数} (hj : j1 < j2)
  证明: T.row_weak' hj hcell

Depends on / 依赖: T.row_weak, row_weak
-/
theorem row_weak {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : Nat} (hj : j1 < j2)
    (hcell : (i, j2) in μ) : T i j1 <= T i j2 :=
  T.row_weak' hj hcell

/--
theorem `col_strict` / 定理 `col_strict`

English:
theorem col_strict
  statement: {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : Nat} (hi : i1 < i2)
  proof: T.col_strict' hi hcell

中文:
定理 col_strict
  结论: {μ : Young图} (T : 半标准Young表 μ) {i1 i2 j : 自然数} (hi : i1 < i2)
  证明: T.col_strict' hi hcell

Depends on / 依赖: T.col_strict, col_strict
-/
theorem col_strict {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : Nat} (hi : i1 < i2)
    (hcell : (i2, j) in μ) : T i1 j < T i2 j :=
  T.col_strict' hi hcell

/--
theorem `zeros` / 定理 `zeros`

English:
theorem zeros
  statement: {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j : Nat}
  proof: T.zeros' not_cell

中文:
定理 zeros
  结论: {μ : Young图} (T : 半标准Young表 μ) {i j : 自然数}
  证明: T.zeros' not_cell

Depends on / 依赖: T.zeros, not_cell
-/
theorem zeros {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j : Nat}
    (not_cell : (i, j) ∉ μ) : T i j = 0 :=
  T.zeros' not_cell

/--
theorem `row_weak_of_le` / 定理 `row_weak_of_le`

English:
theorem row_weak_of_le
  statement: {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : Nat}
  proof: by
  rcases eq_or_lt_of_le hj with h | h
  · rw [h]
  · exact T.row_weak h cell

中文:
定理 row_weak_of_le
  结论: {μ : Young图} (T : 半标准Young表 μ) {i j1 j2 : 自然数}
  证明: by
  rcases eq_or_lt_of_le hj with h | h
  · rw [h]
  · exact T.row_weak h cell

Depends on / 依赖: T.row_weak, eq_or_lt_of_le, row_weak
-/
theorem row_weak_of_le {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : Nat}
    (hj : j1 <= j2) (cell : (i, j2) in μ) : T i j1 <= T i j2 := by
  rcases eq_or_lt_of_le hj with h | h
  · rw [h]
  · exact T.row_weak h cell

/--
theorem `col_weak` / 定理 `col_weak`

English:
theorem col_weak
  statement: {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : Nat} (hi : i1 <= i2)
  proof: by
  rcases eq_or_lt_of_le hi with h | h
  · rw [h]
  · exact le_of_lt (T.col_strict h cell)

中文:
定理 col_weak
  结论: {μ : Young图} (T : 半标准Young表 μ) {i1 i2 j : 自然数} (hi : i1 <= i2)
  证明: by
  rcases eq_or_lt_of_le hi with h | h
  · rw [h]
  · exact le_of_lt (T.col_strict h cell)

Depends on / 依赖: T.col_strict, col_strict, eq_or_lt_of_le, le_of_lt
-/
theorem col_weak {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : Nat} (hi : i1 <= i2)
    (cell : (i2, j) in μ) : T i1 j <= T i2 j := by
  rcases eq_or_lt_of_le hi with h | h
  · rw [h]
  · exact le_of_lt (T.col_strict h cell)

/--
Definition of `highestWeight` / `highestWeight` 的定义

English:
definition highestWeight
  signature: (μ : YoungDiagram)
  body: if (i, j) in μ then i else 0
  row_weak' hj hcell := by
    rw [if_pos hcell]; rw [if_pos (μ.up_left_mem (by rfl) (le_of_lt hj) hcell)]
  col_strict' hi hcell := by
    rwa [if_pos hcell, if_pos (μ.up_left_mem (le_of_lt hi) (by rfl) hcell)]
  zeros' not_cell := if_neg not_cell

@[simp]

中文:
定义 highestWeight
  签名: (μ : Young图)
  定义体: if (i, j) in μ then i else 0
  row_weak' hj hcell := by
    rw [if_pos hcell]; rw [if_pos (μ.up_left_mem (by rfl) (le_of_lt hj) hcell)]
  col_strict' hi hcell := by
    rwa [if_pos hcell, if_pos (μ.up_left_mem (le_of_lt hi) (by rfl) hcell)]
  zeros' not_cell := if_neg not_cell

@[simp]
-/
def highestWeight (μ : YoungDiagram) : SemistandardYoungTableau μ where
  entry i j := if (i, j) in μ then i else 0
  row_weak' hj hcell := by
    rw [if_pos hcell]; rw [if_pos (μ.up_left_mem (by rfl) (le_of_lt hj) hcell)]
  col_strict' hi hcell := by
    rwa [if_pos hcell, if_pos (μ.up_left_mem (le_of_lt hi) (by rfl) hcell)]
  zeros' not_cell := if_neg not_cell

@[simp]
/--
theorem `highestWeight_apply` / 定理 `highestWeight_apply`

English:
theorem highestWeight_apply
  given: {μ : YoungDiagram} {i j : Nat}
  proof: rfl

中文:
定理 highestWeight_apply
  条件: {μ : Young图} {i j : 自然数}
  证明: rfl
-/
theorem highestWeight_apply {μ : YoungDiagram} {i j : Nat} :
    highestWeight μ i j = if (i, j) in μ then i else 0 :=
  rfl

instance {μ : YoungDiagram} : Inhabited (SemistandardYoungTableau μ) :=
  ⟨highestWeight μ⟩

end SemistandardYoungTableau
