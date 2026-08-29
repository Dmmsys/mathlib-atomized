/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
module

public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# Young diagrams

A Young diagram is a finite set of up-left justified boxes:

```text
□□□□□
□□□
□□□
□
```
This Young diagram corresponds to the [5, 3, 3, 1] partition of 12.

We represent it as a lower set in `ℕ × ℕ` in the product partial order. We write `(i, j) ∈ μ`
to say that `(i, j)` (in matrix coordinates) is in the Young diagram `μ`.

## Main definitions

- `YoungDiagram` : Young diagrams
- `YoungDiagram.card` : the number of cells in a Young diagram (its *cardinality*)
- `YoungDiagram.instDistribLatticeYoungDiagram` : a distributive lattice instance for Young diagrams
  ordered by containment, with `(⊥ : YoungDiagram)` the empty diagram.
- `YoungDiagram.row` and `YoungDiagram.rowLen`: rows of a Young diagram and their lengths
- `YoungDiagram.col` and `YoungDiagram.colLen`: columns of a Young diagram and their lengths

## Notation

In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left of (i2, j2). This terminology is used
below, e.g. in `YoungDiagram.up_left_mem`.

## Tags

Young diagram

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/

@[expose] public section


open Function

/-- A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever
a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell
is a cell in row `i` and column `j`, where rows are enumerated downward and columns rightward.

Young diagrams are modeled as finite sets in `ℕ × ℕ` that are lower sets with respect to the
standard order on products. -/
@[ext]
/--
Definition of `YoungDiagram` / `YoungDiagram` 的定义

English:
structure YoungDiagram
  parameters: where
  axioms and operations (2):
    - cells : Finset (Nat × Nat)
    - isLowerSet : IsLowerSet (cells : Set (Nat × Nat))

中文:
结构 Young图
  参数: where
  公理与运算 (2 个):
    - cells : 有限集 (自然数 × 自然数)
    - isLowerSet : 是下集 (cells : 集合 (自然数 × 自然数))
-/
structure YoungDiagram where
  /-- A finite set which represents a finite collection of cells on the `ℕ × ℕ` grid. -/
  cells : Finset (Nat × Nat)
  /-- Cells are up-left justified, witnessed by the fact that `cells` is a lower set in `ℕ × ℕ`. -/
  isLowerSet : IsLowerSet (cells : Set (Nat × Nat))

namespace YoungDiagram

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike YoungDiagram (Nat × Nat)
  body: y.cells
  coe_injective μ ν h := by rwa [YoungDiagram.ext_iff, ← Finset.coe_inj]

中文:
实例 :
  签名: 集合状 Young图 (自然数 × 自然数)
  定义体: y.cells
  coe_injective μ ν h := by rwa [YoungDiagram.ext_iff, ← Finset.coe_inj]

Depends on / 依赖: y.cells
-/
instance : SetLike YoungDiagram (Nat × Nat) where
  coe y := y.cells
  coe_injective μ ν h := by rwa [YoungDiagram.ext_iff, ← Finset.coe_inj]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder YoungDiagram
  body: .ofSetLike YoungDiagram (Nat × Nat)

@[simp]

中文:
实例 :
  签名: 偏序 Young图
  定义体: .ofSetLike YoungDiagram (Nat × Nat)

@[simp]

Depends on / 依赖: YoungDiagram, ofSetLike
-/
instance : PartialOrder YoungDiagram := .ofSetLike YoungDiagram (Nat × Nat)

@[simp]
/--
theorem `mem_cells` / 定理 `mem_cells`

English:
theorem mem_cells
  given: {μ : YoungDiagram} (c : Nat × Nat)
  statement: c in μ.cells ↔ c in μ
  proof: Iff.rfl

@[simp]

中文:
定理 mem_cells
  条件: {μ : Young图} (c : 自然数 × 自然数)
  结论: c in μ.cells ↔ c in μ
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_cells {μ : YoungDiagram} (c : Nat × Nat) : c in μ.cells ↔ c in μ :=
  Iff.rfl

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: (c : Nat × Nat) (cells) (isLowerSet)
  proof: Iff.rfl

中文:
定理 mem_mk
  条件: (c : 自然数 × 自然数) (cells) (isLowerSet)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk (c : Nat × Nat) (cells) (isLowerSet) :
    c in YoungDiagram.mk cells isLowerSet ↔ c in cells :=
  Iff.rfl

/--
Instance `decidableMem` / 实例 `decidableMem`

English:
instance decidableMem
  signature: (μ : YoungDiagram)
  body: inferInstanceAs (DecidablePred (· in μ.cells))

中文:
实例 decidableMem
  签名: (μ : Young图)
  定义体: inferInstanceAs (DecidablePred (· in μ.cells))

Depends on / 依赖: DecidablePred
-/
instance decidableMem (μ : YoungDiagram) : DecidablePred (· in μ) :=
  inferInstanceAs (DecidablePred (· in μ.cells))

/--
theorem `up_left_mem` / 定理 `up_left_mem`

English:
theorem up_left_mem
  statement: (μ : YoungDiagram) {i1 i2 j1 j2 : Nat} (hi : i1 <= i2) (hj : j1 <= j2)
  proof: μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

中文:
定理 up_left_mem
  结论: (μ : Young图) {i1 i2 j1 j2 : 自然数} (hi : i1 <= i2) (hj : j1 <= j2)
  证明: μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

Depends on / 依赖: Prod.mk_le_mk.mpr, isLowerSet, mk_le_mk
-/
theorem up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : Nat} (hi : i1 <= i2) (hj : j1 <= j2)
    (hcell : (i2, j2) in μ) : (i1, j1) in μ :=
  μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

section DistribLattice

@[simp]
/--
theorem `cells_subset_iff` / 定理 `cells_subset_iff`

English:
theorem cells_subset_iff
  given: {μ ν : YoungDiagram}
  statement: μ.cells subseteq ν.cells ↔ μ <= ν
  proof: Iff.rfl

@[simp]

中文:
定理 cells_subset_iff
  条件: {μ ν : Young图}
  结论: μ.cells subseteq ν.cells ↔ μ <= ν
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem cells_subset_iff {μ ν : YoungDiagram} : μ.cells subseteq ν.cells ↔ μ <= ν :=
  Iff.rfl

@[simp]
/--
theorem `cells_ssubset_iff` / 定理 `cells_ssubset_iff`

English:
theorem cells_ssubset_iff
  given: {μ ν : YoungDiagram}
  statement: μ.cells ⊂ ν.cells ↔ μ < ν
  proof: Iff.rfl

中文:
定理 cells_ssubset_iff
  条件: {μ ν : Young图}
  结论: μ.cells ⊂ ν.cells ↔ μ < ν
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem cells_ssubset_iff {μ ν : YoungDiagram} : μ.cells ⊂ ν.cells ↔ μ < ν :=
  Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max YoungDiagram
  body: { cells := μ.cells union ν.cells
      isLowerSet := by
        rw [Finset.coe_union]
        exact μ.isLowerSet.union ν.isLowerSet }

@[simp]

中文:
实例 :
  签名: 最大值 Young图
  定义体: { cells := μ.cells union ν.cells
      isLowerSet := by
        rw [Finset.coe_union]
        exact μ.isLowerSet.union ν.isLowerSet }

@[simp]

Depends on / 依赖: Finset, Finset.coe_union, coe_union, isLowerSet, isLowerSet.union
-/
instance : Max YoungDiagram where
  max μ ν :=
    { cells := μ.cells union ν.cells
      isLowerSet := by
        rw [Finset.coe_union]
        exact μ.isLowerSet.union ν.isLowerSet }

@[simp]
/--
theorem `cells_sup` / 定理 `cells_sup`

English:
theorem cells_sup
  given: (μ ν : YoungDiagram)
  statement: (μ ⊔ ν).cells = μ.cells union ν.cells
  proof: rfl

@[simp, norm_cast]

中文:
定理 cells_sup
  条件: (μ ν : Young图)
  结论: (μ ⊔ ν).cells = μ.cells union ν.cells
  证明: rfl

@[simp, norm_cast]
-/
theorem cells_sup (μ ν : YoungDiagram) : (μ ⊔ ν).cells = μ.cells union ν.cells :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (μ ν : YoungDiagram)
  statement: ↑(μ ⊔ ν) = (μ union ν : Set (Nat × Nat))
  proof: Finset.coe_union _ _

@[simp]

中文:
定理 coe_sup
  条件: (μ ν : Young图)
  结论: ↑(μ ⊔ ν) = (μ union ν : 集合 (自然数 × 自然数))
  证明: Finset.coe_union _ _

@[simp]

Depends on / 依赖: Finset, Finset.coe_union, coe_union
-/
theorem coe_sup (μ ν : YoungDiagram) : ↑(μ ⊔ ν) = (μ union ν : Set (Nat × Nat)) :=
  Finset.coe_union _ _

@[simp]
/--
theorem `mem_sup` / 定理 `mem_sup`

English:
theorem mem_sup
  given: {μ ν : YoungDiagram} {x : Nat × Nat}
  statement: x in μ ⊔ ν ↔ x in μ ∨ x in ν
  proof: Finset.mem_union

中文:
定理 mem_sup
  条件: {μ ν : Young图} {x : 自然数 × 自然数}
  结论: x in μ ⊔ ν ↔ x in μ ∨ x in ν
  证明: Finset.mem_union

Depends on / 依赖: Finset, Finset.mem_union, mem_union
-/
theorem mem_sup {μ ν : YoungDiagram} {x : Nat × Nat} : x in μ ⊔ ν ↔ x in μ ∨ x in ν :=
  Finset.mem_union

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min YoungDiagram
  body: { cells := μ.cells inter ν.cells
      isLowerSet := by
        rw [Finset.coe_inter]
        exact μ.isLowerSet.inter ν.isLowerSet }

@[simp]

中文:
实例 :
  签名: 最小值 Young图
  定义体: { cells := μ.cells inter ν.cells
      isLowerSet := by
        rw [Finset.coe_inter]
        exact μ.isLowerSet.inter ν.isLowerSet }

@[simp]

Depends on / 依赖: Finset, Finset.coe_inter, coe_inter, isLowerSet, isLowerSet.inter
-/
instance : Min YoungDiagram where
  min μ ν :=
    { cells := μ.cells inter ν.cells
      isLowerSet := by
        rw [Finset.coe_inter]
        exact μ.isLowerSet.inter ν.isLowerSet }

@[simp]
/--
theorem `cells_inf` / 定理 `cells_inf`

English:
theorem cells_inf
  given: (μ ν : YoungDiagram)
  statement: (μ ⊓ ν).cells = μ.cells inter ν.cells
  proof: rfl

@[simp, norm_cast]

中文:
定理 cells_inf
  条件: (μ ν : Young图)
  结论: (μ ⊓ ν).cells = μ.cells inter ν.cells
  证明: rfl

@[simp, norm_cast]
-/
theorem cells_inf (μ ν : YoungDiagram) : (μ ⊓ ν).cells = μ.cells inter ν.cells :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (μ ν : YoungDiagram)
  statement: ↑(μ ⊓ ν) = (μ inter ν : Set (Nat × Nat))
  proof: Finset.coe_inter _ _

@[simp]

中文:
定理 coe_inf
  条件: (μ ν : Young图)
  结论: ↑(μ ⊓ ν) = (μ inter ν : 集合 (自然数 × 自然数))
  证明: Finset.coe_inter _ _

@[simp]

Depends on / 依赖: Finset, Finset.coe_inter, coe_inter
-/
theorem coe_inf (μ ν : YoungDiagram) : ↑(μ ⊓ ν) = (μ inter ν : Set (Nat × Nat)) :=
  Finset.coe_inter _ _

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {μ ν : YoungDiagram} {x : Nat × Nat}
  statement: x in μ ⊓ ν ↔ x in μ ∧ x in ν
  proof: Finset.mem_inter

中文:
定理 mem_inf
  条件: {μ ν : Young图} {x : 自然数 × 自然数}
  结论: x in μ ⊓ ν ↔ x in μ ∧ x in ν
  证明: Finset.mem_inter

Depends on / 依赖: Finset, Finset.mem_inter, mem_inter
-/
theorem mem_inf {μ ν : YoungDiagram} {x : Nat × Nat} : x in μ ⊓ ν ↔ x in μ ∧ x in ν :=
  Finset.mem_inter

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot YoungDiagram
  body: { cells := ∅
      isLowerSet := by
        intro a b _ h
        simp only [Finset.coe_empty, Set.mem_empty_iff_false]
        simp only [Finset.coe_empty, Set.mem_empty_iff_false] at h }
  bot_le _ _ := by
    intro y
    simp only [mem_mk, Finset.notMem_empty] at y

@[simp]

中文:
实例 :
  签名: 有底序 Young图
  定义体: { cells := ∅
      isLowerSet := by
        intro a b _ h
        simp only [Finset.coe_empty, Set.mem_empty_iff_false]
        simp only [Finset.coe_empty, Set.mem_empty_iff_false] at h }
  bot_le _ _ := by
    intro y
    simp only [mem_mk, Finset.notMem_empty] at y

@[simp]

Depends on / 依赖: Finset, Finset.coe_empty, Finset.notMem_empty, Set.mem_empty_iff_false, bot_le, coe_empty, isLowerSet, mem_empty_iff_false, mem_mk, notMem_empty
-/
instance : OrderBot YoungDiagram where
  bot :=
    { cells := ∅
      isLowerSet := by
        intro a b _ h
        simp only [Finset.coe_empty, Set.mem_empty_iff_false]
        simp only [Finset.coe_empty, Set.mem_empty_iff_false] at h }
  bot_le _ _ := by
    intro y
    simp only [mem_mk, Finset.notMem_empty] at y

@[simp]
/--
theorem `cells_bot` / 定理 `cells_bot`

English:
theorem cells_bot
  statement: (⊥ : YoungDiagram).cells = ∅
  proof: rfl

@[simp]

中文:
定理 cells_bot
  结论: (⊥ : Young图).cells = ∅
  证明: rfl

@[simp]
-/
theorem cells_bot : (⊥ : YoungDiagram).cells = ∅ :=
  rfl

@[simp]
/--
theorem `notMem_bot` / 定理 `notMem_bot`

English:
theorem notMem_bot
  given: (x : Nat × Nat)
  statement: x ∉ (⊥ : YoungDiagram)
  proof: Finset.notMem_empty x

@[norm_cast]

中文:
定理 notMem_bot
  条件: (x : 自然数 × 自然数)
  结论: x ∉ (⊥ : Young图)
  证明: Finset.notMem_empty x

@[norm_cast]

Depends on / 依赖: Finset, Finset.notMem_empty, notMem_empty
-/
theorem notMem_bot (x : Nat × Nat) : x ∉ (⊥ : YoungDiagram) :=
  Finset.notMem_empty x

@[norm_cast]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: (⊥ : YoungDiagram) = (∅ : Set (Nat × Nat))
  proof: by
  ext; simp

中文:
定理 coe_bot
  结论: (⊥ : Young图) = (∅ : 集合 (自然数 × 自然数))
  证明: by
  ext; simp
-/
theorem coe_bot : (⊥ : YoungDiagram) = (∅ : Set (Nat × Nat)) := by
  ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited YoungDiagram
  body: ⟨⊥⟩

中文:
实例 :
  签名: 可居 Young图
  定义体: ⟨⊥⟩
-/
instance : Inhabited YoungDiagram :=
  ⟨⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribLattice YoungDiagram
  body: Function.Injective.distribLattice YoungDiagram.cells (fun μ ν h => by rwa [YoungDiagram.ext_iff])
    .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 :
  签名: Distrib格 Young图
  定义体: Function.Injective.distribLattice YoungDiagram.cells (fun μ ν h => by rwa [YoungDiagram.ext_iff])
    .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: Function, Function.Injective.distribLattice, Injective, YoungDiagram, YoungDiagram.cells, YoungDiagram.ext_iff, distribLattice, ext_iff
-/
instance : DistribLattice YoungDiagram :=
  Function.Injective.distribLattice YoungDiagram.cells (fun μ ν h => by rwa [YoungDiagram.ext_iff])
    .rfl .rfl (fun _ _ => rfl) fun _ _ => rfl

end DistribLattice

/--
Definition of `card` / `card` 的定义

English:
abbreviation card
  signature: (μ : YoungDiagram)
  body: μ.cells.card

中文:
缩写 card
  签名: (μ : Young图)
  定义体: μ.cells.card
-/
protected abbrev card (μ : YoungDiagram) : Nat :=
  μ.cells.card

section Transpose

/--
Definition of `transpose` / `transpose` 的定义

English:
definition transpose
  signature: (μ : YoungDiagram)
  body: (Equiv.prodComm _ _).finsetCongr μ.cells
  isLowerSet _ _ h := by
    simp only [Finset.mem_coe, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    intro hcell
    apply μ.isLowerSet _ hcell
    simp [h]

@[simp]

中文:
定义 transpose
  签名: (μ : Young图)
  定义体: (Equiv.prodComm _ _).finsetCongr μ.cells
  isLowerSet _ _ h := by
    simp only [Finset.mem_coe, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    intro hcell
    apply μ.isLowerSet _ hcell
    simp [h]

@[simp]

Depends on / 依赖: Equiv.prodComm, finsetCongr, prodComm
-/
def transpose (μ : YoungDiagram) : YoungDiagram where
  cells := (Equiv.prodComm _ _).finsetCongr μ.cells
  isLowerSet _ _ h := by
    simp only [Finset.mem_coe, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    intro hcell
    apply μ.isLowerSet _ hcell
    simp [h]

@[simp]
/--
theorem `mem_transpose` / 定理 `mem_transpose`

English:
theorem mem_transpose
  given: {μ : YoungDiagram} {c : Nat × Nat}
  statement: c in μ.transpose ↔ c.swap in μ
  proof: by
  simp [transpose]

@[simp]

中文:
定理 mem_transpose
  条件: {μ : Young图} {c : 自然数 × 自然数}
  结论: c in μ.transpose ↔ c.swap in μ
  证明: by
  simp [transpose]

@[simp]

Depends on / 依赖: transpose
-/
theorem mem_transpose {μ : YoungDiagram} {c : Nat × Nat} : c in μ.transpose ↔ c.swap in μ := by
  simp [transpose]

@[simp]
/--
theorem `transpose_transpose` / 定理 `transpose_transpose`

English:
theorem transpose_transpose
  given: (μ : YoungDiagram)
  statement: μ.transpose.transpose = μ
  proof: by
  ext x
  simp

中文:
定理 transpose_transpose
  条件: (μ : Young图)
  结论: μ.transpose.transpose = μ
  证明: by
  ext x
  simp
-/
theorem transpose_transpose (μ : YoungDiagram) : μ.transpose.transpose = μ := by
  ext x
  simp

/--
theorem `transpose_eq_iff_eq_transpose` / 定理 `transpose_eq_iff_eq_transpose`

English:
theorem transpose_eq_iff_eq_transpose
  given: {μ ν : YoungDiagram}
  statement: μ.transpose = ν ↔ μ = ν.transpose
  proof: by
  constructor <;>
    · rintro rfl
      simp

@[simp]

中文:
定理 transpose_eq_iff_eq_transpose
  条件: {μ ν : Young图}
  结论: μ.transpose = ν ↔ μ = ν.transpose
  证明: by
  constructor <;>
    · rintro rfl
      simp

@[simp]
-/
theorem transpose_eq_iff_eq_transpose {μ ν : YoungDiagram} : μ.transpose = ν ↔ μ = ν.transpose := by
  constructor <;>
    · rintro rfl
      simp

@[simp]
/--
theorem `transpose_eq_iff` / 定理 `transpose_eq_iff`

English:
theorem transpose_eq_iff
  given: {μ ν : YoungDiagram}
  statement: μ.transpose = ν.transpose ↔ μ = ν
  proof: by
  rw [transpose_eq_iff_eq_transpose]
  simp

中文:
定理 transpose_eq_iff
  条件: {μ ν : Young图}
  结论: μ.transpose = ν.transpose ↔ μ = ν
  证明: by
  rw [transpose_eq_iff_eq_transpose]
  simp

Depends on / 依赖: transpose_eq_iff_eq_transpose
-/
theorem transpose_eq_iff {μ ν : YoungDiagram} : μ.transpose = ν.transpose ↔ μ = ν := by
  rw [transpose_eq_iff_eq_transpose]
  simp

-- This is effectively both directions of `transpose_le_iff` below.
/--
theorem `le_of_transpose_le` / 定理 `le_of_transpose_le`

English:
theorem le_of_transpose_le
  given: {μ ν : YoungDiagram} (h_le : μ.transpose <= ν)
  proof: fun c hc => by
  simp only [mem_transpose]
  apply h_le
  simpa

@[simp]

中文:
定理 le_of_transpose_le
  条件: {μ ν : Young图} (h_le : μ.transpose <= ν)
  证明: fun c hc => by
  simp only [mem_transpose]
  apply h_le
  simpa

@[simp]
-/
protected theorem le_of_transpose_le {μ ν : YoungDiagram} (h_le : μ.transpose <= ν) :
    μ <= ν.transpose := fun c hc => by
  simp only [mem_transpose]
  apply h_le
  simpa

@[simp]
/--
theorem `transpose_le_iff` / 定理 `transpose_le_iff`

English:
theorem transpose_le_iff
  given: {μ ν : YoungDiagram}
  statement: μ.transpose <= ν.transpose ↔ μ <= ν
  proof: ⟨fun h => by
    convert! YoungDiagram.le_of_transpose_le h
    simp, fun h => by
    rw [← transpose_transpose μ] at h
    exact YoungDiagram.le_of_transpose_le h ⟩

@[gcongr, mono]

中文:
定理 transpose_le_iff
  条件: {μ ν : Young图}
  结论: μ.transpose <= ν.transpose ↔ μ <= ν
  证明: ⟨fun h => by
    convert! YoungDiagram.le_of_transpose_le h
    simp, fun h => by
    rw [← transpose_transpose μ] at h
    exact YoungDiagram.le_of_transpose_le h ⟩

@[gcongr, mono]

Depends on / 依赖: YoungDiagram, YoungDiagram.le_of_transpose_le, convert, le_of_transpose_le, transpose_transpose
-/
theorem transpose_le_iff {μ ν : YoungDiagram} : μ.transpose <= ν.transpose ↔ μ <= ν :=
  ⟨fun h => by
    convert! YoungDiagram.le_of_transpose_le h
    simp, fun h => by
    rw [← transpose_transpose μ] at h
    exact YoungDiagram.le_of_transpose_le h ⟩

@[gcongr, mono]
/--
theorem `transpose_mono` / 定理 `transpose_mono`

English:
theorem transpose_mono
  given: {μ ν : YoungDiagram} (h_le : μ <= ν)
  statement: μ.transpose <= ν.transpose
  proof: transpose_le_iff.mpr h_le

中文:
定理 transpose_mono
  条件: {μ ν : Young图} (h_le : μ <= ν)
  结论: μ.transpose <= ν.transpose
  证明: transpose_le_iff.mpr h_le
-/
protected theorem transpose_mono {μ ν : YoungDiagram} (h_le : μ <= ν) : μ.transpose <= ν.transpose :=
  transpose_le_iff.mpr h_le

set_option backward.isDefEq.respectTransparency false in
/-- Transposing Young diagrams is an `OrderIso`. -/
@[simps]
/--
Definition of `transposeOrderIso` / `transposeOrderIso` 的定义

English:
definition transposeOrderIso
  signature: : YoungDiagram ≃o YoungDiagram
  body: ⟨⟨transpose, transpose, fun _ => by simp, fun _ => by simp⟩, by simp⟩

中文:
定义 transposeOrderIso
  签名: : Young图 ≃o Young图
  定义体: ⟨⟨transpose, transpose, fun _ => by simp, fun _ => by simp⟩, by simp⟩

Depends on / 依赖: transpose
-/
def transposeOrderIso : YoungDiagram ≃o YoungDiagram :=
  ⟨⟨transpose, transpose, fun _ => by simp, fun _ => by simp⟩, by simp⟩

end Transpose

section Rows

/-! ### Rows and row lengths of Young diagrams.

This section defines `μ.row` and `μ.rowLen`, with the following API:
      1. `(i, j) ∈ μ ↔ j < μ.rowLen i`
      2. `μ.row i = {i} ×ˢ (Finset.range (μ.rowLen i))`
      3. `μ.rowLen i = (μ.row i).card`
      4. `∀ {i1 i2}, i1 ≤ i2 → μ.rowLen i2 ≤ μ.rowLen i1`

Note: #3 is not convenient for defining `μ.rowLen`; instead, `μ.rowLen` is defined
as the smallest `j` such that `(i, j) ∉ μ`. -/


/--
Definition of `row` / `row` 的定义

English:
definition row
  signature: (μ : YoungDiagram) (i : Nat)
  body: μ.cells.filter fun c => c.fst = i

中文:
定义 row
  签名: (μ : Young图) (i : 自然数)
  定义体: μ.cells.filter fun c => c.fst = i

Depends on / 依赖: c.fst, cells.filter, filter
-/
def row (μ : YoungDiagram) (i : Nat) : Finset (Nat × Nat) :=
  μ.cells.filter fun c => c.fst = i

/--
theorem `mem_row_iff` / 定理 `mem_row_iff`

English:
theorem mem_row_iff
  given: {μ : YoungDiagram} {i : Nat} {c : Nat × Nat}
  statement: c in μ.row i ↔ c in μ ∧ c.fst = i
  proof: by
  simp [row]

中文:
定理 mem_row_iff
  条件: {μ : Young图} {i : 自然数} {c : 自然数 × 自然数}
  结论: c in μ.row i ↔ c in μ ∧ c.fst = i
  证明: by
  simp [row]
-/
theorem mem_row_iff {μ : YoungDiagram} {i : Nat} {c : Nat × Nat} : c in μ.row i ↔ c in μ ∧ c.fst = i := by
  simp [row]

/--
theorem `mk_mem_row_iff` / 定理 `mk_mem_row_iff`

English:
theorem mk_mem_row_iff
  given: {μ : YoungDiagram} {i j : Nat}
  statement: (i, j) in μ.row i ↔ (i, j) in μ
  proof: by simp [row]

中文:
定理 mk_mem_row_iff
  条件: {μ : Young图} {i j : 自然数}
  结论: (i, j) in μ.row i ↔ (i, j) in μ
  证明: by simp [row]
-/
theorem mk_mem_row_iff {μ : YoungDiagram} {i j : Nat} : (i, j) in μ.row i ↔ (i, j) in μ := by simp [row]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_notMem_row` / 定理 `exists_notMem_row`

English:
theorem exists_notMem_row
  given: (μ : YoungDiagram) (i : Nat)
  statement: exists j, (i, j) ∉ μ
  proof: by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_notMem_finset
      (μ.cells.preimage (Prod.mk i) fun _ _ _ _ h => by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  exact ⟨j, hj⟩

中文:
定理 存在_notMem_row
  条件: (μ : Young图) (i : 自然数)
  结论: 存在 j, (i, j) ∉ μ
  证明: by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_notMem_finset
      (μ.cells.preimage (Prod.mk i) fun _ _ _ _ h => by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  exact ⟨j, hj⟩
-/
protected theorem exists_notMem_row (μ : YoungDiagram) (i : Nat) : exists j, (i, j) ∉ μ := by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_notMem_finset
      (μ.cells.preimage (Prod.mk i) fun _ _ _ _ h => by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  exact ⟨j, hj⟩

/--
Definition of `rowLen` / `rowLen` 的定义

English:
definition rowLen
  signature: (μ : YoungDiagram) (i : Nat)
  body: Nat.find μ.exists_notMem_row i

中文:
定义 rowLen
  签名: (μ : Young图) (i : 自然数)
  定义体: Nat.find μ.exists_notMem_row i

Depends on / 依赖: Nat.find, exists_notMem_row
-/
def rowLen (μ : YoungDiagram) (i : Nat) : Nat :=
Nat.find μ.exists_notMem_row i

/--
theorem `mem_iff_lt_rowLen` / 定理 `mem_iff_lt_rowLen`

English:
theorem mem_iff_lt_rowLen
  given: {μ : YoungDiagram} {i j : Nat}
  statement: (i, j) in μ ↔ j < μ.rowLen i
  proof: by
  rw [rowLen]; rw [Nat.lt_find_iff]
  push Not
  exact ⟨fun h _ hmj => μ.up_left_mem (by rfl) hmj h, fun h => h _ (by rfl)⟩

中文:
定理 mem_iff_lt_rowLen
  条件: {μ : Young图} {i j : 自然数}
  结论: (i, j) in μ ↔ j < μ.rowLen i
  证明: by
  rw [rowLen]; rw [Nat.lt_find_iff]
  push Not
  exact ⟨fun h _ hmj => μ.up_left_mem (by rfl) hmj h, fun h => h _ (by rfl)⟩

Depends on / 依赖: Nat.lt_find_iff, lt_find_iff, rowLen, up_left_mem
-/
theorem mem_iff_lt_rowLen {μ : YoungDiagram} {i j : Nat} : (i, j) in μ ↔ j < μ.rowLen i := by
  rw [rowLen]; rw [Nat.lt_find_iff]
  push Not
  exact ⟨fun h _ hmj => μ.up_left_mem (by rfl) hmj h, fun h => h _ (by rfl)⟩

/--
theorem `row_eq_prod` / 定理 `row_eq_prod`

English:
theorem row_eq_prod
  given: {μ : YoungDiagram} {i : Nat}
  statement: μ.row i = {i} ×ˢ Finset.range (μ.rowLen i)
  proof: by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_row_iff,
    mem_iff_lt_rowLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl

中文:
定理 row_eq_prod
  条件: {μ : Young图} {i : 自然数}
  结论: μ.row i = {i} ×ˢ 有限集.range (μ.rowLen i)
  证明: by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_row_iff,
    mem_iff_lt_rowLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl

Depends on / 依赖: Finset, Finset.mem_product, Finset.mem_range, Finset.mem_singleton, and_comm, and_congr_right_iff, mem_iff_lt_rowLen, mem_product, mem_range, mem_row_iff, mem_singleton
-/
theorem row_eq_prod {μ : YoungDiagram} {i : Nat} : μ.row i = {i} ×ˢ Finset.range (μ.rowLen i) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_row_iff,
    mem_iff_lt_rowLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl

/--
theorem `rowLen_eq_card` / 定理 `rowLen_eq_card`

English:
theorem rowLen_eq_card
  given: (μ : YoungDiagram) {i : Nat}
  statement: μ.rowLen i = (μ.row i).card
  proof: by
  simp [row_eq_prod]

@[gcongr, mono]

中文:
定理 rowLen_eq_card
  条件: (μ : Young图) {i : 自然数}
  结论: μ.rowLen i = (μ.row i).card
  证明: by
  simp [row_eq_prod]

@[gcongr, mono]

Depends on / 依赖: row_eq_prod
-/
theorem rowLen_eq_card (μ : YoungDiagram) {i : Nat} : μ.rowLen i = (μ.row i).card := by
  simp [row_eq_prod]

@[gcongr, mono]
/--
theorem `rowLen_anti` / 定理 `rowLen_anti`

English:
theorem rowLen_anti
  given: (μ : YoungDiagram) (i1 i2 : Nat) (hi : i1 <= i2)
  statement: μ.rowLen i2 <= μ.rowLen i1
  proof: by
  by_contra! h_lt
  rw [← lt_self_iff_false (μ.rowLen i1)]
  rw [← mem_iff_lt_rowLen] at h_lt ⊢
  exact μ.up_left_mem hi (by rfl) h_lt

中文:
定理 rowLen_anti
  条件: (μ : Young图) (i1 i2 : 自然数) (hi : i1 <= i2)
  结论: μ.rowLen i2 <= μ.rowLen i1
  证明: by
  by_contra! h_lt
  rw [← lt_self_iff_false (μ.rowLen i1)]
  rw [← mem_iff_lt_rowLen] at h_lt ⊢
  exact μ.up_left_mem hi (by rfl) h_lt

Depends on / 依赖: h_lt, lt_self_iff_false, mem_iff_lt_rowLen, rowLen, up_left_mem
-/
theorem rowLen_anti (μ : YoungDiagram) (i1 i2 : Nat) (hi : i1 <= i2) : μ.rowLen i2 <= μ.rowLen i1 := by
  by_contra! h_lt
  rw [← lt_self_iff_false (μ.rowLen i1)]
  rw [← mem_iff_lt_rowLen] at h_lt ⊢
  exact μ.up_left_mem hi (by rfl) h_lt

end Rows

section Columns

/-! ### Columns and column lengths of Young diagrams.

This section has an identical API to the rows section. -/


/--
Definition of `col` / `col` 的定义

English:
definition col
  signature: (μ : YoungDiagram) (j : Nat)
  body: μ.cells.filter fun c => c.snd = j

中文:
定义 col
  签名: (μ : Young图) (j : 自然数)
  定义体: μ.cells.filter fun c => c.snd = j

Depends on / 依赖: c.snd, cells.filter, filter
-/
def col (μ : YoungDiagram) (j : Nat) : Finset (Nat × Nat) :=
  μ.cells.filter fun c => c.snd = j

/--
theorem `mem_col_iff` / 定理 `mem_col_iff`

English:
theorem mem_col_iff
  given: {μ : YoungDiagram} {j : Nat} {c : Nat × Nat}
  statement: c in μ.col j ↔ c in μ ∧ c.snd = j
  proof: by
  simp [col]

中文:
定理 mem_col_iff
  条件: {μ : Young图} {j : 自然数} {c : 自然数 × 自然数}
  结论: c in μ.col j ↔ c in μ ∧ c.snd = j
  证明: by
  simp [col]
-/
theorem mem_col_iff {μ : YoungDiagram} {j : Nat} {c : Nat × Nat} : c in μ.col j ↔ c in μ ∧ c.snd = j := by
  simp [col]

/--
theorem `mk_mem_col_iff` / 定理 `mk_mem_col_iff`

English:
theorem mk_mem_col_iff
  given: {μ : YoungDiagram} {i j : Nat}
  statement: (i, j) in μ.col j ↔ (i, j) in μ
  proof: by simp [col]

中文:
定理 mk_mem_col_iff
  条件: {μ : Young图} {i j : 自然数}
  结论: (i, j) in μ.col j ↔ (i, j) in μ
  证明: by simp [col]
-/
theorem mk_mem_col_iff {μ : YoungDiagram} {i j : Nat} : (i, j) in μ.col j ↔ (i, j) in μ := by simp [col]

/--
theorem `exists_notMem_col` / 定理 `exists_notMem_col`

English:
theorem exists_notMem_col
  given: (μ : YoungDiagram) (j : Nat)
  statement: exists i, (i, j) ∉ μ.cells
  proof: by
  convert! μ.transpose.exists_notMem_row j using 1
  simp

中文:
定理 存在_notMem_col
  条件: (μ : Young图) (j : 自然数)
  结论: 存在 i, (i, j) ∉ μ.cells
  证明: by
  convert! μ.transpose.exists_notMem_row j using 1
  simp
-/
protected theorem exists_notMem_col (μ : YoungDiagram) (j : Nat) : exists i, (i, j) ∉ μ.cells := by
  convert! μ.transpose.exists_notMem_row j using 1
  simp

/--
Definition of `colLen` / `colLen` 的定义

English:
definition colLen
  signature: (μ : YoungDiagram) (j : Nat)
  body: Nat.find μ.exists_notMem_col j

@[simp]

中文:
定义 colLen
  签名: (μ : Young图) (j : 自然数)
  定义体: Nat.find μ.exists_notMem_col j

@[simp]

Depends on / 依赖: Nat.find, exists_notMem_col
-/
def colLen (μ : YoungDiagram) (j : Nat) : Nat :=
Nat.find μ.exists_notMem_col j

@[simp]
/--
theorem `colLen_transpose` / 定理 `colLen_transpose`

English:
theorem colLen_transpose
  given: (μ : YoungDiagram) (j : Nat)
  statement: μ.transpose.colLen j = μ.rowLen j
  proof: by
  simp [rowLen, colLen]

@[simp]

中文:
定理 colLen_transpose
  条件: (μ : Young图) (j : 自然数)
  结论: μ.transpose.colLen j = μ.rowLen j
  证明: by
  simp [rowLen, colLen]

@[simp]

Depends on / 依赖: colLen, rowLen
-/
theorem colLen_transpose (μ : YoungDiagram) (j : Nat) : μ.transpose.colLen j = μ.rowLen j := by
  simp [rowLen, colLen]

@[simp]
/--
theorem `rowLen_transpose` / 定理 `rowLen_transpose`

English:
theorem rowLen_transpose
  given: (μ : YoungDiagram) (i : Nat)
  statement: μ.transpose.rowLen i = μ.colLen i
  proof: by
  simp [rowLen, colLen]

中文:
定理 rowLen_transpose
  条件: (μ : Young图) (i : 自然数)
  结论: μ.transpose.rowLen i = μ.colLen i
  证明: by
  simp [rowLen, colLen]

Depends on / 依赖: colLen, rowLen
-/
theorem rowLen_transpose (μ : YoungDiagram) (i : Nat) : μ.transpose.rowLen i = μ.colLen i := by
  simp [rowLen, colLen]

/--
theorem `mem_iff_lt_colLen` / 定理 `mem_iff_lt_colLen`

English:
theorem mem_iff_lt_colLen
  given: {μ : YoungDiagram} {i j : Nat}
  statement: (i, j) in μ ↔ i < μ.colLen j
  proof: by
  rw [← rowLen_transpose]; rw [← mem_iff_lt_rowLen]
  simp

中文:
定理 mem_iff_lt_colLen
  条件: {μ : Young图} {i j : 自然数}
  结论: (i, j) in μ ↔ i < μ.colLen j
  证明: by
  rw [← rowLen_transpose]; rw [← mem_iff_lt_rowLen]
  simp

Depends on / 依赖: mem_iff_lt_rowLen, rowLen_transpose
-/
theorem mem_iff_lt_colLen {μ : YoungDiagram} {i j : Nat} : (i, j) in μ ↔ i < μ.colLen j := by
  rw [← rowLen_transpose]; rw [← mem_iff_lt_rowLen]
  simp

/--
theorem `col_eq_prod` / 定理 `col_eq_prod`

English:
theorem col_eq_prod
  given: {μ : YoungDiagram} {j : Nat}
  statement: μ.col j = Finset.range (μ.colLen j) ×ˢ {j}
  proof: by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_col_iff,
    mem_iff_lt_colLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl

中文:
定理 col_eq_prod
  条件: {μ : Young图} {j : 自然数}
  结论: μ.col j = 有限集.range (μ.colLen j) ×ˢ {j}
  证明: by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_col_iff,
    mem_iff_lt_colLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl

Depends on / 依赖: Finset, Finset.mem_product, Finset.mem_range, Finset.mem_singleton, and_comm, and_congr_right_iff, mem_col_iff, mem_iff_lt_colLen, mem_product, mem_range, mem_singleton
-/
theorem col_eq_prod {μ : YoungDiagram} {j : Nat} : μ.col j = Finset.range (μ.colLen j) ×ˢ {j} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_col_iff,
    mem_iff_lt_colLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl

/--
theorem `colLen_eq_card` / 定理 `colLen_eq_card`

English:
theorem colLen_eq_card
  given: (μ : YoungDiagram) {j : Nat}
  statement: μ.colLen j = (μ.col j).card
  proof: by
  simp [col_eq_prod]

@[gcongr, mono]

中文:
定理 colLen_eq_card
  条件: (μ : Young图) {j : 自然数}
  结论: μ.colLen j = (μ.col j).card
  证明: by
  simp [col_eq_prod]

@[gcongr, mono]

Depends on / 依赖: col_eq_prod
-/
theorem colLen_eq_card (μ : YoungDiagram) {j : Nat} : μ.colLen j = (μ.col j).card := by
  simp [col_eq_prod]

@[gcongr, mono]
/--
theorem `colLen_anti` / 定理 `colLen_anti`

English:
theorem colLen_anti
  given: (μ : YoungDiagram) (j1 j2 : Nat) (hj : j1 <= j2)
  statement: μ.colLen j2 <= μ.colLen j1
  proof: by
  convert! μ.transpose.rowLen_anti j1 j2 hj using 1 <;> simp

中文:
定理 colLen_anti
  条件: (μ : Young图) (j1 j2 : 自然数) (hj : j1 <= j2)
  结论: μ.colLen j2 <= μ.colLen j1
  证明: by
  convert! μ.transpose.rowLen_anti j1 j2 hj using 1 <;> simp

Depends on / 依赖: convert, rowLen_anti, transpose, transpose.rowLen_anti
-/
theorem colLen_anti (μ : YoungDiagram) (j1 j2 : Nat) (hj : j1 <= j2) : μ.colLen j2 <= μ.colLen j1 := by
  convert! μ.transpose.rowLen_anti j1 j2 hj using 1 <;> simp

end Columns

section RowLens

/-! ### The list of row lengths of a Young diagram

This section defines `μ.rowLens : List ℕ`, the list of row lengths of a Young diagram `μ`.
  1. `YoungDiagram.rowLens_sorted` : It is weakly decreasing (`List.SortedGE`).
  2. `YoungDiagram.rowLens_pos` : It is strictly positive.

-/


/--
Definition of `rowLens` / `rowLens` 的定义

English:
definition rowLens
  signature: (μ : YoungDiagram)
  body: (List.range <| μ.colLen 0).map μ.rowLen

@[simp]

中文:
定义 rowLens
  签名: (μ : Young图)
  定义体: (List.range <| μ.colLen 0).map μ.rowLen

@[simp]

Depends on / 依赖: List.range, colLen, rowLen
-/
def rowLens (μ : YoungDiagram) : List Nat :=
  (List.range <| μ.colLen 0).map μ.rowLen

@[simp]
/--
theorem `get_rowLens` / 定理 `get_rowLens`

English:
theorem get_rowLens
  given: {μ : YoungDiagram} {i : Nat} {h : i < μ.rowLens.length}
  proof: by simp only [rowLens, List.getElem_range, List.getElem_map]

@[simp]

中文:
定理 get_rowLens
  条件: {μ : Young图} {i : 自然数} {h : i < μ.rowLens.length}
  证明: by simp only [rowLens, List.getElem_range, List.getElem_map]

@[simp]

Depends on / 依赖: List.getElem_map, List.getElem_range, getElem_map, getElem_range, rowLens
-/
theorem get_rowLens {μ : YoungDiagram} {i : Nat} {h : i < μ.rowLens.length} :
    μ.rowLens[i] = μ.rowLen i := by simp only [rowLens, List.getElem_range, List.getElem_map]

@[simp]
/--
theorem `length_rowLens` / 定理 `length_rowLens`

English:
theorem length_rowLens
  given: {μ : YoungDiagram}
  statement: μ.rowLens.length = μ.colLen 0
  proof: by
  simp only [rowLens, List.length_map, List.length_range]

中文:
定理 length_rowLens
  条件: {μ : Young图}
  结论: μ.rowLens.length = μ.colLen 0
  证明: by
  simp only [rowLens, List.length_map, List.length_range]

Depends on / 依赖: List.length_map, List.length_range, length_map, length_range, rowLens
-/
theorem length_rowLens {μ : YoungDiagram} : μ.rowLens.length = μ.colLen 0 := by
  simp only [rowLens, List.length_map, List.length_range]

/--
theorem `rowLens_sorted` / 定理 `rowLens_sorted`

English:
theorem rowLens_sorted
  given: (μ : YoungDiagram)
  statement: μ.rowLens.SortedGE
  proof: (List.pairwise_le_range.map _ μ.rowLen_anti).sortedGE

中文:
定理 rowLens_sorted
  条件: (μ : Young图)
  结论: μ.rowLens.SortedGE
  证明: (List.pairwise_le_range.map _ μ.rowLen_anti).sortedGE

Depends on / 依赖: List.pairwise_le_range.map, pairwise_le_range, rowLen_anti, sortedGE
-/
theorem rowLens_sorted (μ : YoungDiagram) : μ.rowLens.SortedGE :=
  (List.pairwise_le_range.map _ μ.rowLen_anti).sortedGE

/--
theorem `pos_of_mem_rowLens` / 定理 `pos_of_mem_rowLens`

English:
theorem pos_of_mem_rowLens
  given: (μ : YoungDiagram) (x : Nat) (hx : x in μ.rowLens)
  statement: 0 < x
  proof: by
  rw [rowLens]; rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl : μ.rowLen i = x⟩ := hx
  rwa [List.mem_range, ← mem_iff_lt_colLen, mem_iff_lt_rowLen] at hi

中文:
定理 pos_of_mem_rowLens
  条件: (μ : Young图) (x : 自然数) (hx : x in μ.rowLens)
  结论: 0 < x
  证明: by
  rw [rowLens]; rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl : μ.rowLen i = x⟩ := hx
  rwa [List.mem_range, ← mem_iff_lt_colLen, mem_iff_lt_rowLen] at hi

Depends on / 依赖: List.mem_map, List.mem_range, mem_iff_lt_colLen, mem_iff_lt_rowLen, mem_map, mem_range, rowLen, rowLens
-/
theorem pos_of_mem_rowLens (μ : YoungDiagram) (x : Nat) (hx : x in μ.rowLens) : 0 < x := by
  rw [rowLens]; rw [List.mem_map] at hx
  obtain ⟨i, hi, rfl : μ.rowLen i = x⟩ := hx
  rwa [List.mem_range, ← mem_iff_lt_colLen, mem_iff_lt_rowLen] at hi

end RowLens

section EquivListRowLens

/-! ### Equivalence between Young diagrams and lists of natural numbers

This section defines the equivalence between Young diagrams `μ` and weakly decreasing lists `w`
of positive natural numbers, corresponding to row lengths of the diagram:
  `YoungDiagram.equivListRowLens :`
  `YoungDiagram ≃ {w : List ℕ // w.SortedGE ∧ ∀ x ∈ w, 0 < x}`

The two directions are `YoungDiagram.rowLens` (defined above) and `YoungDiagram.ofRowLens`.

-/


/--
Definition of `cellsOfRowLens` / `cellsOfRowLens` 的定义

English:
definition cellsOfRowLens
  signature: : List Nat -> Finset (Nat × Nat)

中文:
定义 cellsOfRowLens
  签名: : 列表 自然数 -> 有限集 (自然数 × 自然数)
-/
protected def cellsOfRowLens : List Nat -> Finset (Nat × Nat)
  | [] => ∅
  | w::ws =>
    ({0} : Finset Nat) ×ˢ Finset.range w union
      (YoungDiagram.cellsOfRowLens ws).map
        (Embedding.prodMap ⟨_, Nat.succ_injective⟩ (Embedding.refl Nat))

/--
theorem `mem_cellsOfRowLens` / 定理 `mem_cellsOfRowLens`

English:
theorem mem_cellsOfRowLens
  given: {w : List Nat} {c : Nat × Nat}
  proof: by
  induction w generalizing c <;> rw [YoungDiagram.cellsOfRowLens]
  · simp
  · rcases c with ⟨⟨_, _⟩, _⟩ <;> simp_all

中文:
定理 mem_cellsOfRowLens
  条件: {w : 列表 自然数} {c : 自然数 × 自然数}
  证明: by
  induction w generalizing c <;> rw [YoungDiagram.cellsOfRowLens]
  · simp
  · rcases c with ⟨⟨_, _⟩, _⟩ <;> simp_all
-/
protected theorem mem_cellsOfRowLens {w : List Nat} {c : Nat × Nat} :
    c in YoungDiagram.cellsOfRowLens w ↔ exists h : c.fst < w.length, c.snd < w[c.fst] := by
  induction w generalizing c <;> rw [YoungDiagram.cellsOfRowLens]
  · simp
  · rcases c with ⟨⟨_, _⟩, _⟩ <;> simp_all

/--
Definition of `ofRowLens` / `ofRowLens` 的定义

English:
definition ofRowLens
  signature: (w : List Nat) (hw : w.SortedGE)
  body: YoungDiagram.cellsOfRowLens w
  isLowerSet := by
    rintro ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 <= i2, hj : j1 <= j2⟩ hcell
    rw [Finset.mem_coe]; rw [YoungDiagram.mem_cellsOfRowLens] at hcell ⊢
    obtain ⟨h1, h2⟩ := hcell
    refine ⟨hi.trans_lt h1, ?_⟩
    calc
      j1 <= j2 := hj
      _ < w[i2] := h2
      _ <= w[i1] := by
        obtain rfl | h := eq_or_lt_of_le hi
        · rfl
        · exact hw.getElem_ge_getElem_of_le h.le

中文:
定义 ofRowLens
  签名: (w : 列表 自然数) (hw : w.SortedGE)
  定义体: YoungDiagram.cellsOfRowLens w
  isLowerSet := by
    rintro ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 <= i2, hj : j1 <= j2⟩ hcell
    rw [Finset.mem_coe]; rw [YoungDiagram.mem_cellsOfRowLens] at hcell ⊢
    obtain ⟨h1, h2⟩ := hcell
    refine ⟨hi.trans_lt h1, ?_⟩
    calc
      j1 <= j2 := hj
      _ < w[i2] := h2
      _ <= w[i1] := by
        obtain rfl | h := eq_or_lt_of_le hi
        · rfl
        · exact hw.getElem_ge_getElem_of_le h.le

Depends on / 依赖: YoungDiagram, YoungDiagram.cellsOfRowLens, cellsOfRowLens
-/
def ofRowLens (w : List Nat) (hw : w.SortedGE) : YoungDiagram where
  cells := YoungDiagram.cellsOfRowLens w
  isLowerSet := by
    rintro ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 <= i2, hj : j1 <= j2⟩ hcell
    rw [Finset.mem_coe]; rw [YoungDiagram.mem_cellsOfRowLens] at hcell ⊢
    obtain ⟨h1, h2⟩ := hcell
    refine ⟨hi.trans_lt h1, ?_⟩
    calc
      j1 <= j2 := hj
      _ < w[i2] := h2
      _ <= w[i1] := by
        obtain rfl | h := eq_or_lt_of_le hi
        · rfl
        · exact hw.getElem_ge_getElem_of_le h.le

/--
theorem `mem_ofRowLens` / 定理 `mem_ofRowLens`

English:
theorem mem_ofRowLens
  given: {w : List Nat} {hw : w.SortedGE} {c : Nat × Nat}
  proof: YoungDiagram.mem_cellsOfRowLens

中文:
定理 mem_ofRowLens
  条件: {w : 列表 自然数} {hw : w.SortedGE} {c : 自然数 × 自然数}
  证明: YoungDiagram.mem_cellsOfRowLens

Depends on / 依赖: YoungDiagram, YoungDiagram.mem_cellsOfRowLens, mem_cellsOfRowLens
-/
theorem mem_ofRowLens {w : List Nat} {hw : w.SortedGE} {c : Nat × Nat} :
    c in ofRowLens w hw ↔ exists h : c.fst < w.length, c.snd < w[c.fst] :=
  YoungDiagram.mem_cellsOfRowLens

/--
theorem `rowLens_length_ofRowLens` / 定理 `rowLens_length_ofRowLens`

English:
theorem rowLens_length_ofRowLens
  given: {w : List Nat} {hw : w.SortedGE} (hpos : forall x in w, 0 < x)
  proof: by
  simp only [length_rowLens, colLen, Nat.find_eq_iff, mem_cells, mem_ofRowLens,
    lt_self_iff_false, IsEmpty.exists_iff, Classical.not_not]
  exact ⟨not_false, fun n hn => ⟨hn, hpos _ (List.getElem_mem hn)⟩⟩

中文:
定理 rowLens_length_ofRowLens
  条件: {w : 列表 自然数} {hw : w.SortedGE} (hpos : 对任意 x in w, 0 < x)
  证明: by
  simp only [length_rowLens, colLen, Nat.find_eq_iff, mem_cells, mem_ofRowLens,
    lt_self_iff_false, IsEmpty.exists_iff, Classical.not_not]
  exact ⟨not_false, fun n hn => ⟨hn, hpos _ (List.getElem_mem hn)⟩⟩

Depends on / 依赖: Classical, Classical.not_not, IsEmpty, IsEmpty.exists_iff, List.getElem_mem, Nat.find_eq_iff, colLen, exists_iff, find_eq_iff, getElem_mem, length_rowLens, lt_self_iff_false, mem_cells, mem_ofRowLens, not_false, not_not
-/
theorem rowLens_length_ofRowLens {w : List Nat} {hw : w.SortedGE} (hpos : forall x in w, 0 < x) :
    (ofRowLens w hw).rowLens.length = w.length := by
  simp only [length_rowLens, colLen, Nat.find_eq_iff, mem_cells, mem_ofRowLens,
    lt_self_iff_false, IsEmpty.exists_iff, Classical.not_not]
  exact ⟨not_false, fun n hn => ⟨hn, hpos _ (List.getElem_mem hn)⟩⟩

/--
theorem `rowLen_ofRowLens` / 定理 `rowLen_ofRowLens`

English:
theorem rowLen_ofRowLens
  given: {w : List Nat} {hw : w.SortedGE} (i : Fin w.length)
  proof: by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens]

中文:
定理 rowLen_ofRowLens
  条件: {w : 列表 自然数} {hw : w.SortedGE} (i : 有限集 w.length)
  证明: by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens]

Depends on / 依赖: Nat.find_eq_iff, find_eq_iff, mem_ofRowLens, rowLen
-/
theorem rowLen_ofRowLens {w : List Nat} {hw : w.SortedGE} (i : Fin w.length) :
    (ofRowLens w hw).rowLen i = w[i] := by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens]

/--
theorem `ofRowLens_to_rowLens_eq_self` / 定理 `ofRowLens_to_rowLens_eq_self`

English:
theorem ofRowLens_to_rowLens_eq_self
  given: {μ : YoungDiagram}
  statement: ofRowLens _ (rowLens_sorted μ) = μ
  proof: by
  ext ⟨i, j⟩
  simp only [mem_cells, mem_ofRowLens, length_rowLens, get_rowLens]
  simpa [← mem_iff_lt_colLen, mem_iff_lt_rowLen] using j.zero_le.trans_lt

中文:
定理 ofRowLens_to_rowLens_eq_self
  条件: {μ : Young图}
  结论: ofRowLens _ (rowLens_sorted μ) = μ
  证明: by
  ext ⟨i, j⟩
  simp only [mem_cells, mem_ofRowLens, length_rowLens, get_rowLens]
  simpa [← mem_iff_lt_colLen, mem_iff_lt_rowLen] using j.zero_le.trans_lt

Depends on / 依赖: get_rowLens, j.zero_le.trans_lt, length_rowLens, mem_cells, mem_iff_lt_colLen, mem_iff_lt_rowLen, mem_ofRowLens, trans_lt, zero_le
-/
theorem ofRowLens_to_rowLens_eq_self {μ : YoungDiagram} : ofRowLens _ (rowLens_sorted μ) = μ := by
  ext ⟨i, j⟩
  simp only [mem_cells, mem_ofRowLens, length_rowLens, get_rowLens]
  simpa [← mem_iff_lt_colLen, mem_iff_lt_rowLen] using j.zero_le.trans_lt

/--
theorem `rowLens_ofRowLens_eq_self` / 定理 `rowLens_ofRowLens_eq_self`

English:
theorem rowLens_ofRowLens_eq_self
  given: {w : List Nat} {hw : w.SortedGE} (hpos : forall x in w, 0 < x)
  proof: List.ext_get (rowLens_length_ofRowLens hpos) fun i h₁ h₂ =>
(get_rowLens (h := h₁)).trans rowLen_ofRowLens ⟨i, h₂⟩

中文:
定理 rowLens_ofRowLens_eq_self
  条件: {w : 列表 自然数} {hw : w.SortedGE} (hpos : 对任意 x in w, 0 < x)
  证明: List.ext_get (rowLens_length_ofRowLens hpos) fun i h₁ h₂ =>
(get_rowLens (h := h₁)).trans rowLen_ofRowLens ⟨i, h₂⟩

Depends on / 依赖: List.ext_get, ext_get, get_rowLens, rowLen_ofRowLens, rowLens_length_ofRowLens
-/
theorem rowLens_ofRowLens_eq_self {w : List Nat} {hw : w.SortedGE} (hpos : forall x in w, 0 < x) :
    (ofRowLens w hw).rowLens = w :=
  List.ext_get (rowLens_length_ofRowLens hpos) fun i h₁ h₂ =>
(get_rowLens (h := h₁)).trans rowLen_ofRowLens ⟨i, h₂⟩

/-- Equivalence between Young diagrams and weakly decreasing lists of positive natural numbers.
A Young diagram `μ` is equivalent to a list of row lengths. -/
@[simps]
/--
Definition of `equivListRowLens` / `equivListRowLens` 的定义

English:
definition equivListRowLens
  signature: : YoungDiagram ≃ { w : List Nat // w.SortedGE ∧ forall x in w, 0 < x } where
  body: ⟨μ.rowLens, μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩
  invFun ww := ofRowLens ww.1 ww.2.1
  left_inv _ := ofRowLens_to_rowLens_eq_self
  right_inv := fun ⟨_, hw⟩ => Subtype.mk_eq_mk.mpr (rowLens_ofRowLens_eq_self hw.2)

中文:
定义 equivListRowLens
  签名: : Young图 ≃ { w : 列表 自然数 // w.SortedGE ∧ 对任意 x in w, 0 < x } where
  定义体: ⟨μ.rowLens, μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩
  invFun ww := ofRowLens ww.1 ww.2.1
  left_inv _ := ofRowLens_to_rowLens_eq_self
  right_inv := fun ⟨_, hw⟩ => Subtype.mk_eq_mk.mpr (rowLens_ofRowLens_eq_self hw.2)

Depends on / 依赖: pos_of_mem_rowLens, rowLens, rowLens_sorted
-/
def equivListRowLens : YoungDiagram ≃ { w : List Nat // w.SortedGE ∧ forall x in w, 0 < x } where
  toFun μ := ⟨μ.rowLens, μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩
  invFun ww := ofRowLens ww.1 ww.2.1
  left_inv _ := ofRowLens_to_rowLens_eq_self
  right_inv := fun ⟨_, hw⟩ => Subtype.mk_eq_mk.mpr (rowLens_ofRowLens_eq_self hw.2)

end EquivListRowLens

end YoungDiagram
