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
/-
**YoungDiagram** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that wh
enever
a cell is present, so are all the ones above and to the left of it. Like matrice
s, an `(i, j)` cell
is a cell in row `i` and column `j`, where rows are enumerated downward and colu
mns rightward.

Young diagrams are modeled as finite sets in `ℕ × ℕ` that are lower sets with re
spect to the
standard order on products.
-/
structure YoungDiagram where
  /-- A finite set which represents a finite collection of cells on the `ℕ × ℕ` grid. -/
  cells : Finset (ℕ × ℕ)
  /-- Cells are up-left justified, witnessed by the fact that `cells` is a lower set in `ℕ × ℕ`. -/
  isLowerSet : IsLowerSet (cells : Set (ℕ × ℕ))

namespace YoungDiagram

/-
**YoungDiagram.** 是 Mathlib 中的一个实例，位于命名空间 `YoungDiagram`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike YoungDiagram (ℕ × ℕ) where
  coe y := y.cells
  coe_injective μ ν h := by rwa [YoungDiagram.ext_iff, ← Finset.coe_inj]
/-
**YoungDiagram.** 是 Mathlib 中的一个实例，位于命名空间 `YoungDiagram`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder YoungDiagram := .ofSetLike YoungDiagram (ℕ × ℕ)

@[simp]
/-
**YoungDiagram.mem_cells** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_cells {μ : YoungDiagram} (c : Nat × Nat) : c in μ.cells ↔ c in μ
参数：c : Nat × Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_cells {μ : YoungDiagram} (c : ℕ × ℕ) : c ∈ μ.cells ↔ c ∈ μ :=
  Iff.rfl

@[simp]
/-
**YoungDiagram.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_mk (c : Nat × Nat) (cells) (isLowerSet) : c in YoungDiagram.mk cells i
sLowerSet ↔ c in cells
参数：c : Nat × Nat；cells；isLowerSet。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_mk (c : ℕ × ℕ) (cells) (isLowerSet) :
    c ∈ YoungDiagram.mk cells isLowerSet ↔ c ∈ cells :=
  Iff.rfl
/-
**YoungDiagram.decidableMem** 是 Mathlib 中的一个实例，位于命名空间 `YoungDiagram`。
形式化陈述：decidableMem (μ : YoungDiagram) : DecidablePred (· in μ)
参数：μ : YoungDiagram。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableMem (μ : YoungDiagram) : DecidablePred (· ∈ μ) :=
  inferInstanceAs (DecidablePred (· ∈ μ.cells))

/-- In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left of (i2, j2). -/
/-
**YoungDiagram.up_left_mem** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : Nat} (hi : i1 <= i2) (hj : j
1 <= j2) (hcell : (i2, j2) in μ) : (i1, j1) in μ
参数：μ : YoungDiagram；hi : i1 <= i2；hj : j1 <= j2；hcell : (i2, j2) in μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `YoungDiagram.isLowerSet`：∀ (self : YoungDiagram), IsLowerSet ↑self.cells
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.mk_le_mk`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : L
E β] {a₁ a₂ : α} {b₁ b₂ : β},   (a₁, b₁) ≤ (a₂, b₂) ↔ a₁ ≤ a₂ ∧ b₁ ≤ b₂

--- 原说明 ---
In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left of (i2, j2).
-/
theorem up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2)
    (hcell : (i2, j2) ∈ μ) : (i1, j1) ∈ μ :=
  μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

section DistribLattice

@[simp]
/-
**YoungDiagram.cells_subset_iff** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：cells_subset_iff {μ ν : YoungDiagram} : μ.cells subseteq ν.cells ↔ μ <= ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cells_subset_iff {μ ν : YoungDiagram} : μ.cells ⊆ ν.cells ↔ μ ≤ ν :=
  Iff.rfl

@[simp]
/-
**YoungDiagram.cells_ssubset_iff** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：cells_ssubset_iff {μ ν : YoungDiagram} : μ.cells ⊂ ν.cells ↔ μ < ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem cells_ssubset_iff {μ ν : YoungDiagram} : μ.cells ⊂ ν.cells ↔ μ < ν :=
  Iff.rfl
/-
**YoungDiagram.** 是 Mathlib 中的一个实例，位于命名空间 `YoungDiagram`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max YoungDiagram where
  max μ ν :=
    { cells := μ.cells ∪ ν.cells
      isLowerSet := by
        rw [Finset.coe_union]
        exact μ.isLowerSet.union ν.isLowerSet }

@[simp]
/-
**YoungDiagram.cells_sup** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：cells_sup (μ ν : YoungDiagram) : (μ ⊔ ν).cells = μ.cells union ν.cells
参数：μ ν : YoungDiagram。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cells_sup (μ ν : YoungDiagram) : (μ ⊔ ν).cells = μ.cells ∪ ν.cells :=
  rfl

@[simp, norm_cast]
/-
**YoungDiagram.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：coe_sup (μ ν : YoungDiagram) : ↑(μ ⊔ ν) = (μ union ν : Set (Nat × Nat))
参数：μ ν : YoungDiagram。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
-/
theorem coe_sup (μ ν : YoungDiagram) : ↑(μ ⊔ ν) = (μ ∪ ν : Set (ℕ × ℕ)) :=
  Finset.coe_union _ _

@[simp]
/-
**YoungDiagram.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_sup {μ ν : YoungDiagram} {x : Nat × Nat} : x in μ ⊔ ν ↔ x in μ ∨ x in 
ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_union`：mem_union : a in s union t ↔ a in s ∨ a in t
-/
theorem mem_sup {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ ⊔ ν ↔ x ∈ μ ∨ x ∈ ν :=
  Finset.mem_union
/-
**YoungDiagram.** 是 Mathlib 中的一个实例，位于命名空间 `YoungDiagram`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min YoungDiagram where
  min μ ν :=
    { cells := μ.cells ∩ ν.cells
      isLowerSet := by
        rw [Finset.coe_inter]
        exact μ.isLowerSet.inter ν.isLowerSet }

@[simp]
/-
**YoungDiagram.cells_inf** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：cells_inf (μ ν : YoungDiagram) : (μ ⊓ ν).cells = μ.cells inter ν.cells
参数：μ ν : YoungDiagram。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cells_inf (μ ν : YoungDiagram) : (μ ⊓ ν).cells = μ.cells ∩ ν.cells :=
  rfl

@[simp, norm_cast]
/-
**YoungDiagram.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：coe_inf (μ ν : YoungDiagram) : ↑(μ ⊓ ν) = (μ inter ν : Set (Nat × Nat))
参数：μ ν : YoungDiagram。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
-/
theorem coe_inf (μ ν : YoungDiagram) : ↑(μ ⊓ ν) = (μ ∩ ν : Set (ℕ × ℕ)) :=
  Finset.coe_inter _ _

@[simp]
/-
**YoungDiagram.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_inf {μ ν : YoungDiagram} {x : Nat × Nat} : x in μ ⊓ ν ↔ x in μ ∧ x in 
ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_inter`：mem_inter {a : α} {s₁ s₂ : Finset α} : a in s₁ inter s
₂ ↔ a in s₁ ∧ a in s₂
-/
theorem mem_inf {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ ⊓ ν ↔ x ∈ μ ∧ x ∈ ν :=
  Finset.mem_inter

/-- The empty Young diagram is `(⊥ : YoungDiagram)`. -/
/-
**YoungDiagram.** 是 Mathlib 中的一个实例，位于命名空间 `YoungDiagram`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty Young diagram is `(⊥ : YoungDiagram)`.
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
/-
**YoungDiagram.cells_bot** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：cells_bot : (⊥ : YoungDiagram).cells = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cells_bot : (⊥ : YoungDiagram).cells = ∅ :=
  rfl

@[simp]
/-
**YoungDiagram.notMem_bot** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：notMem_bot (x : Nat × Nat) : x ∉ (⊥ : YoungDiagram)
参数：x : Nat × Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
-/
theorem notMem_bot (x : ℕ × ℕ) : x ∉ (⊥ : YoungDiagram) :=
  Finset.notMem_empty x

@[norm_cast]
/-
**YoungDiagram.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：coe_bot : (⊥ : YoungDiagram) = (∅ : Set (Nat × Nat))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_bot : (⊥ : YoungDiagram) = (∅ : Set (ℕ × ℕ)) := by
  ext; simp
/-
**YoungDiagram.** 是 Mathlib 中的一个实例，位于命名空间 `YoungDiagram`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited YoungDiagram :=
  ⟨⊥⟩
/-
**YoungDiagram.** 是 Mathlib 中的一个实例，位于命名空间 `YoungDiagram`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribLattice YoungDiagram :=
  Function.Injective.distribLattice YoungDiagram.cells (fun μ ν h ↦ by rwa [YoungDiagram.ext_iff])
    .rfl .rfl (fun _ _ ↦ rfl) fun _ _ ↦ rfl

end DistribLattice

/-- Cardinality of a Young diagram -/
/-
**YoungDiagram.card** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：YoungDiagram → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cardinality of a Young diagram
-/
protected abbrev card (μ : YoungDiagram) : ℕ :=
  μ.cells.card

section Transpose

/-- The `transpose` of a Young diagram is obtained by swapping i's with j's. -/
/-
**YoungDiagram.transpose** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：transpose (μ : YoungDiagram) : YoungDiagram where cells
参数：μ : YoungDiagram。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `transpose` of a Young diagram is obtained by swapping i's with j's.
-/
def transpose (μ : YoungDiagram) : YoungDiagram where
  cells := (Equiv.prodComm _ _).finsetCongr μ.cells
  isLowerSet _ _ h := by
    simp only [Finset.mem_coe, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    intro hcell
    apply μ.isLowerSet _ hcell
    simp [h]

@[simp]
/-
**YoungDiagram.mem_transpose** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_transpose {μ : YoungDiagram} {c : Nat × Nat} : c in μ.transpose ↔ c.sw
ap in μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_transpose {μ : YoungDiagram} {c : ℕ × ℕ} : c ∈ μ.transpose ↔ c.swap ∈ μ := by
  simp [transpose]

@[simp]
/-
**YoungDiagram.transpose_transpose** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：transpose_transpose (μ : YoungDiagram) : μ.transpose.transpose = μ
参数：μ : YoungDiagram。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `YoungDiagram.ext`：∀ {x y : YoungDiagram}, x.cells = y.cells → x = y
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α × β), x.swap.swap
 = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem transpose_transpose (μ : YoungDiagram) : μ.transpose.transpose = μ := by
  ext x
  simp
/-
**YoungDiagram.transpose_eq_iff_eq_transpose** 是 Mathlib 中的一个定理，位于命名空间 `YoungDia
gram`。
形式化陈述：transpose_eq_iff_eq_transpose {μ ν : YoungDiagram} : μ.transpose = ν ↔ μ =
 ν.transpose
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `YoungDiagram.transpose_transpose`：transpose_transpose (μ : YoungDiagram)
 : μ.transpose.transpose = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem transpose_eq_iff_eq_transpose {μ ν : YoungDiagram} : μ.transpose = ν ↔ μ = ν.transpose := by
  constructor <;>
    · rintro rfl
      simp

@[simp]
/-
**YoungDiagram.transpose_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：transpose_eq_iff {μ ν : YoungDiagram} : μ.transpose = ν.transpose ↔ μ = ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `YoungDiagram.transpose_eq_iff_eq_transpose`：transpose_eq_iff_eq_transpos
e {μ ν : YoungDiagram} : μ.transpose = ν ↔ μ = ν.transpose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `YoungDiagram.transpose_transpose`：transpose_transpose (μ : YoungDiagram)
 : μ.transpose.transpose = μ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem transpose_eq_iff {μ ν : YoungDiagram} : μ.transpose = ν.transpose ↔ μ = ν := by
  rw [transpose_eq_iff_eq_transpose]
  simp

-- This is effectively both directions of `transpose_le_iff` below.
/-
**YoungDiagram.le_of_transpose_le** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：∀ {μ ν : YoungDiagram}, μ.transpose ≤ ν → μ ≤ ν.transpose
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α × β), x.swap.swap
 = x
-/
protected theorem le_of_transpose_le {μ ν : YoungDiagram} (h_le : μ.transpose ≤ ν) :
    μ ≤ ν.transpose := fun c hc => by
  simp only [mem_transpose]
  apply h_le
  simpa

@[simp]
/-
**YoungDiagram.transpose_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：transpose_le_iff {μ ν : YoungDiagram} : μ.transpose <= ν.transpose ↔ μ <= 
ν
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `YoungDiagram.transpose_transpose`：transpose_transpose (μ : YoungDiagram)
 : μ.transpose.transpose = μ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `YoungDiagram.le_of_transpose_le`：∀ {μ ν : YoungDiagram}, μ.transpose ≤ ν
 → μ ≤ ν.transpose
-/
theorem transpose_le_iff {μ ν : YoungDiagram} : μ.transpose ≤ ν.transpose ↔ μ ≤ ν :=
  ⟨fun h => by
    convert! YoungDiagram.le_of_transpose_le h
    simp, fun h => by
    rw [← transpose_transpose μ] at h
    exact YoungDiagram.le_of_transpose_le h ⟩

@[gcongr, mono]
/-
**YoungDiagram.transpose_mono** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：∀ {μ ν : YoungDiagram}, μ ≤ ν → μ.transpose ≤ ν.transpose
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `YoungDiagram.transpose_le_iff`：transpose_le_iff {μ ν : YoungDiagram} : μ
.transpose <= ν.transpose ↔ μ <= ν
-/
protected theorem transpose_mono {μ ν : YoungDiagram} (h_le : μ ≤ ν) : μ.transpose ≤ ν.transpose :=
  transpose_le_iff.mpr h_le

set_option backward.isDefEq.respectTransparency false in
/-- Transposing Young diagrams is an `OrderIso`. -/
@[simps]
/-
**YoungDiagram.transposeOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：transposeOrderIso : YoungDiagram ≃o YoungDiagram
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transposing Young diagrams is an `OrderIso`.
-/
def transposeOrderIso : YoungDiagram ≃o YoungDiagram :=
  ⟨⟨transpose, transpose, fun _ => by simp, fun _ => by simp⟩, by simp⟩

end Transpose

section Rows

/-! ### Rows and row lengths of Young diagrams.

This section defines `μ.row` and `μ.rowLen`, with the following API:
      1.  `(i, j) ∈ μ ↔ j < μ.rowLen i`
      2.  `μ.row i = {i} ×ˢ (Finset.range (μ.rowLen i))`
      3.  `μ.rowLen i = (μ.row i).card`
      4.  `∀ {i1 i2}, i1 ≤ i2 → μ.rowLen i2 ≤ μ.rowLen i1`

Note: #3 is not convenient for defining `μ.rowLen`; instead, `μ.rowLen` is defined
as the smallest `j` such that `(i, j) ∉ μ`. -/


/-- The `i`-th row of a Young diagram consists of the cells whose first coordinate is `i`. -/
/-
**YoungDiagram.row** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：row (μ : YoungDiagram) (i : Nat) : Finset (Nat × Nat)
参数：μ : YoungDiagram；i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`-th row of a Young diagram consists of the cells whose first coordinate i
s `i`.
-/
def row (μ : YoungDiagram) (i : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => c.fst = i
/-
**YoungDiagram.mem_row_iff** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_row_iff {μ : YoungDiagram} {i : Nat} {c : Nat × Nat} : c in μ.row i ↔ 
c in μ ∧ c.fst = i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_row_iff {μ : YoungDiagram} {i : ℕ} {c : ℕ × ℕ} : c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i := by
  simp [row]
/-
**YoungDiagram.mk_mem_row_iff** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mk_mem_row_iff {μ : YoungDiagram} {i j : Nat} : (i, j) in μ.row i ↔ (i, j)
 in μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_mem_row_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.row i ↔ (i, j) ∈ μ := by simp [row]

set_option backward.isDefEq.respectTransparency false in
/-
**YoungDiagram.exists_notMem_row** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：∀ (μ : YoungDiagram) (i : ℕ), ∃ j, (i, j) ∉ μ
参数：μ : YoungDiagram；i : ℕ；i, j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Infinite.exists_notMem_finset`：exists_notMem_finset [Infinite α] (s : Fi
nset α) : exists x, x ∉ s
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_preimage`：mem_preimage {f : α -> β} {s : Finset β} {hf : Set.
InjOn f (f ⁻¹' ↑s)} {x : α} : x in preimage s f hf ↔ f x in s
-/
protected theorem exists_notMem_row (μ : YoungDiagram) (i : ℕ) : ∃ j, (i, j) ∉ μ := by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_notMem_finset
      (μ.cells.preimage (Prod.mk i) fun _ _ _ _ h => by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  exact ⟨j, hj⟩

/-- Length of a row of a Young diagram -/
/-
**YoungDiagram.rowLen** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：rowLen (μ : YoungDiagram) (i : Nat) : Nat
参数：μ : YoungDiagram；i : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `YoungDiagram.exists_notMem_row`：∀ (μ : YoungDiagram) (i : ℕ), ∃ j, (i, j
) ∉ μ

--- 原说明 ---
Length of a row of a Young diagram
-/
def rowLen (μ : YoungDiagram) (i : ℕ) : ℕ :=
  Nat.find <| μ.exists_notMem_row i
/-
**YoungDiagram.mem_iff_lt_rowLen** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_iff_lt_rowLen {μ : YoungDiagram} {i j : Nat} : (i, j) in μ ↔ j < μ.row
Len i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `YoungDiagram.exists_notMem_row`：∀ (μ : YoungDiagram) (i : ℕ), ∃ j, (i, j
) ∉ μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `YoungDiagram.rowLen.eq_1`：∀ (μ : YoungDiagram) (i : ℕ), μ.rowLen i = Nat
.find ⋯
· 使用定理 `Nat.lt_find_iff`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (h : ∃ n, p n
) (n : ℕ), n < Nat.find h ↔ ∀ m ≤ n, ¬p m
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `YoungDiagram.up_left_mem`：up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : 
Nat} (hi : i1 <= i2) (hj : j1 <= j2) (hcell : (i2, j2) in μ) : (i1, j1) in μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mem_iff_lt_rowLen {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ j < μ.rowLen i := by
  rw [rowLen, Nat.lt_find_iff]
  push Not
  exact ⟨fun h _ hmj => μ.up_left_mem (by rfl) hmj h, fun h => h _ (by rfl)⟩
/-
**YoungDiagram.row_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：row_eq_prod {μ : YoungDiagram} {i : Nat} : μ.row i = {i} ×ˢ Finset.range (
μ.rowLen i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem row_eq_prod {μ : YoungDiagram} {i : ℕ} : μ.row i = {i} ×ˢ Finset.range (μ.rowLen i) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_row_iff,
    mem_iff_lt_rowLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl
/-
**YoungDiagram.rowLen_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：rowLen_eq_card (μ : YoungDiagram) {i : Nat} : μ.rowLen i = (μ.row i).card
参数：μ : YoungDiagram。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `YoungDiagram.row_eq_prod`：row_eq_prod {μ : YoungDiagram} {i : Nat} : μ.r
ow i = {i} ×ˢ Finset.range (μ.rowLen i)
· 使用定理 `Finset.singleton_product`：singleton_product {a : α} : ({a} : Finset α) ×
ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rowLen_eq_card (μ : YoungDiagram) {i : ℕ} : μ.rowLen i = (μ.row i).card := by
  simp [row_eq_prod]

@[gcongr, mono]
/-
**YoungDiagram.rowLen_anti** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：rowLen_anti (μ : YoungDiagram) (i1 i2 : Nat) (hi : i1 <= i2) : μ.rowLen i2
 <= μ.rowLen i1
参数：μ : YoungDiagram；i1 i2 : Nat；hi : i1 <= i2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用定理 `YoungDiagram.mem_iff_lt_rowLen`：mem_iff_lt_rowLen {μ : YoungDiagram} {i 
j : Nat} : (i, j) in μ ↔ j < μ.rowLen i
· 使用定理 `YoungDiagram.up_left_mem`：up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : 
Nat} (hi : i1 <= i2) (hj : j1 <= j2) (hcell : (i2, j2) in μ) : (i1, j1) in μ
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem rowLen_anti (μ : YoungDiagram) (i1 i2 : ℕ) (hi : i1 ≤ i2) : μ.rowLen i2 ≤ μ.rowLen i1 := by
  by_contra! h_lt
  rw [← lt_self_iff_false (μ.rowLen i1)]
  rw [← mem_iff_lt_rowLen] at h_lt ⊢
  exact μ.up_left_mem hi (by rfl) h_lt

end Rows

section Columns

/-! ### Columns and column lengths of Young diagrams.

This section has an identical API to the rows section. -/


/-- The `j`-th column of a Young diagram consists of the cells whose second coordinate is `j`. -/
/-
**YoungDiagram.col** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：col (μ : YoungDiagram) (j : Nat) : Finset (Nat × Nat)
参数：μ : YoungDiagram；j : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `j`-th column of a Young diagram consists of the cells whose second coordina
te is `j`.
-/
def col (μ : YoungDiagram) (j : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => c.snd = j
/-
**YoungDiagram.mem_col_iff** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_col_iff {μ : YoungDiagram} {j : Nat} {c : Nat × Nat} : c in μ.col j ↔ 
c in μ ∧ c.snd = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_col_iff {μ : YoungDiagram} {j : ℕ} {c : ℕ × ℕ} : c ∈ μ.col j ↔ c ∈ μ ∧ c.snd = j := by
  simp [col]
/-
**YoungDiagram.mk_mem_col_iff** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mk_mem_col_iff {μ : YoungDiagram} {i j : Nat} : (i, j) in μ.col j ↔ (i, j)
 in μ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_mem_col_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.col j ↔ (i, j) ∈ μ := by simp [col]
/-
**YoungDiagram.exists_notMem_col** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：∀ (μ : YoungDiagram) (j : ℕ), ∃ i, (i, j) ∉ μ.cells
参数：μ : YoungDiagram；j : ℕ；i, j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `YoungDiagram.exists_notMem_row`：∀ (μ : YoungDiagram) (i : ℕ), ∃ j, (i, j
) ∉ μ
-/
protected theorem exists_notMem_col (μ : YoungDiagram) (j : ℕ) : ∃ i, (i, j) ∉ μ.cells := by
  convert! μ.transpose.exists_notMem_row j using 1
  simp

/-- Length of a column of a Young diagram -/
/-
**YoungDiagram.colLen** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：colLen (μ : YoungDiagram) (j : Nat) : Nat
参数：μ : YoungDiagram；j : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `YoungDiagram.exists_notMem_col`：∀ (μ : YoungDiagram) (j : ℕ), ∃ i, (i, j
) ∉ μ.cells

--- 原说明 ---
Length of a column of a Young diagram
-/
def colLen (μ : YoungDiagram) (j : ℕ) : ℕ :=
  Nat.find <| μ.exists_notMem_col j

@[simp]
/-
**YoungDiagram.colLen_transpose** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：colLen_transpose (μ : YoungDiagram) (j : Nat) : μ.transpose.colLen j = μ.r
owLen j
参数：μ : YoungDiagram；j : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `YoungDiagram.exists_notMem_row`：∀ (μ : YoungDiagram) (i : ℕ), ∃ j, (i, j
) ∉ μ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `YoungDiagram.exists_notMem_col`：∀ (μ : YoungDiagram) (j : ℕ), ∃ i, (i, j
) ∉ μ.cells
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colLen_transpose (μ : YoungDiagram) (j : ℕ) : μ.transpose.colLen j = μ.rowLen j := by
  simp [rowLen, colLen]

@[simp]
/-
**YoungDiagram.rowLen_transpose** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：rowLen_transpose (μ : YoungDiagram) (i : Nat) : μ.transpose.rowLen i = μ.c
olLen i
参数：μ : YoungDiagram；i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `YoungDiagram.exists_notMem_row`：∀ (μ : YoungDiagram) (i : ℕ), ∃ j, (i, j
) ∉ μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `YoungDiagram.exists_notMem_col`：∀ (μ : YoungDiagram) (j : ℕ), ∃ i, (i, j
) ∉ μ.cells
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rowLen_transpose (μ : YoungDiagram) (i : ℕ) : μ.transpose.rowLen i = μ.colLen i := by
  simp [rowLen, colLen]
/-
**YoungDiagram.mem_iff_lt_colLen** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_iff_lt_colLen {μ : YoungDiagram} {i j : Nat} : (i, j) in μ ↔ i < μ.col
Len j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `YoungDiagram.rowLen_transpose`：rowLen_transpose (μ : YoungDiagram) (i : 
Nat) : μ.transpose.rowLen i = μ.colLen i
· 使用定理 `YoungDiagram.mem_iff_lt_rowLen`：mem_iff_lt_rowLen {μ : YoungDiagram} {i 
j : Nat} : (i, j) in μ ↔ j < μ.rowLen i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_iff_lt_colLen {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ i < μ.colLen j := by
  rw [← rowLen_transpose, ← mem_iff_lt_rowLen]
  simp
/-
**YoungDiagram.col_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：col_eq_prod {μ : YoungDiagram} {j : Nat} : μ.col j = Finset.range (μ.colLe
n j) ×ˢ {j}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem col_eq_prod {μ : YoungDiagram} {j : ℕ} : μ.col j = Finset.range (μ.colLen j) ×ˢ {j} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_col_iff,
    mem_iff_lt_colLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl
/-
**YoungDiagram.colLen_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：colLen_eq_card (μ : YoungDiagram) {j : Nat} : μ.colLen j = (μ.col j).card
参数：μ : YoungDiagram。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk_left_injective`：mk_left_injective {α β : Type*} (b : β) : (fun a
 => mk a b : α -> α × β).Injective
· 使用定理 `YoungDiagram.col_eq_prod`：col_eq_prod {μ : YoungDiagram} {j : Nat} : μ.c
ol j = Finset.range (μ.colLen j) ×ˢ {j}
· 使用引理 `Finset.product_singleton`：product_singleton : s ×ˢ {b} = s.map ⟨fun i =>
 (i, b), Prod.mk_left_injective _⟩
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem colLen_eq_card (μ : YoungDiagram) {j : ℕ} : μ.colLen j = (μ.col j).card := by
  simp [col_eq_prod]

@[gcongr, mono]
/-
**YoungDiagram.colLen_anti** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：colLen_anti (μ : YoungDiagram) (j1 j2 : Nat) (hj : j1 <= j2) : μ.colLen j2
 <= μ.colLen j1
参数：μ : YoungDiagram；j1 j2 : Nat；hj : j1 <= j2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `YoungDiagram.rowLen_transpose`：rowLen_transpose (μ : YoungDiagram) (i : 
Nat) : μ.transpose.rowLen i = μ.colLen i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `YoungDiagram.rowLen_anti`：rowLen_anti (μ : YoungDiagram) (i1 i2 : Nat) (
hi : i1 <= i2) : μ.rowLen i2 <= μ.rowLen i1
-/
theorem colLen_anti (μ : YoungDiagram) (j1 j2 : ℕ) (hj : j1 ≤ j2) : μ.colLen j2 ≤ μ.colLen j1 := by
  convert! μ.transpose.rowLen_anti j1 j2 hj using 1 <;> simp

end Columns

section RowLens

/-! ### The list of row lengths of a Young diagram

This section defines `μ.rowLens : List ℕ`, the list of row lengths of a Young diagram `μ`.
  1. `YoungDiagram.rowLens_sorted` : It is weakly decreasing (`List.SortedGE`).
  2. `YoungDiagram.rowLens_pos` : It is strictly positive.

-/


/-- List of row lengths of a Young diagram -/
/-
**YoungDiagram.rowLens** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：rowLens (μ : YoungDiagram) : List Nat
参数：μ : YoungDiagram。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
List of row lengths of a Young diagram
-/
def rowLens (μ : YoungDiagram) : List ℕ :=
  (List.range <| μ.colLen 0).map μ.rowLen

@[simp]
/-
**YoungDiagram.get_rowLens** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：get_rowLens {μ : YoungDiagram} {i : Nat} {h : i < μ.rowLens.length} : μ.ro
wLens[i] = μ.rowLen i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `List.getElem_range`：∀ {j n : ℕ} (h : j < (List.range n).length), (List.r
ange n)[j] = j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_rowLens {μ : YoungDiagram} {i : Nat} {h : i < μ.rowLens.length} :
    μ.rowLens[i] = μ.rowLen i := by simp only [rowLens, List.getElem_range, List.getElem_map]

@[simp]
/-
**YoungDiagram.length_rowLens** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：length_rowLens {μ : YoungDiagram} : μ.rowLens.length = μ.colLen 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_rowLens {μ : YoungDiagram} : μ.rowLens.length = μ.colLen 0 := by
  simp only [rowLens, List.length_map, List.length_range]
/-
**YoungDiagram.rowLens_sorted** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：rowLens_sorted (μ : YoungDiagram) : μ.rowLens.SortedGE
参数：μ : YoungDiagram。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedGE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≥ x2) l → l.SortedGE
· 使用定理 `List.Pairwise.map`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Prop} {l
 : List α} {S : β → β → Prop} (f : α → β),   (∀ (a b : α), R a b → S (f a) (f b)
) → Lis…
· 使用定理 `YoungDiagram.rowLen_anti`：rowLen_anti (μ : YoungDiagram) (i1 i2 : Nat) (
hi : i1 <= i2) : μ.rowLen i2 <= μ.rowLen i1
· 使用定理 `List.pairwise_le_range`：∀ {n : ℕ}, List.Pairwise (fun x1 x2 => x1 ≤ x2) 
(List.range n)
-/
theorem rowLens_sorted (μ : YoungDiagram) : μ.rowLens.SortedGE :=
  (List.pairwise_le_range.map _ μ.rowLen_anti).sortedGE
/-
**YoungDiagram.pos_of_mem_rowLens** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：pos_of_mem_rowLens (μ : YoungDiagram) (x : Nat) (hx : x in μ.rowLens) : 0 
< x
参数：μ : YoungDiagram；x : Nat；hx : x in μ.rowLens。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `YoungDiagram.rowLens.eq_1`：∀ (μ : YoungDiagram), μ.rowLens = List.map μ.
rowLen (List.range (μ.colLen 0))
· 使用定理 `YoungDiagram.mem_iff_lt_rowLen`：mem_iff_lt_rowLen {μ : YoungDiagram} {i 
j : Nat} : (i, j) in μ ↔ j < μ.rowLen i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `YoungDiagram.mem_iff_lt_colLen`：mem_iff_lt_colLen {μ : YoungDiagram} {i 
j : Nat} : (i, j) in μ ↔ i < μ.colLen j
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
-/
theorem pos_of_mem_rowLens (μ : YoungDiagram) (x : ℕ) (hx : x ∈ μ.rowLens) : 0 < x := by
  rw [rowLens, List.mem_map] at hx
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


/-- The cells making up a `YoungDiagram` from a list of row lengths -/
/-
**YoungDiagram.cellsOfRowLens** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：List ℕ → Finset (ℕ × ℕ)
参数：ℕ × ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cells making up a `YoungDiagram` from a list of row lengths
-/
protected def cellsOfRowLens : List ℕ → Finset (ℕ × ℕ)
  | [] => ∅
  | w::ws =>
    ({0} : Finset ℕ) ×ˢ Finset.range w ∪
      (YoungDiagram.cellsOfRowLens ws).map
        (Embedding.prodMap ⟨_, Nat.succ_injective⟩ (Embedding.refl ℕ))
/-
**YoungDiagram.mem_cellsOfRowLens** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：∀ {w : List ℕ} {c : ℕ × ℕ}, c ∈ YoungDiagram.cellsOfRowLens w ↔ ∃ (h : c.1
 < w.length), c.2 < w[c.1]
参数：h : c.1 < w.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `YoungDiagram.cellsOfRowLens.eq_1`：YoungDiagram.cellsOfRowLens [] = ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Nat.succ_injective`：succ_injective : Injective Nat.succ
· 使用定理 `YoungDiagram.cellsOfRowLens.eq_2`：∀ (w : ℕ) (ws : List ℕ),   YoungDiagra
m.cellsOfRowLens (w :: ws) =     {0} ×ˢ Finset.range w ∪       Finset.map ({ toF
un := Nat.succ, inj' :…
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.singleton_product`：singleton_product {a : α} : ({a} : Finset α) ×
ˢ t = t.map ⟨Prod.mk a, Prod.mk_right_injective _⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Function.Embedding.refl_apply`：∀ (α : Sort u_1) (a : α), (Function.Embed
ding.refl α) a = a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
protected theorem mem_cellsOfRowLens {w : List ℕ} {c : ℕ × ℕ} :
    c ∈ YoungDiagram.cellsOfRowLens w ↔ ∃ h : c.fst < w.length, c.snd < w[c.fst] := by
  induction w generalizing c <;> rw [YoungDiagram.cellsOfRowLens]
  · simp
  · rcases c with ⟨⟨_, _⟩, _⟩ <;> simp_all

/-- Young diagram from a sorted list -/
/-
**YoungDiagram.ofRowLens** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：ofRowLens (w : List Nat) (hw : w.SortedGE) : YoungDiagram where cells
参数：w : List Nat；hw : w.SortedGE。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Young diagram from a sorted list
-/
def ofRowLens (w : List ℕ) (hw : w.SortedGE) : YoungDiagram where
  cells := YoungDiagram.cellsOfRowLens w
  isLowerSet := by
    rintro ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 ≤ i2, hj : j1 ≤ j2⟩ hcell
    rw [Finset.mem_coe, YoungDiagram.mem_cellsOfRowLens] at hcell ⊢
    obtain ⟨h1, h2⟩ := hcell
    refine ⟨hi.trans_lt h1, ?_⟩
    calc
      j1 ≤ j2 := hj
      _ < w[i2] := h2
      _ ≤ w[i1] := by
        obtain rfl | h := eq_or_lt_of_le hi
        · rfl
        · exact hw.getElem_ge_getElem_of_le h.le
/-
**YoungDiagram.mem_ofRowLens** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：mem_ofRowLens {w : List Nat} {hw : w.SortedGE} {c : Nat × Nat} : c in ofRo
wLens w hw ↔ exists h : c.fst < w.length, c.snd < w[c.fst]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `YoungDiagram.mem_cellsOfRowLens`：∀ {w : List ℕ} {c : ℕ × ℕ}, c ∈ YoungDi
agram.cellsOfRowLens w ↔ ∃ (h : c.1 < w.length), c.2 < w[c.1]
-/
theorem mem_ofRowLens {w : List ℕ} {hw : w.SortedGE} {c : ℕ × ℕ} :
    c ∈ ofRowLens w hw ↔ ∃ h : c.fst < w.length, c.snd < w[c.fst] :=
  YoungDiagram.mem_cellsOfRowLens

/-- The number of rows in `ofRowLens w hw` is the length of `w` -/
/-
**YoungDiagram.rowLens_length_ofRowLens** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`
。
形式化陈述：rowLens_length_ofRowLens {w : List Nat} {hw : w.SortedGE} (hpos : forall x
 in w, 0 < x) : (ofRowLens w hw).rowLens.length = w.length
参数：hpos : forall x in w, 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `YoungDiagram.exists_notMem_col`：∀ (μ : YoungDiagram) (j : ℕ), ∃ i, (i, j
) ∉ μ.cells
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `YoungDiagram.length_rowLens`：length_rowLens {μ : YoungDiagram} : μ.rowLe
ns.length = μ.colLen 0
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false`：¬False
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l

--- 原说明 ---
The number of rows in `ofRowLens w hw` is the length of `w`
-/
theorem rowLens_length_ofRowLens {w : List ℕ} {hw : w.SortedGE} (hpos : ∀ x ∈ w, 0 < x) :
    (ofRowLens w hw).rowLens.length = w.length := by
  simp only [length_rowLens, colLen, Nat.find_eq_iff, mem_cells, mem_ofRowLens,
    lt_self_iff_false, IsEmpty.exists_iff, Classical.not_not]
  exact ⟨not_false, fun n hn => ⟨hn, hpos _ (List.getElem_mem hn)⟩⟩

/-- The length of the `i`th row in `ofRowLens w hw` is the `i`th entry of `w` -/
/-
**YoungDiagram.rowLen_ofRowLens** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram`。
形式化陈述：rowLen_ofRowLens {w : List Nat} {hw : w.SortedGE} (i : Fin w.length) : (of
RowLens w hw).rowLen i = w[i]
参数：i : Fin w.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `YoungDiagram.exists_notMem_row`：∀ (μ : YoungDiagram) (i : ℕ), ∃ j, (i, j
) ∉ μ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.find.congr_simp`：∀ {p p_1 : ℕ → Prop} (e_p : p = p_1) {inst : Decida
blePred p} [inst_1 : DecidablePred p_1] (H : ∃ n, p n),   Nat.find H = Nat.find 
⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The length of the `i`th row in `ofRowLens w hw` is the `i`th entry of `w`
-/
theorem rowLen_ofRowLens {w : List ℕ} {hw : w.SortedGE} (i : Fin w.length) :
    (ofRowLens w hw).rowLen i = w[i] := by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens]

/-- The `leftInv` direction of the equivalence -/
/-
**YoungDiagram.ofRowLens_to_rowLens_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiag
ram`。
形式化陈述：ofRowLens_to_rowLens_eq_self {μ : YoungDiagram} : ofRowLens _ (rowLens_sor
ted μ) = μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `YoungDiagram.ext`：∀ {x y : YoungDiagram}, x.cells = y.cells → x = y
· 使用定理 `YoungDiagram.rowLens_sorted`：rowLens_sorted (μ : YoungDiagram) : μ.rowLe
ns.SortedGE
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `YoungDiagram.get_rowLens`：get_rowLens {μ : YoungDiagram} {i : Nat} {h : 
i < μ.rowLens.length} : μ.rowLens[i] = μ.rowLen i
· 使用定理 `YoungDiagram.length_rowLens`：length_rowLens {μ : YoungDiagram} : μ.rowLe
ns.length = μ.colLen 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n

--- 原说明 ---
The `leftInv` direction of the equivalence
-/
theorem ofRowLens_to_rowLens_eq_self {μ : YoungDiagram} : ofRowLens _ (rowLens_sorted μ) = μ := by
  ext ⟨i, j⟩
  simp only [mem_cells, mem_ofRowLens, length_rowLens, get_rowLens]
  simpa [← mem_iff_lt_colLen, mem_iff_lt_rowLen] using j.zero_le.trans_lt

/-- The `rightInv` direction of the equivalence -/
/-
**YoungDiagram.rowLens_ofRowLens_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `YoungDiagram
`。
形式化陈述：rowLens_ofRowLens_eq_self {w : List Nat} {hw : w.SortedGE} (hpos : forall 
x in w, 0 < x) : (ofRowLens w hw).rowLens = w
参数：hpos : forall x in w, 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `YoungDiagram.rowLens_length_ofRowLens`：rowLens_length_ofRowLens {w : Lis
t Nat} {hw : w.SortedGE} (hpos : forall x in w, 0 < x) : (ofRowLens w hw).rowLen
s.length = w.length
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `YoungDiagram.get_rowLens`：get_rowLens {μ : YoungDiagram} {i : Nat} {h : 
i < μ.rowLens.length} : μ.rowLens[i] = μ.rowLen i
· 使用定理 `YoungDiagram.rowLen_ofRowLens`：rowLen_ofRowLens {w : List Nat} {hw : w.S
ortedGE} (i : Fin w.length) : (ofRowLens w hw).rowLen i = w[i]

--- 原说明 ---
The `rightInv` direction of the equivalence
-/
theorem rowLens_ofRowLens_eq_self {w : List ℕ} {hw : w.SortedGE} (hpos : ∀ x ∈ w, 0 < x) :
    (ofRowLens w hw).rowLens = w :=
  List.ext_get (rowLens_length_ofRowLens hpos) fun i h₁ h₂ =>
    (get_rowLens (h := h₁)).trans <| rowLen_ofRowLens ⟨i, h₂⟩

/-- Equivalence between Young diagrams and weakly decreasing lists of positive natural numbers.
A Young diagram `μ` is equivalent to a list of row lengths. -/
@[simps]
/-
**YoungDiagram.equivListRowLens** 是 Mathlib 中的一个定义，位于命名空间 `YoungDiagram`。
形式化陈述：equivListRowLens : YoungDiagram ≃ { w : List Nat // w.SortedGE ∧ forall x 
in w, 0 < x } where toFun μ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `YoungDiagram.ofRowLens_to_rowLens_eq_self`：ofRowLens_to_rowLens_eq_self 
{μ : YoungDiagram} : ofRowLens _ (rowLens_sorted μ) = μ

--- 原说明 ---
Equivalence between Young diagrams and weakly decreasing lists of positive natur
al numbers.
A Young diagram `μ` is equivalent to a list of row lengths.
-/
def equivListRowLens : YoungDiagram ≃ { w : List ℕ // w.SortedGE ∧ ∀ x ∈ w, 0 < x } where
  toFun μ := ⟨μ.rowLens, μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩
  invFun ww := ofRowLens ww.1 ww.2.1
  left_inv _ := ofRowLens_to_rowLens_eq_self
  right_inv := fun ⟨_, hw⟩ => Subtype.mk_eq_mk.mpr (rowLens_ofRowLens_eq_self hw.2)

end EquivListRowLens

end YoungDiagram

