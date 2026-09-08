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


/-- A semistandard Young tableau is a filling of the cells of a Young diagram by natural
numbers, such that the entries in each row are weakly increasing (left to right), and the entries
in each column are strictly increasing (top to bottom).

Here, a semistandard Young tableau is represented as an unrestricted function `ℕ → ℕ → ℕ` that, for
reasons of extensionality, is required to vanish outside `μ`. -/
/-
**SemistandardYoungTableau** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：YoungDiagram → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semistandard Young tableau is a filling of the cells of a Young diagram by nat
ural
numbers, such that the entries in each row are weakly increasing (left to right)
, and the entries
in each column are strictly increasing (top to bottom).

Here, a semistandard Young tableau is represented as an unrestricted function `ℕ
 → ℕ → ℕ` that, for
reasons of extensionality, is required to vanish outside `μ`.
-/
structure SemistandardYoungTableau (μ : YoungDiagram) where
  /-- `entry i j` is value of the `(i, j)` entry of the SSYT `μ`. -/
  entry : ℕ → ℕ → ℕ
  /-- The entries in each row are weakly increasing (left to right). -/
  row_weak' : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → entry i j1 ≤ entry i j2
  /-- The entries in each column are strictly increasing (top to bottom). -/
  col_strict' : ∀ {i1 i2 j : ℕ}, i1 < i2 → (i2, j) ∈ μ → entry i1 j < entry i2 j
  /-- `entry` is required to be zero for all pairs `(i, j) ∉ μ`. -/
  zeros' : ∀ {i j}, (i, j) ∉ μ → entry i j = 0

namespace SemistandardYoungTableau

/-
**SemistandardYoungTableau.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `SemistandardYo
ungTableau`。
形式化陈述：instFunLike {μ : YoungDiagram} : FunLike (SemistandardYoungTableau μ) Nat 
(Nat -> Nat) where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike {μ : YoungDiagram} : FunLike (SemistandardYoungTableau μ) ℕ (ℕ → ℕ) where
  coe := SemistandardYoungTableau.entry
  coe_injective T T' h := by
    cases T
    cases T'
    congr

@[simp]
/-
**SemistandardYoungTableau.to_fun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Semistandard
YoungTableau`。
形式化陈述：to_fun_eq_coe {μ : YoungDiagram} {T : SemistandardYoungTableau μ} : T.entr
y = (T : Nat -> Nat -> Nat)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to_fun_eq_coe {μ : YoungDiagram} {T : SemistandardYoungTableau μ} :
    T.entry = (T : ℕ → ℕ → ℕ) :=
  rfl

@[ext]
/-
**SemistandardYoungTableau.ext** 是 Mathlib 中的一个定理，位于命名空间 `SemistandardYoungTable
au`。
形式化陈述：ext {μ : YoungDiagram} {T T' : SemistandardYoungTableau μ} (h : forall i j
, T i j = T' i j) : T = T'
参数：h : forall i j, T i j = T' i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {μ : YoungDiagram} {T T' : SemistandardYoungTableau μ} (h : ∀ i j, T i j = T' i j) :
    T = T' :=
  DFunLike.ext T T' fun _ ↦ by
    funext
    apply h

/-- Copy of an `SemistandardYoungTableau μ` with a new `entry` equal to the old one. Useful to fix
definitional equalities. -/
/-
**SemistandardYoungTableau.copy** 是 Mathlib 中的一个定义，位于命名空间 `SemistandardYoungTabl
eau`。
形式化陈述：{μ : YoungDiagram} → (T : SemistandardYoungTableau μ) → (entry' : ℕ → ℕ → 
ℕ) → entry' = ⇑T → SemistandardYoungTableau μ
参数：T : SemistandardYoungTableau μ；entry' : ℕ → ℕ → ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of an `SemistandardYoungTableau μ` with a new `entry` equal to the old one.
 Useful to fix
definitional equalities.
-/
protected def copy {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : SemistandardYoungTableau μ where
  entry := entry'
  row_weak' := h.symm ▸ T.row_weak'
  col_strict' := h.symm ▸ T.col_strict'
  zeros' := h.symm ▸ T.zeros'

@[simp]
/-
**SemistandardYoungTableau.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `SemistandardYoung
Tableau`。
形式化陈述：coe_copy {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : Nat
 -> Nat -> Nat) (h : entry' = T) : ⇑(T.copy entry' h) = entry'
参数：T : SemistandardYoungTableau μ；entry' : Nat -> Nat -> Nat；h : entry' = T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : ⇑(T.copy entry' h) = entry' :=
  rfl
/-
**SemistandardYoungTableau.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `SemistandardYoungT
ableau`。
形式化陈述：copy_eq {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : Nat 
-> Nat -> Nat) (h : entry' = T) : T.copy entry' h = T
参数：T : SemistandardYoungTableau μ；entry' : Nat -> Nat -> Nat；h : entry' = T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq {μ : YoungDiagram} (T : SemistandardYoungTableau μ) (entry' : ℕ → ℕ → ℕ)
    (h : entry' = T) : T.copy entry' h = T :=
  DFunLike.ext' h
/-
**SemistandardYoungTableau.row_weak** 是 Mathlib 中的一个定理，位于命名空间 `SemistandardYoung
Tableau`。
形式化陈述：row_weak {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : Na
t} (hj : j1 < j2) (hcell : (i, j2) in μ) : T i j1 <= T i j2
参数：T : SemistandardYoungTableau μ；hj : j1 < j2；hcell : (i, j2) in μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemistandardYoungTableau.row_weak'`：∀ {μ : YoungDiagram} (self : Semista
ndardYoungTableau μ) {i j1 j2 : ℕ},   j1 < j2 → (i, j2) ∈ μ → self.entry i j1 ≤ 
self.entry i j2
-/
theorem row_weak {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : ℕ} (hj : j1 < j2)
    (hcell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 :=
  T.row_weak' hj hcell
/-
**SemistandardYoungTableau.col_strict** 是 Mathlib 中的一个定理，位于命名空间 `SemistandardYou
ngTableau`。
形式化陈述：col_strict {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : 
Nat} (hi : i1 < i2) (hcell : (i2, j) in μ) : T i1 j < T i2 j
参数：T : SemistandardYoungTableau μ；hi : i1 < i2；hcell : (i2, j) in μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemistandardYoungTableau.col_strict'`：∀ {μ : YoungDiagram} (self : Semis
tandardYoungTableau μ) {i1 i2 j : ℕ},   i1 < i2 → (i2, j) ∈ μ → self.entry i1 j 
< self.entry i2 j
-/
theorem col_strict {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : ℕ} (hi : i1 < i2)
    (hcell : (i2, j) ∈ μ) : T i1 j < T i2 j :=
  T.col_strict' hi hcell
/-
**SemistandardYoungTableau.zeros** 是 Mathlib 中的一个定理，位于命名空间 `SemistandardYoungTab
leau`。
形式化陈述：zeros {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j : Nat} (not
_cell : (i, j) ∉ μ) : T i j = 0
参数：T : SemistandardYoungTableau μ；not_cell : (i, j) ∉ μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemistandardYoungTableau.zeros'`：∀ {μ : YoungDiagram} (self : Semistanda
rdYoungTableau μ) {i j : ℕ}, (i, j) ∉ μ → self.entry i j = 0
-/
theorem zeros {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j : ℕ}
    (not_cell : (i, j) ∉ μ) : T i j = 0 :=
  T.zeros' not_cell
/-
**SemistandardYoungTableau.row_weak_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Semistandar
dYoungTableau`。
形式化陈述：row_weak_of_le {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j
2 : Nat} (hj : j1 <= j2) (cell : (i, j2) in μ) : T i j1 <= T i j2
参数：T : SemistandardYoungTableau μ；hj : j1 <= j2；cell : (i, j2) in μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `SemistandardYoungTableau.row_weak`：row_weak {μ : YoungDiagram} (T : Semi
standardYoungTableau μ) {i j1 j2 : Nat} (hj : j1 < j2) (hcell : (i, j2) in μ) : 
T i j1 <= T i j2
-/
theorem row_weak_of_le {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i j1 j2 : ℕ}
    (hj : j1 ≤ j2) (cell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 := by
  rcases eq_or_lt_of_le hj with h | h
  · rw [h]
  · exact T.row_weak h cell
/-
**SemistandardYoungTableau.col_weak** 是 Mathlib 中的一个定理，位于命名空间 `SemistandardYoung
Tableau`。
形式化陈述：col_weak {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : Na
t} (hi : i1 <= i2) (cell : (i2, j) in μ) : T i1 j <= T i2 j
参数：T : SemistandardYoungTableau μ；hi : i1 <= i2；cell : (i2, j) in μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `SemistandardYoungTableau.col_strict`：col_strict {μ : YoungDiagram} (T : 
SemistandardYoungTableau μ) {i1 i2 j : Nat} (hi : i1 < i2) (hcell : (i2, j) in μ
) : T i1 j < T i2 j
-/
theorem col_weak {μ : YoungDiagram} (T : SemistandardYoungTableau μ) {i1 i2 j : ℕ} (hi : i1 ≤ i2)
    (cell : (i2, j) ∈ μ) : T i1 j ≤ T i2 j := by
  rcases eq_or_lt_of_le hi with h | h
  · rw [h]
  · exact le_of_lt (T.col_strict h cell)

/-- The "highest weight" SSYT of a given shape has all i's in row i, for each i. -/
/-
**SemistandardYoungTableau.highestWeight** 是 Mathlib 中的一个定义，位于命名空间 `Semistandard
YoungTableau`。
形式化陈述：highestWeight (μ : YoungDiagram) : SemistandardYoungTableau μ where entry 
i j
参数：μ : YoungDiagram。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "highest weight" SSYT of a given shape has all i's in row i, for each i.
-/
def highestWeight (μ : YoungDiagram) : SemistandardYoungTableau μ where
  entry i j := if (i, j) ∈ μ then i else 0
  row_weak' hj hcell := by
    rw [if_pos hcell, if_pos (μ.up_left_mem (by rfl) (le_of_lt hj) hcell)]
  col_strict' hi hcell := by
    rwa [if_pos hcell, if_pos (μ.up_left_mem (le_of_lt hi) (by rfl) hcell)]
  zeros' not_cell := if_neg not_cell

@[simp]
/-
**SemistandardYoungTableau.highestWeight_apply** 是 Mathlib 中的一个定理，位于命名空间 `Semist
andardYoungTableau`。
形式化陈述：highestWeight_apply {μ : YoungDiagram} {i j : Nat} : highestWeight μ i j =
 if (i, j) in μ then i else 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem highestWeight_apply {μ : YoungDiagram} {i j : ℕ} :
    highestWeight μ i j = if (i, j) ∈ μ then i else 0 :=
  rfl
/-
**SemistandardYoungTableau.** 是 Mathlib 中的一个实例，位于命名空间 `SemistandardYoungTableau`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {μ : YoungDiagram} : Inhabited (SemistandardYoungTableau μ) :=
  ⟨highestWeight μ⟩

end SemistandardYoungTableau

