/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.EpiMono
/-! # Normal forms for morphisms in `SimplexCategoryGenRel`.

In this file, we establish that `P_δ` and `P_σ` morphisms in `SimplexCategoryGenRel`
each admits a normal form.

In both cases, the normal forms are encoded as an integer `m`, and a strictly increasing
list of integers `[i₀,…,iₙ]` such that `iₖ ≤ m + k` for all `k`. We define a predicate
`isAdmissible m : List ℕ → Prop` encoding this property. And provide some lemmas to help
work with such lists.

Normal forms for `P_σ` morphisms are encoded by `m`-admissible lists, in which case the list
`[i₀,…,iₙ]` represents the morphism `σ iₙ ≫ ⋯ ≫ σ i₀ : .mk (m + n) ⟶ .mk n`.

Normal forms for `P_δ` morphisms are encoded by `(m + 1)`-admissible lists, in which case the list
`[i₀,…,iₙ]` represents the morphism `δ i₀ ≫ ⋯ ≫ δ iₙ : .mk n ⟶ .mk (m + n)`.

The results in this file are to be treated as implementation-only, and they only serve as stepping
stones towards proving that the canonical functor
`toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory` is an equivalence.

## References:
* [Kerodon Tag 04FQ](https://kerodon.net/tag/04FQ)
* [Kerodon Tag 04FT](https://kerodon.net/tag/04FT)

## TODOs:
- Show that every `P_δ` admits a unique normal form.
-/

@[expose] public section

namespace SimplexCategoryGenRel

open CategoryTheory

section AdmissibleLists
-- Impl. note: We are not bundling admissible lists as a subtype of `List ℕ` so that it remains
-- easier to perform inductive constructions and proofs on such lists, and we instead bundle
-- propositions asserting that various List constructions produce admissible lists.

variable (m : ℕ)
/-- A list of natural numbers `[i₀, ⋯, iₙ]` is said to be `m`-admissible (for `m : ℕ`) if
`i₀ < ⋯ < iₙ` and `iₖ ≤ m + k` for all `k`. This would suggest the definition
`L.IsChain (· < ·) ∧ ∀ k, (h : k < L.length) → L[k] ≤ m + k`.
However, we instead define `IsAdmissible` inductively and show, in
`isAdmissible_iff_isChain_and_le`, that this is equivalent to the non-inductive definition.
-/
@[mk_iff]
/-
**SimplexCategoryGenRel.IsAdmissible** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimplexCategor
yGenRel`。
形式化陈述：ℕ → List ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A list of natural numbers `[i₀, ⋯, iₙ]` is said to be `m`-admissible (for `m : ℕ
`) if
`i₀ < ⋯ < iₙ` and `iₖ ≤ m + k` for all `k`. This would suggest the definition
`L.IsChain (· < ·) ∧ ∀ k, (h : k < L.length) → L[k] ≤ m + k`.
However, we instead define `IsAdmissible` inductively and show, in
`isAdmissible_iff_isChain_and_le`, that this is equivalent to the non-inductive 
definition.
-/
inductive IsAdmissible : (m : ℕ) → (L : List ℕ) → Prop
  | nil (m : ℕ) : IsAdmissible m []
  | singleton {m a} (ha : a ≤ m) : IsAdmissible m [a]
  | cons_cons {m a b L'} (hab : a < b) (hbL : IsAdmissible (m + 1) (b :: L'))
      (ha : a ≤ m) : IsAdmissible m (a :: b :: L')

attribute [simp, grind ←] IsAdmissible.nil
attribute [grind →] IsAdmissible.cons_cons

section IsAdmissible

variable {m a b : ℕ} {L : List ℕ}

@[simp, grind =]
/-
**SimplexCategoryGenRel.isAdmissible_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Si
mplexCategoryGenRel`。
形式化陈述：isAdmissible_singleton_iff : IsAdmissible m [a] ↔ a <= m
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isAdmissible_singleton_iff : IsAdmissible m [a] ↔ a ≤ m :=
  ⟨fun | .singleton h => h, .singleton⟩

@[simp, grind =]
/-
**SimplexCategoryGenRel.isAdmissible_cons_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `Si
mplexCategoryGenRel`。
形式化陈述：isAdmissible_cons_cons_iff : IsAdmissible m (a :: b :: L) ↔ a < b ∧ IsAdmi
ssible (m + 1) (b :: L) ∧ a <= m
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isAdmissible_cons_cons_iff : IsAdmissible m (a :: b :: L) ↔
    a < b ∧ IsAdmissible (m + 1) (b :: L) ∧ a ≤ m :=
  ⟨fun | .cons_cons hab hbL ha => ⟨hab, hbL, ha⟩, by grind⟩
/-
**SimplexCategoryGenRel.isAdmissible_cons_iff** 是 Mathlib 中的一个定理，位于命名空间 `Simplex
CategoryGenRel`。
形式化陈述：isAdmissible_cons_iff : IsAdmissible m (a :: L) ↔ a <= m ∧ ((_ : 0 < L.len
gth) -> a < L[0]) ∧ IsAdmissible (m + 1) L
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isAdmissible_cons_iff : IsAdmissible m (a :: L) ↔
    a ≤ m ∧ ((_ : 0 < L.length) → a < L[0]) ∧ IsAdmissible (m + 1) L := by
  cases L <;> grind
/-
**SimplexCategoryGenRel.isAdmissible_iff_isChain_and_le** 是 Mathlib 中的一个定理，位于命名空
间 `SimplexCategoryGenRel`。
形式化陈述：isAdmissible_iff_isChain_and_le : IsAdmissible m L ↔ L.IsChain (· < ·) ∧ f
orall k, (h : k < L.length) -> L[k] <= m + k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `List.getElem_singleton`：∀ {α : Type u_1} {a : α} {i : ℕ} (h : i < 1), [a
][i] = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem isAdmissible_iff_isChain_and_le : IsAdmissible m L ↔
    L.IsChain (· < ·) ∧ ∀ k, (h : k < L.length) → L[k] ≤ m + k := by
  induction L using List.twoStepInduction generalizing m with
  | nil => grind
  | singleton _ => simp
  | cons_cons _ _ _ _ IH =>
    simp_rw [isAdmissible_cons_cons_iff, IH, List.length_cons, and_assoc,
      List.isChain_cons_cons, and_assoc, and_congr_right_iff, and_comm]
    exact fun _ _ => ⟨fun h => by grind,
      fun h => ⟨h 0 (by grind), fun k _ => (h (k + 1) (by grind)).trans (by grind)⟩⟩
/-
**SimplexCategoryGenRel.isAdmissible_iff_pairwise_and_le** 是 Mathlib 中的一个定理，位于命名
空间 `SimplexCategoryGenRel`。
形式化陈述：isAdmissible_iff_pairwise_and_le : IsAdmissible m L ↔ L.Pairwise (· < ·) ∧
 forall k, (h : k < L.length) -> L[k] <= m + k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimplexCategoryGenRel.isAdmissible_iff_isChain_and_le`：isAdmissible_iff_
isChain_and_le : IsAdmissible m L ↔ L.IsChain (· < ·) ∧ forall k, (h : k < L.len
gth) -> L[k] <= m + k
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isAdmissible_iff_pairwise_and_le : IsAdmissible m L ↔
    L.Pairwise (· < ·) ∧ ∀ k, (h : k < L.length) → L[k] ≤ m + k := by
  rw [isAdmissible_iff_isChain_and_le, List.isChain_iff_pairwise]
/-
**SimplexCategoryGenRel.isAdmissible_of_isChain_of_forall_getElem_le** 是 Mathlib
 中的一个定理，位于命名空间 `SimplexCategoryGenRel`。
形式化陈述：isAdmissible_of_isChain_of_forall_getElem_le {m L} (hL : L.IsChain (· < ·)
) (hL₂ : forall k, (h : k < L.length) -> L[k] <= m + k) : IsAdmissible m L
参数：hL : L.IsChain (· < ·)；hL₂ : forall k, (h : k < L.length) -> L[k] <= m + k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimplexCategoryGenRel.isAdmissible_iff_isChain_and_le`：isAdmissible_iff_
isChain_and_le : IsAdmissible m L ↔ L.IsChain (· < ·) ∧ forall k, (h : k < L.len
gth) -> L[k] <= m + k
-/
theorem isAdmissible_of_isChain_of_forall_getElem_le {m L} (hL : L.IsChain (· < ·))
    (hL₂ : ∀ k, (h : k < L.length) → L[k] ≤ m + k) : IsAdmissible m L :=
  isAdmissible_iff_isChain_and_le.mpr ⟨hL, hL₂⟩

namespace IsAdmissible

/-
**SimplexCategoryGenRel.IsAdmissible.isChain** 是 Mathlib 中的一个定理，位于命名空间 `SimplexC
ategoryGenRel.IsAdmissible`。
形式化陈述：∀ {m : ℕ} {L : List ℕ}, SimplexCategoryGenRel.IsAdmissible m L → List.IsCh
ain (fun x1 x2 => x1 < x2) L
参数：fun x1 x2 => x1 < x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimplexCategoryGenRel.isAdmissible_iff_isChain_and_le`：isAdmissible_iff_
isChain_and_le : IsAdmissible m L ↔ L.IsChain (· < ·) ∧ forall k, (h : k < L.len
gth) -> L[k] <= m + k
-/
@[grind →] theorem isChain {m L} (hL : IsAdmissible m L) :
    L.IsChain (· < ·) := (isAdmissible_iff_isChain_and_le.mp hL).1
/-
**SimplexCategoryGenRel.IsAdmissible.le** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCatego
ryGenRel.IsAdmissible`。
形式化陈述：∀ {m : ℕ} {L : List ℕ}, SimplexCategoryGenRel.IsAdmissible m L → ∀ (k : ℕ)
 (h : k < L.length), L[k] ≤ m + k
参数：k : ℕ；h : k < L.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimplexCategoryGenRel.isAdmissible_iff_isChain_and_le`：isAdmissible_iff_
isChain_and_le : IsAdmissible m L ↔ L.IsChain (· < ·) ∧ forall k, (h : k < L.len
gth) -> L[k] <= m + k
-/
@[grind →] theorem le {m} {L : List ℕ} (hL : IsAdmissible m L) : ∀ k (h : k < L.length),
    L[k] ≤ m + k := (isAdmissible_iff_isChain_and_le.mp hL).2

/-- The tail of an `m`-admissible list is (m+1)-admissible. -/
/-
**SimplexCategoryGenRel.IsAdmissible.of_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimplexC
ategoryGenRel.IsAdmissible`。
形式化陈述：∀ {m a : ℕ} {L : List ℕ}, SimplexCategoryGenRel.IsAdmissible m (a :: L) → 
SimplexCategoryGenRel.IsAdmissible (m + 1) L
参数：a :: L；m + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The tail of an `m`-admissible list is (m+1)-admissible.
-/
@[grind →] lemma of_cons {m a L} (h : IsAdmissible m (a :: L)) :
    IsAdmissible (m + 1) L := by cases L <;> grind
/-
**SimplexCategoryGenRel.IsAdmissible.cons** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCate
goryGenRel.IsAdmissible`。
形式化陈述：cons {m a L} (hL : IsAdmissible (m + 1) L) (ha : a <= m) (ha' : (_ : 0 < L
.length) -> a < L[0]) : IsAdmissible m (a :: L)
参数：hL : IsAdmissible (m + 1) L；ha : a <= m；ha' : (_ : 0 < L.length) -> a < L[0]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma cons {m a L} (hL : IsAdmissible (m + 1) L) (ha : a ≤ m)
    (ha' : (_ : 0 < L.length) → a < L[0]) : IsAdmissible m (a :: L) := by cases L <;> grind
/-
**SimplexCategoryGenRel.IsAdmissible.sortedLT** 是 Mathlib 中的一个定理，位于命名空间 `Simplex
CategoryGenRel.IsAdmissible`。
形式化陈述：sortedLT {m L} (hL : IsAdmissible m L) : L.SortedLT
参数：hL : IsAdmissible m L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.IsChain.sortedLT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α]
, List.IsChain (fun x1 x2 => x1 < x2) l → l.SortedLT
· 使用定理 `SimplexCategoryGenRel.IsAdmissible.isChain`：∀ {m : ℕ} {L : List ℕ}, Simp
lexCategoryGenRel.IsAdmissible m L → List.IsChain (fun x1 x2 => x1 < x2) L
-/
theorem sortedLT {m L} (hL : IsAdmissible m L) : L.SortedLT :=
  hL.isChain.sortedLT

/-- If `(a :: l)` is `m`-admissible then a is less than all elements of `l` -/
@[grind →]
/-
**SimplexCategoryGenRel.IsAdmissible.head_lt** 是 Mathlib 中的一个引理，位于命名空间 `SimplexC
ategoryGenRel.IsAdmissible`。
形式化陈述：head_lt {m a L} (hL : IsAdmissible m (a :: L)) : forall a' in L, a < a'
参数：hL : IsAdmissible m (a :: L)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.rel_of_pairwise_cons`：∀ {α : Type u_1} {a : α} {l : List α} {R : α 
→ α → Prop}, List.Pairwise R (a :: l) → ∀ {a' : α}, a' ∈ l → R a a'
· 使用定理 `List.SortedLT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLT → List.Pairwise (fun x1 x2 => x1 < x2) l
· 使用定理 `SimplexCategoryGenRel.IsAdmissible.sortedLT`：sortedLT {m L} (hL : IsAdmi
ssible m L) : L.SortedLT

--- 原说明 ---
If `(a :: l)` is `m`-admissible then a is less than all elements of `l`
-/
lemma head_lt {m a L} (hL : IsAdmissible m (a :: L)) :
    ∀ a' ∈ L, a < a' := fun _ => L.rel_of_pairwise_cons hL.sortedLT.pairwise
/-
**SimplexCategoryGenRel.IsAdmissible.getElem_lt** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
exCategoryGenRel.IsAdmissible`。
形式化陈述：∀ {m : ℕ} {L : List ℕ}, SimplexCategoryGenRel.IsAdmissible m L → ∀ {k : ℕ}
 {hk : k < L.length}, L[k] < m + L.length
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_imp_lt_of_le_of_le`：lt_imp_lt_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a < b -> c < d
· 使用定理 `SimplexCategoryGenRel.IsAdmissible.le`：∀ {m : ℕ} {L : List ℕ}, SimplexCa
tegoryGenRel.IsAdmissible m L → ∀ (k : ℕ) (h : k < L.length), L[k] ≤ m + k
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
@[grind →] lemma getElem_lt {m L} (hL : IsAdmissible m L)
    {k : ℕ} {hk : k < L.length} : L[k] < m + L.length := by
  grw [hL.le, hk]

/-- An element of an `m`-admissible list, as an element of the appropriate `Fin` -/
@[simps]
/-
**SimplexCategoryGenRel.IsAdmissible.getElemAsFin** 是 Mathlib 中的一个定义，位于命名空间 `Sim
plexCategoryGenRel.IsAdmissible`。
形式化陈述：getElemAsFin {m L} (hl : IsAdmissible m L) (k : Nat) (hK : k < L.length) :
 Fin (m + k + 1)
参数：hl : IsAdmissible m L；k : Nat；hK : k < L.length。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of an `m`-admissible list, as an element of the appropriate `Fin`
-/
def getElemAsFin {m L} (hl : IsAdmissible m L) (k : ℕ)
    (hK : k < L.length) : Fin (m + k + 1) :=
  Fin.mk L[k] <| Nat.le_iff_lt_add_one.mp (by grind)

/-- The head of an `m`-admissible list. -/
@[simps!]
/-
**SimplexCategoryGenRel.IsAdmissible.head** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCate
goryGenRel.IsAdmissible`。
形式化陈述：head {m a L} (hl : IsAdmissible m (a :: L)) : Fin (m + 1)
参数：hl : IsAdmissible m (a :: L)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The head of an `m`-admissible list.
-/
def head {m a L} (hl : IsAdmissible m (a :: L)) : Fin (m + 1) :=
  hl.getElemAsFin 0 (by grind)
/-
**SimplexCategoryGenRel.IsAdmissible.mono** 是 Mathlib 中的一个定理，位于命名空间 `SimplexCate
goryGenRel.IsAdmissible`。
形式化陈述：mono {n} (hmn : m <= n) (hL : IsAdmissible m L) : IsAdmissible n L
参数：hmn : m <= n；hL : IsAdmissible m L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategoryGenRel.isAdmissible_of_isChain_of_forall_getElem_le`：isAd
missible_of_isChain_of_forall_getElem_le {m L} (hL : L.IsChain (· < ·)) (hL₂ : f
orall k, (h : k < L.length) -> L[k] <= m + k) : IsAdmiss…
-/
theorem mono {n} (hmn : m ≤ n) (hL : IsAdmissible m L) : IsAdmissible n L :=
  isAdmissible_of_isChain_of_forall_getElem_le (by grind) (by grind)

end IsAdmissible

end IsAdmissible

/-- The construction `simplicialInsert` describes inserting an element in a list of integer and
moving it to its "right place" according to the simplicial relations. Somewhat miraculously,
the algorithm is the same for the first or the fifth simplicial relations, making it "valid"
when we treat the list as a normal form for a morphism satisfying `P_δ`, or for a morphism
satisfying `P_σ`!

This is similar in nature to `List.orderedInsert`, but note that we increment one of the element
every time we perform an exchange, making it a different construction. -/
@[local grind]
/-
**SimplexCategoryGenRel.simplicialInsert** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCateg
oryGenRel`。
形式化陈述：ℕ → List ℕ → List ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The construction `simplicialInsert` describes inserting an element in a list of 
integer and
moving it to its "right place" according to the simplicial relations. Somewhat m
iraculously,
the algorithm is the same for the first or the fifth simplicial relations, makin
g it "valid"
when we treat the list as a normal form for a morphism satisfying `P_δ`, or for 
a morphism
satisfying `P_σ`!

This is similar in nature to `List.orderedInsert`, but note that we increment on
e of the element
every time we perform an exchange, making it a different construction.
-/
def simplicialInsert (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else b :: simplicialInsert (a + 1) l

/-- `simplicialInsert` just adds one to the length. -/
/-
**SimplexCategoryGenRel.simplicialInsert_length** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
exCategoryGenRel`。
形式化陈述：simplicialInsert_length (a : Nat) (L : List Nat) : (simplicialInsert a L).
length = L.length + 1
参数：a : Nat；L : List Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`simplicialInsert` just adds one to the length.
-/
lemma simplicialInsert_length (a : ℕ) (L : List ℕ) :
    (simplicialInsert a L).length = L.length + 1 := by
  induction L generalizing a <;> grind

/-- `simplicialInsert` preserves admissibility -/
/-
**SimplexCategoryGenRel.simplicialInsert_isAdmissible** 是 Mathlib 中的一个定理，位于命名空间 
`SimplexCategoryGenRel`。
形式化陈述：simplicialInsert_isAdmissible (L : List Nat) (hL : IsAdmissible (m + 1) L)
 (j : Nat) (hj : j <= m) : IsAdmissible m simplicialInsert j L
参数：L : List Nat；hL : IsAdmissible (m + 1) L；j : Nat；hj : j <= m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`simplicialInsert` preserves admissibility
-/
theorem simplicialInsert_isAdmissible (L : List ℕ) (hL : IsAdmissible (m + 1) L) (j : ℕ)
    (hj : j ≤ m) :
    IsAdmissible m <| simplicialInsert j L := by
  induction L generalizing j m with
  | nil => exact IsAdmissible.singleton hj
  | cons a L h_rec => cases L <;> grind

end AdmissibleLists

section NormalFormsP_σ

-- Impl note.: The definition is a bit awkward with the extra parameters, but this
-- is necessary in order to avoid some type theory hell when proving that `orderedInsert`
-- behaves as expected...

/-- Given a sequence `L = [ i 0, ..., i b ]`, `standardσ m L` i is the morphism
`σ (i b) ≫ … ≫ σ (i 0)`. The construction is provided for any list of natural numbers,
but it is intended to behave well only when the list is admissible. -/
/-
**SimplexCategoryGenRel.standard** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategoryGenRe
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a sequence `L = [ i 0, ..., i b ]`, `standardσ m L` i is the morphism
`σ (i b) ≫ … ≫ σ (i 0)`. The construction is provided for any list of natural nu
mbers,
but it is intended to behave well only when the list is admissible.
-/
def standardσ (L : List ℕ) {m₁ m₂ : ℕ} (h : m₂ + L.length = m₁) : mk m₁ ⟶ mk m₂ :=
  match L with
  | .nil => eqToHom (by grind)
  | .cons a t => standardσ t (by grind) ≫ σ (Fin.ofNat _ a)

@[simp]
/-
**SimplexCategoryGenRel.standard** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGenRe
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma standardσ_nil (m : ℕ) : standardσ .nil (by grind) = 𝟙 (mk m) := rfl

@[simp, reassoc]
/-
**SimplexCategoryGenRel.standard** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGenRe
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma standardσ_cons (L : List ℕ) (a : ℕ) {m₁ m₂ : ℕ} (h : m₂ + (a :: L).length = m₁) :
    standardσ (L.cons a) h = standardσ L (by grind) ≫ σ (Fin.ofNat _ a) := rfl

@[reassoc]
/-
**SimplexCategoryGenRel.standard** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGenRe
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma standardσ_comp_standardσ (L₁ L₂ : List ℕ) {m₁ m₂ m₃ : ℕ}
    (h : m₂ + L₁.length = m₁) (h' : m₃ + L₂.length = m₂) :
    standardσ L₁ h ≫ standardσ L₂ h' = standardσ (L₂ ++ L₁) (by grind) := by
  induction L₂ generalizing L₁ m₁ m₂ m₃ with
  | nil =>
    obtain rfl : m₃ = m₂ := by grind
    simp
  | cons a t H =>
    dsimp at h' ⊢
    obtain rfl : m₂ = (m₃ + t.length) + 1 := by grind
    simp [reassoc_of% (H L₁ (m₁ := m₁) (m₂ := m₃ + t.length + 1) (m₃ := m₃ + 1)
      (by grind) (by grind))]

variable (m : ℕ) (L : List ℕ)

/-- `simplicialEvalσ` is a lift to ℕ of `(toSimplexCategory.map (standardσ m L _ _)).toOrderHom`.
Rather than defining it as such, we define it inductively for less painful inductive reasoning,
(see `simplicialEvalσ_of_isAdmissible`).
It is expected to produce the correct result only if `L` is admissible, and values for
non-admissible lists should be considered junk values. Similarly, values for out-of-bounds inputs
are junk values. -/
@[local grind]
/-
**SimplexCategoryGenRel.simplicialEval** 是 Mathlib 中的一个定义，位于命名空间 `SimplexCategor
yGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`simplicialEvalσ` is a lift to ℕ of `(toSimplexCategory.map (standardσ m L _ _))
.toOrderHom`.
Rather than defining it as such, we define it inductively for less painful induc
tive reasoning,
(see `simplicialEvalσ_of_isAdmissible`).
It is expected to produce the correct result only if `L` is admissible, and valu
es for
non-admissible lists should be considered junk values. Similarly, values for out
-of-bounds inputs
are junk values.
-/
def simplicialEvalσ (L : List ℕ) : ℕ → ℕ :=
  fun j ↦ match L with
  | [] => j
  | a :: L => if a < simplicialEvalσ L j then simplicialEvalσ L j - 1 else simplicialEvalσ L j

@[grind ←]
/-
**SimplexCategoryGenRel.simplicialEval** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategor
yGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma simplicialEvalσ_of_le_mem (j : ℕ) (hj : ∀ k ∈ L, j ≤ k) : simplicialEvalσ L j = j := by
  induction L with | nil => grind | cons _ _ _ => simp only [List.forall_mem_cons] at hj; grind
/-
**SimplexCategoryGenRel.simplicialEval** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategor
yGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma simplicialEvalσ_monotone (L : List ℕ) : Monotone (simplicialEvalσ L) := by
  induction L <;> grind [Monotone]

variable {m}

set_option backward.isDefEq.respectTransparency false in
/- We prove that `simplicialEvalσ` is indeed a lift of
`(toSimplexCategory.map (standardσ m L _ _)).toOrderHom` when the list is admissible. -/
/-
**SimplexCategoryGenRel.simplicialEval** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategor
yGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We prove that `simplicialEvalσ` is indeed a lift of
`(toSimplexCategory.map (standardσ m L _ _)).toOrderHom` when the list is admiss
ible.
-/
lemma simplicialEvalσ_of_isAdmissible
    (m₁ m₂ : ℕ) (hL : IsAdmissible m₂ L) (hk : m₂ + L.length = m₁)
    (j : ℕ) (hj : j < m₁ + 1) :
    (toSimplexCategory.map <| standardσ L hk).toOrderHom ⟨j, hj⟩ =
    simplicialEvalσ L j := by
  induction L generalizing m₁ m₂ with
  | nil =>
    obtain rfl : m₁ = m₂ := by grind
    simp [simplicialEvalσ]
  | cons a L h_rec =>
    simp only [List.length_cons] at hk
    subst hk
    set a₀ := hL.head
    have aux (t : Fin (m₂ + 2)) :
        (a₀.predAbove t : ℕ) = if a < ↑t then (t : ℕ) - 1 else ↑t := by
      simp only [Fin.predAbove, a₀]
      split_ifs with h₁ h₂ h₂
      · rfl
      · simp only [Fin.lt_def, Fin.val_castSucc, IsAdmissible.head_val] at h₁; grind
      · simp only [Fin.lt_def, Fin.val_castSucc, IsAdmissible.head_val, not_lt] at h₁; grind
      · rfl
    have := h_rec _ _ hL.of_cons (by grind) hj
    have ha₀ : Fin.ofNat (m₂ + 1) a = a₀ := by ext; simpa [a₀] using hL.head.prop
    simpa only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, standardσ_cons, Functor.map_comp,
      toSimplexCategory_map_σ, SimplexCategory.σ, SimplexCategory.mkHom,
      SimplexCategory.comp_toOrderHom, SimplexCategory.Hom.toOrderHom_mk, OrderHom.comp_coe,
      Function.comp_apply, Fin.predAboveOrderHom_coe, simplicialEvalσ, ha₀, ← this] using aux _

/-- Performing a simplicial insertion in a list is the same as composition on the right by the
corresponding degeneracy operator. -/
/-
**SimplexCategoryGenRel.standard** 是 Mathlib 中的一个引理，位于命名空间 `SimplexCategoryGenRe
l`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Performing a simplicial insertion in a list is the same as composition on the ri
ght by the
corresponding degeneracy operator.
-/
lemma standardσ_simplicialInsert (hL : IsAdmissible (m + 1) L) (j : ℕ) (hj : j < m + 1)
    (m₁ : ℕ) (hm₁ : m + L.length + 1 = m₁) :
    standardσ (m₂ := m) (simplicialInsert j L) (m₁ := m₁)
      (by simpa only [simplicialInsert_length, add_assoc]) =
    standardσ (m₂ := m + 1) L (by grind) ≫ σ (Fin.ofNat _ j) := by
  induction L generalizing m j with
  | nil => simp [standardσ, simplicialInsert]
  | cons a L h_rec =>
    simp only [simplicialInsert]
    split_ifs
    · simp
    · have : ∀ (j k : ℕ) (h : j < (k + 1)), Fin.ofNat (k + 1) j = j := by simp -- helps grind below
      have : a < m + 2 := by grind -- helps grind below
      have : σ (Fin.ofNat (m + 2) a) ≫ σ (.ofNat _ j) = σ (.ofNat _ (j + 1)) ≫ σ (.ofNat _ a) := by
        convert! σ_comp_σ_nat (n := m) a j (by grind) (by grind) (by grind) <;> grind
      grind [standardσ_cons]

set_option backward.isDefEq.respectTransparency false in
attribute [local grind! .] simplicialInsert_length simplicialInsert_isAdmissible in
/-- Using `standardσ_simplicialInsert`, we can prove that every morphism satisfying `P_σ` is equal
to some `standardσ` for some admissible list of indices. -/
/-
**SimplexCategoryGenRel.exists_normal_form_P_** 是 Mathlib 中的一个定理，位于命名空间 `Simplex
CategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Using `standardσ_simplicialInsert`, we can prove that every morphism satisfying 
`P_σ` is equal
to some `standardσ` for some admissible list of indices.
-/
theorem exists_normal_form_P_σ {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_σ f) :
    ∃ L : List ℕ,
    ∃ m : ℕ, ∃ b : ℕ,
    ∃ h₁ : mk m = y, ∃ h₂ : x = mk (m + b), ∃ h : L.length = b,
    IsAdmissible m L ∧ f = standardσ L (by rw [h, h₁.symm, h₂]; rfl) := by
  induction hf with
  | id n =>
    use [], n.len, 0, rfl, rfl, rfl, IsAdmissible.nil _
    rfl
  | of f hf =>
    cases hf with | @σ m k =>
    use [k.val], m, 1, rfl, rfl, rfl, IsAdmissible.singleton k.is_le
    simp [standardσ]
  | @comp_of _ j x' g g' hg hg' h_rec =>
    cases hg' with | @σ m k =>
    obtain ⟨L₁, m₁, b₁, h₁', rfl, h', hL₁, e₁⟩ := h_rec
    obtain rfl : m₁ = m + 1 := congrArg (fun x ↦ x.len) h₁'
    use simplicialInsert k.val L₁, m, b₁ + 1, rfl, by grind, by grind, by grind
    subst_vars
    have := standardσ (m₁ := m + 1 + L₁.length) [] (by grind) ≫=
      (standardσ_simplicialInsert L₁ hL₁ k k.prop _ rfl).symm
    simp_all [Fin.ofNat_eq_cast, Fin.cast_val_eq_self, standardσ_comp_standardσ_assoc,
      standardσ_comp_standardσ]

section MemIsAdmissible

/-
**SimplexCategoryGenRel.IsAdmissible.simplicialEval** 是 Mathlib 中的一个引理，位于命名空间 `S
implexCategoryGenRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma IsAdmissible.simplicialEvalσ_succ_getElem (hL : IsAdmissible m L)
    {k : ℕ} {hk : k < L.length} : simplicialEvalσ L L[k] = simplicialEvalσ L (L[k] + 1) := by
  induction L generalizing m k <;> grind [→ IsAdmissible.singleton]

local grind_pattern IsAdmissible.simplicialEvalσ_succ_getElem =>
  IsAdmissible m L, simplicialEvalσ L L[k]
/-
**SimplexCategoryGenRel.mem_isAdmissible_of_lt_and_eval_eq_eval_add_one** 是 Math
lib 中的一个引理，位于命名空间 `SimplexCategoryGenRel`。
形式化陈述：mem_isAdmissible_of_lt_and_eval_eq_eval_add_one (hL : IsAdmissible m L) (j
 : Nat) (hj₁ : j < m + L.length) (hj₂ : simplicialEvalσ L j = simplicialEvalσ L 
(j + 1)) : j in L
参数：hL : IsAdmissible m L；j : Nat；hj₁ : j < m + L.length；hj₂ : simplicialEvalσ L 
j = simplicialEvalσ L (j + 1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimplexCategoryGenRel.simplicialEvalσ_monotone`：simplicialEvalσ_monotone
 (L : List Nat) : Monotone (simplicialEvalσ L)
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
-/
lemma mem_isAdmissible_of_lt_and_eval_eq_eval_add_one (hL : IsAdmissible m L)
    (j : ℕ) (hj₁ : j < m + L.length) (hj₂ : simplicialEvalσ L j = simplicialEvalσ L (j + 1)) :
    j ∈ L := by
  induction L generalizing m with
  | nil => grind
  | cons a L h_rec =>
    have := simplicialEvalσ_monotone L (a := a + 1)
    rcases lt_trichotomy j a with h | h | h <;> grind
/-
**SimplexCategoryGenRel.lt_and_eval_eq_eval_add_one_of_mem_isAdmissible** 是 Math
lib 中的一个引理，位于命名空间 `SimplexCategoryGenRel`。
形式化陈述：lt_and_eval_eq_eval_add_one_of_mem_isAdmissible (hL : IsAdmissible m L) (j
 : Nat) (hj : j in L) : j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ
 L (j + 1)
参数：hL : IsAdmissible m L；j : Nat；hj : j in L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lt_and_eval_eq_eval_add_one_of_mem_isAdmissible (hL : IsAdmissible m L) (j : ℕ) (hj : j ∈ L) :
    j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1) := by
  grind [List.mem_iff_getElem]

/-- We can characterize elements in an admissible list as exactly those for which
`simplicialEvalσ` takes the same value twice in a row. -/
/-
**SimplexCategoryGenRel.mem_isAdmissible_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimplexC
ategoryGenRel`。
形式化陈述：mem_isAdmissible_iff (hL : IsAdmissible m L) (j : Nat) : j in L ↔ j < m + 
L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1)
参数：hL : IsAdmissible m L；j : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can characterize elements in an admissible list as exactly those for which
`simplicialEvalσ` takes the same value twice in a row.
-/
lemma mem_isAdmissible_iff (hL : IsAdmissible m L) (j : ℕ) :
    j ∈ L ↔ j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1) := by
  grind [lt_and_eval_eq_eval_add_one_of_mem_isAdmissible,
    mem_isAdmissible_of_lt_and_eval_eq_eval_add_one]

end MemIsAdmissible

end NormalFormsP_σ

end SimplexCategoryGenRel

