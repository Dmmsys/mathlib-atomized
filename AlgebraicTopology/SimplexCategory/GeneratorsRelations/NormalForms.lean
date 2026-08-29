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

variable (m : Nat)
/-- A list of natural numbers `[i₀, ⋯, iₙ]` is said to be `m`-admissible (for `m : ℕ`) if
`i₀ < ⋯ < iₙ` and `iₖ ≤ m + k` for all `k`. This would suggest the definition
`L.IsChain (· < ·) ∧ ∀ k, (h : k < L.length) → L[k] ≤ m + k`.
However, we instead define `IsAdmissible` inductively and show, in
`isAdmissible_iff_isChain_and_le`, that this is equivalent to the non-inductive definition.
-/
@[mk_iff]
/--
Inductive type `IsAdmissible` / 归纳类型 `IsAdmissible`

English:
inductive IsAdmissible
  parameters: : (m : Nat) -> (L : List Nat) -> Prop
  constructors (3):
    - nil: (m : Nat) : IsAdmissible m []
    - singleton: {m a} (ha : a <= m) : IsAdmissible m [a]
    - cons_cons: {m a b L'} (hab : a < b) (hbL : IsAdmissible (m + 1) (b :: L')) (ha : a <= m) : IsAdmissible m (a :: b :: L')

中文:
归纳类型 IsAdmissible
  参数: : (m : 自然数) -> (L : List 自然数) -> 命题
  构造子 (3 个):
    - nil: (m : 自然数) : IsAdmissible m []
    - singleton: {m a} (ha : a <= m) : IsAdmissible m [a]
    - cons_cons: {m a b L'} (hab : a < b) (hbL : IsAdmissible (m + 1) (b :: L')) (ha : a <= m) : IsAdmissible m (a :: b :: L')
-/
inductive IsAdmissible : (m : Nat) -> (L : List Nat) -> Prop
  | nil (m : Nat) : IsAdmissible m []
  | singleton {m a} (ha : a <= m) : IsAdmissible m [a]
  | cons_cons {m a b L'} (hab : a < b) (hbL : IsAdmissible (m + 1) (b :: L'))
      (ha : a <= m) : IsAdmissible m (a :: b :: L')

attribute [simp, grind ←] IsAdmissible.nil
attribute [grind ->] IsAdmissible.cons_cons

section IsAdmissible

variable {m a b : Nat} {L : List Nat}

@[simp, grind =]
/--
theorem `isAdmissible_singleton_iff` / 定理 `isAdmissible_singleton_iff`

English:
theorem isAdmissible_singleton_iff
  statement: IsAdmissible m [a] ↔ a <= m
  proof: ⟨fun | .singleton h => h, .singleton⟩

@[simp, grind =]

中文:
定理 isAdmissible_singleton_iff
  结论: IsAdmissible m [a] ↔ a <= m
  证明: ⟨fun | .singleton h => h, .singleton⟩

@[simp, grind =]

Depends on / 依赖: singleton
-/
theorem isAdmissible_singleton_iff : IsAdmissible m [a] ↔ a <= m :=
  ⟨fun | .singleton h => h, .singleton⟩

@[simp, grind =]
/--
theorem `isAdmissible_cons_cons_iff` / 定理 `isAdmissible_cons_cons_iff`

English:
theorem isAdmissible_cons_cons_iff
  statement: IsAdmissible m (a :: b :: L) ↔
  proof: ⟨fun | .cons_cons hab hbL ha => ⟨hab, hbL, ha⟩, by grind⟩

中文:
定理 isAdmissible_cons_cons_iff
  结论: IsAdmissible m (a :: b :: L) ↔
  证明: ⟨fun | .cons_cons hab hbL ha => ⟨hab, hbL, ha⟩, by grind⟩

Depends on / 依赖: cons_cons
-/
theorem isAdmissible_cons_cons_iff : IsAdmissible m (a :: b :: L) ↔
    a < b ∧ IsAdmissible (m + 1) (b :: L) ∧ a <= m :=
  ⟨fun | .cons_cons hab hbL ha => ⟨hab, hbL, ha⟩, by grind⟩

/--
theorem `isAdmissible_cons_iff` / 定理 `isAdmissible_cons_iff`

English:
theorem isAdmissible_cons_iff
  statement: IsAdmissible m (a :: L) ↔
  proof: by
  cases L <;> grind

中文:
定理 isAdmissible_cons_iff
  结论: IsAdmissible m (a :: L) ↔
  证明: by
  cases L <;> grind
-/
theorem isAdmissible_cons_iff : IsAdmissible m (a :: L) ↔
    a <= m ∧ ((_ : 0 < L.length) -> a < L[0]) ∧ IsAdmissible (m + 1) L := by
  cases L <;> grind

/--
theorem `isAdmissible_iff_isChain_and_le` / 定理 `isAdmissible_iff_isChain_and_le`

English:
theorem isAdmissible_iff_isChain_and_le
  statement: IsAdmissible m L ↔
  proof: by
  induction L using List.twoStepInduction generalizing m with
  | nil => grind
  | singleton _ => simp
  | cons_cons _ _ _ _ IH =>
    simp_rw [isAdmissible_cons_cons_iff, IH, List.length_cons, and_assoc,
      List.isChain_cons_cons, and_assoc, and_congr_right_iff, and_comm]
    exact fun _ _ =>

中文:
定理 isAdmissible_iff_isChain_and_le
  结论: IsAdmissible m L ↔
  证明: by
  induction L using List.twoStepInduction generalizing m with
  | nil => grind
  | singleton _ => simp
  | cons_cons _ _ _ _ IH =>
    simp_rw [isAdmissible_cons_cons_iff, IH, List.length_cons, and_assoc,
      List.isChain_cons_cons, and_assoc, and_congr_right_iff, and_comm]
    exact fun _ _ =>

Depends on / 依赖: List.isChain_cons_cons, List.length_cons, List.twoStepInduction, and_assoc, and_comm, and_congr_right_iff, cons_cons, generalizing, isAdmissible_cons_cons_iff, isChain_cons_cons, length_cons, simp_rw, singleton, twoStepInduction
-/
theorem isAdmissible_iff_isChain_and_le : IsAdmissible m L ↔
    L.IsChain (· < ·) ∧ forall k, (h : k < L.length) -> L[k] <= m + k := by
  induction L using List.twoStepInduction generalizing m with
  | nil => grind
  | singleton _ => simp
  | cons_cons _ _ _ _ IH =>
    simp_rw [isAdmissible_cons_cons_iff, IH, List.length_cons, and_assoc,
      List.isChain_cons_cons, and_assoc, and_congr_right_iff, and_comm]
    exact fun _ _ => ⟨fun h => by grind,
      fun h => ⟨h 0 (by grind), fun k _ => (h (k + 1) (by grind)).trans (by grind)⟩⟩

/--
theorem `isAdmissible_iff_pairwise_and_le` / 定理 `isAdmissible_iff_pairwise_and_le`

English:
theorem isAdmissible_iff_pairwise_and_le
  statement: IsAdmissible m L ↔
  proof: by
  rw [isAdmissible_iff_isChain_and_le]; rw [List.isChain_iff_pairwise]

中文:
定理 isAdmissible_iff_pairwise_and_le
  结论: IsAdmissible m L ↔
  证明: by
  rw [isAdmissible_iff_isChain_and_le]; rw [List.isChain_iff_pairwise]

Depends on / 依赖: List.isChain_iff_pairwise, isAdmissible_iff_isChain_and_le, isChain_iff_pairwise
-/
theorem isAdmissible_iff_pairwise_and_le : IsAdmissible m L ↔
    L.Pairwise (· < ·) ∧ forall k, (h : k < L.length) -> L[k] <= m + k := by
  rw [isAdmissible_iff_isChain_and_le]; rw [List.isChain_iff_pairwise]

/--
theorem `isAdmissible_of_isChain_of_forall_getElem_le` / 定理 `isAdmissible_of_isChain_of_forall_getElem_le`

English:
theorem isAdmissible_of_isChain_of_forall_getElem_le
  statement: {m L} (hL : L.IsChain (· < ·))
  proof: isAdmissible_iff_isChain_and_le.mpr ⟨hL, hL₂⟩

中文:
定理 isAdmissible_of_isChain_of_forall_getElem_le
  结论: {m L} (hL : L.IsChain (· < ·))
  证明: isAdmissible_iff_isChain_and_le.mpr ⟨hL, hL₂⟩

Depends on / 依赖: isAdmissible_iff_isChain_and_le, isAdmissible_iff_isChain_and_le.mpr
-/
theorem isAdmissible_of_isChain_of_forall_getElem_le {m L} (hL : L.IsChain (· < ·))
    (hL₂ : forall k, (h : k < L.length) -> L[k] <= m + k) : IsAdmissible m L :=
  isAdmissible_iff_isChain_and_le.mpr ⟨hL, hL₂⟩

namespace IsAdmissible

/--
theorem `isChain` / 定理 `isChain`

English:
theorem isChain
  given: {m L} (hL : IsAdmissible m L)
  proof: (isAdmissible_iff_isChain_and_le.mp hL).1

中文:
定理 isChain
  条件: {m L} (hL : IsAdmissible m L)
  证明: (isAdmissible_iff_isChain_and_le.mp hL).1
-/
@[grind ->] theorem isChain {m L} (hL : IsAdmissible m L) :
    L.IsChain (· < ·) := (isAdmissible_iff_isChain_and_le.mp hL).1

/--
theorem `le` / 定理 `le`

English:
theorem le
  given: {m} {L : List Nat} (hL : IsAdmissible m L)
  statement: forall k (h : k < L.length),
  proof: (isAdmissible_iff_isChain_and_le.mp hL).2

中文:
定理 le
  条件: {m} {L : List 自然数} (hL : IsAdmissible m L)
  结论: 对任意 k (h : k < L.length),
  证明: (isAdmissible_iff_isChain_and_le.mp hL).2
-/
@[grind ->] theorem le {m} {L : List Nat} (hL : IsAdmissible m L) : forall k (h : k < L.length),
    L[k] <= m + k := (isAdmissible_iff_isChain_and_le.mp hL).2

/--
lemma `of_cons` / 引理 `of_cons`

English:
lemma of_cons
  given: {m a L} (h : IsAdmissible m (a :: L))
  proof: by cases L <;> grind

中文:
引理 of_cons
  条件: {m a L} (h : IsAdmissible m (a :: L))
  证明: by cases L <;> grind
-/
@[grind ->] lemma of_cons {m a L} (h : IsAdmissible m (a :: L)) :
    IsAdmissible (m + 1) L := by cases L <;> grind

/--
lemma `cons` / 引理 `cons`

English:
lemma cons
  statement: {m a L} (hL : IsAdmissible (m + 1) L) (ha : a <= m)
  proof: by cases L <;> grind

中文:
引理 cons
  结论: {m a L} (hL : IsAdmissible (m + 1) L) (ha : a <= m)
  证明: by cases L <;> grind
-/
lemma cons {m a L} (hL : IsAdmissible (m + 1) L) (ha : a <= m)
    (ha' : (_ : 0 < L.length) -> a < L[0]) : IsAdmissible m (a :: L) := by cases L <;> grind

/--
theorem `sortedLT` / 定理 `sortedLT`

English:
theorem sortedLT
  given: {m L} (hL : IsAdmissible m L)
  statement: L.SortedLT
  proof: hL.isChain.sortedLT

中文:
定理 sortedLT
  条件: {m L} (hL : IsAdmissible m L)
  结论: L.SortedLT
  证明: hL.isChain.sortedLT

Depends on / 依赖: hL.isChain.sortedLT, isChain, sortedLT
-/
theorem sortedLT {m L} (hL : IsAdmissible m L) : L.SortedLT :=
  hL.isChain.sortedLT

/-- If `(a :: l)` is `m`-admissible then a is less than all elements of `l` -/
@[grind ->]
/--
lemma `head_lt` / 引理 `head_lt`

English:
lemma head_lt
  given: {m a L} (hL : IsAdmissible m (a :: L))
  proof: fun _ => L.rel_of_pairwise_cons hL.sortedLT.pairwise

中文:
引理 head_lt
  条件: {m a L} (hL : IsAdmissible m (a :: L))
  证明: fun _ => L.rel_of_pairwise_cons hL.sortedLT.pairwise

Depends on / 依赖: L.rel_of_pairwise_cons, hL.sortedLT.pairwise, pairwise, rel_of_pairwise_cons, sortedLT
-/
lemma head_lt {m a L} (hL : IsAdmissible m (a :: L)) :
    forall a' in L, a < a' := fun _ => L.rel_of_pairwise_cons hL.sortedLT.pairwise

/--
lemma `getElem_lt` / 引理 `getElem_lt`

English:
lemma getElem_lt
  statement: {m L} (hL : IsAdmissible m L)
  proof: by
  grw [hL.le, hk]

中文:
引理 getElem_lt
  结论: {m L} (hL : IsAdmissible m L)
  证明: by
  grw [hL.le, hk]
-/
@[grind ->] lemma getElem_lt {m L} (hL : IsAdmissible m L)
    {k : Nat} {hk : k < L.length} : L[k] < m + L.length := by
  grw [hL.le, hk]

/-- An element of an `m`-admissible list, as an element of the appropriate `Fin` -/
@[simps]
/--
Definition of `getElemAsFin` / `getElemAsFin` 的定义

English:
definition getElemAsFin
  signature: {m L} (hl : IsAdmissible m L) (k : Nat)
  body: Fin.mk L[k] Nat.le_iff_lt_add_one.mp (by grind)

中文:
定义 getElemAsFin
  签名: {m L} (hl : IsAdmissible m L) (k : 自然数)
  定义体: Fin.mk L[k] Nat.le_iff_lt_add_one.mp (by grind)

Depends on / 依赖: Fin.mk, Nat.le_iff_lt_add_one.mp, le_iff_lt_add_one
-/
def getElemAsFin {m L} (hl : IsAdmissible m L) (k : Nat)
    (hK : k < L.length) : Fin (m + k + 1) :=
Fin.mk L[k] Nat.le_iff_lt_add_one.mp (by grind)

/-- The head of an `m`-admissible list. -/
@[simps!]
/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: {m a L} (hl : IsAdmissible m (a :: L))
  body: hl.getElemAsFin 0 (by grind)

中文:
定义 head
  签名: {m a L} (hl : IsAdmissible m (a :: L))
  定义体: hl.getElemAsFin 0 (by grind)

Depends on / 依赖: getElemAsFin, hl.getElemAsFin
-/
def head {m a L} (hl : IsAdmissible m (a :: L)) : Fin (m + 1) :=
  hl.getElemAsFin 0 (by grind)

/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {n} (hmn : m <= n) (hL : IsAdmissible m L)
  statement: IsAdmissible n L
  proof: isAdmissible_of_isChain_of_forall_getElem_le (by grind) (by grind)

中文:
定理 mono
  条件: {n} (hmn : m <= n) (hL : IsAdmissible m L)
  结论: IsAdmissible n L
  证明: isAdmissible_of_isChain_of_forall_getElem_le (by grind) (by grind)

Depends on / 依赖: isAdmissible_of_isChain_of_forall_getElem_le
-/
theorem mono {n} (hmn : m <= n) (hL : IsAdmissible m L) : IsAdmissible n L :=
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
/--
Definition of `simplicialInsert` / `simplicialInsert` 的定义

English:
definition simplicialInsert
  signature: (a : Nat)

中文:
定义 simplicialInsert
  签名: (a : 自然数)
-/
def simplicialInsert (a : Nat) : List Nat -> List Nat
  | [] => [a]
  | b :: l => if a < b then a :: b :: l else b :: simplicialInsert (a + 1) l

/--
lemma `simplicialInsert_length` / 引理 `simplicialInsert_length`

English:
lemma simplicialInsert_length
  given: (a : Nat) (L : List Nat)
  proof: by
  induction L generalizing a <;> grind

中文:
引理 simplicialInsert_length
  条件: (a : 自然数) (L : List 自然数)
  证明: by
  induction L generalizing a <;> grind

Depends on / 依赖: generalizing
-/
lemma simplicialInsert_length (a : Nat) (L : List Nat) :
    (simplicialInsert a L).length = L.length + 1 := by
  induction L generalizing a <;> grind

/--
theorem `simplicialInsert_isAdmissible` / 定理 `simplicialInsert_isAdmissible`

English:
theorem simplicialInsert_isAdmissible
  statement: (L : List Nat) (hL : IsAdmissible (m + 1) L) (j : Nat)
  proof: by
  induction L generalizing j m with
  | nil => exact IsAdmissible.singleton hj
  | cons a L h_rec => cases L <;> grind

中文:
定理 simplicialInsert_isAdmissible
  结论: (L : List 自然数) (hL : IsAdmissible (m + 1) L) (j : 自然数)
  证明: by
  induction L generalizing j m with
  | nil => exact IsAdmissible.singleton hj
  | cons a L h_rec => cases L <;> grind

Depends on / 依赖: IsAdmissible, IsAdmissible.singleton, generalizing, h_rec, singleton
-/
theorem simplicialInsert_isAdmissible (L : List Nat) (hL : IsAdmissible (m + 1) L) (j : Nat)
    (hj : j <= m) :
IsAdmissible m simplicialInsert j L := by
  induction L generalizing j m with
  | nil => exact IsAdmissible.singleton hj
  | cons a L h_rec => cases L <;> grind

end AdmissibleLists

section NormalFormsP_σ

-- Impl note.: The definition is a bit awkward with the extra parameters, but this
-- is necessary in order to avoid some type theory hell when proving that `orderedInsert`
-- behaves as expected...

/--
Definition of `standardσ` / `standardσ` 的定义

English:
definition standardσ
  signature: (L : List Nat) {m₁ m₂ : Nat} (h : m₂ + L.length = m₁)
  body: match L with
  | .nil => eqToHom (by grind)
  | .cons a t => standardσ t (by grind) ≫ σ (Fin.ofNat _ a)

@[simp]

中文:
定义 standardσ
  签名: (L : List 自然数) {m₁ m₂ : 自然数} (h : m₂ + L.length = m₁)
  定义体: match L with
  | .nil => eqToHom (by grind)
  | .cons a t => standardσ t (by grind) ≫ σ (Fin.ofNat _ a)

@[simp]

Depends on / 依赖: Fin.ofNat, eqToHom
-/
def standardσ (L : List Nat) {m₁ m₂ : Nat} (h : m₂ + L.length = m₁) : mk m₁ ⟶ mk m₂ :=
  match L with
  | .nil => eqToHom (by grind)
  | .cons a t => standardσ t (by grind) ≫ σ (Fin.ofNat _ a)

@[simp]
/--
lemma `standardσ_nil` / 引理 `standardσ_nil`

English:
lemma standardσ_nil
  given: (m : Nat)
  statement: standardσ .nil (by grind) = 𝟙 (mk m)
  proof: rfl

@[simp, reassoc]

中文:
引理 standardσ_nil
  条件: (m : 自然数)
  结论: standardσ .nil (by grind) = 𝟙 (mk m)
  证明: rfl

@[simp, reassoc]
-/
lemma standardσ_nil (m : Nat) : standardσ .nil (by grind) = 𝟙 (mk m) := rfl

@[simp, reassoc]
/--
lemma `standardσ_cons` / 引理 `standardσ_cons`

English:
lemma standardσ_cons
  given: (L : List Nat) (a : Nat) {m₁ m₂ : Nat} (h : m₂ + (a :: L).length = m₁)
  proof: rfl

@[reassoc]

中文:
引理 standardσ_cons
  条件: (L : List 自然数) (a : 自然数) {m₁ m₂ : 自然数} (h : m₂ + (a :: L).length = m₁)
  证明: rfl

@[reassoc]
-/
lemma standardσ_cons (L : List Nat) (a : Nat) {m₁ m₂ : Nat} (h : m₂ + (a :: L).length = m₁) :
    standardσ (L.cons a) h = standardσ L (by grind) ≫ σ (Fin.ofNat _ a) := rfl

@[reassoc]
/--
lemma `standardσ_comp_standardσ` / 引理 `standardσ_comp_standardσ`

English:
lemma standardσ_comp_standardσ
  statement: (L₁ L₂ : List Nat) {m₁ m₂ m₃ : Nat}
  proof: by
  induction L₂ generalizing L₁ m₁ m₂ m₃ with
  | nil =>
    obtain rfl : m₃ = m₂ := by grind
    simp
  | cons a t H =>
    dsimp at h' ⊢
    obtain rfl : m₂ = (m₃ + t.length) + 1 := by grind
    simp [reassoc_of% (H L₁ (m₁ := m₁) (m₂ := m₃ + t.length + 1) (m₃ := m₃ + 1)
      (by grind) (by grin

中文:
引理 standardσ_comp_standardσ
  结论: (L₁ L₂ : List 自然数) {m₁ m₂ m₃ : 自然数}
  证明: by
  induction L₂ generalizing L₁ m₁ m₂ m₃ with
  | nil =>
    obtain rfl : m₃ = m₂ := by grind
    simp
  | cons a t H =>
    dsimp at h' ⊢
    obtain rfl : m₂ = (m₃ + t.length) + 1 := by grind
    simp [reassoc_of% (H L₁ (m₁ := m₁) (m₂ := m₃ + t.length + 1) (m₃ := m₃ + 1)
      (by grind) (by grin

Depends on / 依赖: generalizing, length, reassoc_of, t.length
-/
lemma standardσ_comp_standardσ (L₁ L₂ : List Nat) {m₁ m₂ m₃ : Nat}
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

variable (m : Nat) (L : List Nat)

/-- `simplicialEvalσ` is a lift to ℕ of `(toSimplexCategory.map (standardσ m L _ _)).toOrderHom`.
Rather than defining it as such, we define it inductively for less painful inductive reasoning,
(see `simplicialEvalσ_of_isAdmissible`).
It is expected to produce the correct result only if `L` is admissible, and values for
non-admissible lists should be considered junk values. Similarly, values for out-of-bounds inputs
are junk values. -/
@[local grind]
/--
Definition of `simplicialEvalσ` / `simplicialEvalσ` 的定义

English:
definition simplicialEvalσ
  signature: (L : List Nat)
  body: fun j => match L with
  | [] => j
  | a :: L => if a < simplicialEvalσ L j then simplicialEvalσ L j - 1 else simplicialEvalσ L j

@[grind ←]

中文:
定义 simplicialEvalσ
  签名: (L : List 自然数)
  定义体: fun j => match L with
  | [] => j
  | a :: L => if a < simplicialEvalσ L j then simplicialEvalσ L j - 1 else simplicialEvalσ L j

@[grind ←]
-/
def simplicialEvalσ (L : List Nat) : Nat -> Nat :=
  fun j => match L with
  | [] => j
  | a :: L => if a < simplicialEvalσ L j then simplicialEvalσ L j - 1 else simplicialEvalσ L j

@[grind ←]
/--
lemma `simplicialEvalσ_of_le_mem` / 引理 `simplicialEvalσ_of_le_mem`

English:
lemma simplicialEvalσ_of_le_mem
  given: (j : Nat) (hj : forall k in L, j <= k)
  statement: simplicialEvalσ L j = j
  proof: by
  induction L with | nil => grind | cons _ _ _ => simp only [List.forall_mem_cons] at hj; grind

中文:
引理 simplicialEvalσ_of_le_mem
  条件: (j : 自然数) (hj : 对任意 k in L, j <= k)
  结论: simplicialEvalσ L j = j
  证明: by
  induction L with | nil => grind | cons _ _ _ => simp only [List.forall_mem_cons] at hj; grind

Depends on / 依赖: List.forall_mem_cons, forall_mem_cons
-/
lemma simplicialEvalσ_of_le_mem (j : Nat) (hj : forall k in L, j <= k) : simplicialEvalσ L j = j := by
  induction L with | nil => grind | cons _ _ _ => simp only [List.forall_mem_cons] at hj; grind

/--
lemma `simplicialEvalσ_monotone` / 引理 `simplicialEvalσ_monotone`

English:
lemma simplicialEvalσ_monotone
  given: (L : List Nat)
  statement: Monotone (simplicialEvalσ L)
  proof: by
  induction L <;> grind [Monotone]

中文:
引理 simplicialEvalσ_monotone
  条件: (L : List 自然数)
  结论: Monotone (simplicialEvalσ L)
  证明: by
  induction L <;> grind [Monotone]

Depends on / 依赖: Monotone
-/
lemma simplicialEvalσ_monotone (L : List Nat) : Monotone (simplicialEvalσ L) := by
  induction L <;> grind [Monotone]

variable {m}

set_option backward.isDefEq.respectTransparency false in
/--
lemma `simplicialEvalσ_of_isAdmissible` / 引理 `simplicialEvalσ_of_isAdmissible`

English:
lemma simplicialEvalσ_of_isAdmissible
  proof: by
  induction L generalizing m₁ m₂ with
  | nil =>
    obtain rfl : m₁ = m₂ := by grind
    simp [simplicialEvalσ]
  | cons a L h_rec =>
    simp only [List.length_cons] at hk
    subst hk
    set a₀ := hL.head
    have aux (t : Fin (m₂ + 2)) :
        (a₀.predAbove t : Nat) = if a < ↑t then (t : N

中文:
引理 simplicialEvalσ_of_isAdmissible
  证明: by
  induction L generalizing m₁ m₂ with
  | nil =>
    obtain rfl : m₁ = m₂ := by grind
    simp [simplicialEvalσ]
  | cons a L h_rec =>
    simp only [List.length_cons] at hk
    subst hk
    set a₀ := hL.head
    have aux (t : Fin (m₂ + 2)) :
        (a₀.predAbove t : Nat) = if a < ↑t then (t : N

Depends on / 依赖: Fin.lt_def, Fin.predAbove, Fin.val_castSucc, IsAdmissible, IsAdmissible.head_val, List.length_cons, generalizing, hL.head, h_rec, head_val, length_cons, lt_def, not_lt, predAbove, split_ifs, val_castSucc
-/
lemma simplicialEvalσ_of_isAdmissible
    (m₁ m₂ : Nat) (hL : IsAdmissible m₂ L) (hk : m₂ + L.length = m₁)
    (j : Nat) (hj : j < m₁ + 1) :
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
        (a₀.predAbove t : Nat) = if a < ↑t then (t : Nat) - 1 else ↑t := by
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

/--
lemma `standardσ_simplicialInsert` / 引理 `standardσ_simplicialInsert`

English:
lemma standardσ_simplicialInsert
  statement: (hL : IsAdmissible (m + 1) L) (j : Nat) (hj : j < m + 1)
  proof: by
  induction L generalizing m j with
  | nil => simp [standardσ, simplicialInsert]
  | cons a L h_rec =>
    simp only [simplicialInsert]
    split_ifs
    · simp
    · have : forall (j k : Nat) (h : j < (k + 1)), Fin.ofNat (k + 1) j = j := by simp -- helps grind below
      have : a < m + 2 := by

中文:
引理 standardσ_simplicialInsert
  结论: (hL : IsAdmissible (m + 1) L) (j : 自然数) (hj : j < m + 1)
  证明: by
  induction L generalizing m j with
  | nil => simp [standardσ, simplicialInsert]
  | cons a L h_rec =>
    simp only [simplicialInsert]
    split_ifs
    · simp
    · have : forall (j k : Nat) (h : j < (k + 1)), Fin.ofNat (k + 1) j = j := by simp -- helps grind below
      have : a < m + 2 := by

Depends on / 依赖: simplicialInsert
-/
lemma standardσ_simplicialInsert (hL : IsAdmissible (m + 1) L) (j : Nat) (hj : j < m + 1)
    (m₁ : Nat) (hm₁ : m + L.length + 1 = m₁) :
    standardσ (m₂ := m) (simplicialInsert j L) (m₁ := m₁)
      (by simpa only [simplicialInsert_length, add_assoc]) =
    standardσ (m₂ := m + 1) L (by grind) ≫ σ (Fin.ofNat _ j) := by
  induction L generalizing m j with
  | nil => simp [standardσ, simplicialInsert]
  | cons a L h_rec =>
    simp only [simplicialInsert]
    split_ifs
    · simp
    · have : forall (j k : Nat) (h : j < (k + 1)), Fin.ofNat (k + 1) j = j := by simp -- helps grind below
      have : a < m + 2 := by grind -- helps grind below
      have : σ (Fin.ofNat (m + 2) a) ≫ σ (.ofNat _ j) = σ (.ofNat _ (j + 1)) ≫ σ (.ofNat _ a) := by
        convert! σ_comp_σ_nat (n := m) a j (by grind) (by grind) (by grind) <;> grind
      grind [standardσ_cons]

set_option backward.isDefEq.respectTransparency false in
attribute [local grind! .] simplicialInsert_length simplicialInsert_isAdmissible in
/--
theorem `exists_normal_form_P_σ` / 定理 `exists_normal_form_P_σ`

English:
theorem exists_normal_form_P_σ
  given: {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_σ f)
  proof: by
  induction hf with
  | id n =>
    use [], n.len, 0, rfl, rfl, rfl, IsAdmissible.nil _
    rfl
  | of f hf =>
    cases hf with | @σ m k =>
    use [k.val], m, 1, rfl, rfl, rfl, IsAdmissible.singleton k.is_le
    simp [standardσ]
  | @comp_of _ j x' g g' hg hg' h_rec =>
    cases hg' with | @σ m

中文:
定理 exists_normal_form_P_σ
  条件: {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_σ f)
  证明: by
  induction hf with
  | id n =>
    use [], n.len, 0, rfl, rfl, rfl, IsAdmissible.nil _
    rfl
  | of f hf =>
    cases hf with | @σ m k =>
    use [k.val], m, 1, rfl, rfl, rfl, IsAdmissible.singleton k.is_le
    simp [standardσ]
  | @comp_of _ j x' g g' hg hg' h_rec =>
    cases hg' with | @σ m

Depends on / 依赖: IsAdmissible, IsAdmissible.nil, IsAdmissible.singleton, comp_of, h_rec, is_le, k.is_le, k.val, n.len, simplicialInsert, singleton, x.len
-/
theorem exists_normal_form_P_σ {x y : SimplexCategoryGenRel} (f : x ⟶ y) (hf : P_σ f) :
    exists L : List Nat,
    exists m : Nat, exists b : Nat,
    exists h₁ : mk m = y, exists h₂ : x = mk (m + b), exists h : L.length = b,
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
    obtain rfl : m₁ = m + 1 := congrArg (fun x => x.len) h₁'
    use simplicialInsert k.val L₁, m, b₁ + 1, rfl, by grind, by grind, by grind
    subst_vars
    have := standardσ (m₁ := m + 1 + L₁.length) [] (by grind) ≫=
      (standardσ_simplicialInsert L₁ hL₁ k k.prop _ rfl).symm
    simp_all [Fin.ofNat_eq_cast, Fin.cast_val_eq_self, standardσ_comp_standardσ_assoc,
      standardσ_comp_standardσ]

section MemIsAdmissible

/--
lemma `IsAdmissible.simplicialEvalσ_succ_getElem` / 引理 `IsAdmissible.simplicialEvalσ_succ_getElem`

English:
lemma IsAdmissible.simplicialEvalσ_succ_getElem
  statement: (hL : IsAdmissible m L)
  proof: by
  induction L generalizing m k <;> grind [-> IsAdmissible.singleton]

local grind_pattern IsAdmissible.simplicialEvalσ_succ_getElem =>
  IsAdmissible m L, simplicialEvalσ L L[k]

中文:
引理 IsAdmissible.simplicialEvalσ_succ_getElem
  结论: (hL : IsAdmissible m L)
  证明: by
  induction L generalizing m k <;> grind [-> IsAdmissible.singleton]

local grind_pattern IsAdmissible.simplicialEvalσ_succ_getElem =>
  IsAdmissible m L, simplicialEvalσ L L[k]

Depends on / 依赖: IsAdmissible, IsAdmissible.singleton, generalizing, singleton
-/
lemma IsAdmissible.simplicialEvalσ_succ_getElem (hL : IsAdmissible m L)
    {k : Nat} {hk : k < L.length} : simplicialEvalσ L L[k] = simplicialEvalσ L (L[k] + 1) := by
  induction L generalizing m k <;> grind [-> IsAdmissible.singleton]

local grind_pattern IsAdmissible.simplicialEvalσ_succ_getElem =>
  IsAdmissible m L, simplicialEvalσ L L[k]

/--
lemma `mem_isAdmissible_of_lt_and_eval_eq_eval_add_one` / 引理 `mem_isAdmissible_of_lt_and_eval_eq_eval_add_one`

English:
lemma mem_isAdmissible_of_lt_and_eval_eq_eval_add_one
  statement: (hL : IsAdmissible m L)
  proof: by
  induction L generalizing m with
  | nil => grind
  | cons a L h_rec =>
    have := simplicialEvalσ_monotone L (a := a + 1)
    rcases lt_trichotomy j a with h | h | h <;> grind

中文:
引理 mem_isAdmissible_of_lt_and_eval_eq_eval_add_one
  结论: (hL : IsAdmissible m L)
  证明: by
  induction L generalizing m with
  | nil => grind
  | cons a L h_rec =>
    have := simplicialEvalσ_monotone L (a := a + 1)
    rcases lt_trichotomy j a with h | h | h <;> grind

Depends on / 依赖: generalizing, h_rec, lt_trichotomy
-/
lemma mem_isAdmissible_of_lt_and_eval_eq_eval_add_one (hL : IsAdmissible m L)
    (j : Nat) (hj₁ : j < m + L.length) (hj₂ : simplicialEvalσ L j = simplicialEvalσ L (j + 1)) :
    j in L := by
  induction L generalizing m with
  | nil => grind
  | cons a L h_rec =>
    have := simplicialEvalσ_monotone L (a := a + 1)
    rcases lt_trichotomy j a with h | h | h <;> grind

/--
lemma `lt_and_eval_eq_eval_add_one_of_mem_isAdmissible` / 引理 `lt_and_eval_eq_eval_add_one_of_mem_isAdmissible`

English:
lemma lt_and_eval_eq_eval_add_one_of_mem_isAdmissible
  given: (hL : IsAdmissible m L) (j : Nat) (hj : j in L)
  proof: by
  grind [List.mem_iff_getElem]

中文:
引理 lt_and_eval_eq_eval_add_one_of_mem_isAdmissible
  条件: (hL : IsAdmissible m L) (j : 自然数) (hj : j in L)
  证明: by
  grind [List.mem_iff_getElem]

Depends on / 依赖: List.mem_iff_getElem, mem_iff_getElem
-/
lemma lt_and_eval_eq_eval_add_one_of_mem_isAdmissible (hL : IsAdmissible m L) (j : Nat) (hj : j in L) :
    j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1) := by
  grind [List.mem_iff_getElem]

/--
lemma `mem_isAdmissible_iff` / 引理 `mem_isAdmissible_iff`

English:
lemma mem_isAdmissible_iff
  given: (hL : IsAdmissible m L) (j : Nat)
  proof: by
  grind [lt_and_eval_eq_eval_add_one_of_mem_isAdmissible,
    mem_isAdmissible_of_lt_and_eval_eq_eval_add_one]

中文:
引理 mem_isAdmissible_iff
  条件: (hL : IsAdmissible m L) (j : 自然数)
  证明: by
  grind [lt_and_eval_eq_eval_add_one_of_mem_isAdmissible,
    mem_isAdmissible_of_lt_and_eval_eq_eval_add_one]

Depends on / 依赖: lt_and_eval_eq_eval_add_one_of_mem_isAdmissible, mem_isAdmissible_of_lt_and_eval_eq_eval_add_one
-/
lemma mem_isAdmissible_iff (hL : IsAdmissible m L) (j : Nat) :
    j in L ↔ j < m + L.length ∧ simplicialEvalσ L j = simplicialEvalσ L (j + 1) := by
  grind [lt_and_eval_eq_eval_add_one_of_mem_isAdmissible,
    mem_isAdmissible_of_lt_and_eval_eq_eval_add_one]

end MemIsAdmissible

end NormalFormsP_σ

end SimplexCategoryGenRel
