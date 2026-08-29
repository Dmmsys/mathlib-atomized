/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.Fin.Basic

/-! # Constructions of embeddings of `Fin n` into a type

* `Fin.Embedding.cons` : from an embedding `x : Fin n ↪ α` and `a : α` such that
  `a ∉ x.range`, construct an embedding `Fin (n + 1) ↪ α` by putting `a` at `0`

* `Fin.Embedding.tail`: the tail of an embedding `x : Fin (n + 1) ↪ α`

* `Fin.Embedding.snoc` : from an embedding `x : Fin n ↪ α` and `a : α`
  such that `a ∉ x.range`, construct an embedding `Fin (n + 1) ↪ α`
  by putting `a` at the end.

* `Fin.Embedding.init`: the init of an embedding `x : Fin (n + 1) ↪ α`

* `Fin.Embedding.append` : merges two embeddings `Fin m ↪ α` and `Fin n ↪ α`
  into an embedding `Fin (m + n) ↪ α` if they have disjoint ranges

-/

@[expose] public section

open Function.Embedding Fin Set Nat

namespace Fin.Embedding

variable {α : Type*}

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: {n : Nat} (x : Fin (n + 1) ↪ α)
  body: ⟨Fin.tail x, x.injective.comp Fin.succ_injective _⟩

@[simp, norm_cast]

中文:
定义 tail
  签名: {n : 自然数} (x : Fin (n + 1) ↪ α)
  定义体: ⟨Fin.tail x, x.injective.comp Fin.succ_injective _⟩

@[simp, norm_cast]

Depends on / 依赖: Fin.succ_injective, Fin.tail, injective, succ_injective, x.injective.comp
-/
def tail {n : Nat} (x : Fin (n + 1) ↪ α) : Fin n ↪ α :=
⟨Fin.tail x, x.injective.comp Fin.succ_injective _⟩

@[simp, norm_cast]
/--
theorem `coe_tail` / 定理 `coe_tail`

English:
theorem coe_tail
  given: {n : Nat} (x : Fin (n + 1) ↪ α)
  statement: ↑(tail x) = Fin.tail x
  proof: rfl

中文:
定理 coe_tail
  条件: {n : 自然数} (x : Fin (n + 1) ↪ α)
  结论: ↑(tail x) = Fin.tail x
  证明: rfl
-/
theorem coe_tail {n : Nat} (x : Fin (n + 1) ↪ α) : ↑(tail x) = Fin.tail x := rfl

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  body: ⟨Fin.cons a x, cons_injective_iff.mpr ⟨ha, x.inj'⟩⟩

@[simp, norm_cast]

中文:
定义 cons
  签名: {n : 自然数} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  定义体: ⟨Fin.cons a x, cons_injective_iff.mpr ⟨ha, x.inj'⟩⟩

@[simp, norm_cast]

Depends on / 依赖: Fin.cons, cons_injective_iff, cons_injective_iff.mpr, x.inj
-/
def cons {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) : Fin (n + 1) ↪ α :=
  ⟨Fin.cons a x, cons_injective_iff.mpr ⟨ha, x.inj'⟩⟩

@[simp, norm_cast]
/--
theorem `coe_cons` / 定理 `coe_cons`

English:
theorem coe_cons
  given: {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  proof: rfl

中文:
定理 coe_cons
  条件: {n : 自然数} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  证明: rfl
-/
theorem coe_cons {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    ↑(cons x ha) = Fin.cons a x := rfl

/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  given: {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  proof: rfl

中文:
定理 tail_cons
  条件: {n : 自然数} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  证明: rfl
-/
theorem tail_cons {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    tail (cons x ha) = x := rfl

/--
Definition of `init` / `init` 的定义

English:
definition init
  signature: {n : Nat} (x : Fin (n + 1) ↪ α)
  body: ⟨Fin.init x, x.injective.comp castSucc_injective _⟩

中文:
定义 init
  签名: {n : 自然数} (x : Fin (n + 1) ↪ α)
  定义体: ⟨Fin.init x, x.injective.comp castSucc_injective _⟩

Depends on / 依赖: Fin.init, castSucc_injective, injective, x.injective.comp
-/
def init {n : Nat} (x : Fin (n + 1) ↪ α) : Fin n ↪ α :=
⟨Fin.init x, x.injective.comp castSucc_injective _⟩

/--
Definition of `snoc` / `snoc` 的定义

English:
definition snoc
  signature: {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  body: ⟨Fin.snoc x a, snoc_injective_iff.mpr ⟨x.inj', ha⟩⟩

@[simp, norm_cast]

中文:
定义 snoc
  签名: {n : 自然数} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  定义体: ⟨Fin.snoc x a, snoc_injective_iff.mpr ⟨x.inj', ha⟩⟩

@[simp, norm_cast]

Depends on / 依赖: Fin.snoc, snoc_injective_iff, snoc_injective_iff.mpr, x.inj
-/
def snoc {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    Fin (n + 1) ↪ α :=
  ⟨Fin.snoc x a, snoc_injective_iff.mpr ⟨x.inj', ha⟩⟩

@[simp, norm_cast]
/--
theorem `coe_snoc` / 定理 `coe_snoc`

English:
theorem coe_snoc
  given: {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  proof: rfl

中文:
定理 coe_snoc
  条件: {n : 自然数} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  证明: rfl
-/
theorem coe_snoc {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    ↑(snoc x ha) = Fin.snoc x a := rfl

/--
theorem `init_snoc` / 定理 `init_snoc`

English:
theorem init_snoc
  given: {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  proof: by
  simp [snoc, init]

中文:
定理 init_snoc
  条件: {n : 自然数} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x)
  证明: by
  simp [snoc, init]
-/
theorem init_snoc {n : Nat} (x : Fin n ↪ α) {a : α} (ha : a ∉ range x) :
    init (snoc x ha) = x := by
  simp [snoc, init]

/--
theorem `snoc_castSucc` / 定理 `snoc_castSucc`

English:
theorem snoc_castSucc
  given: {n : Nat} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x} {i : Fin n}
  proof: by
  rw [coe_snoc]; rw [Fin.snoc_castSucc]

中文:
定理 snoc_castSucc
  条件: {n : 自然数} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x} {i : Fin n}
  证明: by
  rw [coe_snoc]; rw [Fin.snoc_castSucc]

Depends on / 依赖: Fin.snoc_castSucc, coe_snoc, snoc_castSucc
-/
theorem snoc_castSucc {n : Nat} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x} {i : Fin n} :
    snoc x ha i.castSucc = x i := by
  rw [coe_snoc]; rw [Fin.snoc_castSucc]

/--
theorem `snoc_last` / 定理 `snoc_last`

English:
theorem snoc_last
  given: {n : Nat} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x}
  proof: by
  rw [coe_snoc]; rw [Fin.snoc_last]

中文:
定理 snoc_last
  条件: {n : 自然数} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x}
  证明: by
  rw [coe_snoc]; rw [Fin.snoc_last]

Depends on / 依赖: Fin.snoc_last, coe_snoc, snoc_last
-/
theorem snoc_last {n : Nat} {x : Fin n ↪ α} {a : α} {ha : a ∉ range x} :
    snoc x ha (last n) = a := by
  rw [coe_snoc]; rw [Fin.snoc_last]

/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: {m n : Nat} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x) (range y))
  body: ⟨Fin.append x y,
    Fin.append_injective_iff.mpr ⟨x.inj', y.inj', disjoint_range_iff.mp h⟩⟩

@[simp, norm_cast]

中文:
定义 append
  签名: {m n : 自然数} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x) (range y))
  定义体: ⟨Fin.append x y,
    Fin.append_injective_iff.mpr ⟨x.inj', y.inj', disjoint_range_iff.mp h⟩⟩

@[simp, norm_cast]

Depends on / 依赖: Fin.append, Fin.append_injective_iff.mpr, append, append_injective_iff, disjoint_range_iff, disjoint_range_iff.mp, x.inj, y.inj
-/
def append {m n : Nat} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x) (range y)) :
    Fin (m + n) ↪ α :=
  ⟨Fin.append x y,
    Fin.append_injective_iff.mpr ⟨x.inj', y.inj', disjoint_range_iff.mp h⟩⟩

@[simp, norm_cast]
/--
theorem `coe_append` / 定理 `coe_append`

English:
theorem coe_append
  given: {m n : Nat} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x) (range y))
  proof: rfl

中文:
定理 coe_append
  条件: {m n : 自然数} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x) (range y))
  证明: rfl
-/
theorem coe_append {m n : Nat} {x : Fin m ↪ α} {y : Fin n ↪ α} (h : Disjoint (range x) (range y)) :
    append h = Fin.append x y := rfl

end Fin.Embedding

namespace Function.Embedding

variable {α : Type*}

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `twoEmbeddingEquiv` / `twoEmbeddingEquiv` 的定义

English:
definition twoEmbeddingEquiv
  signature: : (Fin 2 ↪ α) ≃ {(a, b) : α × α | a != b} where
  body: ⟨(e 0, e 1), by
    simp only [ne_eq, Fin.isValue, mem_ofPred_eq, EmbeddingLike.apply_eq_iff_eq, zero_eq_one_iff,
      succ_ne_self, not_false_eq_true]⟩
  invFun := fun ⟨⟨a, b⟩, h⟩ => {
    toFun i := if i = 0 then a else b
    inj' i j hij := by
      by_cases hi : i = 0
      · by_cases hj : j = 

中文:
定义 twoEmbeddingEquiv
  签名: : (Fin 2 ↪ α) ≃ {(a, b) : α × α | a != b} where
  定义体: ⟨(e 0, e 1), by
    simp only [ne_eq, Fin.isValue, mem_ofPred_eq, EmbeddingLike.apply_eq_iff_eq, zero_eq_one_iff,
      succ_ne_self, not_false_eq_true]⟩
  invFun := fun ⟨⟨a, b⟩, h⟩ => {
    toFun i := if i = 0 then a else b
    inj' i j hij := by
      by_cases hi : i = 0
      · by_cases hj : j = 

Depends on / 依赖: EmbeddingLike, EmbeddingLike.apply_eq_iff_eq, False.elim, Fin.isValue, Fin.zero_ne_one, Ne.symm, apply_eq_iff_eq, eq_one_of_ne_zero, hij.sym, if_neg, if_pos, invFun, isValue, mem_ofPred_eq, ne_eq, not_false_eq_true, succ_ne_self, zero_eq_one_iff, zero_ne_one
-/
def twoEmbeddingEquiv : (Fin 2 ↪ α) ≃ {(a, b) : α × α | a != b} where
  toFun e := ⟨(e 0, e 1), by
    simp only [ne_eq, Fin.isValue, mem_ofPred_eq, EmbeddingLike.apply_eq_iff_eq, zero_eq_one_iff,
      succ_ne_self, not_false_eq_true]⟩
  invFun := fun ⟨⟨a, b⟩, h⟩ => {
    toFun i := if i = 0 then a else b
    inj' i j hij := by
      by_cases hi : i = 0
      · by_cases hj : j = 0
        · simp [hi, hj]
        · simp only [if_pos hi, eq_one_of_ne_zero j hj,
          if_neg (Ne.symm Fin.zero_ne_one)] at hij
          apply (h hij).elim
      · rw [eq_one_of_ne_zero i hi] at hij ⊢
        by_cases hj : j = 0
        · simp [hj] at hij; exact False.elim (h hij.symm)
        · rw [eq_one_of_ne_zero j hj] }
  left_inv e := by
    ext i
    by_cases hi : i = 0
    · simp [hi]
    · simp [Fin.eq_one_of_ne_zero i hi]

/--
Definition of `embFinTwo` / `embFinTwo` 的定义

English:
definition embFinTwo
  signature: {a b : α} (h : a != b)
  body: twoEmbeddingEquiv.invFun ⟨(a, b), h⟩

中文:
定义 embFinTwo
  签名: {a b : α} (h : a != b)
  定义体: twoEmbeddingEquiv.invFun ⟨(a, b), h⟩

Depends on / 依赖: invFun, twoEmbeddingEquiv, twoEmbeddingEquiv.invFun
-/
def embFinTwo {a b : α} (h : a != b) : Fin 2 ↪ α :=
  twoEmbeddingEquiv.invFun ⟨(a, b), h⟩

/--
theorem `embFinTwo_apply_zero` / 定理 `embFinTwo_apply_zero`

English:
theorem embFinTwo_apply_zero
  given: {a b : α} (h : a != b)
  proof: rfl

中文:
定理 embFinTwo_apply_zero
  条件: {a b : α} (h : a != b)
  证明: rfl
-/
theorem embFinTwo_apply_zero {a b : α} (h : a != b) :
    embFinTwo h 0 = a := rfl

/--
theorem `embFinTwo_apply_one` / 定理 `embFinTwo_apply_one`

English:
theorem embFinTwo_apply_one
  given: {a b : α} (h : a != b)
  proof: rfl

中文:
定理 embFinTwo_apply_one
  条件: {a b : α} (h : a != b)
  证明: rfl
-/
theorem embFinTwo_apply_one {a b : α} (h : a != b) :
    embFinTwo h 1 = b := rfl

end Function.Embedding
