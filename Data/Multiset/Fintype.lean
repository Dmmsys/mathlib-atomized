/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Multiset coercion to type

This module defines a `CoeSort` instance for multisets and gives it a `Fintype` instance.
It also defines `Multiset.toEnumFinset`, which is another way to enumerate the elements of
a multiset. These coercions and definitions make it easier to sum over multisets using existing
`Finset` theory.

## Main definitions

* A coercion from `m : Multiset α` to a `Type*`. Each `x : m` has two components.
  The first, `x.1`, can be obtained via the coercion `↑x : α`,
  and it yields the underlying element of the multiset.
  The second, `x.2`, is a term of `Fin (m.count x)`,
  and its function is to ensure each term appears with the correct multiplicity.
  Note that this coercion requires `DecidableEq α` due to the definition using `Multiset.count`.
* `Multiset.toEnumFinset` is a `Finset` version of this.
* `Multiset.coeEmbedding` is the embedding `m ↪ α × ℕ`, whose first component is the coercion
  and whose second component enumerates elements with multiplicity.
* `Multiset.coeEquiv` is the equivalence `m ≃ m.toEnumFinset`.

## Tags

multiset enumeration
-/

@[expose] public section


variable {α β : Type*} [DecidableEq α] [DecidableEq β] {m : Multiset α}

namespace Multiset

/--
Definition of `ToType` / `ToType` 的定义

English:
definition ToType
  signature: (m : Multiset α)
  body: (x : α) × Fin (m.count x)

中文:
定义 ToType
  签名: (m : Multiset α)
  定义体: (x : α) × Fin (m.count x)

Depends on / 依赖: m.count
-/
def ToType (m : Multiset α) : Type _ := (x : α) × Fin (m.count x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort (Multiset α) (Type _)
  body: ⟨Multiset.ToType⟩

example : DecidableEq m := inferInstanceAs DecidableEq ((x : α) × Fin (m.count x))

中文:
实例 :
  签名: CoeSort (Multiset α) (类型 _)
  定义体: ⟨Multiset.ToType⟩

example : DecidableEq m := inferInstanceAs DecidableEq ((x : α) × Fin (m.count x))

Depends on / 依赖: Multiset, Multiset.ToType, ToType
-/
instance : CoeSort (Multiset α) (Type _) := ⟨Multiset.ToType⟩

example : DecidableEq m := inferInstanceAs DecidableEq ((x : α) × Fin (m.count x))

/-- Constructor for terms of the coercion of `m` to a type.
This helps Lean pick up the correct instances. -/
@[reducible, match_pattern]
/--
Definition of `mkToType` / `mkToType` 的定义

English:
definition mkToType
  signature: (m : Multiset α) (x : α) (i : Fin (m.count x))
  body: ⟨x, i⟩

中文:
定义 mkToType
  签名: (m : Multiset α) (x : α) (i : 有限集 (m.count x))
  定义体: ⟨x, i⟩
-/
def mkToType (m : Multiset α) (x : α) (i : Fin (m.count x)) : m :=
  ⟨x, i⟩

/--
Instance `instCoeSortMultisetType.instCoeOutToType` / 实例 `instCoeSortMultisetType.instCoeOutToType`

English:
instance instCoeSortMultisetType.instCoeOutToType
  signature: : CoeOut m α
  body: ⟨fun x => x.1⟩

中文:
实例 instCoeSortMultisetType.instCoeOutToType
  签名: : CoeOut m α
  定义体: ⟨fun x => x.1⟩
-/
instance instCoeSortMultisetType.instCoeOutToType : CoeOut m α :=
  ⟨fun x => x.1⟩

/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {x : α} {i : Fin (m.count x)}
  statement: ↑(m.mkToType x i) = x
  proof: rfl

中文:
定理 coe_mk
  条件: {x : α} {i : 有限集 (m.count x)}
  结论: ↑(m.mkToType x i) = x
  证明: rfl
-/
theorem coe_mk {x : α} {i : Fin (m.count x)} : ↑(m.mkToType x i) = x :=
  rfl

/--
lemma `coe_mem` / 引理 `coe_mem`

English:
lemma coe_mem
  given: {x : m}
  statement: ↑x in m
  proof: Multiset.count_pos.mp (by have := x.2.2; lia)

@[simp]

中文:
引理 coe_mem
  条件: {x : m}
  结论: ↑x in m
  证明: Multiset.count_pos.mp (by have := x.2.2; lia)

@[simp]
-/
@[simp] lemma coe_mem {x : m} : ↑x in m := Multiset.count_pos.mp (by have := x.2.2; lia)

@[simp]
/--
theorem `forall_coe` / 定理 `forall_coe`

English:
theorem forall_coe
  given: (p : m -> Prop)
  proof: Sigma.forall

@[simp]

中文:
定理 对任意_coe
  条件: (p : m -> 命题)
  证明: Sigma.forall

@[simp]
-/
protected theorem forall_coe (p : m -> Prop) :
    (forall x : m, p x) ↔ forall (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.forall

@[simp]
/--
theorem `exists_coe` / 定理 `exists_coe`

English:
theorem exists_coe
  given: (p : m -> Prop)
  proof: Sigma.exists

中文:
定理 存在_coe
  条件: (p : m -> 命题)
  证明: Sigma.exists
-/
protected theorem exists_coe (p : m -> Prop) :
    (exists x : m, p x) ↔ exists (x : α) (i : Fin (m.count x)), p ⟨x, i⟩ :=
  Sigma.exists

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype { p : α × Nat | p.2 < m.count p.1 }
  body: Fintype.ofFinset
    (m.toFinset.disjiUnion
      (fun x => (Finset.range (m.count x)).map ⟨_, Prod.mk_right_injective x⟩)
      fun x hx y hy hxy => by simp [Function.onFun, Finset.disjoint_right, hxy])
    (by
      rintro ⟨x, i⟩
      simp_rw [Finset.mem_disjiUnion, Multiset.mem_toFinset, Finset.

中文:
实例 :
  签名: 有限类型 { p : α × 自然数 | p.2 < m.count p.1 }
  定义体: Fintype.ofFinset
    (m.toFinset.disjiUnion
      (fun x => (Finset.range (m.count x)).map ⟨_, Prod.mk_right_injective x⟩)
      fun x hx y hy hxy => by simp [Function.onFun, Finset.disjoint_right, hxy])
    (by
      rintro ⟨x, i⟩
      simp_rw [Finset.mem_disjiUnion, Multiset.mem_toFinset, Finset.

Depends on / 依赖: Embedding, Finset, Finset.disjoint_right, Finset.mem_disjiUnion, Finset.mem_map, Finset.mem_range, Finset.range, Fintype, Fintype.ofFinset, Function, Function.Embedding.coeFn_mk, Function.onFun, Multiset, Multiset.count_pos.mp, Multiset.mem_toFinset, Prod.mk_inj, Prod.mk_right_injective, Set.mem_ofPred_eq, and_assoc, and_iff_right_iff_imp
-/
instance : Fintype { p : α × Nat | p.2 < m.count p.1 } :=
  Fintype.ofFinset
    (m.toFinset.disjiUnion
      (fun x => (Finset.range (m.count x)).map ⟨_, Prod.mk_right_injective x⟩)
      fun x hx y hy hxy => by simp [Function.onFun, Finset.disjoint_right, hxy])
    (by
      rintro ⟨x, i⟩
      simp_rw [Finset.mem_disjiUnion, Multiset.mem_toFinset, Finset.mem_map, Finset.mem_range,
        Function.Embedding.coeFn_mk, Prod.mk_inj, Set.mem_ofPred_eq]
      simp only [← and_assoc, exists_eq_right, and_iff_right_iff_imp]
      exact fun h => Multiset.count_pos.mp (by lia))

/--
Definition of `toEnumFinset` / `toEnumFinset` 的定义

English:
definition toEnumFinset
  signature: (m : Multiset α)
  body: { p : α × Nat | p.2 < m.count p.1 }.toFinset

@[simp]

中文:
定义 toEnumFinset
  签名: (m : Multiset α)
  定义体: { p : α × Nat | p.2 < m.count p.1 }.toFinset

@[simp]

Depends on / 依赖: m.count, toFinset
-/
def toEnumFinset (m : Multiset α) : Finset (α × Nat) :=
  { p : α × Nat | p.2 < m.count p.1 }.toFinset

@[simp]
/--
theorem `mem_toEnumFinset` / 定理 `mem_toEnumFinset`

English:
theorem mem_toEnumFinset
  given: (m : Multiset α) (p : α × Nat)
  proof: Set.mem_toFinset

中文:
定理 mem_toEnumFinset
  条件: (m : Multiset α) (p : α × 自然数)
  证明: Set.mem_toFinset

Depends on / 依赖: Set.mem_toFinset, mem_toFinset
-/
theorem mem_toEnumFinset (m : Multiset α) (p : α × Nat) :
    p in m.toEnumFinset ↔ p.2 < m.count p.1 :=
  Set.mem_toFinset

/--
theorem `mem_of_mem_toEnumFinset` / 定理 `mem_of_mem_toEnumFinset`

English:
theorem mem_of_mem_toEnumFinset
  given: {p : α × Nat} (h : p in m.toEnumFinset)
  statement: p.1 in m
  proof: have := (m.mem_toEnumFinset p).mp h; Multiset.count_pos.mp (by lia)

中文:
定理 mem_of_mem_toEnumFinset
  条件: {p : α × 自然数} (h : p in m.toEnumFinset)
  结论: p.1 in m
  证明: have := (m.mem_toEnumFinset p).mp h; Multiset.count_pos.mp (by lia)

Depends on / 依赖: Multiset, Multiset.count_pos.mp, count_pos, m.mem_toEnumFinset, mem_toEnumFinset
-/
theorem mem_of_mem_toEnumFinset {p : α × Nat} (h : p in m.toEnumFinset) : p.1 in m :=
  have := (m.mem_toEnumFinset p).mp h; Multiset.count_pos.mp (by lia)

/--
lemma `toEnumFinset_filter_eq` / 引理 `toEnumFinset_filter_eq`

English:
lemma toEnumFinset_filter_eq
  given: (m : Multiset α) (a : α)
  proof: by aesop

中文:
引理 toEnumFinset_filter_eq
  条件: (m : Multiset α) (a : α)
  证明: by aesop
-/
@[simp] lemma toEnumFinset_filter_eq (m : Multiset α) (a : α) :
    {x in m.toEnumFinset | x.1 = a} = {a} ×ˢ Finset.range (m.count a) := by aesop

/--
lemma `map_toEnumFinset_fst` / 引理 `map_toEnumFinset_fst`

English:
lemma map_toEnumFinset_fst
  given: (m : Multiset α)
  statement: m.toEnumFinset.val.map Prod.fst = m
  proof: by
  ext a; simp [count_map, ← Finset.filter_val, eq_comm (a := a)]

中文:
引理 map_toEnumFinset_fst
  条件: (m : Multiset α)
  结论: m.toEnumFinset.val.map 积类型.fst = m
  证明: by
  ext a; simp [count_map, ← Finset.filter_val, eq_comm (a := a)]
-/
@[simp] lemma map_toEnumFinset_fst (m : Multiset α) : m.toEnumFinset.val.map Prod.fst = m := by
  ext a; simp [count_map, ← Finset.filter_val, eq_comm (a := a)]

/--
lemma `image_toEnumFinset_fst` / 引理 `image_toEnumFinset_fst`

English:
lemma image_toEnumFinset_fst
  given: (m : Multiset α)
  proof: by
  rw [Finset.image]; rw [Multiset.map_toEnumFinset_fst]

中文:
引理 image_toEnumFinset_fst
  条件: (m : Multiset α)
  证明: by
  rw [Finset.image]; rw [Multiset.map_toEnumFinset_fst]
-/
@[simp] lemma image_toEnumFinset_fst (m : Multiset α) :
    m.toEnumFinset.image Prod.fst = m.toFinset := by
  rw [Finset.image]; rw [Multiset.map_toEnumFinset_fst]

/--
lemma `map_fst_le_of_subset_toEnumFinset` / 引理 `map_fst_le_of_subset_toEnumFinset`

English:
lemma map_fst_le_of_subset_toEnumFinset
  given: {s : Finset (α × Nat)} (hsm : s subseteq m.toEnumFinset)
  proof: by
  simp_rw [le_iff_count, count_map]
  rintro a
  obtain ha | ha := (s.1.filter fun x => a = x.1).card.eq_zero_or_pos
  · rw [ha]
    exact Nat.zero_le _
  obtain ⟨n, han, hn⟩ : exists n >= card (s.1.filter fun x => a = x.1) - 1, (a, n) in s := by
    by_contra! h
    replace h : {x in s | x.1 = a

中文:
引理 map_fst_le_of_subset_toEnumFinset
  条件: {s : 有限集 (α × 自然数)} (hsm : s subseteq m.toEnumFinset)
  证明: by
  simp_rw [le_iff_count, count_map]
  rintro a
  obtain ha | ha := (s.1.filter fun x => a = x.1).card.eq_zero_or_pos
  · rw [ha]
    exact Nat.zero_le _
  obtain ⟨n, han, hn⟩ : exists n >= card (s.1.filter fun x => a = x.1) - 1, (a, n) in s := by
    by_contra! h
    replace h : {x in s | x.1 = a
-/
@[simp] lemma map_fst_le_of_subset_toEnumFinset {s : Finset (α × Nat)} (hsm : s subseteq m.toEnumFinset) :
    s.1.map Prod.fst <= m := by
  simp_rw [le_iff_count, count_map]
  rintro a
  obtain ha | ha := (s.1.filter fun x => a = x.1).card.eq_zero_or_pos
  · rw [ha]
    exact Nat.zero_le _
  obtain ⟨n, han, hn⟩ : exists n >= card (s.1.filter fun x => a = x.1) - 1, (a, n) in s := by
    by_contra! h
    replace h : {x in s | x.1 = a} subseteq {a} ×ˢ .range (card (s.1.filter fun x => a = x.1) - 1) := by
      simpa +contextual [forall_comm (β := _ = a), Finset.subset_iff,
        imp_not_comm, not_le, Nat.lt_sub_iff_add_lt] using h
    have : card (s.1.filter fun x => a = x.1) <= card (s.1.filter fun x => a = x.1) - 1 := by
      simpa [Finset.card, eq_comm] using Finset.card_mono h
    lia
  exact Nat.le_of_pred_lt (han.trans_lt <| by simpa using hsm hn)

@[gcongr, mono]
/--
theorem `toEnumFinset_mono` / 定理 `toEnumFinset_mono`

English:
theorem toEnumFinset_mono
  given: {m₁ m₂ : Multiset α} (h : m₁ <= m₂)
  proof: by
  intro p
  simp only [Multiset.mem_toEnumFinset]
  exact lt_of_le_of_lt' (Multiset.le_iff_count.mp h p.1)

@[simp]

中文:
定理 toEnumFinset_mono
  条件: {m₁ m₂ : Multiset α} (h : m₁ <= m₂)
  证明: by
  intro p
  simp only [Multiset.mem_toEnumFinset]
  exact lt_of_le_of_lt' (Multiset.le_iff_count.mp h p.1)

@[simp]

Depends on / 依赖: Multiset, Multiset.le_iff_count.mp, Multiset.mem_toEnumFinset, le_iff_count, lt_of_le_of_lt, mem_toEnumFinset
-/
theorem toEnumFinset_mono {m₁ m₂ : Multiset α} (h : m₁ <= m₂) :
    m₁.toEnumFinset subseteq m₂.toEnumFinset := by
  intro p
  simp only [Multiset.mem_toEnumFinset]
  exact lt_of_le_of_lt' (Multiset.le_iff_count.mp h p.1)

@[simp]
/--
theorem `toEnumFinset_subset_iff` / 定理 `toEnumFinset_subset_iff`

English:
theorem toEnumFinset_subset_iff
  given: {m₁ m₂ : Multiset α}
  proof: ⟨fun h => by simpa using map_fst_le_of_subset_toEnumFinset h, Multiset.toEnumFinset_mono⟩

中文:
定理 toEnumFinset_subset_iff
  条件: {m₁ m₂ : Multiset α}
  证明: ⟨fun h => by simpa using map_fst_le_of_subset_toEnumFinset h, Multiset.toEnumFinset_mono⟩

Depends on / 依赖: Multiset, Multiset.toEnumFinset_mono, map_fst_le_of_subset_toEnumFinset, toEnumFinset_mono
-/
theorem toEnumFinset_subset_iff {m₁ m₂ : Multiset α} :
    m₁.toEnumFinset subseteq m₂.toEnumFinset ↔ m₁ <= m₂ :=
  ⟨fun h => by simpa using map_fst_le_of_subset_toEnumFinset h, Multiset.toEnumFinset_mono⟩

/-- The embedding from a multiset into `α × ℕ` where the second coordinate enumerates repeats.
If you are looking for the function `m → α`, that would be plain `(↑)`. -/
@[simps]
/--
Definition of `coeEmbedding` / `coeEmbedding` 的定义

English:
definition coeEmbedding
  signature: (m : Multiset α)
  body: (x, x.2)
  inj' := by
    intro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    rintro ⟨⟩
    rfl

中文:
定义 coeEmbedding
  签名: (m : Multiset α)
  定义体: (x, x.2)
  inj' := by
    intro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    rintro ⟨⟩
    rfl
-/
def coeEmbedding (m : Multiset α) : m ↪ α × Nat where
  toFun x := (x, x.2)
  inj' := by
    intro ⟨x, i, hi⟩ ⟨y, j, hj⟩
    rintro ⟨⟩
    rfl

/-- Another way to coerce a `Multiset` to a type is to go through `m.toEnumFinset` and coerce
that `Finset` to a type. -/
@[simps]
/--
Definition of `coeEquiv` / `coeEquiv` 的定义

English:
definition coeEquiv
  signature: (m : Multiset α)
  body: ⟨m.coeEmbedding x, by
      rw [Multiset.mem_toEnumFinset]
      exact x.2.2⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_toEnumFinset]
      exact x.2⟩

@[simp]

中文:
定义 coeEquiv
  签名: (m : Multiset α)
  定义体: ⟨m.coeEmbedding x, by
      rw [Multiset.mem_toEnumFinset]
      exact x.2.2⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_toEnumFinset]
      exact x.2⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_toEnumFinset, coeEmbedding, invFun, m.coeEmbedding, mem_toEnumFinset
-/
def coeEquiv (m : Multiset α) : m ≃ m.toEnumFinset where
  toFun x :=
    ⟨m.coeEmbedding x, by
      rw [Multiset.mem_toEnumFinset]
      exact x.2.2⟩
  invFun x :=
    ⟨x.1.1, x.1.2, by
      rw [← Multiset.mem_toEnumFinset]
      exact x.2⟩

@[simp]
/--
theorem `toEmbedding_coeEquiv_trans` / 定理 `toEmbedding_coeEquiv_trans`

English:
theorem toEmbedding_coeEquiv_trans
  given: (m : Multiset α)
  proof: by ext <;> rfl

中文:
定理 toEmbedding_coeEquiv_trans
  条件: (m : Multiset α)
  证明: by ext <;> rfl
-/
theorem toEmbedding_coeEquiv_trans (m : Multiset α) :
    m.coeEquiv.toEmbedding.trans (Function.Embedding.subtype _) = m.coeEmbedding := by ext <;> rfl

/--
Instance `fintypeCoe` / 实例 `fintypeCoe`

English:
instance fintypeCoe
  signature: : Fintype m
  body: Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm

中文:
实例 fintypeCoe
  签名: : 有限类型 m
  定义体: Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, coeEquiv, m.coeEquiv.symm, m.toEnumFinset, ofEquiv, toEnumFinset
-/
instance fintypeCoe : Fintype m :=
  Fintype.ofEquiv m.toEnumFinset m.coeEquiv.symm

attribute [irreducible] fintypeCoe

/--
theorem `map_univ_coeEmbedding` / 定理 `map_univ_coeEmbedding`

English:
theorem map_univ_coeEmbedding
  given: (m : Multiset α)
  proof: by
  ext ⟨x, i⟩
  simp only [Fin.exists_iff, Finset.mem_map, Finset.mem_univ, Multiset.coeEmbedding_apply,
    Prod.mk_inj, Multiset.exists_coe, Multiset.coe_mk,
    exists_prop, exists_eq_right_right, exists_eq_right, Multiset.mem_toEnumFinset, true_and]

@[simp]

中文:
定理 map_univ_coeEmbedding
  条件: (m : Multiset α)
  证明: by
  ext ⟨x, i⟩
  simp only [Fin.exists_iff, Finset.mem_map, Finset.mem_univ, Multiset.coeEmbedding_apply,
    Prod.mk_inj, Multiset.exists_coe, Multiset.coe_mk,
    exists_prop, exists_eq_right_right, exists_eq_right, Multiset.mem_toEnumFinset, true_and]

@[simp]

Depends on / 依赖: Fin.exists_iff, Finset, Finset.mem_map, Finset.mem_univ, Multiset, Multiset.coeEmbedding_apply, Multiset.coe_mk, Multiset.exists_coe, Multiset.mem_toEnumFinset, Prod.mk_inj, coeEmbedding_apply, coe_mk, exists_coe, exists_eq_right, exists_eq_right_right, exists_iff, exists_prop, mem_map, mem_toEnumFinset, mem_univ
-/
theorem map_univ_coeEmbedding (m : Multiset α) :
    (Finset.univ : Finset m).map m.coeEmbedding = m.toEnumFinset := by
  ext ⟨x, i⟩
  simp only [Fin.exists_iff, Finset.mem_map, Finset.mem_univ, Multiset.coeEmbedding_apply,
    Prod.mk_inj, Multiset.exists_coe, Multiset.coe_mk,
    exists_prop, exists_eq_right_right, exists_eq_right, Multiset.mem_toEnumFinset, true_and]

@[simp]
/--
theorem `map_univ_coe` / 定理 `map_univ_coe`

English:
theorem map_univ_coe
  given: (m : Multiset α)
  proof: by
  have := m.map_toEnumFinset_fst
  rw [← m.map_univ_coeEmbedding] at this
  simpa only [Finset.map_val, Multiset.coeEmbedding_apply, Multiset.map_map,
    Function.comp_apply] using this

中文:
定理 map_univ_coe
  条件: (m : Multiset α)
  证明: by
  have := m.map_toEnumFinset_fst
  rw [← m.map_univ_coeEmbedding] at this
  simpa only [Finset.map_val, Multiset.coeEmbedding_apply, Multiset.map_map,
    Function.comp_apply] using this

Depends on / 依赖: Finset, Finset.map_val, Function, Function.comp_apply, Multiset, Multiset.coeEmbedding_apply, Multiset.map_map, coeEmbedding_apply, comp_apply, m.map_toEnumFinset_fst, m.map_univ_coeEmbedding, map_map, map_toEnumFinset_fst, map_univ_coeEmbedding, map_val
-/
theorem map_univ_coe (m : Multiset α) :
    (Finset.univ : Finset m).val.map (fun x : m => (x : α)) = m := by
  have := m.map_toEnumFinset_fst
  rw [← m.map_univ_coeEmbedding] at this
  simpa only [Finset.map_val, Multiset.coeEmbedding_apply, Multiset.map_map,
    Function.comp_apply] using this

/--
theorem `map_univ_comp_coe` / 定理 `map_univ_comp_coe`

English:
theorem map_univ_comp_coe
  given: {β : Type*} (m : Multiset α) (f : α -> β)
  proof: by
  rw [← Multiset.map_map]; rw [Multiset.map_univ_coe]

中文:
定理 map_univ_comp_coe
  条件: {β : 类型} (m : Multiset α) (f : α -> β)
  证明: by
  rw [← Multiset.map_map]; rw [Multiset.map_univ_coe]

Depends on / 依赖: Multiset, Multiset.map_map, Multiset.map_univ_coe, map_map, map_univ_coe
-/
theorem map_univ_comp_coe {β : Type*} (m : Multiset α) (f : α -> β) :
    ((Finset.univ : Finset m).val.map (f ∘ (fun x : m => (x : α)))) = m.map f := by
  rw [← Multiset.map_map]; rw [Multiset.map_univ_coe]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `map_univ` / 定理 `map_univ`

English:
theorem map_univ
  given: {β : Type*} (m : Multiset α) (f : α -> β)
  proof: by
  simp_rw [← Function.comp_apply (f := f)]
  exact map_univ_comp_coe m f

@[simp]

中文:
定理 map_univ
  条件: {β : 类型} (m : Multiset α) (f : α -> β)
  证明: by
  simp_rw [← Function.comp_apply (f := f)]
  exact map_univ_comp_coe m f

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, map_univ_comp_coe, simp_rw
-/
theorem map_univ {β : Type*} (m : Multiset α) (f : α -> β) :
    ((Finset.univ : Finset m).val.map fun (x : m) => f (x : α)) = m.map f := by
  simp_rw [← Function.comp_apply (f := f)]
  exact map_univ_comp_coe m f

@[simp]
/--
theorem `card_toEnumFinset` / 定理 `card_toEnumFinset`

English:
theorem card_toEnumFinset
  given: (m : Multiset α)
  statement: m.toEnumFinset.card = Multiset.card m
  proof: by
  rw [Finset.card]; rw [← Multiset.card_map Prod.fst m.toEnumFinset.val]
  congr
  exact m.map_toEnumFinset_fst

@[simp]

中文:
定理 card_toEnumFinset
  条件: (m : Multiset α)
  结论: m.toEnumFinset.card = Multiset.card m
  证明: by
  rw [Finset.card]; rw [← Multiset.card_map Prod.fst m.toEnumFinset.val]
  congr
  exact m.map_toEnumFinset_fst

@[simp]

Depends on / 依赖: Finset, Finset.card, Multiset, Multiset.card_map, Prod.fst, card_map, m.map_toEnumFinset_fst, m.toEnumFinset.val, map_toEnumFinset_fst, toEnumFinset
-/
theorem card_toEnumFinset (m : Multiset α) : m.toEnumFinset.card = Multiset.card m := by
  rw [Finset.card]; rw [← Multiset.card_map Prod.fst m.toEnumFinset.val]
  congr
  exact m.map_toEnumFinset_fst

@[simp]
/--
theorem `card_coe` / 定理 `card_coe`

English:
theorem card_coe
  given: (m : Multiset α)
  statement: Fintype.card m = Multiset.card m
  proof: by
  rw [Fintype.card_congr m.coeEquiv]
  simp only [Fintype.card_coe, card_toEnumFinset]

@[to_additive]

中文:
定理 card_coe
  条件: (m : Multiset α)
  结论: 有限类型.card m = Multiset.card m
  证明: by
  rw [Fintype.card_congr m.coeEquiv]
  simp only [Fintype.card_coe, card_toEnumFinset]

@[to_additive]

Depends on / 依赖: Fintype, Fintype.card_coe, Fintype.card_congr, card_coe, card_congr, card_toEnumFinset, coeEquiv, m.coeEquiv
-/
theorem card_coe (m : Multiset α) : Fintype.card m = Multiset.card m := by
  rw [Fintype.card_congr m.coeEquiv]
  simp only [Fintype.card_coe, card_toEnumFinset]

@[to_additive]
/--
theorem `prod_eq_prod_coe` / 定理 `prod_eq_prod_coe`

English:
theorem prod_eq_prod_coe
  given: [CommMonoid α] (m : Multiset α)
  statement: m.prod = ∏ x : m, (x : α)
  proof: by
  congr
  simp

@[to_additive]

中文:
定理 prod_eq_prod_coe
  条件: [交换幺半群 α] (m : Multiset α)
  结论: m.乘积 = ∏ x : m, (x : α)
  证明: by
  congr
  simp

@[to_additive]
-/
theorem prod_eq_prod_coe [CommMonoid α] (m : Multiset α) : m.prod = ∏ x : m, (x : α) := by
  congr
  simp

@[to_additive]
/--
theorem `prod_eq_prod_toEnumFinset` / 定理 `prod_eq_prod_toEnumFinset`

English:
theorem prod_eq_prod_toEnumFinset
  given: [CommMonoid α] (m : Multiset α)
  proof: by
  congr
  simp

@[to_additive]

中文:
定理 prod_eq_prod_toEnumFinset
  条件: [交换幺半群 α] (m : Multiset α)
  证明: by
  congr
  simp

@[to_additive]
-/
theorem prod_eq_prod_toEnumFinset [CommMonoid α] (m : Multiset α) :
    m.prod = ∏ x in m.toEnumFinset, x.1 := by
  congr
  simp

@[to_additive]
/--
theorem `prod_toEnumFinset` / 定理 `prod_toEnumFinset`

English:
theorem prod_toEnumFinset
  given: {β : Type*} [CommMonoid β] (m : Multiset α) (f : α -> Nat -> β)
  proof: by
  rw [Fintype.prod_equiv m.coeEquiv (fun x => f x x.2) fun x => f x.1.1 x.1.2]
  · rw [← m.toEnumFinset.prod_coe_sort fun x => f x.1 x.2]
  · intro x
    rfl

中文:
定理 prod_toEnumFinset
  条件: {β : 类型} [交换幺半群 β] (m : Multiset α) (f : α -> 自然数 -> β)
  证明: by
  rw [Fintype.prod_equiv m.coeEquiv (fun x => f x x.2) fun x => f x.1.1 x.1.2]
  · rw [← m.toEnumFinset.prod_coe_sort fun x => f x.1 x.2]
  · intro x
    rfl

Depends on / 依赖: Fintype, Fintype.prod_equiv, coeEquiv, m.coeEquiv, m.toEnumFinset.prod_coe_sort, prod_coe_sort, prod_equiv, toEnumFinset
-/
theorem prod_toEnumFinset {β : Type*} [CommMonoid β] (m : Multiset α) (f : α -> Nat -> β) :
    ∏ x in m.toEnumFinset, f x.1 x.2 = ∏ x : m, f x x.2 := by
  rw [Fintype.prod_equiv m.coeEquiv (fun x => f x x.2) fun x => f x.1.1 x.1.2]
  · rw [← m.toEnumFinset.prod_coe_sort fun x => f x.1 x.2]
  · intro x
    rfl

/--
If `s = t` then there's an equivalence between the appropriate types.
-/
@[simps]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {s t : Multiset α} (h : s = t)
  body: ⟨x.1, x.2.cast (by simp [h])⟩
  invFun x := ⟨x.1, x.2.cast (by simp [h])⟩

中文:
定义 cast
  签名: {s t : Multiset α} (h : s = t)
  定义体: ⟨x.1, x.2.cast (by simp [h])⟩
  invFun x := ⟨x.1, x.2.cast (by simp [h])⟩
-/
def cast {s t : Multiset α} (h : s = t) : s ≃ t where
  toFun x := ⟨x.1, x.2.cast (by simp [h])⟩
  invFun x := ⟨x.1, x.2.cast (by simp [h])⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty (0 : Multiset α)
  body: Fintype.card_eq_zero_iff.mp (by simp)

中文:
实例 :
  签名: 是空 (0 : Multiset α)
  定义体: Fintype.card_eq_zero_iff.mp (by simp)

Depends on / 依赖: Fintype, Fintype.card_eq_zero_iff.mp, card_eq_zero_iff
-/
instance : IsEmpty (0 : Multiset α) := Fintype.card_eq_zero_iff.mp (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty (∅ : Multiset α)
  body: Fintype.card_eq_zero_iff.mp (by simp)

中文:
实例 :
  签名: 是空 (∅ : Multiset α)
  定义体: Fintype.card_eq_zero_iff.mp (by simp)

Depends on / 依赖: Fintype, Fintype.card_eq_zero_iff.mp, card_eq_zero_iff
-/
instance : IsEmpty (∅ : Multiset α) := Fintype.card_eq_zero_iff.mp (by simp)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `consEquiv` / `consEquiv` 的定义

English:
definition consEquiv
  signature: {v : α}
  body: if h : x.1 = v ∧ x.2.val = m.count v then none else some ⟨x.1, ⟨x.2, by
    by_cases hv : x.1 = v
    · simp only [hv, true_and] at h ⊢
      apply lt_of_le_of_ne (Nat.le_of_lt_add_one _) h
      convert! x.2.2 using 1
      simp [hv]
    · convert! x.2.2 using 1
      exact (count_cons_of_ne hv _).

中文:
定义 consEquiv
  签名: {v : α}
  定义体: if h : x.1 = v ∧ x.2.val = m.count v then none else some ⟨x.1, ⟨x.2, by
    by_cases hv : x.1 = v
    · simp only [hv, true_and] at h ⊢
      apply lt_of_le_of_ne (Nat.le_of_lt_add_one _) h
      convert! x.2.2 using 1
      simp [hv]
    · convert! x.2.2 using 1
      exact (count_cons_of_ne hv _).

Depends on / 依赖: Nat.le_of_lt_add_one, castLE, convert, count_cons_of_ne, count_le_count_cons, invFun, le_of_lt_add_one, left_inv, lt_of_le_of_ne, m.count, rename_i, right_inv, true_and, x.elim
-/
def consEquiv {v : α} : v ::ₘ m ≃ Option m where
  toFun x := if h : x.1 = v ∧ x.2.val = m.count v then none else some ⟨x.1, ⟨x.2, by
    by_cases hv : x.1 = v
    · simp only [hv, true_and] at h ⊢
      apply lt_of_le_of_ne (Nat.le_of_lt_add_one _) h
      convert! x.2.2 using 1
      simp [hv]
    · convert! x.2.2 using 1
      exact (count_cons_of_ne hv _).symm
    ⟩⟩
  invFun x := x.elim ⟨v, ⟨m.count v, by simp⟩⟩ (fun x => ⟨x.1, x.2.castLE (count_le_count_cons ..)⟩)
  left_inv := by
    rintro ⟨x, hx⟩
    dsimp only
    split
    · rename_i h
      obtain ⟨rfl, h2⟩ := h
      simp [← h2]
    · simp
  right_inv := by
    rintro (_ | x)
    · simp
    · simp only [Option.elim_some, Fin.val_castLE, Fin.eta, Sigma.eta, dite_eq_ite,
        ite_eq_right_iff, reduceCtorEq, imp_false, not_and]
      rintro rfl
      exact x.2.2.ne

@[simp]
/--
lemma `consEquiv_symm_none` / 引理 `consEquiv_symm_none`

English:
lemma consEquiv_symm_none
  given: {v : α}
  proof: rfl

@[simp]

中文:
引理 consEquiv_symm_none
  条件: {v : α}
  证明: rfl

@[simp]
-/
lemma consEquiv_symm_none {v : α} :
    (consEquiv (m := m) (v := v)).symm none =
      ⟨v, ⟨m.count v, (count_cons_self v m) ▸ (Nat.lt_add_one _)⟩⟩ :=
  rfl

@[simp]
/--
lemma `consEquiv_symm_some` / 引理 `consEquiv_symm_some`

English:
lemma consEquiv_symm_some
  given: {v : α} {x : m}
  proof: rfl

中文:
引理 consEquiv_symm_some
  条件: {v : α} {x : m}
  证明: rfl
-/
lemma consEquiv_symm_some {v : α} {x : m} :
    (consEquiv (v := v)).symm (some x) =
      ⟨x, x.2.castLE (count_le_count_cons ..)⟩ :=
  rfl

/--
lemma `coe_consEquiv_of_ne` / 引理 `coe_consEquiv_of_ne`

English:
lemma coe_consEquiv_of_ne
  given: {v : α} (x : v ::ₘ m) (hx : ↑x != v)
  proof: by
  simp [consEquiv, hx]
  rfl

中文:
引理 coe_consEquiv_of_ne
  条件: {v : α} (x : v ::ₘ m) (hx : ↑x != v)
  证明: by
  simp [consEquiv, hx]
  rfl

Depends on / 依赖: consEquiv
-/
lemma coe_consEquiv_of_ne {v : α} (x : v ::ₘ m) (hx : ↑x != v) :
    consEquiv x = some ⟨x.1, x.2.cast (by simp [hx])⟩ := by
  simp [consEquiv, hx]
  rfl

/--
lemma `coe_consEquiv_of_eq_of_eq` / 引理 `coe_consEquiv_of_eq_of_eq`

English:
lemma coe_consEquiv_of_eq_of_eq
  given: {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 = m.count v)
  proof: by simp [consEquiv, hx, hx2]

中文:
引理 coe_consEquiv_of_eq_of_eq
  条件: {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 = m.count v)
  证明: by simp [consEquiv, hx, hx2]

Depends on / 依赖: consEquiv
-/
lemma coe_consEquiv_of_eq_of_eq {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 = m.count v) :
    consEquiv x = none := by simp [consEquiv, hx, hx2]

/--
lemma `coe_consEquiv_of_eq_of_lt` / 引理 `coe_consEquiv_of_eq_of_lt`

English:
lemma coe_consEquiv_of_eq_of_lt
  given: {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 < m.count v)
  proof: by simp [consEquiv, hx, hx2.ne]

中文:
引理 coe_consEquiv_of_eq_of_lt
  条件: {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 < m.count v)
  证明: by simp [consEquiv, hx, hx2.ne]

Depends on / 依赖: consEquiv, hx2.ne
-/
lemma coe_consEquiv_of_eq_of_lt {v : α} (x : v ::ₘ m) (hx : ↑x = v) (hx2 : x.2 < m.count v) :
    consEquiv x = some ⟨x.1, ⟨x.2, by simpa [hx]⟩⟩ := by simp [consEquiv, hx, hx2.ne]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `mapEquivAux` / `mapEquivAux` 的定义

English:
definition mapEquivAux
  signature: (m : Multiset α) (f : α -> β)
  body: Quotient.recOnSubsingleton m fun l => .mk
    List.recOn l
      ⟨@Equiv.equivOfIsEmpty _ _ (by dsimp; infer_instance) (by dsimp; infer_instance), by simp⟩
.trans fun a s ⟨v, hv⟩ => ⟨Multiset.consEquiv.trans v.optionCongr
.trans (Multiset.cast (map_cons f a s)).symm, fun x => by Multiset.consEquiv.s

中文:
定义 mapEquivAux
  签名: (m : Multiset α) (f : α -> β)
  定义体: Quotient.recOnSubsingleton m fun l => .mk
    List.recOn l
      ⟨@Equiv.equivOfIsEmpty _ _ (by dsimp; infer_instance) (by dsimp; infer_instance), by simp⟩
.trans fun a s ⟨v, hv⟩ => ⟨Multiset.consEquiv.trans v.optionCongr
.trans (Multiset.cast (map_cons f a s)).symm, fun x => by Multiset.consEquiv.s

Depends on / 依赖: Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Equiv.equivOfIsEmpty, Equiv.optionCongr_apply, Equiv.trans_apply, List.recOn, Multiset, Multiset.cast, Multiset.consEquiv.symm, Multiset.consEquiv.trans, Quotient, Quotient.recOnSubsingleton, coe_fn_mk, coe_fn_symm_mk, consEquiv, equivOfIsEmpty, infer_instance, map_cons, optionCongr, optionCongr_apply
-/
def mapEquivAux (m : Multiset α) (f : α -> β) :
    Squash { v : m ≃ m.map f // forall a : m, v a = f a} :=
Quotient.recOnSubsingleton m fun l => .mk
    List.recOn l
      ⟨@Equiv.equivOfIsEmpty _ _ (by dsimp; infer_instance) (by dsimp; infer_instance), by simp⟩
.trans fun a s ⟨v, hv⟩ => ⟨Multiset.consEquiv.trans v.optionCongr
.trans (Multiset.cast (map_cons f a s)).symm, fun x => by Multiset.consEquiv.symm
        simp only [consEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, Equiv.optionCongr_apply,
            Equiv.coe_fn_symm_mk]
        split <;> simp_all⟩

@[deprecated (since := "2026-06-06")] alias mapEquiv_aux := mapEquivAux

/--
Definition of `mapEquiv` / `mapEquiv` 的定义

English:
definition mapEquiv
  signature: (s : Multiset α) (f : α -> β)
  body: (Multiset.mapEquivAux s f).out.1

@[simp]

中文:
定义 mapEquiv
  签名: (s : Multiset α) (f : α -> β)
  定义体: (Multiset.mapEquivAux s f).out.1

@[simp]

Depends on / 依赖: Multiset, Multiset.mapEquivAux, mapEquivAux
-/
noncomputable def mapEquiv (s : Multiset α) (f : α -> β) : s ≃ s.map f :=
  (Multiset.mapEquivAux s f).out.1

@[simp]
/--
theorem `mapEquiv_apply` / 定理 `mapEquiv_apply`

English:
theorem mapEquiv_apply
  given: (s : Multiset α) (f : α -> β) (v : s)
  statement: s.mapEquiv f v = f v
  proof: (Multiset.mapEquivAux s f).out.2 v

中文:
定理 mapEquiv_apply
  条件: (s : Multiset α) (f : α -> β) (v : s)
  结论: s.mapEquiv f v = f v
  证明: (Multiset.mapEquivAux s f).out.2 v

Depends on / 依赖: Multiset, Multiset.mapEquivAux, mapEquivAux
-/
theorem mapEquiv_apply (s : Multiset α) (f : α -> β) (v : s) : s.mapEquiv f v = f v :=
  (Multiset.mapEquivAux s f).out.2 v

end Multiset
