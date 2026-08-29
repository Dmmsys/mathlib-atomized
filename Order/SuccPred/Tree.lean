/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Order.SuccPred.Archimedean
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Atoms
public import Mathlib.Data.SetLike.Basic

/-!
# Rooted trees

This file proves basic results about rooted trees, represented using the ancestorship order.
This is a `PartialOrder`, with `PredOrder` with the immediate parent as a predecessor, and an
`OrderBot` which is the root. We also have an `IsPredArchimedean` assumption to prevent infinite
dangling chains.
-/

@[expose] public section

variable {α : Type*} [PartialOrder α] [PredOrder α] [IsPredArchimedean α]

namespace IsPredArchimedean

variable [OrderBot α]

section DecidableEq

variable [DecidableEq α]

/--
Definition of `findAtom` / `findAtom` 的定义

English:
definition findAtom
  signature: (r : α)
  body: Order.pred^[Nat.find (bot_le (a := r)).exists_pred_iterate - 1] r

@[simp]

中文:
定义 findAtom
  签名: (r : α)
  定义体: Order.pred^[Nat.find (bot_le (a := r)).exists_pred_iterate - 1] r

@[simp]

Depends on / 依赖: Nat.find, Order.pred, bot_le, exists_pred_iterate
-/
def findAtom (r : α) : α :=
  Order.pred^[Nat.find (bot_le (a := r)).exists_pred_iterate - 1] r

@[simp]
/--
lemma `findAtom_le` / 引理 `findAtom_le`

English:
lemma findAtom_le
  given: (r : α)
  statement: findAtom r <= r
  proof: Order.pred_iterate_le _ _

@[simp]

中文:
引理 findAtom_le
  条件: (r : α)
  结论: findAtom r <= r
  证明: Order.pred_iterate_le _ _

@[simp]

Depends on / 依赖: Order.pred_iterate_le, pred_iterate_le
-/
lemma findAtom_le (r : α) : findAtom r <= r :=
  Order.pred_iterate_le _ _

@[simp]
/--
lemma `findAtom_bot` / 引理 `findAtom_bot`

English:
lemma findAtom_bot
  statement: findAtom (⊥ : α) = ⊥
  proof: by
  apply Function.iterate_fixed
  simp

@[simp]

中文:
引理 findAtom_bot
  结论: findAtom (⊥ : α) = ⊥
  证明: by
  apply Function.iterate_fixed
  simp

@[simp]

Depends on / 依赖: Function, Function.iterate_fixed, iterate_fixed
-/
lemma findAtom_bot : findAtom (⊥ : α) = ⊥ := by
  apply Function.iterate_fixed
  simp

@[simp]
/--
lemma `pred_findAtom` / 引理 `pred_findAtom`

English:
lemma pred_findAtom
  given: (r : α)
  statement: Order.pred (findAtom r) = ⊥
  proof: by
  unfold findAtom
  generalize h : Nat.find (bot_le (a := r)).exists_pred_iterate = n
  cases n
  · have : Order.pred^[0] r = ⊥ := by
      rw [← h]
      apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate
    simp only [Function.iterate_zero, id_eq] at this
    simp [this]
  · simp only [Nat.add_sub_cancel_right, ← Function.iterate_succ_apply', Nat.succ_eq_add_one]
    rw [← h]
    apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate

@[simp]

中文:
引理 pred_findAtom
  条件: (r : α)
  结论: Order.pred (findAtom r) = ⊥
  证明: by
  unfold findAtom
  generalize h : Nat.find (bot_le (a := r)).exists_pred_iterate = n
  cases n
  · have : Order.pred^[0] r = ⊥ := by
      rw [← h]
      apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate
    simp only [Function.iterate_zero, id_eq] at this
    simp [this]
  · simp only [Nat.add_sub_cancel_right, ← Function.iterate_succ_apply', Nat.succ_eq_add_one]
    rw [← h]
    apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate

@[simp]

Depends on / 依赖: Function, Function.iterate_succ_apply, Function.iterate_zero, Nat.add_sub_cancel_right, Nat.find, Nat.find_spec, Nat.succ_eq_add_one, Order.pred, add_sub_cancel_right, bot_le, exists_pred_iterate, findAtom, find_spec, generalize, id_eq, iterate_succ_apply, iterate_zero, succ_eq_add_one
-/
lemma pred_findAtom (r : α) : Order.pred (findAtom r) = ⊥ := by
  unfold findAtom
  generalize h : Nat.find (bot_le (a := r)).exists_pred_iterate = n
  cases n
  · have : Order.pred^[0] r = ⊥ := by
      rw [← h]
      apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate
    simp only [Function.iterate_zero, id_eq] at this
    simp [this]
  · simp only [Nat.add_sub_cancel_right, ← Function.iterate_succ_apply', Nat.succ_eq_add_one]
    rw [← h]
    apply Nat.find_spec (bot_le (a := r)).exists_pred_iterate

@[simp]
/--
lemma `findAtom_eq_bot` / 引理 `findAtom_eq_bot`

English:
lemma findAtom_eq_bot
  given: {r : α}
  proof: by
    unfold findAtom at h
    have := Nat.find_min' (bot_le (a := r)).exists_pred_iterate h
    replace : Nat.find (bot_le (a := r)).exists_pred_iterate = 0 := by lia
    simpa [this] using h
  mpr h := by simp [h]

中文:
引理 findAtom_eq_bot
  条件: {r : α}
  证明: by
    unfold findAtom at h
    have := Nat.find_min' (bot_le (a := r)).exists_pred_iterate h
    replace : Nat.find (bot_le (a := r)).exists_pred_iterate = 0 := by lia
    simpa [this] using h
  mpr h := by simp [h]

Depends on / 依赖: Nat.find, Nat.find_min, bot_le, exists_pred_iterate, findAtom, find_min, replace
-/
lemma findAtom_eq_bot {r : α} :
    findAtom r = ⊥ ↔ r = ⊥ where
  mp h := by
    unfold findAtom at h
    have := Nat.find_min' (bot_le (a := r)).exists_pred_iterate h
    replace : Nat.find (bot_le (a := r)).exists_pred_iterate = 0 := by lia
    simpa [this] using h
  mpr h := by simp [h]

/--
lemma `findAtom_ne_bot` / 引理 `findAtom_ne_bot`

English:
lemma findAtom_ne_bot
  given: {r : α}
  proof: findAtom_eq_bot.not

中文:
引理 findAtom_ne_bot
  条件: {r : α}
  证明: findAtom_eq_bot.not

Depends on / 依赖: findAtom_eq_bot, findAtom_eq_bot.not
-/
lemma findAtom_ne_bot {r : α} :
    findAtom r != ⊥ ↔ r != ⊥ := findAtom_eq_bot.not

/--
lemma `isAtom_findAtom` / 引理 `isAtom_findAtom`

English:
lemma isAtom_findAtom
  given: {r : α} (hr : r != ⊥)
  proof: by
  constructor
  · simp [hr]
  · intro b hb
    apply Order.le_pred_of_lt at hb
    simpa using hb

@[simp]

中文:
引理 isAtom_findAtom
  条件: {r : α} (hr : r != ⊥)
  证明: by
  constructor
  · simp [hr]
  · intro b hb
    apply Order.le_pred_of_lt at hb
    simpa using hb

@[simp]

Depends on / 依赖: Order.le_pred_of_lt, le_pred_of_lt
-/
lemma isAtom_findAtom {r : α} (hr : r != ⊥) :
    IsAtom (findAtom r) := by
  constructor
  · simp [hr]
  · intro b hb
    apply Order.le_pred_of_lt at hb
    simpa using hb

@[simp]
/--
lemma `isAtom_findAtom_iff` / 引理 `isAtom_findAtom_iff`

English:
lemma isAtom_findAtom_iff
  given: {r : α}
  proof: isAtom_findAtom
  mp h nh := by simp only [nh, findAtom_bot] at h; exact h.1 rfl

中文:
引理 isAtom_findAtom_iff
  条件: {r : α}
  证明: isAtom_findAtom
  mp h nh := by simp only [nh, findAtom_bot] at h; exact h.1 rfl

Depends on / 依赖: isAtom_findAtom
-/
lemma isAtom_findAtom_iff {r : α} :
    IsAtom (findAtom r) ↔ r != ⊥ where
  mpr := isAtom_findAtom
  mp h nh := by simp only [nh, findAtom_bot] at h; exact h.1 rfl

end DecidableEq

/--
Instance `instIsAtomic` / 实例 `instIsAtomic`

English:
instance instIsAtomic
  signature: : IsAtomic α where
  body: by classical
    rw [or_iff_not_imp_left]
    intro hb
    use findAtom b, isAtom_findAtom hb, findAtom_le b

中文:
实例 instIsAtomic
  签名: : 是原子的 α where
  定义体: by classical
    rw [or_iff_not_imp_left]
    intro hb
    use findAtom b, isAtom_findAtom hb, findAtom_le b

Depends on / 依赖: classical, findAtom, findAtom_le, isAtom_findAtom, or_iff_not_imp_left
-/
instance instIsAtomic : IsAtomic α where
  eq_bot_or_exists_atom_le b := by classical
    rw [or_iff_not_imp_left]
    intro hb
    use findAtom b, isAtom_findAtom hb, findAtom_le b

end IsPredArchimedean

/--
Definition of `RootedTree` / `RootedTree` 的定义

English:
structure RootedTree
  parameters: where
  axioms and operations (5):
    - α : Type*
    - [semilatticeInf : SemilatticeInf α]
    - [orderBot : OrderBot α]
    - [predOrder : PredOrder α]
    - [isPredArchimedean : IsPredArchimedean α]

中文:
结构 有根树
  参数: where
  公理与运算 (5 个):
    - α : 类型
    - [semilatticeInf : SemilatticeInf α]
    - [orderBot : 有底序 α]
    - [predOrder : Pred序 α]
    - [isPredArchimedean : 是PredArchimedean α]
-/
structure RootedTree where
  /-- The type representing the elements in the tree. -/
  α : Type*
  /-- The type should be a `SemilatticeInf`,
  where `inf` is the least common ancestor in the tree. -/
  [semilatticeInf : SemilatticeInf α]
  /-- The type should have a bottom, the root. -/
  [orderBot : OrderBot α]
  /-- The type should have a predecessor for every element, its parent. -/
  [predOrder : PredOrder α]
  /-- The predecessor relationship should be archimedean. -/
  [isPredArchimedean : IsPredArchimedean α]

attribute [coe] RootedTree.α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort RootedTree Type*
  body: ⟨RootedTree.α⟩

中文:
实例 :
  签名: CoeSort 有根树 类型
  定义体: ⟨RootedTree.α⟩

Depends on / 依赖: RootedTree
-/
instance : CoeSort RootedTree Type* := ⟨RootedTree.α⟩

attribute [instance] RootedTree.semilatticeInf RootedTree.predOrder
    RootedTree.orderBot RootedTree.isPredArchimedean

/--
Definition of `SubRootedTree` / `SubRootedTree` 的定义

English:
definition SubRootedTree
  signature: (t : RootedTree)
  body: t

中文:
定义 SubRootedTree
  签名: (t : 有根树)
  定义体: t
-/
def SubRootedTree (t : RootedTree) : Type* := t

/--
Definition of `SubRootedTree.root` / `SubRootedTree.root` 的定义

English:
definition SubRootedTree.root
  signature: {t : RootedTree} (v : SubRootedTree t)
  body: v

中文:
定义 SubRootedTree.root
  签名: {t : 有根树} (v : SubRootedTree t)
  定义体: v
-/
def SubRootedTree.root {t : RootedTree} (v : SubRootedTree t) : t := v

/--
Definition of `RootedTree.subtree` / `RootedTree.subtree` 的定义

English:
definition RootedTree.subtree
  signature: (t : RootedTree) (r : t)
  body: r

@[simp]

中文:
定义 有根树.subtree
  签名: (t : 有根树) (r : t)
  定义体: r

@[simp]
-/
def RootedTree.subtree (t : RootedTree) (r : t) : SubRootedTree t := r

@[simp]
/--
lemma `RootedTree.root_subtree` / 引理 `RootedTree.root_subtree`

English:
lemma RootedTree.root_subtree
  given: (t : RootedTree) (r : t)
  statement: (t.subtree r).root = r
  proof: rfl

@[simp]

中文:
引理 有根树.root_subtree
  条件: (t : 有根树) (r : t)
  结论: (t.subtree r).root = r
  证明: rfl

@[simp]
-/
lemma RootedTree.root_subtree (t : RootedTree) (r : t) : (t.subtree r).root = r := rfl

@[simp]
/--
lemma `RootedTree.subtree_root` / 引理 `RootedTree.subtree_root`

English:
lemma RootedTree.subtree_root
  given: (t : RootedTree) (v : SubRootedTree t)
  statement: t.subtree v.root = v
  proof: rfl

@[ext]

中文:
引理 有根树.subtree_root
  条件: (t : 有根树) (v : SubRootedTree t)
  结论: t.subtree v.root = v
  证明: rfl

@[ext]
-/
lemma RootedTree.subtree_root (t : RootedTree) (v : SubRootedTree t) : t.subtree v.root = v := rfl

@[ext]
/--
lemma `SubRootedTree.ext` / 引理 `SubRootedTree.ext`

English:
lemma SubRootedTree.ext
  statement: {t : RootedTree} {v₁ v₂ : SubRootedTree t}
  proof: h

中文:
引理 SubRootedTree.ext
  结论: {t : 有根树} {v₁ v₂ : SubRootedTree t}
  证明: h
-/
lemma SubRootedTree.ext {t : RootedTree} {v₁ v₂ : SubRootedTree t}
    (h : v₁.root = v₂.root) : v₁ = v₂ := h

instance (t : RootedTree) : SetLike (SubRootedTree t) t where
  coe v := Set.Ici v.root
  coe_injective a₁ a₂ h := by
    simpa only [Set.Ici_inj, ← SubRootedTree.ext_iff] using h

/--
lemma `SubRootedTree.mem_iff` / 引理 `SubRootedTree.mem_iff`

English:
lemma SubRootedTree.mem_iff
  given: {t : RootedTree} {r : SubRootedTree t} {v : t}
  proof: Iff.rfl

中文:
引理 SubRootedTree.mem_iff
  条件: {t : 有根树} {r : SubRootedTree t} {v : t}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma SubRootedTree.mem_iff {t : RootedTree} {r : SubRootedTree t} {v : t} :
    v in r ↔ r.root <= v := Iff.rfl

/--
The coercion from a `SubRootedTree` to a `RootedTree`.
-/
@[coe, reducible]
/--
Definition of `SubRootedTree.coeTree` / `SubRootedTree.coeTree` 的定义

English:
definition SubRootedTree.coeTree
  signature: {t : RootedTree} (r : SubRootedTree t)
  body: Set.Ici r.root

中文:
定义 SubRootedTree.coeTree
  签名: {t : 有根树} (r : SubRootedTree t)
  定义体: Set.Ici r.root

Depends on / 依赖: MonomialOrder, MonomialOrder.leadingCoeff, Set.Ici, coeff_mul_of_degree_add, degree_mul_of_mul_leadingCoeff_ne_zero, hf.leadingCoeff_eq_one, hg.leadingCoeff_eq_one, leadingCoeff, leadingCoeff_eq_one, m.leadingCoeff, nontriviality, one_mul, one_ne_zero, r.root
-/
noncomputable def SubRootedTree.coeTree {t : RootedTree} (r : SubRootedTree t) : RootedTree where
  α := Set.Ici r.root

noncomputable instance (t : RootedTree) : CoeOut (SubRootedTree t) RootedTree :=
  ⟨SubRootedTree.coeTree⟩

@[simp]
/--
lemma `SubRootedTree.bot_mem_iff` / 引理 `SubRootedTree.bot_mem_iff`

English:
lemma SubRootedTree.bot_mem_iff
  given: {t : RootedTree} (r : SubRootedTree t)
  proof: by
  simp [mem_iff]

中文:
引理 SubRootedTree.bot_mem_iff
  条件: {t : 有根树} (r : SubRootedTree t)
  证明: by
  simp [mem_iff]

Depends on / 依赖: mem_iff
-/
lemma SubRootedTree.bot_mem_iff {t : RootedTree} (r : SubRootedTree t) :
    ⊥ in r ↔ r.root = ⊥ := by
  simp [mem_iff]

/--
Definition of `RootedTree.subtrees` / `RootedTree.subtrees` 的定义

English:
definition RootedTree.subtrees
  signature: (t : RootedTree)
  body: {x | IsAtom x.root}

中文:
定义 有根树.subtrees
  签名: (t : 有根树)
  定义体: {x | IsAtom x.root}

Depends on / 依赖: IsAtom, x.root
-/
def RootedTree.subtrees (t : RootedTree) : Set (SubRootedTree t) :=
  {x | IsAtom x.root}

variable {t : RootedTree}

/--
lemma `SubRootedTree.root_ne_bot_of_mem_subtrees` / 引理 `SubRootedTree.root_ne_bot_of_mem_subtrees`

English:
lemma SubRootedTree.root_ne_bot_of_mem_subtrees
  given: (r : SubRootedTree t) (hr : r in t.subtrees)
  proof: by
  simp only [RootedTree.subtrees, Set.mem_ofPred_eq] at hr
  exact hr.1

中文:
引理 SubRootedTree.root_ne_bot_of_mem_subtrees
  条件: (r : SubRootedTree t) (hr : r in t.subtrees)
  证明: by
  simp only [RootedTree.subtrees, Set.mem_ofPred_eq] at hr
  exact hr.1

Depends on / 依赖: RootedTree, RootedTree.subtrees, Set.mem_ofPred_eq, mem_ofPred_eq, subtrees
-/
lemma SubRootedTree.root_ne_bot_of_mem_subtrees (r : SubRootedTree t) (hr : r in t.subtrees) :
    r.root != ⊥ := by
  simp only [RootedTree.subtrees, Set.mem_ofPred_eq] at hr
  exact hr.1

/--
lemma `RootedTree.mem_subtrees_disjoint_iff` / 引理 `RootedTree.mem_subtrees_disjoint_iff`

English:
lemma RootedTree.mem_subtrees_disjoint_iff
  statement: {t₁ t₂ : SubRootedTree t}
  proof: by
    intro nh
    have : t₁.root <= (v₁ : t) ⊓ (v₂ : t) := by
      simp only [le_inf_iff]
      exact ⟨h₁, nh ▸ h₂⟩
    rw [h.eq_bot] at this
    simp only [le_bot_iff] at this
    exact t₁.root_ne_bot_of_mem_subtrees ht₁ this
  mpr h := by
    rw [SubRootedTree.mem_iff] at h₁ h₂
    contrapose h
    rw [disjoint_iff]; rw [← ne_eq]; rw [← bot_lt_iff_ne_bot] at h
    rcases lt_or_le_of_directed (by simp : v₁ ⊓ v₂ <= v₁) h₁ with oh | oh
    · simp_all [RootedTree.subtrees, IsAtom.lt_iff]
    rw [le_inf_iff] at oh
    ext
    simpa only [ht₂.le_iff_eq ht₁.1, ht₁.le_iff_eq ht₂.1, eq_comm, or_self] using
      le_total_of_directed oh.2 h₂

中文:
引理 有根树.mem_subtrees_disjoint_iff
  结论: {t₁ t₂ : SubRootedTree t}
  证明: by
    intro nh
    have : t₁.root <= (v₁ : t) ⊓ (v₂ : t) := by
      simp only [le_inf_iff]
      exact ⟨h₁, nh ▸ h₂⟩
    rw [h.eq_bot] at this
    simp only [le_bot_iff] at this
    exact t₁.root_ne_bot_of_mem_subtrees ht₁ this
  mpr h := by
    rw [SubRootedTree.mem_iff] at h₁ h₂
    contrapose h
    rw [disjoint_iff]; rw [← ne_eq]; rw [← bot_lt_iff_ne_bot] at h
    rcases lt_or_le_of_directed (by simp : v₁ ⊓ v₂ <= v₁) h₁ with oh | oh
    · simp_all [RootedTree.subtrees, IsAtom.lt_iff]
    rw [le_inf_iff] at oh
    ext
    simpa only [ht₂.le_iff_eq ht₁.1, ht₁.le_iff_eq ht₂.1, eq_comm, or_self] using
      le_total_of_directed oh.2 h₂

Depends on / 依赖: IsAtom, IsAtom.lt_iff, RootedTree, RootedTree.subtrees, SubRootedTree, SubRootedTree.mem_iff, bot_lt_iff_ne_bot, contrapose, disjoint_iff, eq_bot, h.eq_bot, le_bot_iff, le_iff_eq, le_inf_iff, lt_iff, lt_or_le_of_directed, mem_iff, ne_eq, root_ne_bot_of_mem_subtrees, subtrees
-/
lemma RootedTree.mem_subtrees_disjoint_iff {t₁ t₂ : SubRootedTree t}
    (ht₁ : t₁ in t.subtrees) (ht₂ : t₂ in t.subtrees) (v₁ v₂ : t) (h₁ : v₁ in t₁)
    (h₂ : v₂ in t₂) :
    Disjoint v₁ v₂ ↔ t₁ != t₂ where
  mp h := by
    intro nh
    have : t₁.root <= (v₁ : t) ⊓ (v₂ : t) := by
      simp only [le_inf_iff]
      exact ⟨h₁, nh ▸ h₂⟩
    rw [h.eq_bot] at this
    simp only [le_bot_iff] at this
    exact t₁.root_ne_bot_of_mem_subtrees ht₁ this
  mpr h := by
    rw [SubRootedTree.mem_iff] at h₁ h₂
    contrapose h
    rw [disjoint_iff]; rw [← ne_eq]; rw [← bot_lt_iff_ne_bot] at h
    rcases lt_or_le_of_directed (by simp : v₁ ⊓ v₂ <= v₁) h₁ with oh | oh
    · simp_all [RootedTree.subtrees, IsAtom.lt_iff]
    rw [le_inf_iff] at oh
    ext
    simpa only [ht₂.le_iff_eq ht₁.1, ht₁.le_iff_eq ht₂.1, eq_comm, or_self] using
      le_total_of_directed oh.2 h₂

/--
lemma `RootedTree.subtrees_disjoint` / 引理 `RootedTree.subtrees_disjoint`

English:
lemma RootedTree.subtrees_disjoint
  statement: t.subtrees.PairwiseDisjoint ((↑) : _ -> Set t)
  proof: by
  intro t₁ ht₁ t₂ ht₂ h
  rw [Function.onFun_apply]; rw [Set.disjoint_left]
  intro a ha hb
  rw [← mem_subtrees_disjoint_iff ht₁ ht₂ a a ha hb]; rw [disjoint_self] at h
  subst h
  simp only [SetLike.mem_coe, SubRootedTree.bot_mem_iff] at ha
  exact t₁.root_ne_bot_of_mem_subtrees ht₁ ha

中文:
引理 有根树.subtrees_disjoint
  结论: t.subtrees.PairwiseDisjoint ((↑) : _ -> 集合 t)
  证明: by
  intro t₁ ht₁ t₂ ht₂ h
  rw [Function.onFun_apply]; rw [Set.disjoint_left]
  intro a ha hb
  rw [← mem_subtrees_disjoint_iff ht₁ ht₂ a a ha hb]; rw [disjoint_self] at h
  subst h
  simp only [SetLike.mem_coe, SubRootedTree.bot_mem_iff] at ha
  exact t₁.root_ne_bot_of_mem_subtrees ht₁ ha

Depends on / 依赖: Function, Function.onFun_apply, Set.disjoint_left, SetLike, SetLike.mem_coe, SubRootedTree, SubRootedTree.bot_mem_iff, bot_mem_iff, disjoint_left, disjoint_self, mem_coe, mem_subtrees_disjoint_iff, onFun_apply, root_ne_bot_of_mem_subtrees
-/
lemma RootedTree.subtrees_disjoint : t.subtrees.PairwiseDisjoint ((↑) : _ -> Set t) := by
  intro t₁ ht₁ t₂ ht₂ h
  rw [Function.onFun_apply]; rw [Set.disjoint_left]
  intro a ha hb
  rw [← mem_subtrees_disjoint_iff ht₁ ht₂ a a ha hb]; rw [disjoint_self] at h
  subst h
  simp only [SetLike.mem_coe, SubRootedTree.bot_mem_iff] at ha
  exact t₁.root_ne_bot_of_mem_subtrees ht₁ ha

/--
Definition of `RootedTree.subtreeOf` / `RootedTree.subtreeOf` 的定义

English:
definition RootedTree.subtreeOf
  signature: (t : RootedTree) [DecidableEq t] (v : t)
  body: t.subtree (IsPredArchimedean.findAtom v)

@[simp]

中文:
定义 有根树.subtreeOf
  签名: (t : 有根树) [DecidableEq t] (v : t)
  定义体: t.subtree (IsPredArchimedean.findAtom v)

@[simp]

Depends on / 依赖: IsPredArchimedean, IsPredArchimedean.findAtom, findAtom, subtree, t.subtree
-/
def RootedTree.subtreeOf (t : RootedTree) [DecidableEq t] (v : t) : SubRootedTree t :=
  t.subtree (IsPredArchimedean.findAtom v)

@[simp]
/--
lemma `RootedTree.mem_subtreeOf` / 引理 `RootedTree.mem_subtreeOf`

English:
lemma RootedTree.mem_subtreeOf
  given: [DecidableEq t] {v : t}
  proof: by
  simp [SubRootedTree.mem_iff, RootedTree.subtreeOf]

中文:
引理 有根树.mem_subtreeOf
  条件: [DecidableEq t] {v : t}
  证明: by
  simp [SubRootedTree.mem_iff, RootedTree.subtreeOf]

Depends on / 依赖: RootedTree, RootedTree.subtreeOf, SubRootedTree, SubRootedTree.mem_iff, mem_iff, subtreeOf
-/
lemma RootedTree.mem_subtreeOf [DecidableEq t] {v : t} :
    v in t.subtreeOf v := by
  simp [SubRootedTree.mem_iff, RootedTree.subtreeOf]

/--
lemma `RootedTree.subtreeOf_mem_subtrees` / 引理 `RootedTree.subtreeOf_mem_subtrees`

English:
lemma RootedTree.subtreeOf_mem_subtrees
  given: [DecidableEq t] {v : t} (hr : v != ⊥)
  proof: by
  simpa [RootedTree.subtrees, RootedTree.subtreeOf]

中文:
引理 有根树.subtreeOf_mem_subtrees
  条件: [DecidableEq t] {v : t} (hr : v != ⊥)
  证明: by
  simpa [RootedTree.subtrees, RootedTree.subtreeOf]

Depends on / 依赖: RootedTree, RootedTree.subtreeOf, RootedTree.subtrees, subtreeOf, subtrees
-/
lemma RootedTree.subtreeOf_mem_subtrees [DecidableEq t] {v : t} (hr : v != ⊥) :
    t.subtreeOf v in t.subtrees := by
  simpa [RootedTree.subtrees, RootedTree.subtreeOf]
