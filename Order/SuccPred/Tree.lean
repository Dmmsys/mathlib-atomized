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
The unique atom less than an element in an `OrderBot` with archimedean predecessor.
-/
/-
**IsPredArchimedean.findAtom** 是 Mathlib 中的一个定义，位于命名空间 `IsPredArchimedean`。
形式化陈述：findAtom (r : α) : α
参数：r : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unique atom less than an element in an `OrderBot` with archimedean predecess
or.
-/
def findAtom (r : α) : α :=
  Order.pred^[Nat.find (bot_le (a := r)).exists_pred_iterate - 1] r

@[simp]
/-
**IsPredArchimedean.findAtom_le** 是 Mathlib 中的一个引理，位于命名空间 `IsPredArchimedean`。
形式化陈述：findAtom_le (r : α) : findAtom r <= r
参数：r : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.pred_iterate_le`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pr
edOrder α] (k : ℕ) (x : α), Order.pred^[k] x ≤ x
-/
lemma findAtom_le (r : α) : findAtom r ≤ r :=
  Order.pred_iterate_le _ _

@[simp]
/-
**IsPredArchimedean.findAtom_bot** 是 Mathlib 中的一个引理，位于命名空间 `IsPredArchimedean`。
形式化陈述：findAtom_bot : findAtom (⊥ : α) = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.iterate_fixed`：iterate_fixed {x} (h : f x = x) (n : Nat) : f^[n
] x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.pred_bot`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : PredO
rder α] [inst_2 : OrderBot α], Order.pred ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma findAtom_bot : findAtom (⊥ : α) = ⊥ := by
  apply Function.iterate_fixed
  simp

@[simp]
/-
**IsPredArchimedean.pred_findAtom** 是 Mathlib 中的一个引理，位于命名空间 `IsPredArchimedean`。
形式化陈述：pred_findAtom (r : α) : Order.pred (findAtom r) = ⊥
参数：r : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.exists_pred_iterate`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 
: PredOrder α] [IsPredArchimedean α] {a b : α},   b ≤ a → ∃ n, Order.pred^[n] a 
= b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `Order.pred_bot`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : PredO
rder α] [inst_2 : OrderBot α], Order.pred ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_sub_cancel_right`：∀ (n m : ℕ), n + m - m = n
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
/-
**IsPredArchimedean.findAtom_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `IsPredArchimedean
`。
形式化陈述：findAtom_eq_bot {r : α} : findAtom r = ⊥ ↔ r = ⊥ where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.exists_pred_iterate`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 
: PredOrder α] [IsPredArchimedean α] {a b : α},   b ≤ a → ∃ n, Order.pred^[n] a 
= b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsPredArchimedean.findAtom.congr_simp`：∀ {α : Type u_1} [inst : PartialO
rder α] [inst_1 : PredOrder α] [inst_2 : IsPredArchimedean α] [inst_3 : OrderBot
 α]   [inst_4 : DecidableEq…
· 使用引理 `IsPredArchimedean.findAtom_bot`：findAtom_bot : findAtom (⊥ : α) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma findAtom_eq_bot {r : α} :
    findAtom r = ⊥ ↔ r = ⊥ where
  mp h := by
    unfold findAtom at h
    have := Nat.find_min' (bot_le (a := r)).exists_pred_iterate h
    replace : Nat.find (bot_le (a := r)).exists_pred_iterate = 0 := by lia
    simpa [this] using h
  mpr h := by simp [h]
/-
**IsPredArchimedean.findAtom_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `IsPredArchimedean
`。
形式化陈述：findAtom_ne_bot {r : α} : findAtom r != ⊥ ↔ r != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `IsPredArchimedean.findAtom_eq_bot`：findAtom_eq_bot {r : α} : findAtom r 
= ⊥ ↔ r = ⊥ where mp h
-/
lemma findAtom_ne_bot {r : α} :
    findAtom r ≠ ⊥ ↔ r ≠ ⊥ := findAtom_eq_bot.not
/-
**IsPredArchimedean.isAtom_findAtom** 是 Mathlib 中的一个引理，位于命名空间 `IsPredArchimedean
`。
形式化陈述：isAtom_findAtom {r : α} (hr : r != ⊥) : IsAtom (findAtom r)
参数：hr : r != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `IsPredArchimedean.pred_findAtom`：pred_findAtom (r : α) : Order.pred (fin
dAtom r) = ⊥
· 使用定理 `Order.le_pred_of_lt`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pred
Order α] {a b : α}, b < a → b ≤ Order.pred a
-/
lemma isAtom_findAtom {r : α} (hr : r ≠ ⊥) :
    IsAtom (findAtom r) := by
  constructor
  · simp [hr]
  · intro b hb
    apply Order.le_pred_of_lt at hb
    simpa using hb

@[simp]
/-
**IsPredArchimedean.isAtom_findAtom_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsPredArchime
dean`。
形式化陈述：isAtom_findAtom_iff {r : α} : IsAtom (findAtom r) ↔ r != ⊥ where mpr
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsPredArchimedean.findAtom.congr_simp`：∀ {α : Type u_1} [inst : PartialO
rder α] [inst_1 : PredOrder α] [inst_2 : IsPredArchimedean α] [inst_3 : OrderBot
 α]   [inst_4 : DecidableEq…
· 使用引理 `IsPredArchimedean.findAtom_bot`：findAtom_bot : findAtom (⊥ : α) = ⊥
· 使用引理 `IsPredArchimedean.isAtom_findAtom`：isAtom_findAtom {r : α} (hr : r != ⊥)
 : IsAtom (findAtom r)
-/
lemma isAtom_findAtom_iff {r : α} :
    IsAtom (findAtom r) ↔ r ≠ ⊥ where
  mpr := isAtom_findAtom
  mp h nh := by simp only [nh, findAtom_bot] at h; exact h.1 rfl

end DecidableEq

/-
**IsPredArchimedean.instIsAtomic** 是 Mathlib 中的一个实例，位于命名空间 `IsPredArchimedean`。
形式化陈述：instIsAtomic : IsAtomic α where eq_bot_or_exists_atom_le b
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `IsPredArchimedean.isAtom_findAtom`：isAtom_findAtom {r : α} (hr : r != ⊥)
 : IsAtom (findAtom r)
· 使用引理 `IsPredArchimedean.findAtom_le`：findAtom_le (r : α) : findAtom r <= r
-/
instance instIsAtomic : IsAtomic α where
  eq_bot_or_exists_atom_le b := by classical
    rw [or_iff_not_imp_left]
    intro hb
    use findAtom b, isAtom_findAtom hb, findAtom_le b

end IsPredArchimedean

/--
The type of rooted trees.
-/
/-
**RootedTree** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u_2 + 1)
参数：u_2 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of rooted trees.
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
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort RootedTree Type* := ⟨RootedTree.α⟩

attribute [instance] RootedTree.semilatticeInf RootedTree.predOrder
    RootedTree.orderBot RootedTree.isPredArchimedean

/--
A subtree is represented by its root, therefore this is a type synonym.
-/
/-
**SubRootedTree** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SubRootedTree (t : RootedTree) : Type*
参数：t : RootedTree。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtree is represented by its root, therefore this is a type synonym.
-/
def SubRootedTree (t : RootedTree) : Type* := t

/--
The root of a `SubRootedTree`.
-/
/-
**SubRootedTree.root** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SubRootedTree.root {t : RootedTree} (v : SubRootedTree t) : t
参数：v : SubRootedTree t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The root of a `SubRootedTree`.
-/
def SubRootedTree.root {t : RootedTree} (v : SubRootedTree t) : t := v

/--
The `SubRootedTree` rooted at a given node.
-/
/-
**RootedTree.subtree** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RootedTree.subtree (t : RootedTree) (r : t) : SubRootedTree t
参数：t : RootedTree；r : t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `SubRootedTree` rooted at a given node.
-/
def RootedTree.subtree (t : RootedTree) (r : t) : SubRootedTree t := r

@[simp]
/-
**RootedTree.root_subtree** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RootedTree.root_subtree (t : RootedTree) (r : t) : (t.subtree r).root = r
参数：t : RootedTree；r : t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RootedTree.root_subtree (t : RootedTree) (r : t) : (t.subtree r).root = r := rfl

@[simp]
/-
**RootedTree.subtree_root** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RootedTree.subtree_root (t : RootedTree) (v : SubRootedTree t) : t.subtree
 v.root = v
参数：t : RootedTree；v : SubRootedTree t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma RootedTree.subtree_root (t : RootedTree) (v : SubRootedTree t) : t.subtree v.root = v := rfl

@[ext]
/-
**SubRootedTree.ext** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SubRootedTree.ext {t : RootedTree} {v₁ v₂ : SubRootedTree t} (h : v₁.root 
= v₂.root) : v₁ = v₂
参数：h : v₁.root = v₂.root。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma SubRootedTree.ext {t : RootedTree} {v₁ v₂ : SubRootedTree t}
    (h : v₁.root = v₂.root) : v₁ = v₂ := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (t : RootedTree) : SetLike (SubRootedTree t) t where
  coe v := Set.Ici v.root
  coe_injective a₁ a₂ h := by
    simpa only [Set.Ici_inj, ← SubRootedTree.ext_iff] using h
/-
**SubRootedTree.mem_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SubRootedTree.mem_iff {t : RootedTree} {r : SubRootedTree t} {v : t} : v i
n r ↔ r.root <= v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma SubRootedTree.mem_iff {t : RootedTree} {r : SubRootedTree t} {v : t} :
    v ∈ r ↔ r.root ≤ v := Iff.rfl

/--
The coercion from a `SubRootedTree` to a `RootedTree`.
-/
@[coe, reducible]
/-
**SubRootedTree.coeTree** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SubRootedTree.coeTree {t : RootedTree} (r : SubRootedTree t) : RootedTree 
where α
参数：r : SubRootedTree t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from a `SubRootedTree` to a `RootedTree`.
-/
noncomputable def SubRootedTree.coeTree {t : RootedTree} (r : SubRootedTree t) : RootedTree where
  α := Set.Ici r.root
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance (t : RootedTree) : CoeOut (SubRootedTree t) RootedTree :=
  ⟨SubRootedTree.coeTree⟩

@[simp]
/-
**SubRootedTree.bot_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SubRootedTree.bot_mem_iff {t : RootedTree} (r : SubRootedTree t) : ⊥ in r 
↔ r.root = ⊥
参数：r : SubRootedTree t。
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
lemma SubRootedTree.bot_mem_iff {t : RootedTree} (r : SubRootedTree t) :
    ⊥ ∈ r ↔ r.root = ⊥ := by
  simp [mem_iff]

/--
All of the immediate subtrees of a given rooted tree, that is subtrees which are rooted at a direct
child of the root (or, order-theoretically, at an atom).
-/
/-
**RootedTree.subtrees** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RootedTree.subtrees (t : RootedTree) : Set (SubRootedTree t)
参数：t : RootedTree。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All of the immediate subtrees of a given rooted tree, that is subtrees which are
 rooted at a direct
child of the root (or, order-theoretically, at an atom).
-/
def RootedTree.subtrees (t : RootedTree) : Set (SubRootedTree t) :=
  {x | IsAtom x.root}

variable {t : RootedTree}
/-
**SubRootedTree.root_ne_bot_of_mem_subtrees** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：SubRootedTree.root_ne_bot_of_mem_subtrees (r : SubRootedTree t) (hr : r in
 t.subtrees) : r.root != ⊥
参数：r : SubRootedTree t；hr : r in t.subtrees。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma SubRootedTree.root_ne_bot_of_mem_subtrees (r : SubRootedTree t) (hr : r ∈ t.subtrees) :
    r.root ≠ ⊥ := by
  simp only [RootedTree.subtrees, Set.mem_ofPred_eq] at hr
  exact hr.1
/-
**RootedTree.mem_subtrees_disjoint_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RootedTree.mem_subtrees_disjoint_iff {t₁ t₂ : SubRootedTree t} (ht₁ : t₁ i
n t.subtrees) (ht₂ : t₂ in t.subtrees) (v₁ v₂ : t) (h₁ : v₁ in t₁) (h₂ : v₂ in t
₂) : Disjoint v₁ v₂ ↔ t₁ != t₂ where mp h
参数：ht₁ : t₁ in t.subtrees；ht₂ : t₂ in t.subtrees；v₁ v₂ : t；h₁ : v₁ in t₁；h₂ : v₂
 in t₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SubRootedTree.root_ne_bot_of_mem_subtrees`：SubRootedTree.root_ne_bot_of_
mem_subtrees (r : SubRootedTree t) (hr : r in t.subtrees) : r.root != ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `lt_or_le_of_directed`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 :
 PredOrder α] [IsPredArchimedean α] {r v₁ v₂ : α},   v₂ ≤ r → v₁ ≤ r → v₂ < v₁ ∨
 v₁ ≤ v₂
· 使用定理 `RootedTree.isPredArchimedean`：∀ (self : RootedTree), IsPredArchimedean ↑
self
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `SubRootedTree.mem_iff`：SubRootedTree.mem_iff {t : RootedTree} {r : SubRo
otedTree t} {v : t} : v in r ↔ r.root <= v
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用引理 `SubRootedTree.ext`：SubRootedTree.ext {t : RootedTree} {v₁ v₂ : SubRooted
Tree t} (h : v₁.root = v₂.root) : v₁ = v₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `IsAtom.le_iff_eq`：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= 
a ↔ b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `le_total_of_directed`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : Pre
dOrder α] [IsPredArchimedean α] {r v₁ v₂ : α},   v₁ ≤ r → v₂ ≤ r → v₂ ≤ v₁ ∨ v₁ 
≤ v₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
-/
lemma RootedTree.mem_subtrees_disjoint_iff {t₁ t₂ : SubRootedTree t}
    (ht₁ : t₁ ∈ t.subtrees) (ht₂ : t₂ ∈ t.subtrees) (v₁ v₂ : t) (h₁ : v₁ ∈ t₁)
    (h₂ : v₂ ∈ t₂) :
    Disjoint v₁ v₂ ↔ t₁ ≠ t₂ where
  mp h := by
    intro nh
    have : t₁.root ≤ (v₁ : t) ⊓ (v₂ : t) := by
      simp only [le_inf_iff]
      exact ⟨h₁, nh ▸ h₂⟩
    rw [h.eq_bot] at this
    simp only [le_bot_iff] at this
    exact t₁.root_ne_bot_of_mem_subtrees ht₁ this
  mpr h := by
    rw [SubRootedTree.mem_iff] at h₁ h₂
    contrapose h
    rw [disjoint_iff, ← ne_eq, ← bot_lt_iff_ne_bot] at h
    rcases lt_or_le_of_directed (by simp : v₁ ⊓ v₂ ≤ v₁) h₁ with oh | oh
    · simp_all [RootedTree.subtrees, IsAtom.lt_iff]
    rw [le_inf_iff] at oh
    ext
    simpa only [ht₂.le_iff_eq ht₁.1, ht₁.le_iff_eq ht₂.1, eq_comm, or_self] using
      le_total_of_directed oh.2 h₂
/-
**RootedTree.subtrees_disjoint** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RootedTree.subtrees_disjoint : t.subtrees.PairwiseDisjoint ((↑) : _ -> Set
 t)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.onFun_apply`：onFun_apply (f : β -> β -> γ) (g : α -> β) (a b : 
α) : onFun f g a b = f (g a) (g b)
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用引理 `SubRootedTree.root_ne_bot_of_mem_subtrees`：SubRootedTree.root_ne_bot_of_
mem_subtrees (r : SubRootedTree t) (hr : r in t.subtrees) : r.root != ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `disjoint_self`：disjoint_self : Disjoint a a ↔ a = ⊥
· 使用引理 `RootedTree.mem_subtrees_disjoint_iff`：RootedTree.mem_subtrees_disjoint_i
ff {t₁ t₂ : SubRootedTree t} (ht₁ : t₁ in t.subtrees) (ht₂ : t₂ in t.subtrees) (
v₁ v₂ : t) (h₁ : v₁ in t₁)…
-/
lemma RootedTree.subtrees_disjoint : t.subtrees.PairwiseDisjoint ((↑) : _ → Set t) := by
  intro t₁ ht₁ t₂ ht₂ h
  rw [Function.onFun_apply, Set.disjoint_left]
  intro a ha hb
  rw [← mem_subtrees_disjoint_iff ht₁ ht₂ a a ha hb, disjoint_self] at h
  subst h
  simp only [SetLike.mem_coe, SubRootedTree.bot_mem_iff] at ha
  exact t₁.root_ne_bot_of_mem_subtrees ht₁ ha

/--
The immediate subtree of `t` containing `v`, or all of `t` if `v` is the root.
-/
/-
**RootedTree.subtreeOf** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RootedTree.subtreeOf (t : RootedTree) [DecidableEq t] (v : t) : SubRootedT
ree t
参数：t : RootedTree；v : t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootedTree.isPredArchimedean`：∀ (self : RootedTree), IsPredArchimedean ↑
self

--- 原说明 ---
The immediate subtree of `t` containing `v`, or all of `t` if `v` is the root.
-/
def RootedTree.subtreeOf (t : RootedTree) [DecidableEq t] (v : t) : SubRootedTree t :=
  t.subtree (IsPredArchimedean.findAtom v)

@[simp]
/-
**RootedTree.mem_subtreeOf** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RootedTree.mem_subtreeOf [DecidableEq t] {v : t} : v in t.subtreeOf v
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RootedTree.isPredArchimedean`：∀ (self : RootedTree), IsPredArchimedean ↑
self
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma RootedTree.mem_subtreeOf [DecidableEq t] {v : t} :
    v ∈ t.subtreeOf v := by
  simp [SubRootedTree.mem_iff, RootedTree.subtreeOf]
/-
**RootedTree.subtreeOf_mem_subtrees** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RootedTree.subtreeOf_mem_subtrees [DecidableEq t] {v : t} (hr : v != ⊥) : 
t.subtreeOf v in t.subtrees
参数：hr : v != ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootedTree.isPredArchimedean`：∀ (self : RootedTree), IsPredArchimedean ↑
self
-/
lemma RootedTree.subtreeOf_mem_subtrees [DecidableEq t] {v : t} (hr : v ≠ ⊥) :
    t.subtreeOf v ∈ t.subtrees := by
  simpa [RootedTree.subtrees, RootedTree.subtreeOf]
