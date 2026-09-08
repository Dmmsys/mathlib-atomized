/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.Nat.Dist
public import Mathlib.Data.Ordmap.Ordnode
public import Mathlib.Tactic.Abel

/-!
# Invariants for the verification of `Ordnode`

An `Ordnode`, defined in `Mathlib/Data/Ordmap/Ordnode.lean`, is an inductive type which describes a
tree which stores the `size` at internal nodes.

In this file we define the correctness invariant of an `Ordnode`, comprising:

* `Ordnode.Sized t`: All internal `size` fields must match the actual measured
  size of the tree. (This is not hard to satisfy.)
* `Ordnode.Balanced t`: Unless the tree has the form `()` or `((a) b)` or `(a (b))`
  (that is, nil or a single singleton subtree), the two subtrees must satisfy
  `size l ≤ δ * size r` and `size r ≤ δ * size l`, where `δ := 3` is a global
  parameter of the data structure (and this property must hold recursively at subtrees).
  This is why we say this is a "size balanced tree" data structure.
* `Ordnode.Bounded lo hi t`: The members of the tree must be in strictly increasing order,
  meaning that if `a` is in the left subtree and `b` is the root, then `a ≤ b` and
  `¬(b ≤ a)`. We enforce this using `Ordnode.Bounded` which includes also a global
  upper and lower bound.

This whole file is in the `Ordnode` namespace, because we first have to prove the correctness of
all the operations (and defining what correctness means here is somewhat subtle).
The actual `Ordset` operations are in `Mathlib/Data/Ordmap/Ordset.lean`.

## TODO

This file is incomplete, in the sense that the intent is to have verified
versions and lemmas about all the definitions in `Ordnode.lean`, but at the moment only
a few operations are verified (the hard part should be out of the way, but still).
Contributors are encouraged to pick this up and finish the job, if it appeals to you.

## Tags

ordered map, ordered set, data structure, verified programming
-/

@[expose] public section


variable {α : Type*}

namespace Ordnode

/-! ### delta and ratio -/


/-
**Ordnode.not_le_delta** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：not_le_delta {s} (H : 1 <= s) : ¬s <= delta * 0
参数：H : 1 <= s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a

--- 原说明 ---
### delta and ratio
-/
theorem not_le_delta {s} (H : 1 ≤ s) : ¬s ≤ delta * 0 :=
  not_le_of_gt H
/-
**Ordnode.delta_lt_false** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：delta_lt_false {a b : Nat} (h₁ : delta * a < b) (h₂ : delta * b < a) : Fal
se
参数：h₁ : delta * a < b；h₂ : delta * b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
-/
theorem delta_lt_false {a b : ℕ} (h₁ : delta * a < b) (h₂ : delta * b < a) : False :=
  not_le_of_gt (lt_trans (mul_lt_mul_of_pos_left h₁ <| by decide) h₂) <| by
    simpa [mul_assoc] using Nat.mul_le_mul_right a (by decide : 1 ≤ delta * delta)

/-! ### `singleton` -/


/-! ### `size` and `empty` -/


/-- O(n). Computes the actual number of elements in the set, ignoring the cached `size` field. -/
/-
**Ordnode.realSize** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：{α : Type u_1} → Ordnode α → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
O(n). Computes the actual number of elements in the set, ignoring the cached `si
ze` field.
-/
def realSize : Ordnode α → ℕ
  | nil => 0
  | node _ l _ r => realSize l + realSize r + 1

/-! ### `Sized` -/


/-- The `Sized` property asserts that all the `size` fields in nodes match the actual size of the
respective subtrees. -/
/-
**Ordnode.Sized** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：{α : Type u_1} → Ordnode α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Sized` property asserts that all the `size` fields in nodes match the actua
l size of the
respective subtrees.
-/
def Sized : Ordnode α → Prop
  | nil => True
  | node s l _ r => s = size l + size r + 1 ∧ Sized l ∧ Sized r
/-
**Ordnode.Sized.node'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → r.Size
d → (l.node' x r).Sized
参数：l.node' x r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sized.node' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (node' l x r) :=
  ⟨rfl, hl, hr⟩
/-
**Ordnode.Sized.eq_node'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α},   (Ordno
de.node s l x r).Sized → Ordnode.node s l x r = l.node' x r
参数：Ordnode.node s l x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Sized.eq_node' {s l x r} (h : @Sized α (node s l x r)) : node s l x r = .node' l x r := by
  rw [h.1]
/-
**Ordnode.Sized.size_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α},   (Ordno
de.node s l x r).Sized → (Ordnode.node s l x r).size = l.size + r.size + 1
参数：Ordnode.node s l x r；Ordnode.node s l x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem Sized.size_eq {s l x r} (H : Sized (@node α s l x r)) :
    size (@node α s l x r) = size l + size r + 1 :=
  H.1

@[elab_as_elim]
/-
**Ordnode.Sized.induction** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {t : Ordnode α},   t.Sized →     ∀ {C : Ordnode α → Prop}
,       C Ordnode.nil → (∀ (l : Ordnode α) (x : α) (r : Ordnode α), C l → C r → 
C (l.node' x r)) → C t
参数：∀ (l : Ordnode α) (x : α) (r : Ordnode α), C l → C r → C (l.node' x r)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.Sized.eq_node'`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α}
 {r : Ordnode α},   (Ordnode.node s l x r).Sized → Ordnode.node s l x r = l.node
' x r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Sized.induction {t} (hl : @Sized α t) {C : Ordnode α → Prop} (H0 : C nil)
    (H1 : ∀ l x r, C l → C r → C (.node' l x r)) : C t := by
  induction t with
  | nil => exact H0
  | node _ _ _ _ t_ih_l t_ih_r =>
    rw [hl.eq_node']
    exact H1 _ _ _ (t_ih_l hl.2.1) (t_ih_r hl.2.2)
/-
**Ordnode.size_eq_realSize** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → t.size = t.realSize
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem size_eq_realSize : ∀ {t : Ordnode α}, Sized t → size t = realSize t
  | nil, _ => rfl
  | node s l x r, ⟨h₁, h₂, h₃⟩ => by
    rw [size, h₁, size_eq_realSize h₂, size_eq_realSize h₃]; rfl

@[simp]
/-
**Ordnode.Sized.size_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → (t.size = 0 ↔ t = Ordnode.nil)
参数：t.size = 0 ↔ t = Ordnode.nil。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem Sized.size_eq_zero {t : Ordnode α} (ht : Sized t) : size t = 0 ↔ t = nil := by
  cases t <;> [simp; simp [ht.1]]
/-
**Ordnode.Sized.pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α} {r : Ordnode α}, (Ordnode
.node s l x r).Sized → 0 < s
参数：Ordnode.node s l x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
-/
theorem Sized.pos {s l x r} (h : Sized (@node α s l x r)) : 0 < s := by
  rw [h.1]; apply Nat.le_add_left

/-! `dual` -/


/-
**Ordnode.dual_dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
参数：t : Ordnode α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dual`
-/
theorem dual_dual : ∀ t : Ordnode α, dual (dual t) = t
  | nil => rfl
  | node s l x r => by rw [dual, dual, dual_dual l, dual_dual r]

@[simp]
/-
**Ordnode.size_dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：size_dual (t : Ordnode α) : size (dual t) = size t
参数：t : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem size_dual (t : Ordnode α) : size (dual t) = size t := by cases t <;> rfl

/-! `Balanced` -/


/-- The `BalancedSz l r` asserts that a hypothetical tree with children of sizes `l` and `r` is
balanced: either `l ≤ δ * r` and `r ≤ δ * r`, or the tree is trivial with a singleton on one side
and nothing on the other. -/
/-
**Ordnode.BalancedSz** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：BalancedSz (l r : Nat) : Prop
参数：l r : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `BalancedSz l r` asserts that a hypothetical tree with children of sizes `l`
 and `r` is
balanced: either `l ≤ δ * r` and `r ≤ δ * r`, or the tree is trivial with a sing
leton on one side
and nothing on the other.
-/
def BalancedSz (l r : ℕ) : Prop :=
  l + r ≤ 1 ∨ l ≤ delta * r ∧ r ≤ delta * l
/-
**Ordnode.BalancedSz.dec** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode.BalancedSz`。
形式化陈述：DecidableRel Ordnode.BalancedSz
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance BalancedSz.dec : DecidableRel BalancedSz := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The `Balanced t` asserts that the tree `t` satisfies the balance invariants
(at every level). -/
/-
**Ordnode.Balanced** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：{α : Type u_1} → Ordnode α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Balanced t` asserts that the tree `t` satisfies the balance invariants
(at every level).
-/
def Balanced : Ordnode α → Prop
  | nil => True
  | node _ l _ r => BalancedSz (size l) (size r) ∧ Balanced l ∧ Balanced r
/-
**Ordnode.Balanced.dec** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode.Balanced`。
形式化陈述：{α : Type u_1} → DecidablePred Ordnode.Balanced
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Balanced.dec : DecidablePred (@Balanced α)
  | nil => inferInstanceAs <| Decidable True
  | node _ l _ r =>
    haveI := Balanced.dec l
    haveI := Balanced.dec r
    inferInstanceAs <| Decidable (BalancedSz l.size r.size ∧ l.Balanced ∧ r.Balanced)

@[symm]
/-
**Ordnode.BalancedSz.symm** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.BalancedSz`。
形式化陈述：∀ {l r : ℕ}, Ordnode.BalancedSz l r → Ordnode.BalancedSz r l
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `And.symm`：∀ {a b : Prop}, a ∧ b → b ∧ a
-/
theorem BalancedSz.symm {l r : ℕ} : BalancedSz l r → BalancedSz r l :=
  Or.imp (by rw [add_comm]; exact id) And.symm
/-
**Ordnode.balancedSz_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：balancedSz_zero {l : Nat} : BalancedSz l 0 ↔ l <= 1
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem balancedSz_zero {l : ℕ} : BalancedSz l 0 ↔ l ≤ 1 := by
  simp +contextual [BalancedSz]
/-
**Ordnode.balancedSz_up** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：balancedSz_up {l r₁ r₂ : Nat} (h₁ : r₁ <= r₂) (h₂ : l + r₂ <= 1 ∨ r₂ <= de
lta * l) (H : BalancedSz l r₁) : BalancedSz l r₂
参数：h₁ : r₁ <= r₂；h₂ : l + r₂ <= 1 ∨ r₂ <= delta * l；H : BalancedSz l r₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.add_le_add_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k + n ≤ k + m
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
-/
theorem balancedSz_up {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : l + r₂ ≤ 1 ∨ r₂ ≤ delta * l)
    (H : BalancedSz l r₁) : BalancedSz l r₂ := by
  refine or_iff_not_imp_left.2 fun h => ?_
  refine ⟨?_, h₂.resolve_left h⟩
  cases H with
  | inl H =>
    cases r₂
    · cases h (le_trans (Nat.add_le_add_left (Nat.zero_le _) _) H)
    · exact le_trans (le_trans (Nat.le_add_right _ _) H) (Nat.le_add_left 1 _)
  | inr H =>
    exact le_trans H.1 (Nat.mul_le_mul_left _ h₁)
/-
**Ordnode.balancedSz_down** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：balancedSz_down {l r₁ r₂ : Nat} (h₁ : r₁ <= r₂) (h₂ : l + r₂ <= 1 ∨ l <= d
elta * r₁) (H : BalancedSz l r₂) : BalancedSz l r₁
参数：h₁ : r₁ <= r₂；h₂ : l + r₂ <= 1 ∨ l <= delta * r₁；H : BalancedSz l r₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.add_le_add_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k + n ≤ k + m
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem balancedSz_down {l r₁ r₂ : ℕ} (h₁ : r₁ ≤ r₂) (h₂ : l + r₂ ≤ 1 ∨ l ≤ delta * r₁)
    (H : BalancedSz l r₂) : BalancedSz l r₁ :=
  have : l + r₂ ≤ 1 → BalancedSz l r₁ := fun H => Or.inl (le_trans (Nat.add_le_add_left h₁ _) H)
  Or.casesOn H this fun H => Or.casesOn h₂ this fun h₂ => Or.inr ⟨h₂, le_trans h₁ H.2⟩
/-
**Ordnode.Balanced.dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Balanced`。
形式化陈述：∀ {α : Type u_1} {t : Ordnode α}, t.Balanced → t.dual.Balanced
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Balanced.dual : ∀ {t : Ordnode α}, Balanced t → Balanced (dual t)
  | nil, _ => ⟨⟩
  | node _ l _ r, ⟨b, bl, br⟩ => ⟨by rw [size_dual, size_dual]; exact b.symm, br.dual, bl.dual⟩

/-! ### `rotate` and `balance` -/


/-- Build a tree from three nodes, left associated (ignores the invariants). -/
/-
**Ordnode.node3L** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : O
rdnode α
参数：l : Ordnode α；x : α；m : Ordnode α；y : α；r : Ordnode α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a tree from three nodes, left associated (ignores the invariants).
-/
def node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' (node' l x m) y r

/-- Build a tree from three nodes, right associated (ignores the invariants). -/
/-
**Ordnode.node3R** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : O
rdnode α
参数：l : Ordnode α；x : α；m : Ordnode α；y : α；r : Ordnode α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a tree from three nodes, right associated (ignores the invariants).
-/
def node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) : Ordnode α :=
  node' l x (node' m y r)

/-- Build a tree from three nodes, with `a () b -> (a ()) b` and `a (b c) d -> ((a b) (c d))`. -/
/-
**Ordnode.node4L** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：{α : Type u_1} → Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a tree from three nodes, with `a () b -> (a ()) b` and `a (b c) d -> ((a b
) (c d))`.
-/
def node4L : Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
  | l, x, nil, z, r => node3L l x nil z r

-- should not happen
/-- Build a tree from three nodes, with `a () b -> a (() b)` and `a (b c) d -> ((a b) (c d))`. -/
/-
**Ordnode.node4R** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：{α : Type u_1} → Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Build a tree from three nodes, with `a () b -> a (() b)` and `a (b c) d -> ((a b
) (c d))`.
-/
def node4R : Ordnode α → α → Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ ml y mr, z, r => node' (node' l x ml) y (node' mr z r)
  | l, x, nil, z, r => node3R l x nil z r

-- should not happen
/-- Concatenate two nodes, performing a left rotation `x (y z) -> ((x y) z)`
if balance is upset. -/
/-
**Ordnode.rotateL** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：{α : Type u_1} → Ordnode α → α → Ordnode α → Ordnode α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Concatenate two nodes, performing a left rotation `x (y z) -> ((x y) z)`
if balance is upset.
-/
def rotateL : Ordnode α → α → Ordnode α → Ordnode α
  | l, x, node _ m y r => if size m < ratio * size r then node3L l x m y r else node4L l x m y r
  | l, x, nil => node' l x nil
/-
**Ordnode.rotateL_node** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：rotateL_node (l : Ordnode α) (x : α) (sz : Nat) (m : Ordnode α) (y : α) (r
 : Ordnode α) : rotateL l x (node sz m y r) = if size m < ratio * size r then no
de3L l x m y r else node4L l x m y r
参数：l : Ordnode α；x : α；sz : Nat；m : Ordnode α；y : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rotateL_node (l : Ordnode α) (x : α) (sz : ℕ) (m : Ordnode α) (y : α) (r : Ordnode α) :
    rotateL l x (node sz m y r) =
      if size m < ratio * size r then node3L l x m y r else node4L l x m y r :=
  rfl
/-
**Ordnode.rotateL_nil** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：rotateL_nil (l : Ordnode α) (x : α) : rotateL l x nil = node' l x nil
参数：l : Ordnode α；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rotateL_nil (l : Ordnode α) (x : α) : rotateL l x nil = node' l x nil :=
  rfl

-- should not happen
/-- Concatenate two nodes, performing a right rotation `(x y) z -> (x (y z))`
if balance is upset. -/
/-
**Ordnode.rotateR** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：{α : Type u_1} → Ordnode α → α → Ordnode α → Ordnode α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Concatenate two nodes, performing a right rotation `(x y) z -> (x (y z))`
if balance is upset.
-/
def rotateR : Ordnode α → α → Ordnode α → Ordnode α
  | node _ l x m, y, r => if size m < ratio * size l then node3R l x m y r else node4R l x m y r
  | nil, y, r => node' nil y r
/-
**Ordnode.rotateR_node** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：rotateR_node (sz : Nat) (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r
 : Ordnode α) : rotateR (node sz l x m) y r = if size m < ratio * size l then no
de3R l x m y r else node4R l x m y r
参数：sz : Nat；l : Ordnode α；x : α；m : Ordnode α；y : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rotateR_node (sz : ℕ) (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    rotateR (node sz l x m) y r =
      if size m < ratio * size l then node3R l x m y r else node4R l x m y r :=
  rfl
/-
**Ordnode.rotateR_nil** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：rotateR_nil (y : α) (r : Ordnode α) : rotateR nil y r = node' nil y r
参数：y : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rotateR_nil (y : α) (r : Ordnode α) : rotateR nil y r = node' nil y r :=
  rfl

-- should not happen
/-- A left balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
/-
**Ordnode.balanceL'** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：balanceL' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α
参数：l : Ordnode α；x : α；r : Ordnode α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A left balance operation. This will rebalance a concatenation, assuming the orig
inal nodes are
not too far from balanced.
-/
def balanceL' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r
  else if size l > delta * size r then rotateR l x r else node' l x r

/-- A right balance operation. This will rebalance a concatenation, assuming the original nodes are
not too far from balanced. -/
/-
**Ordnode.balanceR'** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：balanceR' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α
参数：l : Ordnode α；x : α；r : Ordnode α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A right balance operation. This will rebalance a concatenation, assuming the ori
ginal nodes are
not too far from balanced.
-/
def balanceR' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r
  else if size r > delta * size l then rotateL l x r else node' l x r

/-- The full balance operation. This is the same as `balance`, but with less manual inlining.
It is somewhat easier to work with this version in proofs. -/
/-
**Ordnode.balance'** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：balance' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α
参数：l : Ordnode α；x : α；r : Ordnode α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full balance operation. This is the same as `balance`, but with less manual 
inlining.
It is somewhat easier to work with this version in proofs.
-/
def balance' (l : Ordnode α) (x : α) (r : Ordnode α) : Ordnode α :=
  if size l + size r ≤ 1 then node' l x r
  else
    if size r > delta * size l then rotateL l x r
    else if size l > delta * size r then rotateR l x r else node' l x r
/-
**Ordnode.dual_node'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_node' (l : Ordnode α) (x : α) (r : Ordnode α) : dual (node' l x r) = 
node' (dual r) x (dual l)
参数：l : Ordnode α；x : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dual_node' (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (node' l x r) = node' (dual r) x (dual l) := by simp [node', add_comm]
/-
**Ordnode.dual_node3L** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α
) : dual (node3L l x m y r) = node3R (dual r) y (dual m) x (dual l)
参数：l : Ordnode α；x : α；m : Ordnode α；y : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.dual.eq_2`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x_1 : α) (
r : Ordnode α),   (Ordnode.node sz l x_1 r).dual = Ordnode.node sz r.dual x_1 l.
dual
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.node.injEq`：∀ {α : Type u} (size : ℕ) (l : Ordnode α) (x : α) (r
 : Ordnode α) (size_1 : ℕ) (l_1 : Ordnode α) (x_1 : α)   (r_1 : Ordnode α),   (O
rdnode.n…
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem dual_node3L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3L l x m y r) = node3R (dual r) y (dual m) x (dual l) := by
  simp [node3L, node3R, add_comm]
/-
**Ordnode.dual_node3R** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α
) : dual (node3R l x m y r) = node3L (dual r) y (dual m) x (dual l)
参数：l : Ordnode α；x : α；m : Ordnode α；y : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.dual.eq_2`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x_1 : α) (
r : Ordnode α),   (Ordnode.node sz l x_1 r).dual = Ordnode.node sz r.dual x_1 l.
dual
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.node.injEq`：∀ {α : Type u} (size : ℕ) (l : Ordnode α) (x : α) (r
 : Ordnode α) (size_1 : ℕ) (l_1 : Ordnode α) (x_1 : α)   (r_1 : Ordnode α),   (O
rdnode.n…
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem dual_node3R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node3R l x m y r) = node3L (dual r) y (dual m) x (dual l) := by
  simp [node3L, node3R, add_comm]
/-
**Ordnode.dual_node4L** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_node4L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α
) : dual (node4L l x m y r) = node4R (dual r) y (dual m) x (dual l)
参数：l : Ordnode α；x : α；m : Ordnode α；y : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.dual_node3L`：dual_node3L (l : Ordnode α) (x : α) (m : Ordnode α)
 (y : α) (r : Ordnode α) : dual (node3L l x m y r) = node3R (dual r) y (dual m) 
x (dual l…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.dual.eq_2`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x_1 : α) (
r : Ordnode α),   (Ordnode.node sz l x_1 r).dual = Ordnode.node sz r.dual x_1 l.
dual
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.node.injEq`：∀ {α : Type u} (size : ℕ) (l : Ordnode α) (x : α) (r
 : Ordnode α) (size_1 : ℕ) (l_1 : Ordnode α) (x_1 : α)   (r_1 : Ordnode α),   (O
rdnode.n…
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem dual_node4L (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4L l x m y r) = node4R (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [node4L, node4R, node3R, dual_node3L, add_comm]
/-
**Ordnode.dual_node4R** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_node4R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α
) : dual (node4R l x m y r) = node4L (dual r) y (dual m) x (dual l)
参数：l : Ordnode α；x : α；m : Ordnode α；y : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.dual_node3R`：dual_node3R (l : Ordnode α) (x : α) (m : Ordnode α)
 (y : α) (r : Ordnode α) : dual (node3R l x m y r) = node3L (dual r) y (dual m) 
x (dual l…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.dual.eq_2`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x_1 : α) (
r : Ordnode α),   (Ordnode.node sz l x_1 r).dual = Ordnode.node sz r.dual x_1 l.
dual
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.node.injEq`：∀ {α : Type u} (size : ℕ) (l : Ordnode α) (x : α) (r
 : Ordnode α) (size_1 : ℕ) (l_1 : Ordnode α) (x_1 : α)   (r_1 : Ordnode α),   (O
rdnode.n…
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem dual_node4R (l : Ordnode α) (x : α) (m : Ordnode α) (y : α) (r : Ordnode α) :
    dual (node4R l x m y r) = node4L (dual r) y (dual m) x (dual l) := by
  cases m <;> simp [node4L, node4R, node3L, dual_node3R, add_comm]
/-
**Ordnode.dual_rotateL** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_rotateL (l : Ordnode α) (x : α) (r : Ordnode α) : dual (rotateL l x r
) = rotateR (dual r) x (dual l)
参数：l : Ordnode α；x : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.dual.eq_2`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x_1 : α) (
r : Ordnode α),   (Ordnode.node sz l x_1 r).dual = Ordnode.node sz r.dual x_1 l.
dual
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Ordnode.node.injEq`：∀ {α : Type u} (size : ℕ) (l : Ordnode α) (x : α) (r
 : Ordnode α) (size_1 : ℕ) (l_1 : Ordnode α) (x_1 : α)   (r_1 : Ordnode α),   (O
rdnode.n…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ordnode.dual_node3L`：dual_node3L (l : Ordnode α) (x : α) (m : Ordnode α)
 (y : α) (r : Ordnode α) : dual (node3L l x m y r) = node3R (dual r) y (dual m) 
x (dual l…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.dual_node4L`：dual_node4L (l : Ordnode α) (x : α) (m : Ordnode α)
 (y : α) (r : Ordnode α) : dual (node4L l x m y r) = node4R (dual r) y (dual m) 
x (dual l…
-/
theorem dual_rotateL (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (rotateL l x r) = rotateR (dual r) x (dual l) := by
  cases r <;> simp [rotateL, rotateR]; split_ifs <;>
    simp [dual_node3L, dual_node4L, node3R]
/-
**Ordnode.dual_rotateR** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode α) : dual (rotateR l x r
) = rotateL (dual r) x (dual l)
参数：l : Ordnode α；x : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
· 使用定理 `Ordnode.dual_rotateL`：dual_rotateL (l : Ordnode α) (x : α) (r : Ordnode 
α) : dual (rotateL l x r) = rotateR (dual r) x (dual l)
-/
theorem dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (rotateR l x r) = rotateL (dual r) x (dual l) := by
  rw [← dual_dual (rotateL _ _ _), dual_rotateL, dual_dual, dual_dual]
/-
**Ordnode.dual_balance'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_balance' (l : Ordnode α) (x : α) (r : Ordnode α) : dual (balance' l x
 r) = balance' (dual r) x (dual l)
参数：l : Ordnode α；x : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ordnode.node.injEq`：∀ {α : Type u} (size : ℕ) (l : Ordnode α) (x : α) (r
 : Ordnode α) (size_1 : ℕ) (l_1 : Ordnode α) (x_1 : α)   (r_1 : Ordnode α),   (O
rdnode.n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.dual_rotateL`：dual_rotateL (l : Ordnode α) (x : α) (r : Ordnode 
α) : dual (rotateL l x r) = rotateR (dual r) x (dual l)
· 使用定理 `Ordnode.delta_lt_false`：delta_lt_false {a b : Nat} (h₁ : delta * a < b) 
(h₂ : delta * b < a) : False
· 使用定理 `Ordnode.dual_rotateR`：dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode 
α) : dual (rotateR l x r) = rotateL (dual r) x (dual l)
-/
theorem dual_balance' (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balance' l x r) = balance' (dual r) x (dual l) := by
  simp [balance', add_comm]; split_ifs with h h_1 h_2 <;>
    simp [dual_rotateL, dual_rotateR, add_comm]
  cases delta_lt_false h_1 h_2
/-
**Ordnode.dual_balanceL** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_balanceL (l : Ordnode α) (x : α) (r : Ordnode α) : dual (balanceL l x
 r) = balanceR (dual r) x (dual l)
参数：l : Ordnode α；x : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
-/
theorem dual_balanceL (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balanceL l x r) = balanceR (dual r) x (dual l) := by
  unfold balanceL balanceR
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · obtain - | ⟨ls, ll, lx, lr⟩ := l; · rfl
    obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;>
      dsimp only [dual, id] <;> try rfl
    split_ifs with h <;> repeat simp [add_comm]
  · obtain - | ⟨ls, ll, lx, lr⟩ := l; · rfl
    dsimp only [dual, id]
    split_ifs; swap; · simp [add_comm]
    obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;> try rfl
    dsimp only [dual, id]
    split_ifs with h <;> simp [add_comm]
/-
**Ordnode.dual_balanceR** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_balanceR (l : Ordnode α) (x : α) (r : Ordnode α) : dual (balanceR l x
 r) = balanceL (dual r) x (dual l)
参数：l : Ordnode α；x : α；r : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
· 使用定理 `Ordnode.dual_balanceL`：dual_balanceL (l : Ordnode α) (x : α) (r : Ordnod
e α) : dual (balanceL l x r) = balanceR (dual r) x (dual l)
-/
theorem dual_balanceR (l : Ordnode α) (x : α) (r : Ordnode α) :
    dual (balanceR l x r) = balanceL (dual r) x (dual l) := by
  rw [← dual_dual (balanceL _ _ _), dual_balanceL, dual_dual, dual_dual]
/-
**Ordnode.Sized.node3L** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordn
ode α},   l.Sized → m.Sized → r.Sized → (l.node3L x m y r).Sized
参数：l.node3L x m y r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Sized.node'`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordno
de α}, l.Sized → r.Sized → (l.node' x r).Sized
-/
theorem Sized.node3L {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node3L l x m y r) :=
  (hl.node' hm).node' hr
/-
**Ordnode.Sized.node3R** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordn
ode α},   l.Sized → m.Sized → r.Sized → (l.node3R x m y r).Sized
参数：l.node3R x m y r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Sized.node'`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordno
de α}, l.Sized → r.Sized → (l.node' x r).Sized
-/
theorem Sized.node3R {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node3R l x m y r) :=
  hl.node' (hm.node' hr)
/-
**Ordnode.Sized.node4L** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {m : Ordnode α} {y : α} {r : Ordn
ode α},   l.Sized → m.Sized → r.Sized → (l.node4L x m y r).Sized
参数：l.node4L x m y r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Sized.node'`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordno
de α}, l.Sized → r.Sized → (l.node' x r).Sized
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Sized.node4L {l x m y r} (hl : @Sized α l) (hm : Sized m) (hr : Sized r) :
    Sized (node4L l x m y r) := by
  cases m <;> [exact (hl.node' hm).node' hr; exact (hl.node' hm.2.1).node' (hm.2.2.node' hr)]
/-
**Ordnode.node3L_size** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：node3L_size {l x m y r} : size (@node3L α l x m y r) = size l + size m + s
ize r + 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
theorem node3L_size {l x m y r} : size (@node3L α l x m y r) = size l + size m + size r + 2 := by
  dsimp [node3L, node', size]; rw [add_right_comm _ 1]
/-
**Ordnode.node3R_size** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：node3R_size {l x m y r} : size (@node3R α l x m y r) = size l + size m + s
ize r + 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
theorem node3R_size {l x m y r} : size (@node3R α l x m y r) = size l + size m + size r + 2 := by
  dsimp [node3R, node', size]; rw [← add_assoc, ← add_assoc]
/-
**Ordnode.node4L_size** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：node4L_size {l x m y r} (hm : Sized m) : size (@node4L α l x m y r) = size
 l + size m + size r + 2
参数：hm : Sized m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `_private.Mathlib.Data.Ordmap.Invariants.0.Ordnode.node4L_size._abel_1_5`
：∀ {α : Type u_1} {l r : Ordnode α}, l.size + 1 + r.size = l.size + r.size + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.Data.Ordmap.Invariants.0.Ordnode.node4L_size._abel_1_9`
：∀ {α : Type u_1} {l r : Ordnode α} (l_1 r_1 : Ordnode α),   ((match l with     
      | Ordnode.nil => 0           | Ordnode.node sz l x r =>…
-/
theorem node4L_size {l x m y r} (hm : Sized m) :
    size (@node4L α l x m y r) = size l + size m + size r + 2 := by
  cases m
  · simp [node4L, node3L, node']
    abel
  · simp [node4L, node', size, hm.1]; abel
/-
**Ordnode.Sized.dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → t.dual.Sized
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sized.dual : ∀ {t : Ordnode α}, Sized t → Sized (dual t)
  | nil, _ => ⟨⟩
  | node _ l _ r, ⟨rfl, sl, sr⟩ => ⟨by simp [size_dual, add_comm], Sized.dual sr, Sized.dual sl⟩
/-
**Ordnode.Sized.dual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {t : Ordnode α}, t.dual.Sized ↔ t.Sized
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
· 使用定理 `Ordnode.Sized.dual`：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → t.dual.S
ized
-/
theorem Sized.dual_iff {t : Ordnode α} : Sized (.dual t) ↔ Sized t :=
  ⟨fun h => by rw [← dual_dual t]; exact h.dual, Sized.dual⟩
/-
**Ordnode.Sized.rotateL** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → r.Size
d → (l.rotateL x r).Sized
参数：l.rotateL x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Sized.node'`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordno
de α}, l.Sized → r.Sized → (l.node' x r).Sized
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.rotateL_node`：rotateL_node (l : Ordnode α) (x : α) (sz : Nat) (m
 : Ordnode α) (y : α) (r : Ordnode α) : rotateL l x (node sz m y r) = if size m 
< ratio * …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ordnode.Sized.node3L`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {m : Ordn
ode α} {y : α} {r : Ordnode α},   l.Sized → m.Sized → r.Sized → (l.node3L x m y 
r).Sized
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.Sized.node4L`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {m : Ordn
ode α} {y : α} {r : Ordnode α},   l.Sized → m.Sized → r.Sized → (l.node4L x m y 
r).Sized
-/
theorem Sized.rotateL {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (rotateL l x r) := by
  cases r; · exact hl.node' hr
  rw [Ordnode.rotateL_node]; split_ifs
  · exact hl.node3L hr.2.1 hr.2.2
  · exact hl.node4L hr.2.1 hr.2.2
/-
**Ordnode.Sized.rotateR** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → r.Size
d → (l.rotateR x r).Sized
参数：l.rotateR x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordnode.Sized.dual_iff`：∀ {α : Type u_1} {t : Ordnode α}, t.dual.Sized ↔
 t.Sized
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.dual_rotateR`：dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode 
α) : dual (rotateR l x r) = rotateL (dual r) x (dual l)
· 使用定理 `Ordnode.Sized.rotateL`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ord
node α}, l.Sized → r.Sized → (l.rotateL x r).Sized
· 使用定理 `Ordnode.Sized.dual`：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → t.dual.S
ized
-/
theorem Sized.rotateR {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (rotateR l x r) :=
  Sized.dual_iff.1 <| by rw [dual_rotateR]; exact hr.dual.rotateL hl.dual
/-
**Ordnode.Sized.rotateL_size** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordnode α}, r.Sized → (l.rot
ateL x r).size = l.size + r.size + 1
参数：l.rotateL x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ordnode.node3L_size`：node3L_size {l x m y r} : size (@node3L α l x m y r
) = size l + size m + size r + 2
· 使用定理 `Nat.Simproc.add_eq_add_ge`：∀ (a c : ℕ) {b d : ℕ}, b ≥ d → (a + b = c + d
) = (a + (b - d) = c)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `_private.Mathlib.Data.Ordmap.Invariants.0.Ordnode.Sized.rotateL_size._ab
el_1_4`：∀ {α : Type u_1} {l : Ordnode α} (l_1 r : Ordnode α), l.size + l_1.size 
+ r.size + 1 = l.size + (l_1.size + r.size + 1)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.node4L_size`：node4L_size {l x m y r} (hm : Sized m) : size (@nod
e4L α l x m y r) = size l + size m + size r + 2
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Sized.rotateL_size {l x r} (hm : Sized r) :
    size (@Ordnode.rotateL α l x r) = size l + size r + 1 := by
  cases r <;> simp [Ordnode.rotateL]
  simp only [hm.1]
  split_ifs <;> simp [node3L_size, node4L_size hm.2.1] <;> abel
/-
**Ordnode.Sized.rotateR_size** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → (l.rot
ateR x r).size = l.size + r.size + 1
参数：l.rotateR x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `Ordnode.dual_rotateR`：dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode 
α) : dual (rotateR l x r) = rotateL (dual r) x (dual l)
· 使用定理 `Ordnode.Sized.rotateL_size`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r 
: Ordnode α}, r.Sized → (l.rotateL x r).size = l.size + r.size + 1
· 使用定理 `Ordnode.Sized.dual`：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → t.dual.S
ized
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem Sized.rotateR_size {l x r} (hl : Sized l) :
    size (@Ordnode.rotateR α l x r) = size l + size r + 1 := by
  rw [← size_dual, dual_rotateR, hl.dual.rotateL_size, size_dual, size_dual, add_comm (size l)]
/-
**Ordnode.Sized.balance'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Sized`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordnode α}, l.Sized → r.Size
d → (l.balance' x r).Sized
参数：l.balance' x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ordnode.Sized.node'`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ordno
de α}, l.Sized → r.Sized → (l.node' x r).Sized
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.Sized.rotateL`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ord
node α}, l.Sized → r.Sized → (l.rotateL x r).Sized
· 使用定理 `Ordnode.Sized.rotateR`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r : Ord
node α}, l.Sized → r.Sized → (l.rotateR x r).Sized
-/
theorem Sized.balance' {l x r} (hl : @Sized α l) (hr : Sized r) : Sized (balance' l x r) := by
  unfold Ordnode.balance'; split_ifs
  · exact hl.node' hr
  · exact hl.rotateL hr
  · exact hl.rotateR hr
  · exact hl.node' hr
/-
**Ordnode.size_balance'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：size_balance' {l x r} (hl : @Sized α l) (hr : Sized r) : size (@balance' α
 l x r) = size l + size r + 1
参数：hl : @Sized α l；hr : Sized r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.Sized.rotateL_size`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r 
: Ordnode α}, r.Sized → (l.rotateL x r).size = l.size + r.size + 1
· 使用定理 `Ordnode.Sized.rotateR_size`：∀ {α : Type u_1} {l : Ordnode α} {x : α} {r 
: Ordnode α}, l.Sized → (l.rotateR x r).size = l.size + r.size + 1
-/
theorem size_balance' {l x r} (hl : @Sized α l) (hr : Sized r) :
    size (@balance' α l x r) = size l + size r + 1 := by
  unfold balance'; split_ifs
  · rfl
  · exact hr.rotateL_size
  · exact hl.rotateR_size
  · rfl

/-! ## `All`, `Any`, `Emem`, `Amem` -/


/-
**Ordnode.All.imp** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.All`。
形式化陈述：∀ {α : Type u_1} {P Q : α → Prop}, (∀ (a : α), P a → Q a) → ∀ {t : Ordnode
 α}, Ordnode.All P t → Ordnode.All Q t
参数：∀ (a : α), P a → Q a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
## `All`, `Any`, `Emem`, `Amem`
-/
theorem All.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, All P t → All Q t
  | nil, _ => ⟨⟩
  | node _ _ _ _, ⟨h₁, h₂, h₃⟩ => ⟨h₁.imp H, H _ h₂, h₃.imp H⟩
/-
**Ordnode.Any.imp** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Any`。
形式化陈述：∀ {α : Type u_1} {P Q : α → Prop}, (∀ (a : α), P a → Q a) → ∀ {t : Ordnode
 α}, Ordnode.Any P t → Ordnode.Any Q t
参数：∀ (a : α), P a → Q a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Any.imp {P Q : α → Prop} (H : ∀ a, P a → Q a) : ∀ {t}, Any P t → Any Q t
  | nil => id
  | node _ _ _ _ => Or.imp (Any.imp H) <| Or.imp (H _) (Any.imp H)
/-
**Ordnode.all_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_singleton {P : α -> Prop} {x : α} : All P (singleton x) ↔ P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem all_singleton {P : α → Prop} {x : α} : All P (singleton x) ↔ P x :=
  ⟨fun h => h.2.1, fun h => ⟨⟨⟩, h, ⟨⟩⟩⟩
/-
**Ordnode.any_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：any_singleton {P : α -> Prop} {x : α} : Any P (singleton x) ↔ P x
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem any_singleton {P : α → Prop} {x : α} : Any P (singleton x) ↔ P x :=
  ⟨by rintro (⟨⟨⟩⟩ | h | ⟨⟨⟩⟩); exact h, fun h => Or.inr (Or.inl h)⟩
/-
**Ordnode.all_dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} {t : Ordnode α}, Ordnode.All P t.dual ↔ Or
dnode.All P t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem all_dual {P : α → Prop} : ∀ {t : Ordnode α}, All P (dual t) ↔ All P t
  | nil => Iff.rfl
  | node _ _l _x _r =>
    ⟨fun ⟨hr, hx, hl⟩ => ⟨all_dual.1 hl, hx, all_dual.1 hr⟩, fun ⟨hl, hx, hr⟩ =>
      ⟨all_dual.2 hr, hx, all_dual.2 hl⟩⟩
/-
**Ordnode.all_iff_forall** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} {t : Ordnode α}, Ordnode.All P t ↔ ∀ (x : 
α), Ordnode.Emem x t → P x
参数：x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem all_iff_forall {P : α → Prop} : ∀ {t}, All P t ↔ ∀ x, Emem x t → P x
  | nil => (iff_true_intro <| by rintro _ ⟨⟩).symm
  | node _ l x r => by simp [All, Emem, all_iff_forall, Any, or_imp, forall_and]
/-
**Ordnode.any_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} {t : Ordnode α}, Ordnode.Any P t ↔ ∃ x, Or
dnode.Emem x t ∧ P x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem any_iff_exists {P : α → Prop} : ∀ {t}, Any P t ↔ ∃ x, Emem x t ∧ P x
  | nil => ⟨by rintro ⟨⟩, by rintro ⟨_, ⟨⟩, _⟩⟩
  | node _ l x r => by simp only [Emem]; simp [Any, any_iff_exists, or_and_right, exists_or]
/-
**Ordnode.emem_iff_all** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：emem_iff_all {x : α} {t} : Emem x t ↔ forall P, All P t -> P x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordnode.all_iff_forall`：∀ {α : Type u_1} {P : α → Prop} {t : Ordnode α},
 Ordnode.All P t ↔ ∀ (x : α), Ordnode.Emem x t → P x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem emem_iff_all {x : α} {t} : Emem x t ↔ ∀ P, All P t → P x :=
  ⟨fun h _ al => all_iff_forall.1 al _ h, fun H => H _ <| all_iff_forall.2 fun _ => id⟩
/-
**Ordnode.all_node'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_node' {P l x r} : @All α P (node' l x r) ↔ All P l ∧ P x ∧ All P r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem all_node' {P l x r} : @All α P (node' l x r) ↔ All P l ∧ P x ∧ All P r :=
  Iff.rfl
/-
**Ordnode.all_node3L** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_node3L {P l x m y r} : @All α P (node3L l x m y r) ↔ All P l ∧ P x ∧ A
ll P m ∧ P y ∧ All P r
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
theorem all_node3L {P l x m y r} :
    @All α P (node3L l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  simp [node3L, all_node', and_assoc]
/-
**Ordnode.all_node3R** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_node3R {P l x m y r} : @All α P (node3R l x m y r) ↔ All P l ∧ P x ∧ A
ll P m ∧ P y ∧ All P r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem all_node3R {P l x m y r} :
    @All α P (node3R l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r :=
  Iff.rfl
/-
**Ordnode.all_node4L** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_node4L {P l x m y r} : @All α P (node4L l x m y r) ↔ All P l ∧ P x ∧ A
ll P m ∧ P y ∧ All P r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem all_node4L {P l x m y r} :
    @All α P (node4L l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  cases m <;> simp [node4L, all_node', All, all_node3L, and_assoc]
/-
**Ordnode.all_node4R** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_node4R {P l x m y r} : @All α P (node4R l x m y r) ↔ All P l ∧ P x ∧ A
ll P m ∧ P y ∧ All P r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem all_node4R {P l x m y r} :
    @All α P (node4R l x m y r) ↔ All P l ∧ P x ∧ All P m ∧ P y ∧ All P r := by
  cases m <;> simp [node4R, all_node', All, all_node3R, and_assoc]
/-
**Ordnode.all_rotateL** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_rotateL {P l x r} : @All α P (rotateL l x r) ↔ All P l ∧ P x ∧ All P r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem all_rotateL {P l x r} : @All α P (rotateL l x r) ↔ All P l ∧ P x ∧ All P r := by
  cases r <;> simp [rotateL, all_node']; split_ifs <;>
    simp [all_node3L, all_node4L, All]
/-
**Ordnode.all_rotateR** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_rotateR {P l x r} : @All α P (rotateR l x r) ↔ All P l ∧ P x ∧ All P r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.all_dual`：∀ {α : Type u_1} {P : α → Prop} {t : Ordnode α}, Ordno
de.All P t.dual ↔ Ordnode.All P t
· 使用定理 `Ordnode.dual_rotateR`：dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode 
α) : dual (rotateR l x r) = rotateL (dual r) x (dual l)
· 使用定理 `Ordnode.all_rotateL`：all_rotateL {P l x r} : @All α P (rotateL l x r) ↔ 
All P l ∧ P x ∧ All P r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem all_rotateR {P l x r} : @All α P (rotateR l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [← all_dual, dual_rotateR, all_rotateL]; simp [all_dual, and_comm, and_left_comm, and_assoc]
/-
**Ordnode.all_balance'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_balance' {P l x r} : @All α P (balance' l x r) ↔ All P l ∧ P x ∧ All P
 r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balance'.eq_1`：∀ {α : Type u_1} (l : Ordnode α) (x : α) (r : Ord
node α),   l.balance' x r =     if l.size + r.size ≤ 1 then l.node' x r     else
       if r…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem all_balance' {P l x r} : @All α P (balance' l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balance']; split_ifs <;> simp [all_node', all_rotateL, all_rotateR]

/-! ### `toList` -/


/-
**Ordnode.foldr_cons_eq_toList** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (t : Ordnode α) (r : List α), Ordnode.foldr List.cons t r
 = t.toList ++ r
参数：t : Ordnode α；r : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `toList`
-/
theorem foldr_cons_eq_toList : ∀ (t : Ordnode α) (r : List α), t.foldr List.cons r = toList t ++ r
  | nil, _ => rfl
  | node _ l x r, r' => by
    rw [foldr, foldr_cons_eq_toList l, foldr_cons_eq_toList r, ← List.cons_append,
        ← List.append_assoc, ← foldr_cons_eq_toList l]; rfl

@[simp]
/-
**Ordnode.toList_nil** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：toList_nil : toList (@nil α) = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toList_nil : toList (@nil α) = [] :=
  rfl

@[simp]
/-
**Ordnode.toList_node** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：toList_node (s l x r) : toList (@node α s l x r) = toList l ++ x :: toList
 r
参数：s l x r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.toList.eq_1`：∀ {α : Type u_1} (t : Ordnode α), t.toList = Ordnod
e.foldr List.cons t []
· 使用定理 `Ordnode.foldr.eq_2`：∀ {α : Type u_1} {β : Sort u_2} (f : α → β → β) (x :
 β) (size : ℕ) (l : Ordnode α) (x_2 : α) (r : Ordnode α),   Ordnode.foldr f (Ord
node.nod…
· 使用定理 `Ordnode.foldr_cons_eq_toList`：∀ {α : Type u_1} (t : Ordnode α) (r : List
 α), Ordnode.foldr List.cons t r = t.toList ++ r
-/
theorem toList_node (s l x r) : toList (@node α s l x r) = toList l ++ x :: toList r := by
  rw [toList, foldr, foldr_cons_eq_toList]; rfl
/-
**Ordnode.emem_iff_mem_toList** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：emem_iff_mem_toList {x : α} {t} : Emem x t ↔ x in toList t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ordnode.toList_node`：toList_node (s l x r) : toList (@node α s l x r) = 
toList l ++ x :: toList r
-/
theorem emem_iff_mem_toList {x : α} {t} : Emem x t ↔ x ∈ toList t := by
  unfold Emem; induction t <;> simp [Any, *]
/-
**Ordnode.length_toList'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (t : Ordnode α), t.toList.length = t.realSize
参数：t : Ordnode α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_toList' : ∀ t : Ordnode α, (toList t).length = t.realSize
  | nil => rfl
  | node _ l _ r => by
    rw [toList_node, List.length_append, List.length_cons, length_toList' l,
        length_toList' r]; rfl
/-
**Ordnode.length_toList** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：length_toList {t : Ordnode α} (h : Sized t) : (toList t).length = t.size
参数：h : Sized t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.length_toList'`：∀ {α : Type u_1} (t : Ordnode α), t.toList.lengt
h = t.realSize
· 使用定理 `Ordnode.size_eq_realSize`：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → t.
size = t.realSize
-/
theorem length_toList {t : Ordnode α} (h : Sized t) : (toList t).length = t.size := by
  rw [length_toList', size_eq_realSize h]
/-
**Ordnode.equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：equiv_iff {t₁ t₂ : Ordnode α} (h₁ : Sized t₁) (h₂ : Sized t₂) : Equiv t₁ t
₂ ↔ toList t₁ = toList t₂
参数：h₁ : Sized t₁；h₂ : Sized t₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_iff_right_of_imp`：∀ {b a : Prop}, (b → a) → (a ∧ b ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.length_toList`：length_toList {t : Ordnode α} (h : Sized t) : (to
List t).length = t.size
-/
theorem equiv_iff {t₁ t₂ : Ordnode α} (h₁ : Sized t₁) (h₂ : Sized t₂) :
    Equiv t₁ t₂ ↔ toList t₁ = toList t₂ :=
  and_iff_right_of_imp fun h => by rw [← length_toList h₁, h, length_toList h₂]

/-! ### `mem` -/


/-
**Ordnode.pos_size_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：pos_size_of_mem [LE α] [DecidableLE α] {x : α} {t : Ordnode α} (h : Sized 
t) (h_mem : x in t) : 0 < size t
参数：h : Sized t；h_mem : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
### `mem`
-/
theorem pos_size_of_mem [LE α] [DecidableLE α] {x : α} {t : Ordnode α} (h : Sized t)
    (h_mem : x ∈ t) : 0 < size t := by cases t; · { contradiction }; · { simp [h.1] }

/-! ### `(find/erase/split)(Min/Max)` -/


/-
**Ordnode.findMin'_dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (t : Ordnode α) (x : α), t.dual.findMin' x = Ordnode.find
Max' x t
参数：t : Ordnode α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.findMax'`：findMax'_dual (t) (x : α) : findMax' x (dual t) = find
Min' t x

--- 原说明 ---
### `(find/erase/split)(Min/Max)`
-/
theorem findMin'_dual : ∀ (t) (x : α), findMin' (dual t) x = findMax' x t
  | nil, _ => rfl
  | node _ _ x r, _ => findMin'_dual r x
/-
**Ordnode.findMax'_dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (t : Ordnode α) (x : α), Ordnode.findMax' x t.dual = t.fi
ndMin' x
参数：t : Ordnode α；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.findMax'`：findMax'_dual (t) (x : α) : findMax' x (dual t) = find
Min' t x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.findMin'_dual`：∀ {α : Type u_1} (t : Ordnode α) (x : α), t.dual.
findMin' x = Ordnode.findMax' x t
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
-/
theorem findMax'_dual (t) (x : α) : findMax' x (dual t) = findMin' t x := by
  rw [← findMin'_dual, dual_dual]
/-
**Ordnode.findMin_dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (t : Ordnode α), t.dual.findMin = t.findMax
参数：t : Ordnode α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Ordnode.findMax'`：findMax'_dual (t) (x : α) : findMax' x (dual t) = find
Min' t x
· 使用定理 `Ordnode.findMin'_dual`：∀ {α : Type u_1} (t : Ordnode α) (x : α), t.dual.
findMin' x = Ordnode.findMax' x t
-/
theorem findMin_dual : ∀ t : Ordnode α, findMin (dual t) = findMax t
  | nil => rfl
  | node _ _ _ _ => congr_arg some <| findMin'_dual _ _
/-
**Ordnode.findMax_dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：findMax_dual (t : Ordnode α) : findMax (dual t) = findMin t
参数：t : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.findMin_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.findMin =
 t.findMax
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
-/
theorem findMax_dual (t : Ordnode α) : findMax (dual t) = findMin t := by
  rw [← findMin_dual, dual_dual]
/-
**Ordnode.dual_eraseMin** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (t : Ordnode α), t.eraseMin.dual = t.dual.eraseMax
参数：t : Ordnode α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_eraseMin : ∀ t : Ordnode α, dual (eraseMin t) = eraseMax (dual t)
  | nil => rfl
  | node _ nil _ _ => rfl
  | node _ (node sz l' y r') x r => by
    rw [eraseMin, dual_balanceR, dual_eraseMin (node sz l' y r'), dual, dual, dual, eraseMax]
/-
**Ordnode.dual_eraseMax** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_eraseMax (t : Ordnode α) : dual (eraseMax t) = eraseMin (dual t)
参数：t : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
· 使用定理 `Ordnode.dual_eraseMin`：∀ {α : Type u_1} (t : Ordnode α), t.eraseMin.dual
 = t.dual.eraseMax
-/
theorem dual_eraseMax (t : Ordnode α) : dual (eraseMax t) = eraseMin (dual t) := by
  rw [← dual_dual (eraseMin _), dual_eraseMin, dual_dual]
/-
**Ordnode.splitMin_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (s : ℕ) (l : Ordnode α) (x : α) (r : Ordnode α),   l.spli
tMin' x r = (l.findMin' x, (Ordnode.node s l x r).eraseMin)
参数：s : ℕ；l : Ordnode α；x : α；r : Ordnode α；l.findMin' x, (Ordnode.node s l x r).
eraseMin。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem splitMin_eq :
    ∀ (s l) (x : α) (r), splitMin' l x r = (findMin' l x, eraseMin (node s l x r))
  | _, nil, _, _ => rfl
  | _, node ls ll lx lr, x, r => by rw [splitMin', splitMin_eq ls ll lx lr, findMin', eraseMin]
/-
**Ordnode.splitMax_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} (s : ℕ) (l : Ordnode α) (x : α) (r : Ordnode α),   l.spli
tMax' x r = ((Ordnode.node s l x r).eraseMax, Ordnode.findMax' x r)
参数：s : ℕ；l : Ordnode α；x : α；r : Ordnode α；(Ordnode.node s l x r).eraseMax, Ordn
ode.findMax' x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.findMax'`：findMax'_dual (t) (x : α) : findMax' x (dual t) = find
Min' t x
-/
theorem splitMax_eq :
    ∀ (s l) (x : α) (r), splitMax' l x r = (eraseMax (node s l x r), findMax' x r)
  | _, _, _, nil => rfl
  | _, l, x, node ls ll lx lr => by rw [splitMax', splitMax_eq ls ll lx lr, findMax', eraseMax]

@[elab_as_elim]
/-
**Ordnode.findMin'_all** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} (t : Ordnode α) (x : α), Ordnode.All P t →
 P x → P (t.findMin' x)
参数：t : Ordnode α；x : α；t.findMin' x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem findMin'_all {P : α → Prop} : ∀ (t) (x : α), All P t → P x → P (findMin' t x)
  | nil, _x, _, hx => hx
  | node _ ll lx _, _, ⟨h₁, h₂, _⟩, _ => findMin'_all ll lx h₁ h₂

@[elab_as_elim]
/-
**Ordnode.findMax'_all** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} {P : α → Prop} (x : α) (t : Ordnode α), P x → Ordnode.All
 P t → P (Ordnode.findMax' x t)
参数：x : α；t : Ordnode α；Ordnode.findMax' x t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.findMax'`：findMax'_dual (t) (x : α) : findMax' x (dual t) = find
Min' t x
-/
theorem findMax'_all {P : α → Prop} : ∀ (x : α) (t), P x → All P t → P (findMax' x t)
  | _x, nil, hx, _ => hx
  | _, node _ _ lx lr, _, ⟨_, h₂, h₃⟩ => findMax'_all lx lr h₂ h₃

/-! ### `glue` -/


/-! ### `merge` -/


@[simp]
/-
**Ordnode.merge_nil_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：merge_nil_left (t : Ordnode α) : merge t nil = t
参数：t : Ordnode α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
### `merge`
-/
theorem merge_nil_left (t : Ordnode α) : merge t nil = t := by cases t <;> rfl

@[simp]
/-
**Ordnode.merge_nil_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：merge_nil_right (t : Ordnode α) : merge nil t = t
参数：t : Ordnode α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem merge_nil_right (t : Ordnode α) : merge nil t = t :=
  rfl

@[simp]
/-
**Ordnode.merge_node** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：merge_node {ls ll lx lr rs rl rx rr} : merge (@node α ls ll lx lr) (node r
s rl rx rr) = if delta * ls < rs then balanceL (merge (node ls ll lx lr) rl) rx 
rr else if delta * rs < ls then balanceR ll lx (merge lr (node rs rl rx rr)) els
e glue (node ls ll lx lr) (node rs rl rx rr)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem merge_node {ls ll lx lr rs rl rx rr} :
    merge (@node α ls ll lx lr) (node rs rl rx rr) =
      if delta * ls < rs then balanceL (merge (node ls ll lx lr) rl) rx rr
      else if delta * rs < ls then balanceR ll lx (merge lr (node rs rl rx rr))
      else glue (node ls ll lx lr) (node rs rl rx rr) :=
  rfl

/-! ### `insert` -/


set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.dual_insert** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：dual_insert [LE α] [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) : foral
l t : Ordnode α, dual (Ordnode.insert x t) = @Ordnode.insert αᵒᵈ _ _ x (dual t) 
| nil => rfl | node _ l y r => by have : @cmpLE αᵒᵈ _ _ x y = cmpLE y x
参数：· <= ·；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### `insert`
-/
theorem dual_insert [LE α] [@Std.Total α (· ≤ ·)] [DecidableLE α] (x : α) :
    ∀ t : Ordnode α, dual (Ordnode.insert x t) = @Ordnode.insert αᵒᵈ _ _ x (dual t)
  | nil => rfl
  | node _ l y r => by
    have : @cmpLE αᵒᵈ _ _ x y = cmpLE y x := rfl
    rw [Ordnode.insert, dual, Ordnode.insert, this, ← cmpLE_swap x y]
    cases cmpLE x y <;>
      simp [Ordering.swap, dual_balanceL, dual_balanceR, dual_insert]

/-! ### `balance` properties -/


set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.balance_eq_balance'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：balance_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Size
d l) (sr : Sized r) : @balance α l x r = balance' l x r
参数：hl : Balanced l；hr : Balanced r；sl : Sized l；sr : Sized r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.Sized.eq_node'`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α}
 {r : Ordnode α},   (Ordnode.node s l x r).Sized → Ordnode.node s l x r = l.node
' x r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordnode.balancedSz_zero`：balancedSz_zero {l : Nat} : BalancedSz l 0 ↔ l 
<= 1
· 使用定理 `Ordnode.BalancedSz.symm`：∀ {l r : ℕ}, Ordnode.BalancedSz l r → Ordnode.B
alancedSz r l
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Nat.succ_le_succ_iff`：∀ {a b : ℕ}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordnode.size.eq_2`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x_1 : α) (
r : Ordnode α), (Ordnode.node sz l x_1 r).size = sz
· 使用定理 `Ordnode.Sized.size_eq_zero`：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → 
(t.size = 0 ↔ t = Ordnode.nil)
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Ordnode.rotateL_node`：rotateL_node (l : Ordnode α) (x : α) (sz : Nat) (m
 : Ordnode α) (y : α) (r : Ordnode α) : rotateL l x (node sz m y r) = if size m 
< ratio * …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
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
· 使用定理 `Ordnode.Sized.pos`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α} {r :
 Ordnode α}, (Ordnode.node s l x r).Sized → 0 < s
· 使用定理 `Ordnode.rotateL.eq_1`：∀ {α : Type u_1} (x : Ordnode α) (x_1 : α) (size :
 ℕ) (m : Ordnode α) (y : α) (r : Ordnode α),   x.rotateL x_1 (Ordnode.node size 
m y r) =  …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
### `balance` properties
-/
theorem balance_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r) : @balance α l x r = balance' l x r := by
  obtain - | ⟨ls, ll, lx, lr⟩ := l
  · obtain - | ⟨rs, rl, rx, rr⟩ := r
    · rfl
    · rw [sr.eq_node'] at hr ⊢
      obtain - | ⟨rls, rll, rlx, rlr⟩ := rl <;> obtain - | ⟨rrs, rrl, rrx, rrr⟩ := rr <;>
        dsimp +instances [balance, balance']
      · rfl
      · have : size rrl = 0 ∧ size rrr = 0 := by
          have := balancedSz_zero.1 hr.1.symm
          rwa [size, sr.2.2.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sr.2.2.2.1.size_eq_zero.1 this.1
        cases sr.2.2.2.2.size_eq_zero.1 this.2
        obtain rfl : rrs = 1 := sr.2.2.1
        rw [if_neg, rotateL_node, if_pos]; · rfl
        all_goals (try dsimp only [size]); decide
      · have : size rll = 0 ∧ size rlr = 0 := by
          have := balancedSz_zero.1 hr.1
          rwa [size, sr.2.1.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sr.2.1.2.1.size_eq_zero.1 this.1
        cases sr.2.1.2.2.size_eq_zero.1 this.2
        obtain rfl : rls = 1 := sr.2.1.1
        rw [if_neg, rotateL_node, if_neg]; · rfl
        all_goals (try dsimp only [size]); decide
      · symm; rw [zero_add, if_neg, rotateL]
        · dsimp only [size_node]; split_ifs
          · simp [node3L, node']; abel
          · simp [node4L, node', sr.2.1.1]; abel
        · exact not_le_of_gt (Nat.succ_lt_succ (add_pos sr.2.1.pos sr.2.2.pos))
  · obtain - | ⟨rs, rl, rx, rr⟩ := r
    · rw [sl.eq_node'] at hl ⊢
      obtain - | ⟨lls, lll, llx, llr⟩ := ll <;> obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr <;>
        dsimp [balance, balance']
      · rfl
      · have : size lrl = 0 ∧ size lrr = 0 := by
          have := balancedSz_zero.1 hl.1.symm
          rwa [size, sl.2.2.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sl.2.2.2.1.size_eq_zero.1 this.1
        cases sl.2.2.2.2.size_eq_zero.1 this.2
        obtain rfl : lrs = 1 := sl.2.2.1
        rw [if_neg, rotateR_node, if_neg]; · rfl
        all_goals (try dsimp only [size]); decide
      · have : size lll = 0 ∧ size llr = 0 := by
          have := balancedSz_zero.1 hl.1
          rwa [size, sl.2.1.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
        cases sl.2.1.2.1.size_eq_zero.1 this.1
        cases sl.2.1.2.2.size_eq_zero.1 this.2
        obtain rfl : lls = 1 := sl.2.1.1
        rw [if_neg, rotateR_node, if_pos]; · rfl
        all_goals (try dsimp only [size]); decide
      · symm; rw [if_neg, rotateR]
        · dsimp only [size_node]; split_ifs
          · simp [node3R, node']; abel
          · simp [node4R, node', sl.2.2.1]; abel
        · exact not_le_of_gt (Nat.succ_lt_succ (add_pos sl.2.1.pos sl.2.2.pos))
    · simp only [balance, id_eq, balance', size_node, gt_iff_lt]
      symm; rw [if_neg]
      · split_ifs with h h_1
        · have rd : delta ≤ size rl + size rr := by
            have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sl.pos) h
            rwa [sr.1, Nat.lt_succ_iff] at this
          obtain - | ⟨rls, rll, rlx, rlr⟩ := rl
          · rw [size, zero_add] at rd
            exact absurd (le_trans rd (balancedSz_zero.1 hr.1.symm)) (by decide)
          obtain - | ⟨rrs, rrl, rrx, rrr⟩ := rr
          · exact absurd (le_trans rd (balancedSz_zero.1 hr.1)) (by decide)
          dsimp [rotateL]; split_ifs
          · simp [node3L, node', sr.1]; abel
          · simp [node4L, node', sr.1, sr.2.1.1]; abel
        · have ld : delta ≤ size ll + size lr := by
            have := lt_of_le_of_lt (Nat.mul_le_mul_left _ sr.pos) h_1
            rwa [sl.1, Nat.lt_succ_iff] at this
          obtain - | ⟨lls, lll, llx, llr⟩ := ll
          · rw [size, zero_add] at ld
            exact absurd (le_trans ld (balancedSz_zero.1 hl.1.symm)) (by decide)
          obtain - | ⟨lrs, lrl, lrx, lrr⟩ := lr
          · exact absurd (le_trans ld (balancedSz_zero.1 hl.1)) (by decide)
          dsimp [rotateR]; split_ifs
          · simp [node3R, node', sl.1]; abel
          · simp [node4R, node', sl.1, sl.2.2.1]; abel
        · simp [node']
      · exact not_le_of_gt (add_le_add (Nat.succ_le_of_lt sl.pos) (Nat.succ_le_of_lt sr.pos))
/-
**Ordnode.balanceL_eq_balance** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：balanceL_eq_balance {l x r} (sl : Sized l) (sr : Sized r) (H1 : size l = 0
 -> size r <= 1) (H2 : 1 <= size l -> 1 <= size r -> size r <= delta * size l) :
 @balanceL α l x r = balance l x r
参数：sl : Sized l；sr : Sized r；H1 : size l = 0 -> size r <= 1；H2 : 1 <= size l -> 
1 <= size r -> size r <= delta * size l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Nat.succ_le_succ_iff`：∀ {a b : ℕ}, a.succ ≤ b.succ ↔ a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.size.eq_2`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x_1 : α) (
r : Ordnode α), (Ordnode.node sz l x_1 r).size = sz
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordnode.Sized.size_eq_zero`：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → 
(t.size = 0 ↔ t = Ordnode.nil)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordnode.Sized.eq_node'`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α}
 {r : Ordnode α},   (Ordnode.node s l x r).Sized → Ordnode.node s l x r = l.node
' x r
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Ordnode.Sized.pos`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α} {r :
 Ordnode α}, (Ordnode.node s l x r).Sized → 0 < s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem balanceL_eq_balance {l x r} (sl : Sized l) (sr : Sized r) (H1 : size l = 0 → size r ≤ 1)
    (H2 : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l) :
    @balanceL α l x r = balance l x r := by
  obtain - | ⟨rs, rl, rx, rr⟩ := r
  · rfl
  · obtain - | ⟨ls, ll, lx, lr⟩ := l
    · have : size rl = 0 ∧ size rr = 0 := by
        have := H1 rfl
        rwa [size, sr.1, Nat.succ_le_succ_iff, Nat.le_zero, add_eq_zero] at this
      cases sr.2.1.size_eq_zero.1 this.1
      cases sr.2.2.size_eq_zero.1 this.2
      rw [sr.eq_node']; rfl
    · replace H2 : ¬rs > delta * ls := not_lt_of_ge (H2 sl.pos sr.pos)
      simp [balanceL, balance, H2]; split_ifs <;> simp [add_comm]

/-- `Raised n m` means `m` is either equal or one up from `n`. -/
/-
**Ordnode.Raised** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：Raised (n m : Nat) : Prop
参数：n m : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Raised n m` means `m` is either equal or one up from `n`.
-/
def Raised (n m : ℕ) : Prop :=
  m = n ∨ m = n + 1
/-
**Ordnode.raised_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：raised_iff {n m} : Raised n m ↔ n <= m ∧ m <= n + 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem raised_iff {n m} : Raised n m ↔ n ≤ m ∧ m ≤ n + 1 := by
  constructor
  · rintro (rfl | rfl)
    · exact ⟨le_rfl, Nat.le_succ _⟩
    · exact ⟨Nat.le_succ _, le_rfl⟩
  · rintro ⟨h₁, h₂⟩
    rcases eq_or_lt_of_le h₁ with (rfl | h₁)
    · exact Or.inl rfl
    · exact Or.inr (le_antisymm h₂ h₁)
/-
**Ordnode.Raised.dist_le** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Raised`。
形式化陈述：∀ {n m : ℕ}, Ordnode.Raised n m → n.dist m ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordnode.raised_iff`：raised_iff {n m} : Raised n m ↔ n <= m ∧ m <= n + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.dist_eq_sub_of_le`：dist_eq_sub_of_le {n m : Nat} (h : n <= m) : dist
 n m = m - n
· 使用定理 `tsub_le_iff_left`：tsub_le_iff_left : a - b <= c ↔ a <= b + c
-/
theorem Raised.dist_le {n m} (H : Raised n m) : Nat.dist n m ≤ 1 := by
  obtain ⟨H1, H2⟩ := raised_iff.1 H; rwa [Nat.dist_eq_sub_of_le H1, tsub_le_iff_left]
/-
**Ordnode.Raised.dist_le'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Raised`。
形式化陈述：∀ {n m : ℕ}, Ordnode.Raised n m → m.dist n ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.dist_comm`：dist_comm (n m : Nat) : dist n m = dist m n
· 使用定理 `Ordnode.Raised.dist_le`：∀ {n m : ℕ}, Ordnode.Raised n m → n.dist m ≤ 1
-/
theorem Raised.dist_le' {n m} (H : Raised n m) : Nat.dist m n ≤ 1 := by
  rw [Nat.dist_comm]; exact H.dist_le
/-
**Ordnode.Raised.add_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Raised`。
形式化陈述：∀ (k : ℕ) {n m : ℕ}, Ordnode.Raised n m → Ordnode.Raised (k + n) (k + m)
参数：k : ℕ；k + n；k + m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Raised.add_left (k) {n m} (H : Raised n m) : Raised (k + n) (k + m) := by
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl
/-
**Ordnode.Raised.add_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Raised`。
形式化陈述：∀ (k : ℕ) {n m : ℕ}, Ordnode.Raised n m → Ordnode.Raised (n + k) (m + k)
参数：k : ℕ；n + k；m + k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.Raised.add_left`：∀ (k : ℕ) {n m : ℕ}, Ordnode.Raised n m → Ordno
de.Raised (k + n) (k + m)
-/
theorem Raised.add_right (k) {n m} (H : Raised n m) : Raised (n + k) (m + k) := by
  rw [add_comm, add_comm m]; exact H.add_left _
/-
**Ordnode.Raised.right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Raised`。
形式化陈述：∀ {α : Type u_1} {l : Ordnode α} {x₁ x₂ : α} {r₁ r₂ : Ordnode α},   Ordnod
e.Raised r₁.size r₂.size → Ordnode.Raised (l.node' x₁ r₁).size (l.node' x₂ r₂).s
ize
参数：l.node' x₁ r₁；l.node' x₂ r₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.node'.eq_1`：∀ {α : Type u_1} (l : Ordnode α) (x : α) (r : Ordnod
e α), l.node' x r = Ordnode.node (l.size + r.size + 1) l x r
· 使用定理 `Ordnode.size_node`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x : α) (r 
: Ordnode α), (Ordnode.node sz l x r).size = sz
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Raised.right {l x₁ x₂ r₁ r₂} (H : Raised (size r₁) (size r₂)) :
    Raised (size (@node' α l x₁ r₁)) (size (@node' α l x₂ r₂)) := by
  rw [node', size_node, size_node]; generalize size r₂ = m at H ⊢
  rcases H with (rfl | rfl)
  · exact Or.inl rfl
  · exact Or.inr rfl
/-
**Ordnode.balanceL_eq_balance'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：balanceL_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Siz
ed l) (sr : Sized r) (H : (exists l', Raised l' (size l) ∧ BalancedSz l' (size r
)) ∨ exists r', Raised (size r) r' ∧ BalancedSz (size l) r') : @balanceL α l x r
 = balance' l x r
参数：hl : Balanced l；hr : Balanced r；sl : Sized l；sr : Sized r；H : (exists l', Rai
sed l' (size l) ∧ BalancedSz l' (size r)) ∨ exists r', Raised (size r) r' ∧ Bala
ncedSz (size l) r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.balance_eq_balance'`：balance_eq_balance' {l x r} (hl : Balanced 
l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) : @balance α l x r = balance'
 l x r
· 使用定理 `Ordnode.balanceL_eq_balance`：balanceL_eq_balance {l x r} (sl : Sized l) 
(sr : Sized r) (H1 : size l = 0 -> size r <= 1) (H2 : 1 <= size l -> 1 <= size r
 -> size r <= del…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordnode.balancedSz_zero`：balancedSz_zero {l : Nat} : BalancedSz l 0 ↔ l 
<= 1
· 使用定理 `Ordnode.BalancedSz.symm`：∀ {l r : ℕ}, Ordnode.BalancedSz l r → Ordnode.B
alancedSz r l
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.raised_iff`：raised_iff {n m} : Raised n m ↔ n <= m ∧ m <= n + 1
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
-/
theorem balanceL_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r)
    (H :
      (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    @balanceL α l x r = balance' l x r := by
  rw [← balance_eq_balance' hl hr sl sr, balanceL_eq_balance sl sr]
  · intro l0; rw [l0] at H
    rcases H with (⟨_, ⟨⟨⟩⟩ | ⟨⟨⟩⟩, H⟩ | ⟨r', e, H⟩)
    · exact balancedSz_zero.1 H.symm
    exact le_trans (raised_iff.1 e).1 (balancedSz_zero.1 H.symm)
  · intro l1 _
    rcases H with (⟨l', e, H | ⟨_, H₂⟩⟩ | ⟨r', e, H | ⟨_, H₂⟩⟩)
    · exact le_trans (le_trans (Nat.le_add_left _ _) H) (mul_pos (by decide) l1 : (0 : ℕ) < _)
    · exact le_trans H₂ (Nat.mul_le_mul_left _ (raised_iff.1 e).1)
    · cases raised_iff.1 e; unfold delta; lia
    · exact le_trans (raised_iff.1 e).1 H₂
/-
**Ordnode.balance_sz_dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：balance_sz_dual {l r} (H : (exists l', Raised (@size α l) l' ∧ BalancedSz 
l' (@size α r)) ∨ exists r', Raised r' (size r) ∧ BalancedSz (size l) r') : (exi
sts l', Raised l' (size (dual r)) ∧ BalancedSz l' (size (dual l))) ∨ exists r', 
Raised (size (dual l)) r' ∧ BalancedSz (size (dual r)) r'
参数：H : (exists l', Raised (@size α l) l' ∧ BalancedSz l' (@size α r)) ∨ exists r
', Raised r' (size r) ∧ BalancedSz (size l) r'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `Ordnode.BalancedSz.symm`：∀ {l r : ℕ}, Ordnode.BalancedSz l r → Ordnode.B
alancedSz r l
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
theorem balance_sz_dual {l r}
    (H : (∃ l', Raised (@size α l) l' ∧ BalancedSz l' (@size α r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    (∃ l', Raised l' (size (dual r)) ∧ BalancedSz l' (size (dual l))) ∨
      ∃ r', Raised (size (dual l)) r' ∧ BalancedSz (size (dual r)) r' := by
  rw [size_dual, size_dual]
  exact
    H.symm.imp (Exists.imp fun _ => And.imp_right BalancedSz.symm)
      (Exists.imp fun _ => And.imp_right BalancedSz.symm)
/-
**Ordnode.size_balanceL** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：size_balanceL {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (
sr : Sized r) (H : (exists l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨ ex
ists r', Raised (size r) r' ∧ BalancedSz (size l) r') : size (@balanceL α l x r)
 = size l + size r + 1
参数：hl : Balanced l；hr : Balanced r；sl : Sized l；sr : Sized r；H : (exists l', Rai
sed l' (size l) ∧ BalancedSz l' (size r)) ∨ exists r', Raised (size r) r' ∧ Bala
ncedSz (size l) r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balanceL_eq_balance'`：balanceL_eq_balance' {l x r} (hl : Balance
d l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised l' 
(size l) ∧ Balance…
· 使用定理 `Ordnode.size_balance'`：size_balance' {l x r} (hl : @Sized α l) (hr : Siz
ed r) : size (@balance' α l x r) = size l + size r + 1
-/
theorem size_balanceL {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    size (@balanceL α l x r) = size l + size r + 1 := by
  rw [balanceL_eq_balance' hl hr sl sr H, size_balance' sl sr]
/-
**Ordnode.all_balanceL** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_balanceL {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) 
(sr : Sized r) (H : (exists l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨ e
xists r', Raised (size r) r' ∧ BalancedSz (size l) r') : All P (@balanceL α l x 
r) ↔ All P l ∧ P x ∧ All P r
参数：hl : Balanced l；hr : Balanced r；sl : Sized l；sr : Sized r；H : (exists l', Rai
sed l' (size l) ∧ BalancedSz l' (size r)) ∨ exists r', Raised (size r) r' ∧ Bala
ncedSz (size l) r'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balanceL_eq_balance'`：balanceL_eq_balance' {l x r} (hl : Balance
d l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised l' 
(size l) ∧ Balance…
· 使用定理 `Ordnode.all_balance'`：all_balance' {P l x r} : @All α P (balance' l x r)
 ↔ All P l ∧ P x ∧ All P r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem all_balanceL {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H :
      (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    All P (@balanceL α l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balanceL_eq_balance' hl hr sl sr H, all_balance']
/-
**Ordnode.balanceR_eq_balance'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：balanceR_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Siz
ed l) (sr : Sized r) (H : (exists l', Raised (size l) l' ∧ BalancedSz l' (size r
)) ∨ exists r', Raised r' (size r) ∧ BalancedSz (size l) r') : @balanceR α l x r
 = balance' l x r
参数：hl : Balanced l；hr : Balanced r；sl : Sized l；sr : Sized r；H : (exists l', Rai
sed (size l) l' ∧ BalancedSz l' (size r)) ∨ exists r', Raised r' (size r) ∧ Bala
ncedSz (size l) r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
· 使用定理 `Ordnode.dual_balanceR`：dual_balanceR (l : Ordnode α) (x : α) (r : Ordnod
e α) : dual (balanceR l x r) = balanceL (dual r) x (dual l)
· 使用定理 `Ordnode.balanceL_eq_balance'`：balanceL_eq_balance' {l x r} (hl : Balance
d l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised l' 
(size l) ∧ Balance…
· 使用定理 `Ordnode.Balanced.dual`：∀ {α : Type u_1} {t : Ordnode α}, t.Balanced → t.
dual.Balanced
· 使用定理 `Ordnode.Sized.dual`：∀ {α : Type u_1} {t : Ordnode α}, t.Sized → t.dual.S
ized
· 使用定理 `Ordnode.balance_sz_dual`：balance_sz_dual {l r} (H : (exists l', Raised (
@size α l) l' ∧ BalancedSz l' (@size α r)) ∨ exists r', Raised r' (size r) ∧ Bal
ancedSz (size…
· 使用定理 `Ordnode.dual_balance'`：dual_balance' (l : Ordnode α) (x : α) (r : Ordnod
e α) : dual (balance' l x r) = balance' (dual r) x (dual l)
-/
theorem balanceR_eq_balance' {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l)
    (sr : Sized r)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    @balanceR α l x r = balance' l x r := by
  rw [← dual_dual (balanceR l x r), dual_balanceR,
    balanceL_eq_balance' hr.dual hl.dual sr.dual sl.dual (balance_sz_dual H), ← dual_balance',
    dual_dual]
/-
**Ordnode.size_balanceR** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：size_balanceR {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (
sr : Sized r) (H : (exists l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨ ex
ists r', Raised r' (size r) ∧ BalancedSz (size l) r') : size (@balanceR α l x r)
 = size l + size r + 1
参数：hl : Balanced l；hr : Balanced r；sl : Sized l；sr : Sized r；H : (exists l', Rai
sed (size l) l' ∧ BalancedSz l' (size r)) ∨ exists r', Raised r' (size r) ∧ Bala
ncedSz (size l) r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balanceR_eq_balance'`：balanceR_eq_balance' {l x r} (hl : Balance
d l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised (si
ze l) l' ∧ Balance…
· 使用定理 `Ordnode.size_balance'`：size_balance' {l x r} (hl : @Sized α l) (hr : Siz
ed r) : size (@balance' α l x r) = size l + size r + 1
-/
theorem size_balanceR {l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    size (@balanceR α l x r) = size l + size r + 1 := by
  rw [balanceR_eq_balance' hl hr sl sr H, size_balance' sl sr]
/-
**Ordnode.all_balanceR** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：all_balanceR {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) 
(sr : Sized r) (H : (exists l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨ e
xists r', Raised r' (size r) ∧ BalancedSz (size l) r') : All P (@balanceR α l x 
r) ↔ All P l ∧ P x ∧ All P r
参数：hl : Balanced l；hr : Balanced r；sl : Sized l；sr : Sized r；H : (exists l', Rai
sed (size l) l' ∧ BalancedSz l' (size r)) ∨ exists r', Raised r' (size r) ∧ Bala
ncedSz (size l) r'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balanceR_eq_balance'`：balanceR_eq_balance' {l x r} (hl : Balance
d l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised (si
ze l) l' ∧ Balance…
· 使用定理 `Ordnode.all_balance'`：all_balance' {P l x r} : @All α P (balance' l x r)
 ↔ All P l ∧ P x ∧ All P r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem all_balanceR {P l x r} (hl : Balanced l) (hr : Balanced r) (sl : Sized l) (sr : Sized r)
    (H :
      (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    All P (@balanceR α l x r) ↔ All P l ∧ P x ∧ All P r := by
  rw [balanceR_eq_balance' hl hr sl sr H, all_balance']

section Bounded

variable [Preorder α]

/-- `Bounded t lo hi` says that every element `x ∈ t` is in the range `lo < x < hi`, and also this
property holds recursively in subtrees, making the full tree a BST. The bounds can be set to
`lo = ⊥` and `hi = ⊤` if we care only about the internal ordering constraints. -/
/-
**Ordnode.Bounded** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：{α : Type u_1} → [Preorder α] → Ordnode α → WithBot α → WithTop α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Bounded t lo hi` says that every element `x ∈ t` is in the range `lo < x < hi`,
 and also this
property holds recursively in subtrees, making the full tree a BST. The bounds c
an be set to
`lo = ⊥` and `hi = ⊤` if we care only about the internal ordering constraints.
-/
def Bounded : Ordnode α → WithBot α → WithTop α → Prop
  | nil, some a, some b => a < b
  | nil, _, _ => True
  | node _ l x r, o₁, o₂ => Bounded l o₁ x ∧ Bounded r (↑x) o₂
/-
**Ordnode.Bounded.dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α},   t.Bounded o₁ o₂ → t.dual.Bounded o₂ o₁
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.dual :
    ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → @Bounded αᵒᵈ _ (dual t) o₂ o₁
  | nil, o₁, o₂, h => by cases o₁ <;> cases o₂ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨Or.dual, ol.dual⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.Bounded.dual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α},   t.Bounded o₁ o₂ ↔ t.dual.Bounded o₂ o₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Bounded.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   t.Bounded o₁ o₂ → t.dual.Bounded o₂ o₁
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderDual.Preorder.dual_dual`：∀ (α : Type u_2) [H : Preorder α], OrderDu
al.instPreorder αᵒᵈ = H
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
-/
theorem Bounded.dual_iff {t : Ordnode α} {o₁ o₂} :
    Bounded t o₁ o₂ ↔ @Bounded αᵒᵈ _ (.dual t) o₂ o₁ :=
  ⟨Bounded.dual, fun h => by
    have := Bounded.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩
/-
**Ordnode.Bounded.weak_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α}, t.Bounded o₁ o₂ → t.Bounded ⊥ o₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.weak_left : ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → Bounded t ⊥ o₂
  | nil, o₁, o₂, h => by cases o₂ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨ol.weak_left, Or⟩
/-
**Ordnode.Bounded.weak_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α}, t.Bounded o₁ o₂ → t.Bounded o₁ ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.weak_right : ∀ {t : Ordnode α} {o₁ o₂}, Bounded t o₁ o₂ → Bounded t o₁ ⊤
  | nil, o₁, o₂, h => by cases o₁ <;> trivial
  | node _ _ _ _, _, _, ⟨ol, Or⟩ => ⟨ol, Or.weak_right⟩
/-
**Ordnode.Bounded.weak** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α}, t.Bounded o₁ o₂ → t.Bounded ⊥ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Bounded.weak_right`：∀ {α : Type u_1} [inst : Preorder α] {t : Or
dnode α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Bounded o₁ o₂ → t.Bounded o₁ ⊤
· 使用定理 `Ordnode.Bounded.weak_left`：∀ {α : Type u_1} [inst : Preorder α] {t : Ord
node α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Bounded o₁ o₂ → t.Bounded ⊥ o₂
-/
theorem Bounded.weak {t : Ordnode α} {o₁ o₂} (h : Bounded t o₁ o₂) : Bounded t ⊥ ⊤ :=
  h.weak_left.weak_right
/-
**Ordnode.Bounded.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x y : α},   x ≤ y → ∀ {t : Ordnode α
} {o : WithTop α}, t.Bounded (↑y) o → t.Bounded (↑x) o
参数：↑y；↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.mono_left {x y : α} (xy : x ≤ y) :
    ∀ {t : Ordnode α} {o}, Bounded t y o → Bounded t x o
  | nil, none, _ => ⟨⟩
  | nil, some _, h => lt_of_le_of_lt xy h
  | node _ _ _ _, _o, ⟨ol, or⟩ => ⟨ol.mono_left xy, or⟩
/-
**Ordnode.Bounded.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x y : α},   x ≤ y → ∀ {t : Ordnode α
} {o : WithBot α}, t.Bounded o ↑x → t.Bounded o ↑y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.mono_right {x y : α} (xy : x ≤ y) :
    ∀ {t : Ordnode α} {o}, Bounded t o x → Bounded t o y
  | nil, none, _ => ⟨⟩
  | nil, some _, h => lt_of_lt_of_le h xy
  | node _ _ _ _, _o, ⟨ol, or⟩ => ⟨ol, or.mono_right xy⟩
/-
**Ordnode.Bounded.to_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {x y : α}, t.Bounded 
↑x ↑y → x < y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.to_lt : ∀ {t : Ordnode α} {x y : α}, Bounded t x y → x < y
  | nil, _, _, h => h
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ => lt_trans h₁.to_lt h₂.to_lt
/-
**Ordnode.Bounded.to_nil** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α},   t.Bounded o₁ o₂ → Ordnode.nil.Bounded o₁ o₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Bounded.to_lt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode
 α} {x y : α}, t.Bounded ↑x ↑y → x < y
-/
theorem Bounded.to_nil {t : Ordnode α} : ∀ {o₁ o₂}, Bounded t o₁ o₂ → Bounded nil o₁ o₂
  | none, _, _ => ⟨⟩
  | some _, none, _ => ⟨⟩
  | some _, some _, h => h.to_lt
/-
**Ordnode.Bounded.trans_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ : Ordnode α} {x : α} {o₁ : Wit
hBot α} {o₂ : WithTop α},   t₁.Bounded o₁ ↑x → t₂.Bounded (↑x) o₂ → t₂.Bounded o
₁ o₂
参数：↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Bounded.weak_left`：∀ {α : Type u_1} [inst : Preorder α] {t : Ord
node α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Bounded o₁ o₂ → t.Bounded ⊥ o₂
· 使用定理 `Ordnode.Bounded.mono_left`：∀ {α : Type u_1} [inst : Preorder α] {x y : α
},   x ≤ y → ∀ {t : Ordnode α} {o : WithTop α}, t.Bounded (↑y) o → t.Bounded (↑x
) o
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordnode.Bounded.to_lt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode
 α} {x y : α}, t.Bounded ↑x ↑y → x < y
-/
theorem Bounded.trans_left {t₁ t₂ : Ordnode α} {x : α} :
    ∀ {o₁ o₂}, Bounded t₁ o₁ x → Bounded t₂ x o₂ → Bounded t₂ o₁ o₂
  | none, _, _, h₂ => h₂.weak_left
  | some _, _, h₁, h₂ => h₂.mono_left (le_of_lt h₁.to_lt)
/-
**Ordnode.Bounded.trans_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ : Ordnode α} {x : α} {o₁ : Wit
hBot α} {o₂ : WithTop α},   t₁.Bounded o₁ ↑x → t₂.Bounded (↑x) o₂ → t₁.Bounded o
₁ o₂
参数：↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Bounded.weak_right`：∀ {α : Type u_1} [inst : Preorder α] {t : Or
dnode α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Bounded o₁ o₂ → t.Bounded o₁ ⊤
· 使用定理 `Ordnode.Bounded.mono_right`：∀ {α : Type u_1} [inst : Preorder α] {x y : 
α},   x ≤ y → ∀ {t : Ordnode α} {o : WithBot α}, t.Bounded o ↑x → t.Bounded o ↑y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Ordnode.Bounded.to_lt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode
 α} {x y : α}, t.Bounded ↑x ↑y → x < y
-/
theorem Bounded.trans_right {t₁ t₂ : Ordnode α} {x : α} :
    ∀ {o₁ o₂}, Bounded t₁ o₁ x → Bounded t₂ x o₂ → Bounded t₁ o₁ o₂
  | _, none, h₁, _ => h₁.weak_right
  | _, some _, h₁, h₂ => h₁.mono_right (le_of_lt h₂.to_lt)
/-
**Ordnode.Bounded.mem_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o : WithBot α} {x : 
α},   t.Bounded o ↑x → Ordnode.All (fun x_1 => x_1 < x) t
参数：fun x_1 => x_1 < x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.mem_lt : ∀ {t o} {x : α}, Bounded t o x → All (· < x) t
  | nil, _, _, _ => ⟨⟩
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ =>
    ⟨h₁.mem_lt.imp fun _ h => lt_trans h h₂.to_lt, h₂.to_lt, h₂.mem_lt⟩
/-
**Ordnode.Bounded.mem_gt** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o : WithTop α} {x : 
α},   t.Bounded (↑x) o → Ordnode.All (fun x_1 => x_1 > x) t
参数：↑x；fun x_1 => x_1 > x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.mem_gt : ∀ {t o} {x : α}, Bounded t x o → All (· > x) t
  | nil, _, _, _ => ⟨⟩
  | node _ _ _ _, _, _, ⟨h₁, h₂⟩ => ⟨h₁.mem_gt, h₁.to_lt, h₂.mem_gt.imp fun _ => lt_trans h₁.to_lt⟩
/-
**Ordnode.Bounded.of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α} {x : α},   t.Bounded o₁ o₂ → Ordnode.nil.Bounded o₁ ↑x → Ordnode.Al
l (fun x_1 => x_1 < x) t → t.Bounded o₁ ↑x
参数：fun x_1 => x_1 < x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.of_lt :
    ∀ {t o₁ o₂} {x : α}, Bounded t o₁ o₂ → Bounded nil o₁ x → All (· < x) t → Bounded t o₁ x
  | nil, _, _, _, _, hn, _ => hn
  | node _ _ _ _, _, _, _, ⟨h₁, h₂⟩, _, ⟨_, al₂, al₃⟩ => ⟨h₁, h₂.of_lt al₂ al₃⟩
/-
**Ordnode.Bounded.of_gt** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α} {x : α},   t.Bounded o₁ o₂ → Ordnode.nil.Bounded (↑x) o₂ → Ordnode.
All (fun x_1 => x_1 > x) t → t.Bounded (↑x) o₂
参数：↑x；fun x_1 => x_1 > x；↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Bounded.of_gt :
    ∀ {t o₁ o₂} {x : α}, Bounded t o₁ o₂ → Bounded nil x o₂ → All (· > x) t → Bounded t x o₂
  | nil, _, _, _, _, hn, _ => hn
  | node _ _ _ _, _, _, _, ⟨h₁, h₂⟩, _, ⟨al₁, al₂, _⟩ => ⟨h₁.of_gt al₂ al₁, h₂⟩
/-
**Ordnode.Bounded.to_sep** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Bounded`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ : Ordnode α} {o₁ : WithBot α} 
{o₂ : WithTop α} {x : α},   t₁.Bounded o₁ ↑x → t₂.Bounded (↑x) o₂ → Ordnode.All 
(fun y => Ordnode.All (fun z => y < z) t₂) t₁
参数：↑x；fun y => Ordnode.All (fun z => y < z) t₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.All.imp`：∀ {α : Type u_1} {P Q : α → Prop}, (∀ (a : α), P a → Q 
a) → ∀ {t : Ordnode α}, Ordnode.All P t → Ordnode.All Q t
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Ordnode.Bounded.mem_gt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnod
e α} {o : WithTop α} {x : α},   t.Bounded (↑x) o → Ordnode.All (fun x_1 => x_1 >
 x) t
· 使用定理 `Ordnode.Bounded.mem_lt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnod
e α} {o : WithBot α} {x : α},   t.Bounded o ↑x → Ordnode.All (fun x_1 => x_1 < x
) t
-/
theorem Bounded.to_sep {t₁ t₂ o₁ o₂} {x : α}
    (h₁ : Bounded t₁ o₁ (x : WithTop α)) (h₂ : Bounded t₂ (x : WithBot α) o₂) :
    t₁.All fun y => t₂.All fun z : α => y < z := by
  refine h₁.mem_lt.imp fun y yx => ?_
  exact h₂.mem_gt.imp fun z xz => lt_trans yx xz

end Bounded

end Ordnode

