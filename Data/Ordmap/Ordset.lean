/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Ordmap.Invariants

/-!
# Verification of `Ordnode`

This file uses the invariants defined in `Mathlib/Data/Ordmap/Invariants.lean` to construct
`Ordset α`, a wrapper around `Ordnode α` which includes the correctness invariant of the type.
It exposes parallel operations like `insert` as functions on `Ordset` that do the same thing but
bundle the correctness proofs.

The advantage is that it is possible to, for example, prove that the result of `find` on `insert`
will actually find the element, while `Ordnode` cannot guarantee this if the input tree did not
satisfy the type invariants.

## Main definitions

* `Ordnode.Valid`: The validity predicate for an `Ordnode` subtree.
* `Ordset α`: A well-formed set of values of type `α`.

## Implementation notes

Because the `Ordnode` file was ported from Haskell, the correctness invariants of some
of the functions have not been spelled out, and some theorems like
`Ordnode.Valid'.balanceL_aux` show very intricate assumptions on the sizes,
which may need to be revised if it turns out some operations violate these assumptions,
because there is a decent amount of slop in the actual data structure invariants, so the
theorem will go through with multiple choices of assumption.
-/

@[expose] public section


variable {α : Type*}

namespace Ordnode

section Valid

variable [Preorder α]

/-- The validity predicate for an `Ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. This version of `Valid` also puts all elements in the tree in the interval `(lo, hi)`. -/
/-
**Ordnode.Valid'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α} {o} (h : Valid' y
 t o) : Valid' x t o
参数：xy : x <= y；h : Valid' y t o。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The validity predicate for an `Ordnode` subtree. This asserts that the `size` fi
elds are
correct, the tree is balanced, and the elements of the tree are organized accord
ing to the
ordering. This version of `Valid` also puts all elements in the tree in the inte
rval `(lo, hi)`.
-/
structure Valid' (lo : WithBot α) (t : Ordnode α) (hi : WithTop α) : Prop where
  ord : t.Bounded lo hi
  sz : t.Sized
  bal : t.Balanced

/-- The validity predicate for an `Ordnode` subtree. This asserts that the `size` fields are
correct, the tree is balanced, and the elements of the tree are organized according to the
ordering. -/
/-
**Ordnode.Valid** 是 Mathlib 中的一个定义，位于命名空间 `Ordnode`。
形式化陈述：Valid (t : Ordnode α) : Prop
参数：t : Ordnode α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o

--- 原说明 ---
The validity predicate for an `Ordnode` subtree. This asserts that the `size` fi
elds are
correct, the tree is balanced, and the elements of the tree are organized accord
ing to the
ordering.
-/
def Valid (t : Ordnode α) : Prop :=
  Valid' ⊥ t ⊤
/-
**Ordnode.Valid'.mono_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x y : α},   x ≤ y → ∀ {t : Ordnode α
} {o : WithTop α}, Ordnode.Valid' (↑y) t o → Ordnode.Valid' (↑x) t o
参数：↑y；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Bounded.mono_left`：∀ {α : Type u_1} [inst : Preorder α] {x y : α
},   x ≤ y → ∀ {t : Ordnode α} {o : WithTop α}, t.Bounded (↑y) o → t.Bounded (↑x
) o
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.mono_left {x y : α} (xy : x ≤ y) {t : Ordnode α} {o} (h : Valid' y t o) :
    Valid' x t o :=
  ⟨h.1.mono_left xy, h.2, h.3⟩
/-
**Ordnode.Valid'.mono_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x y : α},   x ≤ y → ∀ {t : Ordnode α
} {o : WithBot α}, Ordnode.Valid' o t ↑x → Ordnode.Valid' o t ↑y
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Bounded.mono_right`：∀ {α : Type u_1} [inst : Preorder α] {x y : 
α},   x ≤ y → ∀ {t : Ordnode α} {o : WithBot α}, t.Bounded o ↑x → t.Bounded o ↑y
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.mono_right {x y : α} (xy : x ≤ y) {t : Ordnode α} {o} (h : Valid' o t x) :
    Valid' o t y :=
  ⟨h.1.mono_right xy, h.2, h.3⟩
/-
**Ordnode.Valid'.trans_left** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ : Ordnode α} {x : α} {o₁ : Wit
hBot α} {o₂ : WithTop α},   t₁.Bounded o₁ ↑x → Ordnode.Valid' (↑x) t₂ o₂ → Ordno
de.Valid' o₁ t₂ o₂
参数：↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Bounded.trans_left`：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ 
: Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   t₁.Bounded o₁ ↑x → t₂.
Bounded (↑x) o₂ …
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.trans_left {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (h : Bounded t₁ o₁ x)
    (H : Valid' x t₂ o₂) : Valid' o₁ t₂ o₂ :=
  ⟨h.trans_left H.1, H.2, H.3⟩
/-
**Ordnode.Valid'.trans_right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ : Ordnode α} {x : α} {o₁ : Wit
hBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t₁ ↑x → t₂.Bounded (↑x) o₂ → Ordno
de.Valid' o₁ t₁ o₂
参数：↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Bounded.trans_right`：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂
 : Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   t₁.Bounded o₁ ↑x → t₂
.Bounded (↑x) o₂ …
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.trans_right {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t₁ x)
    (h : Bounded t₂ x o₂) : Valid' o₁ t₁ o₂ :=
  ⟨H.1.trans_right h, H.2, H.3⟩
/-
**Ordnode.Valid'.of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {x : α} {o₁ : WithBot
 α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.nil.Bounded o₁ ↑x → Ord
node.All (fun x_1 => x_1 < x) t → Ordnode.Valid' o₁ t ↑x
参数：fun x_1 => x_1 < x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Bounded.of_lt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode
 α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},   t.Bounded o₁ o₂ → Ordnode.nil.B
ounded o₁ ↑…
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.of_lt {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil o₁ x)
    (h₂ : All (· < x) t) : Valid' o₁ t x :=
  ⟨H.1.of_lt h₁ h₂, H.2, H.3⟩
/-
**Ordnode.Valid'.of_gt** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {x : α} {o₁ : WithBot
 α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.nil.Bounded (↑x) o₂ → O
rdnode.All (fun x_1 => x_1 > x) t → Ordnode.Valid' (↑x) t o₂
参数：↑x；fun x_1 => x_1 > x；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Bounded.of_gt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode
 α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},   t.Bounded o₁ o₂ → Ordnode.nil.B
ounded (↑x)…
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.of_gt {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil x o₂)
    (h₂ : All (· > x) t) : Valid' x t o₂ :=
  ⟨H.1.of_gt h₁ h₂, H.2, H.3⟩
/-
**Ordnode.Valid'.valid** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α}, Ordnode.Valid' o₁ t o₂ → t.Valid
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Bounded.weak`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α}, t.Bounded o₁ o₂ → t.Bounded ⊥ ⊤
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.valid {t o₁ o₂} (h : @Valid' α _ o₁ t o₂) : Valid t :=
  ⟨h.1.weak, h.2, h.3⟩
/-
**Ordnode.valid'_nil** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {o₁ : WithBot α} {o₂ : WithTop α},   
Ordnode.nil.Bounded o₁ o₂ → Ordnode.Valid' o₁ Ordnode.nil o₂
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem valid'_nil {o₁ o₂} (h : Bounded nil o₁ o₂) : Valid' o₁ (@nil α) o₂ :=
  ⟨h, ⟨⟩, ⟨⟩⟩
/-
**Ordnode.valid_nil** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：valid_nil : Valid (@nil α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.valid'_nil`：∀ {α : Type u_1} [inst : Preorder α] {o₁ : WithBot α
} {o₂ : WithTop α},   Ordnode.nil.Bounded o₁ o₂ → Ordnode.Valid' o₁ Ordnode.nil 
o₂
-/
theorem valid_nil : Valid (@nil α) :=
  valid'_nil ⟨⟩
/-
**Ordnode.Valid'.node** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : 
Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ord
node.Valid' (↑x) r o₂ →       Ordnode.BalancedSz l.size r.size → s = l.size + r.
size + 1 → Ordnode.Valid' o₁ (Ordnode.node s l x r) o₂
参数：↑x；Ordnode.node s l x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.node {s l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : BalancedSz (size l) (size r)) (hs : s = size l + size r + 1) :
    Valid' o₁ (@node α s l x r) o₂ :=
  ⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.Valid'.dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o₂ t.dual o₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
-/
theorem Valid'.dual : ∀ {t : Ordnode α} {o₁ o₂}, Valid' o₁ t o₂ → @Valid' αᵒᵈ _ o₂ (dual t) o₁
  | .nil, _, _, h => valid'_nil h.1.dual
  | .node _ l _ r, _, _, ⟨⟨ol, Or⟩, ⟨rfl, sl, sr⟩, ⟨b, bl, br⟩⟩ =>
    let ⟨ol', sl', bl'⟩ := Valid'.dual ⟨ol, sl, bl⟩
    let ⟨or', sr', br'⟩ := Valid'.dual ⟨Or, sr, br⟩
    ⟨⟨or', ol'⟩, ⟨by simp [size_dual, add_comm], sr', sl'⟩,
      ⟨by rw [size_dual, size_dual]; exact b.symm, br', bl'⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.Valid'.dual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α} {o₁ : WithBot α} {o₂ 
: WithTop α},   Ordnode.Valid' o₁ t o₂ ↔ Ordnode.Valid' o₂ t.dual o₁
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α
} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o
₂ t.dual …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderDual.Preorder.dual_dual`：∀ (α : Type u_2) [H : Preorder α], OrderDu
al.instPreorder αᵒᵈ = H
· 使用定理 `Ordnode.dual_dual`：∀ {α : Type u_1} (t : Ordnode α), t.dual.dual = t
-/
theorem Valid'.dual_iff {t : Ordnode α} {o₁ o₂} : Valid' o₁ t o₂ ↔ @Valid' αᵒᵈ _ o₂ (.dual t) o₁ :=
  ⟨Valid'.dual, fun h => by
    have := Valid'.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩
/-
**Ordnode.Valid.dual** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α}, t.Valid → t.dual.Val
id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α
} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o
₂ t.dual …
-/
theorem Valid.dual {t : Ordnode α} : Valid t → @Valid αᵒᵈ _ (.dual t) :=
  Valid'.dual
/-
**Ordnode.Valid.dual_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α}, t.Valid ↔ t.dual.Val
id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'.dual_iff`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordno
de α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ ↔ Ordnode.Vali
d' o₂ t.dual …
-/
theorem Valid.dual_iff {t : Ordnode α} : Valid t ↔ @Valid αᵒᵈ _ (.dual t) :=
  Valid'.dual_iff
/-
**Ordnode.Valid'.left** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : 
Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ (Ordnode.node 
s l x r) o₂ → Ordnode.Valid' o₁ l ↑x
参数：Ordnode.node s l x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.left {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂) : Valid' o₁ l x :=
  ⟨H.1.1, H.2.2.1, H.3.2.1⟩
/-
**Ordnode.Valid'.right** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : 
Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ (Ordnode.node 
s l x r) o₂ → Ordnode.Valid' (↑x) r o₂
参数：Ordnode.node s l x r；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.right {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂) : Valid' x r o₂ :=
  ⟨H.1.2, H.2.2.2, H.3.2.2⟩

nonrec theorem Valid.left {s l x r} (H : Valid (@node α s l x r)) : Valid l :=
  H.left.valid

nonrec theorem Valid.right {s l x r} (H : Valid (@node α s l x r)) : Valid r :=
  H.right.valid
/-
**Ordnode.Valid.size_eq** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : 
Ordnode α},   (Ordnode.node s l x r).Valid → (Ordnode.node s l x r).size = l.siz
e + r.size + 1
参数：Ordnode.node s l x r；Ordnode.node s l x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
-/
theorem Valid.size_eq {s l x r} (H : Valid (@node α s l x r)) :
    size (@node α s l x r) = size l + size r + 1 :=
  H.2.1
/-
**Ordnode.Valid'.node'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ → Ordnode.BalancedSz l.size r.size → Ordnode.Valid' o₁ (l.node' x 
r) o₂
参数：↑x；l.node' x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.node`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ …
-/
theorem Valid'.node' {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : BalancedSz (size l) (size r)) : Valid' o₁ (@node' α l x r) o₂ :=
  hl.node hr H rfl
/-
**Ordnode.valid'_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {x : α} {o₁ : WithBot α} {o₂ : WithTo
p α},   Ordnode.nil.Bounded o₁ ↑x → Ordnode.nil.Bounded (↑x) o₂ → Ordnode.Valid'
 o₁ {x} o₂
参数：↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'.node`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ …
· 使用定理 `Ordnode.valid'_nil`：∀ {α : Type u_1} [inst : Preorder α] {o₁ : WithBot α
} {o₂ : WithTop α},   Ordnode.nil.Bounded o₁ o₂ → Ordnode.Valid' o₁ Ordnode.nil 
o₂
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem valid'_singleton {x : α} {o₁ o₂} (h₁ : Bounded nil o₁ x) (h₂ : Bounded nil x o₂) :
    Valid' o₁ (singleton x : Ordnode α) o₂ :=
  (valid'_nil h₁).node (valid'_nil h₂) (Or.inl zero_le_one) rfl
/-
**Ordnode.valid_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：valid_singleton {x : α} : Valid (singleton x : Ordnode α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.valid'_singleton`：∀ {α : Type u_1} [inst : Preorder α] {x : α} {
o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.nil.Bounded o₁ ↑x → Ordnode.nil.Boun
ded (↑x) o₂ → …
-/
theorem valid_singleton {x : α} : Valid (singleton x : Ordnode α) :=
  valid'_singleton ⟨⟩ ⟨⟩
/-
**Ordnode.Valid'.node3L** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {m : Ordnode 
α} {y : α} {r : Ordnode α} {o₁ : WithBot α}   {o₂ : WithTop α},   Ordnode.Valid'
 o₁ l ↑x →     Ordnode.Valid' (↑x) m ↑y →       Ordnode.Valid' (↑y) r o₂ →      
   Ordnode.BalancedSz l.size m.size →           Ordnode.BalancedSz (l.size + m.s
ize + 1) r.size → Ordnode.Valid' o₁ (l.node3L x m y r) o₂
参数：↑x；↑y；l.size + m.size + 1；l.node3L x m y r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.node'`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode 
α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o
₁ l ↑x →  …
-/
theorem Valid'.node3L {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' y r o₂) (H1 : BalancedSz (size l) (size m))
    (H2 : BalancedSz (size l + size m + 1) (size r)) : Valid' o₁ (@node3L α l x m y r) o₂ :=
  (hl.node' hm H1).node' hr H2
/-
**Ordnode.Valid'.node3R** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {m : Ordnode 
α} {y : α} {r : Ordnode α} {o₁ : WithBot α}   {o₂ : WithTop α},   Ordnode.Valid'
 o₁ l ↑x →     Ordnode.Valid' (↑x) m ↑y →       Ordnode.Valid' (↑y) r o₂ →      
   Ordnode.BalancedSz l.size (m.size + r.size + 1) →           Ordnode.BalancedS
z m.size r.size → Ordnode.Valid' o₁ (l.node3R x m y r) o₂
参数：↑x；↑y；m.size + r.size + 1；l.node3R x m y r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.node'`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode 
α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o
₁ l ↑x →  …
-/
theorem Valid'.node3R {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' y r o₂) (H1 : BalancedSz (size l) (size m + size r + 1))
    (H2 : BalancedSz (size m) (size r)) : Valid' o₁ (@node3R α l x m y r) o₂ :=
  hl.node' (hm.node' hr H2) H1
/-
**Ordnode.Valid'.node4L_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.node4L_lemma₁ {a b c d : ℕ} (lr₂ : 3 * (b + c + 1 + d) ≤ 16 * a + 9)
    (mr₂ : b + c + 1 ≤ 3 * d) (mm₁ : b ≤ 3 * c) : b < 3 * a + 1 := by lia
/-
**Ordnode.Valid'.node4L_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.node4L_lemma₂ {b c d : ℕ} (mr₂ : b + c + 1 ≤ 3 * d) : c ≤ 3 * d := by lia
/-
**Ordnode.Valid'.node4L_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.node4L_lemma₃ {b c d : ℕ} (mr₁ : 2 * d ≤ b + c + 1) (mm₁ : b ≤ 3 * c) :
    d ≤ 3 * c := by lia
/-
**Ordnode.Valid'.node4L_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.node4L_lemma₄ {a b c d : ℕ} (lr₁ : 3 * a ≤ b + c + 1 + d) (mr₂ : b + c + 1 ≤ 3 * d)
    (mm₁ : b ≤ 3 * c) : a + b + 1 ≤ 3 * (c + d + 1) := by lia
/-
**Ordnode.Valid'.node4L_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.node4L_lemma₅ {a b c d : ℕ} (lr₂ : 3 * (b + c + 1 + d) ≤ 16 * a + 9)
    (mr₁ : 2 * d ≤ b + c + 1) (mm₂ : c ≤ 3 * b) : c + d + 1 ≤ 3 * (a + b + 1) := by lia
/-
**Ordnode.Valid'.node4L** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {m : Ordnode 
α} {y : α} {r : Ordnode α} {o₁ : WithBot α}   {o₂ : WithTop α},   Ordnode.Valid'
 o₁ l ↑x →     Ordnode.Valid' (↑x) m ↑y →       Ordnode.Valid' (↑y) r o₂ →      
   0 < m.size →           l.size = 0 ∧ m.size = 1 ∧ r.size ≤ 1 ∨               0
 < l.size ∧                 Ordnode.ratio * r.size ≤ m.size ∧                   
Ordnode.delta * l.size ≤ m.size + r.size ∧                     3 * (m.size + r.s
ize) ≤ 16 * l.size + 9 ∧ m.size ≤ Ordnode.delta * r.size →             Ordnode.V
alid' o₁ (l.node4L x m y r) o₂
参数：↑x；↑y；m.size + r.size；l.node4L x m y r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_eq_zero`：∀ {α : Type u} [inst : AddCommMonoid α] [Subsingleton (AddU
nits α)] {a b : α}, a + b = 0 ↔ a = 0 ∧ b = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.succ_inj`：∀ {a b : ℕ}, a.succ = b.succ ↔ a = b
· 使用定理 `Ordnode.Sized.size_eq`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α} 
{r : Ordnode α},   (Ordnode.node s l x r).Sized → (Ordnode.node s l x r).size = 
l.size + r.…
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_le_mul_iff_right₀`：mul_le_mul_iff_right₀ [PosMulMono α] [PosMulRefle
ctLE α] (a0 : 0 < a) : a * b <= a * c ↔ b <= c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 58 条，此处仅展示前 30 条）
-/
theorem Valid'.node4L {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' (↑y) r o₂) (Hm : 0 < size m)
    (H : size l = 0 ∧ size m = 1 ∧ size r ≤ 1 ∨
        0 < size l ∧
          ratio * size r ≤ size m ∧
            delta * size l ≤ size m + size r ∧
              3 * (size m + size r) ≤ 16 * size l + 9 ∧ size m ≤ delta * size r) :
    Valid' o₁ (@node4L α l x m y r) o₂ := by
  obtain - | ⟨s, ml, z, mr⟩ := m; · cases Hm
  suffices
    BalancedSz (size l) (size ml) ∧
      BalancedSz (size mr) (size r) ∧ BalancedSz (size l + size ml + 1) (size mr + size r + 1) from
    Valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2
  rcases H with (⟨l0, m1, r0⟩ | ⟨l0, mr₁, lr₁, lr₂, mr₂⟩)
  · rw [hm.2.size_eq, Nat.succ_inj, add_eq_zero] at m1
    rw [l0, m1.1, m1.2]; revert r0; rcases size r with (_ | _ | _) <;>
      [decide; decide; (intro r0; unfold BalancedSz delta; lia)]
  · rcases Nat.eq_zero_or_pos (size r) with r0 | r0
    · rw [r0] at mr₂; cases not_le_of_gt Hm mr₂
    rw [hm.2.size_eq] at lr₁ lr₂ mr₁ mr₂
    by_cases mm : size ml + size mr ≤ 1
    · dsimp [delta, ratio] at lr₁ mr₁
      have r1 : r.size = 1 := by lia
      have l1 : l.size = 1 := by lia
      rw [r1, add_assoc] at lr₁
      rw [l1, r1]
      revert mm; cases size ml <;> cases size mr <;> intro mm
      · decide
      · rw [zero_add] at mm; rcases mm with (_ | ⟨⟨⟩⟩)
        decide
      · rcases mm with (_ | ⟨⟨⟩⟩); decide
      · rw [Nat.succ_add] at mm; rcases mm with (_ | ⟨⟨⟩⟩)
    rcases hm.3.1.resolve_left mm with ⟨mm₁, mm₂⟩
    rcases Nat.eq_zero_or_pos (size ml) with ml0 | ml0
    · rw [ml0, mul_zero, Nat.le_zero] at mm₂
      rw [ml0, mm₂] at mm; cases mm (by decide)
    have : 2 * size l ≤ size ml + size mr + 1 := by
      have := Nat.mul_le_mul_left ratio lr₁
      rw [mul_left_comm, mul_add] at this
      have := le_trans this (add_le_add_right mr₁ _)
      rw [← Nat.succ_mul] at this
      exact (mul_le_mul_iff_right₀ (by decide)).1 this
    refine ⟨Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · refine (mul_le_mul_iff_right₀ (by decide)).1 (le_trans this ?_)
      rw [two_mul, Nat.succ_le_iff]
      refine add_lt_add_of_lt_of_le ?_ mm₂
      simpa using! mul_lt_mul_of_pos_right (by decide : 1 < 3) ml0
    · exact Nat.le_of_lt_succ (Valid'.node4L_lemma₁ lr₂ mr₂ mm₁)
    · exact Valid'.node4L_lemma₂ mr₂
    · exact Valid'.node4L_lemma₃ mr₁ mm₁
    · exact Valid'.node4L_lemma₄ lr₁ mr₂ mm₁
    · exact Valid'.node4L_lemma₅ lr₂ mr₁ mm₂
/-
**Ordnode.Valid'.rotateL_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.rotateL_lemma₁ {a b c : ℕ} (H2 : 3 * a ≤ b + c) (hb₂ : c ≤ 3 * b) : a ≤ 3 * b := by
  lia
/-
**Ordnode.Valid'.rotateL_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.rotateL_lemma₂ {a b c : ℕ} (H3 : 2 * (b + c) ≤ 9 * a + 3) (h : b < 2 * c) :
    b < 3 * a + 1 := by lia
/-
**Ordnode.Valid'.rotateL_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.rotateL_lemma₃ {a b c : ℕ} (H2 : 3 * a ≤ b + c) (h : b < 2 * c) : a + b < 3 * c := by
  lia
/-
**Ordnode.Valid'.rotateL_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.rotateL_lemma₄ {a b : ℕ} (H3 : 2 * b ≤ 9 * a + 3) : 3 * b ≤ 16 * a + 9 := by
  lia
/-
**Ordnode.Valid'.rotateL** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       ¬l.size + r.size ≤ 1 →         Ordnode.delta * l.size < r.
size →           2 * r.size ≤ 9 * l.size + 5 ∨ r.size ≤ 3 → Ordnode.Valid' o₁ (l
.rotateL x r) o₂
参数：↑x；l.rotateL x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Nat.le_of_add_le_add_right`：∀ {a b c : ℕ}, a + b ≤ c + b → a ≤ c
· 使用定理 `Nat.le_of_succ_le_succ`：∀ {n m : ℕ}, n.succ ≤ m.succ → n ≤ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.Sized.size_eq`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α} 
{r : Ordnode α},   (Ordnode.node s l x r).Sized → (Ordnode.node s l x r).size = 
l.size + r.…
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_iff_left_of_imp`：∀ {b a : Prop}, (b → a) → (a ∨ b ↔ a)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Ordnode.rotateL_node`：rotateL_node (l : Ordnode α) (x : α) (sz : Nat) (m
 : Ordnode α) (y : α) (r : Ordnode α) : rotateL l x (node sz m y r) = if size m 
< ratio * …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_lt_mul_iff_right₀`：mul_lt_mul_iff_right₀ [PosMulStrictMono α] [PosMu
lReflectLT α] (a0 : 0 < a) : a * b < a * c ↔ b < c where mp h
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ordnode.balancedSz_zero`：balancedSz_zero {l : Nat} : BalancedSz l 0 ↔ l 
<= 1
· 使用定理 `Ordnode.BalancedSz.symm`：∀ {l r : ℕ}, Ordnode.BalancedSz l r → Ordnode.B
alancedSz r l
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
（共 49 条，此处仅展示前 30 条）
-/
theorem Valid'.rotateL {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H1 : ¬size l + size r ≤ 1) (H2 : delta * size l < size r)
    (H3 : 2 * size r ≤ 9 * size l + 5 ∨ size r ≤ 3) : Valid' o₁ (@rotateL α l x r) o₂ := by
  obtain - | ⟨rs, rl, rx, rr⟩ := r; · cases H2
  rw [hr.2.size_eq, Nat.lt_succ_iff] at H2
  rw [hr.2.size_eq] at H3
  replace H3 : 2 * (size rl + size rr) ≤ 9 * size l + 3 ∨ size rl + size rr ≤ 2 :=
    H3.imp (@Nat.le_of_add_le_add_right _ 2 _) Nat.le_of_succ_le_succ
  have H3_0 (l0 : size l = 0) : size rl + size rr ≤ 2 := by lia
  have H3p : size l > 0 → 2 * (size rl + size rr) ≤ 9 * size l + 3 := fun l0 : 1 ≤ size l =>
    (or_iff_left_of_imp <| by lia).1 H3
  have ablem : ∀ {a b : ℕ}, 1 ≤ a → a + b ≤ 2 → b ≤ 1 := by lia
  have hlp : size l > 0 → ¬size rl + size rr ≤ 1 := fun l0 hb =>
    absurd (le_trans (le_trans (Nat.mul_le_mul_left _ l0) H2) hb) (by decide)
  rw [Ordnode.rotateL_node]; split_ifs with h
  · have rr0 : size rr > 0 :=
      (mul_lt_mul_iff_right₀ (by decide)).1 (lt_of_le_of_lt (Nat.zero_le _) h : ratio * 0 < _)
    suffices BalancedSz (size l) (size rl) ∧ BalancedSz (size l + size rl + 1) (size rr) by
      exact hl.node3L hr.left hr.right this.1 this.2
    rcases Nat.eq_zero_or_pos (size l) with l0 | l0
    · rw [l0]; replace H3 := H3_0 l0
      have := hr.3.1
      rcases Nat.eq_zero_or_pos (size rl) with rl0 | rl0
      · rw [rl0] at this ⊢
        rw [le_antisymm (balancedSz_zero.1 this.symm) rr0]
        decide
      have rr1 : size rr = 1 := le_antisymm (ablem rl0 H3) rr0
      rw [add_comm] at H3
      rw [rr1, show size rl = 1 from le_antisymm (ablem rr0 H3) rl0]
      decide
    replace H3 := H3p l0
    rcases hr.3.1.resolve_left (hlp l0) with ⟨_, hb₂⟩
    refine ⟨Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · exact Valid'.rotateL_lemma₁ H2 hb₂
    · exact Nat.le_of_lt_succ (Valid'.rotateL_lemma₂ H3 h)
    · exact Valid'.rotateL_lemma₃ H2 h
    · exact
        le_trans hb₂
          (Nat.mul_le_mul_left _ <| le_trans (Nat.le_add_left _ _) (Nat.le_add_right _ _))
  · rcases Nat.eq_zero_or_pos (size rl) with rl0 | rl0
    · rw [rl0, not_lt, Nat.le_zero, Nat.mul_eq_zero] at h
      replace h := h.resolve_left (by decide)
      rw [rl0, h, Nat.le_zero, Nat.mul_eq_zero] at H2
      rw [hr.2.size_eq, rl0, h, H2.resolve_left (by decide)] at H1
      cases H1 (by decide)
    refine hl.node4L hr.left hr.right rl0 ?_
    rcases Nat.eq_zero_or_pos (size l) with l0 | l0
    · replace H3 := H3_0 l0
      rcases Nat.eq_zero_or_pos (size rr) with rr0 | rr0
      · have := hr.3.1
        rw [rr0] at this
        exact Or.inl ⟨l0, le_antisymm (balancedSz_zero.1 this) rl0, rr0.symm ▸ zero_le_one⟩
      exact Or.inl ⟨l0, le_antisymm (ablem rr0 <| by rwa [add_comm]) rl0, ablem rl0 H3⟩
    exact
      Or.inr ⟨l0, not_lt.1 h, H2, Valid'.rotateL_lemma₄ (H3p l0), (hr.3.1.resolve_left (hlp l0)).1⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.Valid'.rotateR** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       ¬l.size + r.size ≤ 1 →         Ordnode.delta * r.size < l.
size →           2 * l.size ≤ 9 * r.size + 5 ∨ l.size ≤ 3 → Ordnode.Valid' o₁ (l
.rotateR x r) o₂
参数：↑x；l.rotateR x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordnode.Valid'.dual_iff`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordno
de α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ ↔ Ordnode.Vali
d' o₂ t.dual …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.dual_rotateR`：dual_rotateR (l : Ordnode α) (x : α) (r : Ordnode 
α) : dual (rotateR l x r) = rotateL (dual r) x (dual l)
· 使用定理 `Ordnode.Valid'.rotateL`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnod
e α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid'
 o₁ l ↑x →  …
· 使用定理 `Ordnode.Valid'.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α
} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o
₂ t.dual …
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem Valid'.rotateR {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H1 : ¬size l + size r ≤ 1) (H2 : delta * size r < size l)
    (H3 : 2 * size l ≤ 9 * size r + 5 ∨ size l ≤ 3) : Valid' o₁ (@rotateR α l x r) o₂ := by
  refine Valid'.dual_iff.2 ?_
  rw [dual_rotateR]
  refine hr.dual.rotateL hl.dual ?_ ?_ ?_
  · rwa [size_dual, size_dual, add_comm]
  · rwa [size_dual, size_dual]
  · rwa [size_dual, size_dual]
/-
**Ordnode.Valid'.balance'_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       2 * r.size ≤ 9 * l.size + 5 ∨ r.size ≤ 3 →         2 * l.s
ize ≤ 9 * r.size + 5 ∨ l.size ≤ 3 → Ordnode.Valid' o₁ (l.balance' x r) o₂
参数：↑x；l.balance' x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balance'.eq_1`：∀ {α : Type u_1} (l : Ordnode α) (x : α) (r : Ord
node α),   l.balance' x r =     if l.size + r.size ≤ 1 then l.node' x r     else
       if r…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ordnode.Valid'.node'`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode 
α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o
₁ l ↑x →  …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.Valid'.rotateL`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnod
e α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid'
 o₁ l ↑x →  …
· 使用定理 `Ordnode.Valid'.rotateR`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnod
e α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid'
 o₁ l ↑x →  …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem Valid'.balance'_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : 2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3)
    (H₂ : 2 * @size α l ≤ 9 * size r + 5 ∨ size l ≤ 3) : Valid' o₁ (@balance' α l x r) o₂ := by
  rw [balance']; split_ifs with h h_1 h_2
  · exact hl.node' hr (Or.inl h)
  · exact hl.rotateL hr h h_1 H₁
  · exact hl.rotateR hr h h_2 H₂
  · exact hl.node' hr (Or.inr ⟨not_lt.1 h_2, not_lt.1 h_1⟩)
/-
**Ordnode.Valid'.balance'_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_2} {l : Ordnode α} {l' : ℕ} {r : Ordnode α} {r' : ℕ},   Ordn
ode.BalancedSz l' r' →     l.size.dist l' ≤ 1 ∧ r.size = r' ∨ r.size.dist r' ≤ 1
 ∧ l.size = l' → 2 * r.size ≤ 9 * l.size + 5 ∨ r.size ≤ 3
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `Nat.dist_tri_right`：dist_tri_right (n m : Nat) : m <= n + dist n m
· 使用定理 `Nat.add_le_add_left`：∀ {n m : ℕ}, n ≤ m → ∀ (k : ℕ), k + n ≤ k + m
· 使用定理 `Nat.dist_tri_left'`：dist_tri_left' (n m : Nat) : n <= dist n m + m
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.mul_succ`：∀ (n m : ℕ), n * m.succ = n * m + n
· 使用定理 `Nat.dist_tri_right'`：dist_tri_right' (n m : Nat) : n <= m + dist n m
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem Valid'.balance'_lemma {α l l' r r'} (H1 : BalancedSz l' r')
    (H2 : Nat.dist (@size α l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l') :
    2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3 := by
  suffices @size α r ≤ 3 * (size l + 1) by lia
  rcases H2 with (⟨hl, rfl⟩ | ⟨hr, rfl⟩) <;> rcases H1 with (h | ⟨_, h₂⟩)
  · exact le_trans (Nat.le_add_left _ _) (le_trans h (Nat.le_add_left _ _))
  · exact
      le_trans h₂
        (Nat.mul_le_mul_left _ <| le_trans (Nat.dist_tri_right _ _) (Nat.add_le_add_left hl _))
  · exact
      le_trans (Nat.dist_tri_left' _ _)
        (le_trans (add_le_add hr (le_trans (Nat.le_add_left _ _) h)) (by lia))
  · rw [Nat.mul_succ]
    exact le_trans (Nat.dist_tri_right' _ _) (add_le_add h₂ (le_trans hr (by decide)))
/-
**Ordnode.Valid'.balance'** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       (∃ l' r', Ordnode.BalancedSz l' r' ∧ (l.size.dist l' ≤ 1 ∧
 r.size = r' ∨ r.size.dist r' ≤ 1 ∧ l.size = l')) →         Ordnode.Valid' o₁ (l
.balance' x r) o₂
参数：↑x；∃ l' r', Ordnode.BalancedSz l' r' ∧ (l.size.dist l' ≤ 1 ∧ r.size = r' ∨ r.
size.dist r' ≤ 1 ∧ l.size = l')；l.balance' x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.balance'_aux`：∀ {α : Type u_1} [inst : Preorder α] {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ l ↑x →  …
· 使用定理 `Ordnode.Valid'.balance'_lemma`：∀ {α : Type u_2} {l : Ordnode α} {l' : ℕ}
 {r : Ordnode α} {r' : ℕ},   Ordnode.BalancedSz l' r' →     l.size.dist l' ≤ 1 ∧
 r.size = r' ∨ r.si…
· 使用定理 `Ordnode.BalancedSz.symm`：∀ {l r : ℕ}, Ordnode.BalancedSz l r → Ordnode.B
alancedSz r l
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
theorem Valid'.balance' {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : ∃ l' r', BalancedSz l' r' ∧
          (Nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
    Valid' o₁ (@balance' α l x r) o₂ :=
  let ⟨_, _, H1, H2⟩ := H
  Valid'.balance'_aux hl hr (Valid'.balance'_lemma H1 H2) (Valid'.balance'_lemma H1.symm H2.symm)
/-
**Ordnode.Valid'.balance** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       (∃ l' r', Ordnode.BalancedSz l' r' ∧ (l.size.dist l' ≤ 1 ∧
 r.size = r' ∨ r.size.dist r' ≤ 1 ∧ l.size = l')) →         Ordnode.Valid' o₁ (l
.balance x r) o₂
参数：↑x；∃ l' r', Ordnode.BalancedSz l' r' ∧ (l.size.dist l' ≤ 1 ∧ r.size = r' ∨ r.
size.dist r' ≤ 1 ∧ l.size = l')；l.balance x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balance_eq_balance'`：balance_eq_balance' {l x r} (hl : Balanced 
l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) : @balance α l x r = balance'
 l x r
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.balance'`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordno
de α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid
' o₁ l ↑x →  …
-/
theorem Valid'.balance {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : ∃ l' r', BalancedSz l' r' ∧
          (Nat.dist (size l) l' ≤ 1 ∧ size r = r' ∨ Nat.dist (size r) r' ≤ 1 ∧ size l = l')) :
    Valid' o₁ (@balance α l x r) o₂ := by
  rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2]; exact hl.balance' hr H
/-
**Ordnode.Valid'.balanceL_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       (l.size = 0 → r.size ≤ 1) →         (1 ≤ l.size → 1 ≤ r.si
ze → r.size ≤ Ordnode.delta * l.size) →           2 * l.size ≤ 9 * r.size + 5 ∨ 
l.size ≤ 3 → Ordnode.Valid' o₁ (l.balanceL x r) o₂
参数：↑x；l.size = 0 → r.size ≤ 1；1 ≤ l.size → 1 ≤ r.size → r.size ≤ Ordnode.delta *
 l.size；l.balanceL x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balanceL_eq_balance`：balanceL_eq_balance {l x r} (sl : Sized l) 
(sr : Sized r) (H1 : size l = 0 -> size r <= 1) (H2 : 1 <= size l -> 1 <= size r
 -> size r <= del…
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.balance_eq_balance'`：balance_eq_balance' {l x r} (hl : Balanced 
l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) : @balance α l x r = balance'
 l x r
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用定理 `Ordnode.Valid'.balance'_aux`：∀ {α : Type u_1} [inst : Preorder α] {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ l ↑x →  …
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.mul_le_mul_left`：∀ {n m : ℕ} (k : ℕ), n ≤ m → k * n ≤ k * m
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
theorem Valid'.balanceL_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : size l = 0 → size r ≤ 1) (H₂ : 1 ≤ size l → 1 ≤ size r → size r ≤ delta * size l)
    (H₃ : 2 * @size α l ≤ 9 * size r + 5 ∨ size l ≤ 3) : Valid' o₁ (@balanceL α l x r) o₂ := by
  rw [balanceL_eq_balance hl.2 hr.2 H₁ H₂, balance_eq_balance' hl.3 hr.3 hl.2 hr.2]
  refine hl.balance'_aux hr (Or.inl ?_) H₃
  rcases Nat.eq_zero_or_pos (size r) with r0 | r0
  · rw [r0]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos (size l) with l0 | l0
  · rw [l0]; exact le_trans (Nat.mul_le_mul_left _ (H₁ l0)) (by decide)
  replace H₂ : _ ≤ 3 * _ := H₂ l0 r0; lia
/-
**Ordnode.Valid'.balanceL** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       ((∃ l', Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r
.size) ∨           ∃ r', Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r'
) →         Ordnode.Valid' o₁ (l.balanceL x r) o₂
参数：↑x；(∃ l', Ordnode.Raised l' l.size ∧ Ordnode.BalancedSz l' r.size) ∨         
  ∃ r', Ordnode.Raised r.size r' ∧ Ordnode.BalancedSz l.size r'；l.balanceL x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.balanceL_eq_balance'`：balanceL_eq_balance' {l x r} (hl : Balance
d l) (hr : Balanced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised l' 
(size l) ∧ Balance…
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.balance'`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordno
de α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid
' o₁ l ↑x →  …
· 使用定理 `Ordnode.Raised.dist_le'`：∀ {n m : ℕ}, Ordnode.Raised n m → m.dist n ≤ 1
· 使用定理 `Ordnode.Raised.dist_le`：∀ {n m : ℕ}, Ordnode.Raised n m → n.dist m ≤ 1
-/
theorem Valid'.balanceL {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : (∃ l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    Valid' o₁ (@balanceL α l x r) o₂ := by
  rw [balanceL_eq_balance' hl.3 hr.3 hl.2 hr.2 H]
  refine hl.balance' hr ?_
  rcases H with (⟨l', e, H⟩ | ⟨r', e, H⟩)
  · exact ⟨_, _, H, Or.inl ⟨e.dist_le', rfl⟩⟩
  · exact ⟨_, _, H, Or.inr ⟨e.dist_le, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.Valid'.balanceR_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       (r.size = 0 → l.size ≤ 1) →         (1 ≤ r.size → 1 ≤ l.si
ze → l.size ≤ Ordnode.delta * r.size) →           2 * r.size ≤ 9 * l.size + 5 ∨ 
r.size ≤ 3 → Ordnode.Valid' o₁ (l.balanceR x r) o₂
参数：↑x；r.size = 0 → l.size ≤ 1；1 ≤ r.size → 1 ≤ l.size → l.size ≤ Ordnode.delta *
 r.size；l.balanceR x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.Valid'.dual_iff`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordno
de α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ ↔ Ordnode.Vali
d' o₂ t.dual …
· 使用定理 `Ordnode.dual_balanceR`：dual_balanceR (l : Ordnode α) (x : α) (r : Ordnod
e α) : dual (balanceR l x r) = balanceL (dual r) x (dual l)
· 使用定理 `Ordnode.Valid'.balanceL_aux`：∀ {α : Type u_1} [inst : Preorder α] {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ l ↑x →  …
· 使用定理 `Ordnode.Valid'.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α
} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o
₂ t.dual …
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
-/
theorem Valid'.balanceR_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : size r = 0 → size l ≤ 1) (H₂ : 1 ≤ size r → 1 ≤ size l → size l ≤ delta * size r)
    (H₃ : 2 * @size α r ≤ 9 * size l + 5 ∨ size r ≤ 3) : Valid' o₁ (@balanceR α l x r) o₂ := by
  rw [Valid'.dual_iff, dual_balanceR]
  have := hr.dual.balanceL_aux hl.dual
  rw [size_dual, size_dual] at this
  exact this H₁ H₂ H₃

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.Valid'.balanceR** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       ((∃ l', Ordnode.Raised l.size l' ∧ Ordnode.BalancedSz l' r
.size) ∨           ∃ r', Ordnode.Raised r' r.size ∧ Ordnode.BalancedSz l.size r'
) →         Ordnode.Valid' o₁ (l.balanceR x r) o₂
参数：↑x；(∃ l', Ordnode.Raised l.size l' ∧ Ordnode.BalancedSz l' r.size) ∨         
  ∃ r', Ordnode.Raised r' r.size ∧ Ordnode.BalancedSz l.size r'；l.balanceR x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.Valid'.dual_iff`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordno
de α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ ↔ Ordnode.Vali
d' o₂ t.dual …
· 使用定理 `Ordnode.dual_balanceR`：dual_balanceR (l : Ordnode α) (x : α) (r : Ordnod
e α) : dual (balanceR l x r) = balanceL (dual r) x (dual l)
· 使用定理 `Ordnode.Valid'.balanceL`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordno
de α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid
' o₁ l ↑x →  …
· 使用定理 `Ordnode.Valid'.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α
} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o
₂ t.dual …
· 使用定理 `Ordnode.balance_sz_dual`：balance_sz_dual {l r} (H : (exists l', Raised (
@size α l) l' ∧ BalancedSz l' (@size α r)) ∨ exists r', Raised r' (size r) ∧ Bal
ancedSz (size…
-/
theorem Valid'.balanceR {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : (∃ l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        ∃ r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    Valid' o₁ (@balanceR α l x r) o₂ := by
  rw [Valid'.dual_iff, dual_balanceR]; exact hr.dual.balanceL hl.dual (balance_sz_dual H)
/-
**Ordnode.Valid'.eraseMax_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : 
Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ (Ordnode.node 
s l x r) o₂ →     Ordnode.Valid' o₁ (l.node' x r).eraseMax ↑(Ordnode.findMax' x 
r) ∧       (l.node' x r).size = (l.node' x r).eraseMax.size + 1
参数：Ordnode.node s l x r；l.node' x r；Ordnode.findMax' x r；l.node' x r；l.node' x r
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Sized.eq_node'`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α}
 {r : Ordnode α},   (Ordnode.node s l x r).Sized → Ordnode.node s l x r = l.node
' x r
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.findMax'`：findMax'_dual (t) (x : α) : findMax' x (dual t) = find
Min' t x
· 使用定理 `Ordnode.Valid'.left`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.Valid'.right`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : 
Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.
Valid' o₁ …
· 使用定理 `Ordnode.Valid'.balanceL`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordno
de α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid
' o₁ l ↑x →  …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用定理 `Ordnode.eraseMax.eq_3`：∀ {α : Type u_1} (size : ℕ) (l : Ordnode α) (x_1 
: α) (sz : ℕ) (l' : Ordnode α) (y : α) (r' : Ordnode α),   (Ordnode.node size l 
x_1 (Ordnod…
· 使用定理 `Ordnode.size_balanceL`：size_balanceL {l x r} (hl : Balanced l) (hr : Bal
anced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised l' (size l) ∧ Bal
ancedSz l' …
· 使用定理 `Ordnode.size_node`：∀ {α : Type u_1} (sz : ℕ) (l : Ordnode α) (x : α) (r 
: Ordnode α), (Ordnode.node sz l x r).size = sz
-/
theorem Valid'.eraseMax_aux {s l x r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂) :
    Valid' o₁ (@eraseMax α (.node' l x r)) ↑(findMax' x r) ∧
      size (.node' l x r) = size (eraseMax (.node' l x r)) + 1 := by
  have := H.2.eq_node'; rw [this] at H; clear this
  induction r generalizing l x o₁ with
  | nil => exact ⟨H.left, rfl⟩
  | node rs rl rx rr _ IHrr =>
    have := H.2.2.2.eq_node'; rw [this] at H ⊢
    rcases IHrr H.right with ⟨h, e⟩
    refine ⟨Valid'.balanceL H.left h (Or.inr ⟨_, Or.inr e, H.3.1⟩), ?_⟩
    rw [eraseMax, size_balanceL H.3.2.1 h.3 H.2.2.1 h.2 (Or.inr ⟨_, Or.inr e, H.3.1⟩)]
    rw [size_node, e]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.Valid'.eraseMin_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : Ordnode α} {x : α} {r : 
Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ (Ordnode.node 
s l x r) o₂ →     Ordnode.Valid' (↑(l.findMin' x)) (l.node' x r).eraseMin o₂ ∧ (
l.node' x r).size = (l.node' x r).eraseMin.size + 1
参数：Ordnode.node s l x r；↑(l.findMin' x)；l.node' x r；l.node' x r；l.node' x r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.findMax'`：findMax'_dual (t) (x : α) : findMax' x (dual t) = find
Min' t x
· 使用定理 `Ordnode.Valid'.eraseMax_aux`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ
} {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   O
rdnode.Valid' o₁ …
· 使用定理 `Ordnode.Valid'.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α
} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o
₂ t.dual …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.findMax'_dual`：∀ {α : Type u_1} (t : Ordnode α) (x : α), Ordnode
.findMax' x t.dual = t.findMin' x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.Valid'.dual_iff`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordno
de α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ ↔ Ordnode.Vali
d' o₂ t.dual …
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `Ordnode.dual_eraseMin`：∀ {α : Type u_1} (t : Ordnode α), t.eraseMin.dual
 = t.dual.eraseMax
· 使用定理 `Ordnode.dual_node'`：dual_node' (l : Ordnode α) (x : α) (r : Ordnode α) :
 dual (node' l x r) = node' (dual r) x (dual l)
-/
theorem Valid'.eraseMin_aux {s l} {x : α} {r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂) :
    Valid' ↑(findMin' l x) (@eraseMin α (.node' l x r)) o₂ ∧
      size (.node' l x r) = size (eraseMin (.node' l x r)) + 1 := by
  have := H.dual.eraseMax_aux
  rwa [← dual_node', size_dual, ← dual_eraseMin, size_dual, ← Valid'.dual_iff, findMax'_dual]
    at this
/-
**Ordnode.eraseMin.valid** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.eraseMin`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α}, t.Valid → t.eraseMin
.Valid
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.valid_nil`：valid_nil : Valid (@nil α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.Sized.eq_node'`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α}
 {r : Ordnode α},   (Ordnode.node s l x r).Sized → Ordnode.node s l x r = l.node
' x r
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.valid`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α}, Ordnode.Valid' o₁ t o₂ → t.Valid
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.eraseMin_aux`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ
} {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   O
rdnode.Valid' o₁ …
-/
theorem eraseMin.valid : ∀ {t}, @Valid α _ t → Valid (eraseMin t)
  | nil, _ => valid_nil
  | node _ l x r, h => by rw [h.2.eq_node']; exact h.eraseMin_aux.1.valid

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.eraseMax.valid** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.eraseMax`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α}, t.Valid → t.eraseMax
.Valid
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.Valid.dual_iff`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnod
e α}, t.Valid ↔ t.dual.Valid
· 使用定理 `Ordnode.dual_eraseMax`：dual_eraseMax (t : Ordnode α) : dual (eraseMax t)
 = eraseMin (dual t)
· 使用定理 `Ordnode.eraseMin.valid`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnod
e α}, t.Valid → t.eraseMin.Valid
· 使用定理 `Ordnode.Valid.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α}
, t.Valid → t.dual.Valid
-/
theorem eraseMax.valid {t} (h : @Valid α _ t) : Valid (eraseMax t) := by
  rw [Valid.dual_iff, dual_eraseMax]; exact eraseMin.valid h.dual
/-
**Ordnode.Valid'.glue_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l r : Ordnode α} {o₁ : WithBot α} {o
₂ : WithTop α},   Ordnode.Valid' o₁ l o₂ →     Ordnode.Valid' o₁ r o₂ →       Or
dnode.All (fun x => Ordnode.All (fun y => x < y) r) l →         Ordnode.Balanced
Sz l.size r.size → Ordnode.Valid' o₁ (l.glue r) o₂ ∧ (l.glue r).size = l.size + 
r.size
参数：fun x => Ordnode.All (fun y => x < y) r；l.glue r；l.glue r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ordnode.findMax'`：findMax'_dual (t) (x : α) : findMax' x (dual t) = find
Min' t x
· 使用定理 `Ordnode.splitMax_eq`：∀ {α : Type u_1} (s : ℕ) (l : Ordnode α) (x : α) (r
 : Ordnode α),   l.splitMax' x r = ((Ordnode.node s l x r).eraseMax, Ordnode.fin
dMax' x r…
· 使用定理 `Ordnode.Valid'.eraseMax_aux`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ
} {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   O
rdnode.Valid' o₁ …
· 使用定理 `Ordnode.Sized.eq_node'`：∀ {α : Type u_1} {s : ℕ} {l : Ordnode α} {x : α}
 {r : Ordnode α},   (Ordnode.node s l x r).Sized → Ordnode.node s l x r = l.node
' x r
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.balanceR`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordno
de α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid
' o₁ l ↑x →  …
· 使用定理 `Ordnode.Valid'.of_gt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode
.nil.Bound…
· 使用定理 `Ordnode.findMax'_all`：∀ {α : Type u_1} {P : α → Prop} (x : α) (t : Ordno
de α), P x → Ordnode.All P t → P (Ordnode.findMax' x t)
· 使用定理 `Ordnode.Bounded.to_nil`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnod
e α} {o₁ : WithBot α} {o₂ : WithTop α},   t.Bounded o₁ o₂ → Ordnode.nil.Bounded 
o₁ o₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.All.imp`：∀ {α : Type u_1} {P Q : α → Prop}, (∀ (a : α), P a → Q 
a) → ∀ {t : Ordnode α}, Ordnode.All P t → Ordnode.All Q t
· 使用定理 `Ordnode.Bounded.mono_left`：∀ {α : Type u_1} [inst : Preorder α] {x y : α
},   x ≤ y → ∀ {t : Ordnode α} {o : WithTop α}, t.Bounded (↑y) o → t.Bounded (↑x
) o
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.size_balanceR`：size_balanceR {l x r} (hl : Balanced l) (hr : Bal
anced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised (size l) l' ∧ Bal
ancedSz l' …
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.splitMin_eq`：∀ {α : Type u_1} (s : ℕ) (l : Ordnode α) (x : α) (r
 : Ordnode α),   l.splitMin' x r = (l.findMin' x, (Ordnode.node s l x r).eraseMi
n)
· 使用定理 `Ordnode.Valid'.eraseMin_aux`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ
} {l : Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   O
rdnode.Valid' o₁ …
· 使用定理 `Ordnode.Valid'.balanceL`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordno
de α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid
' o₁ l ↑x →  …
· 使用定理 `Ordnode.Valid'.of_lt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode
.nil.Bound…
（共 37 条，此处仅展示前 30 条）
-/
theorem Valid'.glue_aux {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
    (sep : l.All fun x => r.All fun y => x < y) (bal : BalancedSz (size l) (size r)) :
    Valid' o₁ (@glue α l r) o₂ ∧ size (glue l r) = size l + size r := by
  obtain - | ⟨ls, ll, lx, lr⟩ := l; · exact ⟨hr, (zero_add _).symm⟩
  obtain - | ⟨rs, rl, rx, rr⟩ := r; · exact ⟨hl, rfl⟩
  dsimp [glue]; split_ifs
  · rw [splitMax_eq]
    · obtain ⟨v, e⟩ := Valid'.eraseMax_aux hl
      suffices H : _ by
        refine ⟨Valid'.balanceR v (hr.of_gt ?_ ?_) H, ?_⟩
        · refine findMax'_all (P := fun a : α => Bounded nil (a : WithTop α) o₂)
            lx lr hl.1.2.to_nil (sep.2.2.imp ?_)
          exact fun x h => hr.1.2.to_nil.mono_left (le_of_lt h.2.1)
        · exact @findMax'_all _ (fun a => All (· > a) (.node rs rl rx rr)) lx lr sep.2.1 sep.2.2
        · rw [size_balanceR v.3 hr.3 v.2 hr.2 H, add_right_comm, ← e, hl.2.1]; rfl
      refine Or.inl ⟨_, Or.inr e, ?_⟩
      rwa [hl.2.eq_node'] at bal
  · rw [splitMin_eq]
    · obtain ⟨v, e⟩ := Valid'.eraseMin_aux hr
      suffices H : _ by
        refine ⟨Valid'.balanceL (hl.of_lt ?_ ?_) v H, ?_⟩
        · refine @findMin'_all (P := fun a : α => Bounded nil o₁ (a : WithBot α))
            _ rl rx (sep.2.1.1.imp ?_) hr.1.1.to_nil
          exact fun y h => hl.1.1.to_nil.mono_right (le_of_lt h)
        · exact
            @findMin'_all _ (fun a => All (· < a) (.node ls ll lx lr)) rl rx
              (all_iff_forall.2 fun x hx => sep.imp fun y hy => all_iff_forall.1 hy.1 _ hx)
              (sep.imp fun y hy => hy.2.1)
        · rw [size_balanceL hl.3 v.3 hl.2 v.2 H, add_assoc, ← e, hr.2.1]; rfl
      refine Or.inr ⟨_, Or.inr e, ?_⟩
      rwa [hr.2.eq_node'] at bal
/-
**Ordnode.Valid'.glue** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α} {x : α} {r : Ordnode 
α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l ↑x →     Ordnode.Val
id' (↑x) r o₂ →       Ordnode.BalancedSz l.size r.size → Ordnode.Valid' o₁ (l.gl
ue r) o₂ ∧ (l.glue r).size = l.size + r.size
参数：↑x；l.glue r；l.glue r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.glue_aux`：∀ {α : Type u_1} [inst : Preorder α] {l r : Ord
node α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l o₂ →     Ordnod
e.Valid' o₁ r…
· 使用定理 `Ordnode.Valid'.trans_right`：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ 
: Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t₁ ↑
x → t₂.Bounded (…
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.trans_left`：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ :
 Ordnode α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   t₁.Bounded o₁ ↑x → Ordn
ode.Valid' (↑x)…
· 使用定理 `Ordnode.Bounded.to_sep`：∀ {α : Type u_1} [inst : Preorder α] {t₁ t₂ : Or
dnode α} {o₁ : WithBot α} {o₂ : WithTop α} {x : α},   t₁.Bounded o₁ ↑x → t₂.Boun
ded (↑x) o₂ …
-/
theorem Valid'.glue {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂) :
    BalancedSz (size l) (size r) →
      Valid' o₁ (@glue α l r) o₂ ∧ size (@glue α l r) = size l + size r :=
  Valid'.glue_aux (hl.trans_right hr.1) (hr.trans_left hl.1) (hl.1.to_sep hr.1)
/-
**Ordnode.Valid'.merge_lemma** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {a b c : ℕ}, 3 * a < b + c + 1 → b ≤ 3 * c → 2 * (a + b) ≤ 9 * c + 5
参数：a + b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Valid'.merge_lemma {a b c : ℕ} (h₁ : 3 * a < b + c + 1) (h₂ : b ≤ 3 * c) :
    2 * (a + b) ≤ 9 * c + 5 := by lia
/-
**Ordnode.Valid'.merge_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l r : Ordnode α} {o₁ : WithBot α} {o
₂ : WithTop α},   Ordnode.Valid' o₁ l o₂ →     Ordnode.Valid' o₁ r o₂ →       Or
dnode.All (fun x => Ordnode.All (fun y => x < y) r) l →         Ordnode.Valid' o
₁ (l.merge r) o₂ ∧ (l.merge r).size = l.size + r.size
参数：fun x => Ordnode.All (fun y => x < y) r；l.merge r；l.merge r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.merge_node`：merge_node {ls ll lx lr rs rl rx rr} : merge (@node 
α ls ll lx lr) (node rs rl rx rr) = if delta * ls < rs then balanceL (merge (nod
e ls ll …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ordnode.Valid'.of_lt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode
.nil.Bound…
· 使用定理 `Ordnode.Bounded.to_nil`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnod
e α} {o₁ : WithBot α} {o₂ : WithTop α},   t.Bounded o₁ o₂ → Ordnode.nil.Bounded 
o₁ o₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.All.imp`：∀ {α : Type u_1} {P Q : α → Prop}, (∀ (a : α), P a → Q 
a) → ∀ {t : Ordnode α}, Ordnode.All P t → Ordnode.All Q t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordnode.Valid'.left`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ …
· 使用定理 `Ordnode.Valid'.merge_aux₁`：∀ {α : Type u_1} [inst : Preorder α] {o₁ : Wi
thBot α} {o₂ : WithTop α} {ls : ℕ} {ll : Ordnode α} {lx : α}   {lr : Ordnode α} 
{rs : ℕ} {rl : …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.Valid'.right`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : 
Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.
Valid' o₁ …
· 使用定理 `Ordnode.Valid'.of_gt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode
.nil.Bound…
· 使用定理 `Ordnode.Valid'.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α
} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o
₂ t.dual …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `Ordnode.Valid'.dual_iff`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordno
de α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ ↔ Ordnode.Vali
d' o₂ t.dual …
· 使用定理 `Ordnode.dual_balanceR`：dual_balanceR (l : Ordnode α) (x : α) (r : Ordnod
e α) : dual (balanceR l x r) = balanceL (dual r) x (dual l)
· 使用定理 `Ordnode.Valid'.glue_aux`：∀ {α : Type u_1} [inst : Preorder α] {l r : Ord
node α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l o₂ →     Ordnod
e.Valid' o₁ r…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem Valid'.merge_aux₁ {o₁ o₂ ls ll lx lr rs rl rx rr t}
    (hl : Valid' o₁ (@Ordnode.node α ls ll lx lr) o₂) (hr : Valid' o₁ (.node rs rl rx rr) o₂)
    (h : delta * ls < rs) (v : Valid' o₁ t rx) (e : size t = ls + size rl) :
    Valid' o₁ (.balanceL t rx rr) o₂ ∧ size (.balanceL t rx rr) = ls + rs := by
  rw [hl.2.1] at e
  rw [hl.2.1, hr.2.1, delta] at h
  rcases hr.3.1 with (H | ⟨hr₁, hr₂⟩); · lia
  suffices H₂ : _ by
    suffices H₁ : _ by
      refine ⟨Valid'.balanceL_aux v hr.right H₁ H₂ ?_, ?_⟩
      · rw [e]; exact Or.inl (Valid'.merge_lemma h hr₁)
      · rw [balanceL_eq_balance v.2 hr.2.2.2 H₁ H₂, balance_eq_balance' v.3 hr.3.2.2 v.2 hr.2.2.2,
          size_balance' v.2 hr.2.2.2, e, hl.2.1, hr.2.1]
        abel
    · rw [e, add_right_comm]; rintro ⟨⟩
  intro _ _; rw [e]; unfold delta at hr₂ ⊢; lia

set_option backward.isDefEq.respectTransparency false in
/-
**Ordnode.Valid'.merge_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l r : Ordnode α} {o₁ : WithBot α} {o
₂ : WithTop α},   Ordnode.Valid' o₁ l o₂ →     Ordnode.Valid' o₁ r o₂ →       Or
dnode.All (fun x => Ordnode.All (fun y => x < y) r) l →         Ordnode.Valid' o
₁ (l.merge r) o₂ ∧ (l.merge r).size = l.size + r.size
参数：fun x => Ordnode.All (fun y => x < y) r；l.merge r；l.merge r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.merge_node`：merge_node {ls ll lx lr rs rl rx rr} : merge (@node 
α ls ll lx lr) (node rs rl rx rr) = if delta * ls < rs then balanceL (merge (nod
e ls ll …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Ordnode.Valid'.of_lt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode
.nil.Bound…
· 使用定理 `Ordnode.Bounded.to_nil`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnod
e α} {o₁ : WithBot α} {o₂ : WithTop α},   t.Bounded o₁ o₂ → Ordnode.nil.Bounded 
o₁ o₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.All.imp`：∀ {α : Type u_1} {P Q : α → Prop}, (∀ (a : α), P a → Q 
a) → ∀ {t : Ordnode α}, Ordnode.All P t → Ordnode.All Q t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordnode.Valid'.left`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ …
· 使用定理 `Ordnode.Valid'.merge_aux₁`：∀ {α : Type u_1} [inst : Preorder α] {o₁ : Wi
thBot α} {o₂ : WithTop α} {ls : ℕ} {ll : Ordnode α} {lx : α}   {lr : Ordnode α} 
{rs : ℕ} {rl : …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Ordnode.Valid'.right`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : 
Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.
Valid' o₁ …
· 使用定理 `Ordnode.Valid'.of_gt`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode 
α} {x : α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode
.nil.Bound…
· 使用定理 `Ordnode.Valid'.dual`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordnode α
} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ → Ordnode.Valid' o
₂ t.dual …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Ordnode.size_dual`：size_dual (t : Ordnode α) : size (dual t) = size t
· 使用定理 `Ordnode.Valid'.dual_iff`：∀ {α : Type u_1} [inst : Preorder α] {t : Ordno
de α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ t o₂ ↔ Ordnode.Vali
d' o₂ t.dual …
· 使用定理 `Ordnode.dual_balanceR`：dual_balanceR (l : Ordnode α) (x : α) (r : Ordnod
e α) : dual (balanceR l x r) = balanceL (dual r) x (dual l)
· 使用定理 `Ordnode.Valid'.glue_aux`：∀ {α : Type u_1} [inst : Preorder α] {l r : Ord
node α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l o₂ →     Ordnod
e.Valid' o₁ r…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem Valid'.merge_aux {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
    (sep : l.All fun x => r.All fun y => x < y) :
    Valid' o₁ (@merge α l r) o₂ ∧ size (merge l r) = size l + size r := by
  induction l generalizing o₁ o₂ r with
  | nil => exact ⟨hr, (zero_add _).symm⟩
  | node ls ll lx lr _ IHlr => ?_
  induction r generalizing o₁ o₂ with
  | nil => exact ⟨hl, rfl⟩
  | node rs rl rx rr IHrl _ => ?_
  rw [merge_node]; split_ifs with h h_1
  · obtain ⟨v, e⟩ := IHrl (hl.of_lt hr.1.1.to_nil <| sep.imp fun x h => h.2.1) hr.left
      (sep.imp fun x h => h.1)
    exact Valid'.merge_aux₁ hl hr h v e
  · obtain ⟨v, e⟩ := IHlr hl.right (hr.of_gt hl.1.2.to_nil sep.2.1) sep.2.2
    have := Valid'.merge_aux₁ hr.dual hl.dual h_1 v.dual
    rw [size_dual, add_comm, size_dual, ← dual_balanceR, ← Valid'.dual_iff, size_dual,
      add_comm rs] at this
    exact this e
  · refine Valid'.glue_aux hl hr sep (Or.inr ⟨not_lt.1 h_1, not_lt.1 h⟩)
/-
**Ordnode.Valid.merge** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l r : Ordnode α},   l.Valid → r.Vali
d → Ordnode.All (fun x => Ordnode.All (fun y => x < y) r) l → (l.merge r).Valid
参数：fun x => Ordnode.All (fun y => x < y) r；l.merge r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.merge_aux`：∀ {α : Type u_1} [inst : Preorder α] {l r : Or
dnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁ l o₂ →     Ordno
de.Valid' o₁ r…
-/
theorem Valid.merge {l r} (hl : Valid l) (hr : Valid r)
    (sep : l.All fun x => r.All fun y => x < y) : Valid (@merge α l r) :=
  (Valid'.merge_aux hl hr sep).1
/-
**Ordnode.insertWith.valid_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.insertWith`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Std.Total fun x1 x2 => x1 ≤ x2] [ins
t_2 : DecidableLE α] (f : α → α) (x : α),   (∀ (y : α), x ≤ y ∧ y ≤ x → x ≤ f y 
∧ f y ≤ x) →     ∀ {t : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},       Ordn
ode.Valid' o₁ t o₂ →         Ordnode.nil.Bounded o₁ ↑x →           Ordnode.nil.B
ounded (↑x) o₂ →             Ordnode.Valid' o₁ (Ordnode.insertWith f x t) o₂ ∧ O
rdnode.Raised t.size (Ordnode.insertWith f x t).size
参数：f : α → α；x : α；∀ (y : α), x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x；↑x；Ordnode.inser
tWith f x t；Ordnode.insertWith f x t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
-/
theorem insertWith.valid_aux [@Std.Total α (· ≤ ·)] [DecidableLE α] (f : α → α) (x : α)
    (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) :
    ∀ {t o₁ o₂},
      Valid' o₁ t o₂ →
        Bounded nil o₁ x →
          Bounded nil x o₂ →
            Valid' o₁ (insertWith f x t) o₂ ∧ Raised (size t) (size (insertWith f x t))
  | nil, _, _, _, bl, br => ⟨valid'_singleton bl br, Or.inr rfl⟩
  | node sz l y r, o₁, o₂, h, bl, br => by
    rw [insertWith, cmpLE]
    split_ifs with h_1 h_2 <;> dsimp only
    · rcases h with ⟨⟨lx, xr⟩, hs, hb⟩
      rcases hf _ ⟨h_1, h_2⟩ with ⟨xf, fx⟩
      refine
        ⟨⟨⟨lx.mono_right (le_trans h_2 xf), xr.mono_left (le_trans fx h_1)⟩, hs, hb⟩, Or.inl rfl⟩
    · rcases insertWith.valid_aux f x hf h.left bl (lt_of_le_not_ge h_1 h_2) with ⟨vl, e⟩
      suffices H : _ by
        refine ⟨vl.balanceL h.right H, ?_⟩
        rw [size_balanceL vl.3 h.3.2.2 vl.2 h.2.2.2 H, h.2.size_eq]
        exact (e.add_right _).add_right _
      exact Or.inl ⟨_, e, h.3.1⟩
    · have : y < x := lt_of_le_not_ge ((total_of (· ≤ ·) _ _).resolve_left h_1) h_1
      rcases insertWith.valid_aux f x hf h.right this br with ⟨vr, e⟩
      suffices H : _ by
        refine ⟨h.left.balanceR vr H, ?_⟩
        rw [size_balanceR h.3.2.1 vr.3 h.2.2.1 vr.2 H, h.2.size_eq]
        exact (e.add_left _).add_right _
      exact Or.inr ⟨_, e, h.3.1⟩
/-
**Ordnode.insertWith.valid** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.insertWith`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Std.Total fun x1 x2 => x1 ≤ x2] [ins
t_2 : DecidableLE α] (f : α → α) (x : α),   (∀ (y : α), x ≤ y ∧ y ≤ x → x ≤ f y 
∧ f y ≤ x) → ∀ {t : Ordnode α}, t.Valid → (Ordnode.insertWith f x t).Valid
参数：f : α → α；x : α；∀ (y : α), x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x；Ordnode.insertWi
th f x t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.insertWith.valid_aux`：∀ {α : Type u_1} [inst : Preorder α] [Std.
Total fun x1 x2 => x1 ≤ x2] [inst_2 : DecidableLE α] (f : α → α) (x : α),   (∀ (
y : α), x ≤ y ∧ y …
-/
theorem insertWith.valid [@Std.Total α (· ≤ ·)] [DecidableLE α] (f : α → α) (x : α)
    (hf : ∀ y, x ≤ y ∧ y ≤ x → x ≤ f y ∧ f y ≤ x) {t} (h : Valid t) : Valid (insertWith f x t) :=
  (insertWith.valid_aux _ _ hf h ⟨⟩ ⟨⟩).1
/-
**Ordnode.insert_eq_insertWith** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableLE α] (x : α) (t :
 Ordnode α),   Ordnode.insert x t = Ordnode.insertWith (fun x_1 => x) x t
参数：x : α；t : Ordnode α；fun x_1 => x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insert_eq_insertWith [DecidableLE α] (x : α) :
    ∀ t, Ordnode.insert x t = insertWith (fun _ => x) x t
  | nil => rfl
  | node _ l y r => by
    unfold Ordnode.insert insertWith; cases cmpLE x y <;> simp [insert_eq_insertWith]
/-
**Ordnode.insert.valid** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.insert`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Std.Total fun x1 x2 => x1 ≤ x2] [ins
t_2 : DecidableLE α] (x : α) {t : Ordnode α},   t.Valid → (Ordnode.insert x t).V
alid
参数：x : α；Ordnode.insert x t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.insert_eq_insertWith`：∀ {α : Type u_1} [inst : Preorder α] [inst
_1 : DecidableLE α] (x : α) (t : Ordnode α),   Ordnode.insert x t = Ordnode.inse
rtWith (fun x_1 =>…
· 使用定理 `Ordnode.insertWith.valid`：∀ {α : Type u_1} [inst : Preorder α] [Std.Tota
l fun x1 x2 => x1 ≤ x2] [inst_2 : DecidableLE α] (f : α → α) (x : α),   (∀ (y : 
α), x ≤ y ∧ y …
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem insert.valid [@Std.Total α (· ≤ ·)] [DecidableLE α] (x : α) {t} (h : Valid t) :
    Valid (Ordnode.insert x t) := by
  rw [insert_eq_insertWith]; exact insertWith.valid _ _ (fun _ _ => ⟨le_rfl, le_rfl⟩) h
/-
**Ordnode.insert'_eq_insertWith** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableLE α] (x : α) (t :
 Ordnode α),   Ordnode.insert' x t = Ordnode.insertWith id x t
参数：x : α；t : Ordnode α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.insert'`：insert'.valid [@Std.Total α (· <= ·)] [DecidableLE α] (
x : α) {t} (h : Valid t) : Valid (insert' x t)
-/
theorem insert'_eq_insertWith [DecidableLE α] (x : α) :
    ∀ t, insert' x t = insertWith id x t
  | nil => rfl
  | node _ l y r => by
    unfold insert' insertWith; cases cmpLE x y <;> simp [insert'_eq_insertWith]
/-
**Ordnode.insert'.valid** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.insert'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [Std.Total fun x1 x2 => x1 ≤ x2] [ins
t_2 : DecidableLE α] (x : α) {t : Ordnode α},   t.Valid → (Ordnode.insert' x t).
Valid
参数：x : α；Ordnode.insert' x t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.insert'`：insert'.valid [@Std.Total α (· <= ·)] [DecidableLE α] (
x : α) {t} (h : Valid t) : Valid (insert' x t)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.insert'_eq_insertWith`：∀ {α : Type u_1} [inst : Preorder α] [ins
t_1 : DecidableLE α] (x : α) (t : Ordnode α),   Ordnode.insert' x t = Ordnode.in
sertWith id x t
· 使用定理 `Ordnode.insertWith.valid`：∀ {α : Type u_1} [inst : Preorder α] [Std.Tota
l fun x1 x2 => x1 ≤ x2] [inst_2 : DecidableLE α] (f : α → α) (x : α),   (∀ (y : 
α), x ≤ y ∧ y …
-/
theorem insert'.valid [@Std.Total α (· ≤ ·)] [DecidableLE α]
    (x : α) {t} (h : Valid t) : Valid (insert' x t) := by
  rw [insert'_eq_insertWith]; exact insertWith.valid _ _ (fun _ => id) h
/-
**Ordnode.Valid'.map_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {β : Type u_2} [inst_1 : Preorder β] 
{f : α → β},   StrictMono f →     ∀ {t : Ordnode α} {a₁ : WithBot α} {a₂ : WithT
op α},       Ordnode.Valid' a₁ t a₂ →         Ordnode.Valid' (Option.map f a₁) (
Ordnode.map f t) (Option.map f a₂) ∧ (Ordnode.map f t).size = t.size
参数：Option.map f a₁；Ordnode.map f t；Option.map f a₂；Ordnode.map f t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Ordnode.valid'_nil`：∀ {α : Type u_1} [inst : Preorder α] {o₁ : WithBot α
} {o₂ : WithTop α},   Ordnode.nil.Bounded o₁ o₂ → Ordnode.Valid' o₁ Ordnode.nil 
o₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.Bounded.eq_1`：∀ {α : Type u_1} [inst : Preorder α] (a b : α), Or
dnode.nil.Bounded (some a) (some b) = (a < b)
· 使用定理 `Ordnode.Valid'.ord`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Bounded lo hi
· 使用定理 `Ordnode.Valid'.left`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ …
· 使用定理 `Ordnode.Valid'.right`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : 
Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.
Valid' o₁ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
-/
theorem Valid'.map_aux {β} [Preorder β] {f : α → β} (f_strict_mono : StrictMono f) {t a₁ a₂}
    (h : Valid' a₁ t a₂) :
    Valid' (Option.map f a₁) (map f t) (Option.map f a₂) ∧ (map f t).size = t.size := by
  induction t generalizing a₁ a₂ with
  | nil =>
    simp only [map, size_nil, and_true]; apply valid'_nil
    cases a₁; · trivial
    cases a₂; · trivial
    simp only [Option.map, Bounded]
    exact f_strict_mono h.ord
  | node _ _ _ _ t_ih_l t_ih_r =>
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    obtain ⟨t_l_valid, t_l_size⟩ := t_ih_l'
    obtain ⟨t_r_valid, t_r_size⟩ := t_ih_r'
    simp only [map, size_node, and_true]
    constructor
    · exact And.intro t_l_valid.ord t_r_valid.ord
    · constructor
      · rw [t_l_size, t_r_size]; exact h.sz.1
      · constructor
        · exact t_l_valid.sz
        · exact t_r_valid.sz
    · constructor
      · rw [t_l_size, t_r_size]; exact h.bal.1
      · constructor
        · exact t_l_valid.bal
        · exact t_r_valid.bal
/-
**Ordnode.map.valid** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.map`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {β : Type u_2} [inst_1 : Preorder β] 
{f : α → β},   StrictMono f → ∀ {t : Ordnode α}, t.Valid → (Ordnode.map f t).Val
id
参数：Ordnode.map f t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.map_aux`：∀ {α : Type u_1} [inst : Preorder α] {β : Type u
_2} [inst_1 : Preorder β] {f : α → β},   StrictMono f →     ∀ {t : Ordnode α} {a
₁ : WithBot …
-/
theorem map.valid {β} [Preorder β] {f : α → β} (f_strict_mono : StrictMono f) {t} (h : Valid t) :
    Valid (map f t) :=
  (Valid'.map_aux f_strict_mono h).1
/-
**Ordnode.Valid'.erase_aux** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.Valid'`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableLE α] (x : α) {t :
 Ordnode α} {a₁ : WithBot α} {a₂ : WithTop α},   Ordnode.Valid' a₁ t a₂ → Ordnod
e.Valid' a₁ (Ordnode.erase x t) a₂ ∧ Ordnode.Raised (Ordnode.erase x t).size t.s
ize
参数：x : α；Ordnode.erase x t；Ordnode.erase x t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Ordnode.Valid'.left`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ …
· 使用定理 `Ordnode.Valid'.right`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : 
Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.
Valid' o₁ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用定理 `Ordnode.Valid'.balanceR`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordno
de α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid
' o₁ l ↑x →  …
· 使用定理 `Ordnode.size_balanceR`：size_balanceR {l x r} (hl : Balanced l) (hr : Bal
anced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised (size l) l' ∧ Bal
ancedSz l' …
· 使用定理 `Ordnode.Raised.add_right`：∀ (k : ℕ) {n m : ℕ}, Ordnode.Raised n m → Ordn
ode.Raised (n + k) (m + k)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordnode.Valid'.glue`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α
} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁
 l ↑x →  …
· 使用定理 `Ordnode.Valid'.balanceL`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordno
de α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid
' o₁ l ↑x →  …
· 使用定理 `Ordnode.size_balanceL`：size_balanceL {l x r} (hl : Balanced l) (hr : Bal
anced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised l' (size l) ∧ Bal
ancedSz l' …
· 使用定理 `Ordnode.Raised.add_left`：∀ (k : ℕ) {n m : ℕ}, Ordnode.Raised n m → Ordno
de.Raised (k + n) (k + m)
-/
theorem Valid'.erase_aux [DecidableLE α] (x : α) {t a₁ a₂} (h : Valid' a₁ t a₂) :
    Valid' a₁ (erase x t) a₂ ∧ Raised (erase x t).size t.size := by
  induction t generalizing a₁ a₂ with
  | nil =>
    simpa [erase, Raised]
  | node _ t_l t_x t_r t_ih_l t_ih_r =>
    simp only [erase, size_node]
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    obtain ⟨t_l_valid, t_l_size⟩ := t_ih_l'
    obtain ⟨t_r_valid, t_r_size⟩ := t_ih_r'
    cases cmpLE x t_x <;> rw [h.sz.1]
    · suffices h_balanceable : _ by
        constructor
        · exact Valid'.balanceR t_l_valid h.right h_balanceable
        · rw [size_balanceR t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz h_balanceable]
          repeat apply Raised.add_right
          exact t_l_size
      left; exists t_l.size; exact And.intro t_l_size h.bal.1
    · have h_glue := Valid'.glue h.left h.right h.bal.1
      obtain ⟨h_glue_valid, h_glue_sized⟩ := h_glue
      constructor
      · exact h_glue_valid
      · right; rw [h_glue_sized]
    · suffices h_balanceable : _ by
        constructor
        · exact Valid'.balanceL h.left t_r_valid h_balanceable
        · rw [size_balanceL h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz h_balanceable]
          apply Raised.add_right
          apply Raised.add_left
          exact t_r_size
      right; exists t_r.size; exact And.intro t_r_size h.bal.1
/-
**Ordnode.erase.valid** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode.erase`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] [inst_1 : DecidableLE α] (x : α) {t :
 Ordnode α},   t.Valid → (Ordnode.erase x t).Valid
参数：x : α；Ordnode.erase x t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `Ordnode.Valid'.erase_aux`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 :
 DecidableLE α] (x : α) {t : Ordnode α} {a₁ : WithBot α} {a₂ : WithTop α},   Ord
node.Valid' a₁…
-/
theorem erase.valid [DecidableLE α] (x : α) {t} (h : Valid t) : Valid (erase x t) :=
  (Valid'.erase_aux x h).1
/-
**Ordnode.size_erase_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ordnode`。
形式化陈述：size_erase_of_mem [DecidableLE α] {x : α} {t a₁ a₂} (h : Valid' a₁ t a₂) (
h_mem : x in t) : size (erase x t) = size t - 1
参数：h : Valid' a₁ t a₂；h_mem : x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.Valid'`：Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α}
 {o} (h : Valid' y t o) : Valid' x t o
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Ordnode.Valid'.left`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : O
rdnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.V
alid' o₁ …
· 使用定理 `Ordnode.Valid'.right`：∀ {α : Type u_1} [inst : Preorder α] {s : ℕ} {l : 
Ordnode α} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.
Valid' o₁ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordnode.erase.eq_def`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Decidable
LE α] (x : α) (x_1 : Ordnode α),   Ordnode.erase x x_1 =     match x_1 with     
| Ordnode.…
· 使用定理 `Ordnode.Valid'.erase_aux`：∀ {α : Type u_1} [inst : Preorder α] [inst_1 :
 DecidableLE α] (x : α) {t : Ordnode α} {a₁ : WithBot α} {a₂ : WithTop α},   Ord
node.Valid' a₁…
· 使用定理 `Ordnode.size_balanceR`：size_balanceR {l x r} (hl : Balanced l) (hr : Bal
anced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised (size l) l' ∧ Bal
ancedSz l' …
· 使用定理 `Ordnode.Valid'.bal`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α
} {t : Ordnode α} {hi : WithTop α},   Ordnode.Valid' lo t hi → t.Balanced
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ordnode.pos_size_of_mem`：pos_size_of_mem [LE α] [DecidableLE α] {x : α} 
{t : Ordnode α} (h : Sized t) (h_mem : x in t) : 0 < size t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `Nat.succ_add_sub_one`：∀ (n m : ℕ), m.succ + n - 1 = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ordnode.Valid'.glue`：∀ {α : Type u_1} [inst : Preorder α] {l : Ordnode α
} {x : α} {r : Ordnode α} {o₁ : WithBot α} {o₂ : WithTop α},   Ordnode.Valid' o₁
 l ↑x →  …
· 使用定理 `Ordnode.size_balanceL`：size_balanceL {l x r} (hl : Balanced l) (hr : Bal
anced r) (sl : Sized l) (sr : Sized r) (H : (exists l', Raised l' (size l) ∧ Bal
ancedSz l' …
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
-/
theorem size_erase_of_mem [DecidableLE α] {x : α} {t a₁ a₂} (h : Valid' a₁ t a₂)
    (h_mem : x ∈ t) : size (erase x t) = size t - 1 := by
  induction t generalizing a₁ a₂ with
  | nil =>
    contradiction
  | node _ t_l t_x t_r t_ih_l t_ih_r =>
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    dsimp only [Membership.mem, mem] at h_mem
    unfold erase
    revert h_mem; cases cmpLE x t_x <;> intro h_mem <;> dsimp only at h_mem ⊢
    · have t_ih_l := t_ih_l' h_mem
      clear t_ih_l' t_ih_r'
      have t_l_h := Valid'.erase_aux x h.left
      obtain ⟨t_l_valid, t_l_size⟩ := t_l_h
      rw [size_balanceR t_l_valid.bal h.right.bal t_l_valid.sz h.right.sz
          (Or.inl (Exists.intro t_l.size (And.intro t_l_size h.bal.1)))]
      rw [t_ih_l, h.sz.1]
      have h_pos_t_l_size := pos_size_of_mem h.left.sz h_mem
      revert h_pos_t_l_size; rcases t_l.size with - | t_l_size <;> intro h_pos_t_l_size
      · cases h_pos_t_l_size
      · simp [Nat.add_right_comm]
    · rw [(Valid'.glue h.left h.right h.bal.1).2, h.sz.1]; rfl
    · have t_ih_r := t_ih_r' h_mem
      clear t_ih_l' t_ih_r'
      have t_r_h := Valid'.erase_aux x h.right
      obtain ⟨t_r_valid, t_r_size⟩ := t_r_h
      rw [size_balanceL h.left.bal t_r_valid.bal h.left.sz t_r_valid.sz
          (Or.inr (Exists.intro t_r.size (And.intro t_r_size h.bal.1)))]
      rw [t_ih_r, h.sz.1]
      have h_pos_t_r_size := pos_size_of_mem h.right.sz h_mem
      revert h_pos_t_r_size; rcases t_r.size with - | t_r_size <;> intro h_pos_t_r_size
      · cases h_pos_t_r_size
      · simp [Nat.add_assoc]

end Valid

end Ordnode

/-- An `Ordset α` is a finite set of values, represented as a tree. The operations on this type
maintain that the tree is balanced and correctly stores subtree sizes at each level. The
correctness property of the tree is baked into the type, so all operations on this type are correct
by construction. -/
/-
**Ordset** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ordset (α : Type*) [Preorder α]
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `Ordset α` is a finite set of values, represented as a tree. The operations o
n this type
maintain that the tree is balanced and correctly stores subtree sizes at each le
vel. The
correctness property of the tree is baked into the type, so all operations on th
is type are correct
by construction.
-/
def Ordset (α : Type*) [Preorder α] :=
  { t : Ordnode α // t.Valid }

namespace Ordset

open Ordnode

variable [Preorder α]

/-- O(1). The empty set. -/
nonrec def nil : Ordset α :=
  ⟨nil, ⟨⟩, ⟨⟩, ⟨⟩⟩

/-- O(1). Get the size of the set. -/
/-
**Ordset.size** 是 Mathlib 中的一个定义，位于命名空间 `Ordset`。
形式化陈述：size (s : Ordset α) : Nat
参数：s : Ordset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
O(1). Get the size of the set.
-/
def size (s : Ordset α) : ℕ :=
  s.1.size

/-- O(1). Construct a singleton set containing value `a`. -/
/-
**Ordset.singleton** 是 Mathlib 中的一个定义，位于命名空间 `Ordset`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → α → Ordset α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.valid_singleton`：valid_singleton {x : α} : Valid (singleton x : 
Ordnode α)

--- 原说明 ---
O(1). Construct a singleton set containing value `a`.
-/
protected def singleton (a : α) : Ordset α :=
  ⟨singleton a, valid_singleton⟩
/-
**Ordset.instEmptyCollection** 是 Mathlib 中的一个实例，位于命名空间 `Ordset`。
形式化陈述：instEmptyCollection : EmptyCollection (Ordset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instEmptyCollection : EmptyCollection (Ordset α) :=
  ⟨nil⟩
/-
**Ordset.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Ordset`。
形式化陈述：instInhabited : Inhabited (Ordset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited : Inhabited (Ordset α) :=
  ⟨nil⟩
/-
**Ordset.instSingleton** 是 Mathlib 中的一个实例，位于命名空间 `Ordset`。
形式化陈述：instSingleton : Singleton α (Ordset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSingleton : Singleton α (Ordset α) :=
  ⟨Ordset.singleton⟩

/-- O(1). Is the set empty? -/
/-
**Ordset.Empty** 是 Mathlib 中的一个定义，位于命名空间 `Ordset`。
形式化陈述：Empty (s : Ordset α) : Prop
参数：s : Ordset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
O(1). Is the set empty?
-/
def Empty (s : Ordset α) : Prop :=
  s = ∅
/-
**Ordset.empty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordset`。
形式化陈述：empty_iff {s : Ordset α} : s = ∅ ↔ s.1.empty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem empty_iff {s : Ordset α} : s = ∅ ↔ s.1.empty :=
  ⟨fun h => by cases h; exact rfl,
    fun h => by cases s with | mk s_val _ => cases s_val <;> [rfl; cases h]⟩
/-
**Ordset.Empty.instDecidablePred** 是 Mathlib 中的一个定义，位于命名空间 `Ordset.Empty`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → DecidablePred Ordset.Empty
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ordset.empty_iff`：empty_iff {s : Ordset α} : s = ∅ ↔ s.1.empty
-/
instance Empty.instDecidablePred : DecidablePred (@Empty α _) :=
  fun _ => decidable_of_iff' _ empty_iff

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, this replaces it. -/
/-
**Ordset.insert** 是 Mathlib 中的一个定义，位于命名空间 `Ordset`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → [Std.Total fun x1 x2 => x1 ≤ x2] → 
[DecidableLE α] → α → Ordset α → Ordset α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
O(log n). Insert an element into the set, preserving balance and the BST propert
y.
  If an equivalent element is already in the set, this replaces it.
-/
protected def insert [@Std.Total α (· ≤ ·)] [DecidableLE α] (x : α) (s : Ordset α) :
    Ordset α :=
  ⟨Ordnode.insert x s.1, insert.valid _ s.2⟩
/-
**Ordset.instInsert** 是 Mathlib 中的一个实例，位于命名空间 `Ordset`。
形式化陈述：instInsert [@Std.Total α (· <= ·)] [DecidableLE α] : Insert α (Ordset α)
参数：· <= ·。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInsert [@Std.Total α (· ≤ ·)] [DecidableLE α] : Insert α (Ordset α) :=
  ⟨Ordset.insert⟩

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, the set is returned as is. -/
nonrec def insert' [@Std.Total α (· ≤ ·)] [DecidableLE α] (x : α) (s : Ordset α) :
    Ordset α :=
  ⟨insert' x s.1, insert'.valid _ s.2⟩

section

variable [DecidableLE α]

/-- O(log n). Does the set contain the element `x`? That is,
  is there an element that is equivalent to `x` in the order? -/
/-
**Ordset.mem** 是 Mathlib 中的一个定义，位于命名空间 `Ordset`。
形式化陈述：mem (x : α) (s : Ordset α) : Bool
参数：x : α；s : Ordset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
O(log n). Does the set contain the element `x`? That is,
  is there an element that is equivalent to `x` in the order?
-/
def mem (x : α) (s : Ordset α) : Bool :=
  x ∈ s.val

/-- O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
  if it exists. -/
/-
**Ordset.find** 是 Mathlib 中的一个定义，位于命名空间 `Ordset`。
形式化陈述：find (x : α) (s : Ordset α) : Option α
参数：x : α；s : Ordset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
O(log n). Retrieve an element in the set that is equivalent to `x` in the order,
  if it exists.
-/
def find (x : α) (s : Ordset α) : Option α :=
  Ordnode.find x s.val
/-
**Ordset.instMembership** 是 Mathlib 中的一个实例，位于命名空间 `Ordset`。
形式化陈述：instMembership : Membership α (Ordset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMembership : Membership α (Ordset α) :=
  ⟨fun s x => mem x s⟩
/-
**Ordset.mem.decidable** 是 Mathlib 中的一个定义，位于命名空间 `Ordset.mem`。
形式化陈述：{α : Type u_1} → [inst : Preorder α] → [inst_1 : DecidableLE α] → (x : α) 
→ (s : Ordset α) → Decidable (x ∈ s)
参数：x : α；s : Ordset α；x ∈ s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mem.decidable (x : α) (s : Ordset α) : Decidable (x ∈ s) :=
  instDecidableEqBool _ _
/-
**Ordset.pos_size_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Ordset`。
形式化陈述：pos_size_of_mem {x : α} {t : Ordset α} (h_mem : x in t) : 0 < size t
参数：h_mem : x in t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordnode.pos_size_of_mem`：pos_size_of_mem [LE α] [DecidableLE α] {x : α} 
{t : Ordnode α} (h : Sized t) (h_mem : x in t) : 0 < size t
· 使用定理 `Ordnode.Valid'.sz`：∀ {α : Type u_1} [inst : Preorder α] {lo : WithBot α}
 {t : Ordnode α} {hi : WithTop α}, Ordnode.Valid' lo t hi → t.Sized
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.decide_eq_true`：∀ {b : Bool} {x : Decidable (b = true)}, decide (b 
= true) = b
-/
theorem pos_size_of_mem {x : α} {t : Ordset α} (h_mem : x ∈ t) : 0 < size t := by
  simp only [Membership.mem, mem, Bool.decide_eq_true] at h_mem
  apply Ordnode.pos_size_of_mem t.property.sz h_mem

end

/-- O(log n). Remove an element from the set equivalent to `x`. Does nothing if there
is no such element. -/
/-
**Ordset.erase** 是 Mathlib 中的一个定义，位于命名空间 `Ordset`。
形式化陈述：erase [DecidableLE α] (x : α) (s : Ordset α) : Ordset α
参数：x : α；s : Ordset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
O(log n). Remove an element from the set equivalent to `x`. Does nothing if ther
e
is no such element.
-/
def erase [DecidableLE α] (x : α) (s : Ordset α) : Ordset α :=
  ⟨Ordnode.erase x s.val, Ordnode.erase.valid x s.property⟩

/-- O(n). Map a function across a tree, without changing the structure. -/
/-
**Ordset.map** 是 Mathlib 中的一个定义，位于命名空间 `Ordset`。
形式化陈述：map {β} [Preorder β] (f : α -> β) (f_strict_mono : StrictMono f) (s : Ords
et α) : Ordset β
参数：f : α -> β；f_strict_mono : StrictMono f；s : Ordset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
O(n). Map a function across a tree, without changing the structure.
-/
def map {β} [Preorder β] (f : α → β) (f_strict_mono : StrictMono f) (s : Ordset α) : Ordset β :=
  ⟨Ordnode.map f s.val, Ordnode.map.valid f_strict_mono s.property⟩

end Ordset

