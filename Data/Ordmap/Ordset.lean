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

/--
Definition of `Valid'` / `Valid'` 的定义

English:
structure Valid'
  parameters: (lo : WithBot α) (t : Ordnode α) (hi : WithTop α)
  axioms and operations (3):
    - ord : t.Bounded lo hi
    - sz : t.Sized
    - bal : t.Balanced

中文:
结构 Valid'
  参数: (lo : WithBot α) (t : Ordnode α) (hi : WithTop α)
  公理与运算 (3 个):
    - ord : t.Bounded lo hi
    - sz : t.Sized
    - bal : t.Balanced
-/
structure Valid' (lo : WithBot α) (t : Ordnode α) (hi : WithTop α) : Prop where
  ord : t.Bounded lo hi
  sz : t.Sized
  bal : t.Balanced

/--
Definition of `Valid` / `Valid` 的定义

English:
definition Valid
  signature: (t : Ordnode α)
  body: Valid' ⊥ t ⊤

中文:
定义 Valid
  签名: (t : Ordnode α)
  定义体: Valid' ⊥ t ⊤
-/
def Valid (t : Ordnode α) : Prop :=
  Valid' ⊥ t ⊤

/--
theorem `Valid'.mono_left` / 定理 `Valid'.mono_left`

English:
theorem Valid'.mono_left
  given: {x y : α} (xy : x <= y) {t : Ordnode α} {o} (h : Valid' y t o)
  proof: ⟨h.1.mono_left xy, h.2, h.3⟩

中文:
定理 Valid'.mono_left
  条件: {x y : α} (xy : x <= y) {t : Ordnode α} {o} (h : Valid' y t o)
  证明: ⟨h.1.mono_left xy, h.2, h.3⟩

Depends on / 依赖: mono_left
-/
theorem Valid'.mono_left {x y : α} (xy : x <= y) {t : Ordnode α} {o} (h : Valid' y t o) :
    Valid' x t o :=
  ⟨h.1.mono_left xy, h.2, h.3⟩

/--
theorem `Valid'.mono_right` / 定理 `Valid'.mono_right`

English:
theorem Valid'.mono_right
  given: {x y : α} (xy : x <= y) {t : Ordnode α} {o} (h : Valid' o t x)
  proof: ⟨h.1.mono_right xy, h.2, h.3⟩

中文:
定理 Valid'.mono_right
  条件: {x y : α} (xy : x <= y) {t : Ordnode α} {o} (h : Valid' o t x)
  证明: ⟨h.1.mono_right xy, h.2, h.3⟩
-/
theorem Valid'.mono_right {x y : α} (xy : x <= y) {t : Ordnode α} {o} (h : Valid' o t x) :
    Valid' o t y :=
  ⟨h.1.mono_right xy, h.2, h.3⟩

/--
theorem `Valid'.trans_left` / 定理 `Valid'.trans_left`

English:
theorem Valid'.trans_left
  statement: {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (h : Bounded t₁ o₁ x)
  proof: ⟨h.trans_left H.1, H.2, H.3⟩

中文:
定理 Valid'.trans_left
  结论: {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (h : Bounded t₁ o₁ x)
  证明: ⟨h.trans_left H.1, H.2, H.3⟩
-/
theorem Valid'.trans_left {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (h : Bounded t₁ o₁ x)
    (H : Valid' x t₂ o₂) : Valid' o₁ t₂ o₂ :=
  ⟨h.trans_left H.1, H.2, H.3⟩

/--
theorem `Valid'.trans_right` / 定理 `Valid'.trans_right`

English:
theorem Valid'.trans_right
  statement: {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t₁ x)
  proof: ⟨H.1.trans_right h, H.2, H.3⟩

中文:
定理 Valid'.trans_right
  结论: {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t₁ x)
  证明: ⟨H.1.trans_right h, H.2, H.3⟩
-/
theorem Valid'.trans_right {t₁ t₂ : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t₁ x)
    (h : Bounded t₂ x o₂) : Valid' o₁ t₁ o₂ :=
  ⟨H.1.trans_right h, H.2, H.3⟩

/--
theorem `Valid'.of_lt` / 定理 `Valid'.of_lt`

English:
theorem Valid'.of_lt
  statement: {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil o₁ x)
  proof: ⟨H.1.of_lt h₁ h₂, H.2, H.3⟩

中文:
定理 Valid'.of_lt
  结论: {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil o₁ x)
  证明: ⟨H.1.of_lt h₁ h₂, H.2, H.3⟩
-/
theorem Valid'.of_lt {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil o₁ x)
    (h₂ : All (· < x) t) : Valid' o₁ t x :=
  ⟨H.1.of_lt h₁ h₂, H.2, H.3⟩

/--
theorem `Valid'.of_gt` / 定理 `Valid'.of_gt`

English:
theorem Valid'.of_gt
  statement: {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil x o₂)
  proof: ⟨H.1.of_gt h₁ h₂, H.2, H.3⟩

中文:
定理 Valid'.of_gt
  结论: {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil x o₂)
  证明: ⟨H.1.of_gt h₁ h₂, H.2, H.3⟩
-/
theorem Valid'.of_gt {t : Ordnode α} {x : α} {o₁ o₂} (H : Valid' o₁ t o₂) (h₁ : Bounded nil x o₂)
    (h₂ : All (· > x) t) : Valid' x t o₂ :=
  ⟨H.1.of_gt h₁ h₂, H.2, H.3⟩

/--
theorem `Valid'.valid` / 定理 `Valid'.valid`

English:
theorem Valid'.valid
  given: {t o₁ o₂} (h : @Valid' α _ o₁ t o₂)
  statement: Valid t
  proof: ⟨h.1.weak, h.2, h.3⟩

中文:
定理 Valid'.valid
  条件: {t o₁ o₂} (h : @Valid' α _ o₁ t o₂)
  结论: Valid t
  证明: ⟨h.1.weak, h.2, h.3⟩
-/
theorem Valid'.valid {t o₁ o₂} (h : @Valid' α _ o₁ t o₂) : Valid t :=
  ⟨h.1.weak, h.2, h.3⟩

/--
theorem `valid'_nil` / 定理 `valid'_nil`

English:
theorem valid'_nil
  given: {o₁ o₂} (h : Bounded nil o₁ o₂)
  statement: Valid' o₁ (@nil α) o₂
  proof: ⟨h, ⟨⟩, ⟨⟩⟩

中文:
定理 valid'_nil
  条件: {o₁ o₂} (h : Bounded nil o₁ o₂)
  结论: Valid' o₁ (@nil α) o₂
  证明: ⟨h, ⟨⟩, ⟨⟩⟩
-/
theorem valid'_nil {o₁ o₂} (h : Bounded nil o₁ o₂) : Valid' o₁ (@nil α) o₂ :=
  ⟨h, ⟨⟩, ⟨⟩⟩

/--
theorem `valid_nil` / 定理 `valid_nil`

English:
theorem valid_nil
  statement: Valid (@nil α)
  proof: valid'_nil ⟨⟩

中文:
定理 valid_nil
  结论: Valid (@nil α)
  证明: valid'_nil ⟨⟩

Depends on / 依赖: _nil
-/
theorem valid_nil : Valid (@nil α) :=
  valid'_nil ⟨⟩

/--
theorem `Valid'.node` / 定理 `Valid'.node`

English:
theorem Valid'.node
  statement: {s l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: ⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩

中文:
定理 Valid'.node
  结论: {s l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: ⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩
-/
theorem Valid'.node {s l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : BalancedSz (size l) (size r)) (hs : s = size l + size r + 1) :
    Valid' o₁ (@node α s l x r) o₂ :=
  ⟨⟨hl.1, hr.1⟩, ⟨hs, hl.2, hr.2⟩, ⟨H, hl.3, hr.3⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Valid'.dual` / 定理 `Valid'.dual`

English:
theorem Valid'.dual
  statement: forall {t : Ordnode α} {o₁ o₂}, Valid' o₁ t o₂ -> @Valid' αᵒᵈ _ o₂ (dual t) o₁
  proof: Valid'.dual ⟨ol, sl, bl⟩
    let ⟨or', sr', br'⟩ := Valid'.dual ⟨Or, sr, br⟩
    ⟨⟨or', ol'⟩, ⟨by simp [size_dual, add_comm], sr', sl'⟩,
      ⟨by rw [size_dual, size_dual]; exact b.symm, br', bl'⟩⟩

中文:
定理 Valid'.dual
  结论: 对任意 {t : Ordnode α} {o₁ o₂}, Valid' o₁ t o₂ -> @Valid' αᵒᵈ _ o₂ (dual t) o₁
  证明: Valid'.dual ⟨ol, sl, bl⟩
    let ⟨or', sr', br'⟩ := Valid'.dual ⟨Or, sr, br⟩
    ⟨⟨or', ol'⟩, ⟨by simp [size_dual, add_comm], sr', sl'⟩,
      ⟨by rw [size_dual, size_dual]; exact b.symm, br', bl'⟩⟩
-/
theorem Valid'.dual : forall {t : Ordnode α} {o₁ o₂}, Valid' o₁ t o₂ -> @Valid' αᵒᵈ _ o₂ (dual t) o₁
  | .nil, _, _, h => valid'_nil h.1.dual
  | .node _ l _ r, _, _, ⟨⟨ol, Or⟩, ⟨rfl, sl, sr⟩, ⟨b, bl, br⟩⟩ =>
    let ⟨ol', sl', bl'⟩ := Valid'.dual ⟨ol, sl, bl⟩
    let ⟨or', sr', br'⟩ := Valid'.dual ⟨Or, sr, br⟩
    ⟨⟨or', ol'⟩, ⟨by simp [size_dual, add_comm], sr', sl'⟩,
      ⟨by rw [size_dual, size_dual]; exact b.symm, br', bl'⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Valid'.dual_iff` / 定理 `Valid'.dual_iff`

English:
theorem Valid'.dual_iff
  given: {t : Ordnode α} {o₁ o₂}
  statement: Valid' o₁ t o₂ ↔ @Valid' αᵒᵈ _ o₂ (.dual t) o₁
  proof: ⟨Valid'.dual, fun h => by
    have := Valid'.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩

中文:
定理 Valid'.dual_iff
  条件: {t : Ordnode α} {o₁ o₂}
  结论: Valid' o₁ t o₂ ↔ @Valid' αᵒᵈ _ o₂ (.dual t) o₁
  证明: ⟨Valid'.dual, fun h => by
    have := Valid'.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩
-/
theorem Valid'.dual_iff {t : Ordnode α} {o₁ o₂} : Valid' o₁ t o₂ ↔ @Valid' αᵒᵈ _ o₂ (.dual t) o₁ :=
  ⟨Valid'.dual, fun h => by
    have := Valid'.dual h; rwa [dual_dual, OrderDual.Preorder.dual_dual] at this⟩

/--
theorem `Valid.dual` / 定理 `Valid.dual`

English:
theorem Valid.dual
  given: {t : Ordnode α}
  statement: Valid t -> @Valid αᵒᵈ _ (.dual t)
  proof: Valid'.dual

中文:
定理 Valid.dual
  条件: {t : Ordnode α}
  结论: Valid t -> @Valid αᵒᵈ _ (.dual t)
  证明: Valid'.dual
-/
theorem Valid.dual {t : Ordnode α} : Valid t -> @Valid αᵒᵈ _ (.dual t) :=
  Valid'.dual

/--
theorem `Valid.dual_iff` / 定理 `Valid.dual_iff`

English:
theorem Valid.dual_iff
  given: {t : Ordnode α}
  statement: Valid t ↔ @Valid αᵒᵈ _ (.dual t)
  proof: Valid'.dual_iff

中文:
定理 Valid.dual_iff
  条件: {t : Ordnode α}
  结论: Valid t ↔ @Valid αᵒᵈ _ (.dual t)
  证明: Valid'.dual_iff

Depends on / 依赖: dual_iff
-/
theorem Valid.dual_iff {t : Ordnode α} : Valid t ↔ @Valid αᵒᵈ _ (.dual t) :=
  Valid'.dual_iff

/--
theorem `Valid'.left` / 定理 `Valid'.left`

English:
theorem Valid'.left
  given: {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂)
  statement: Valid' o₁ l x
  proof: ⟨H.1.1, H.2.2.1, H.3.2.1⟩

中文:
定理 Valid'.left
  条件: {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂)
  结论: Valid' o₁ l x
  证明: ⟨H.1.1, H.2.2.1, H.3.2.1⟩
-/
theorem Valid'.left {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂) : Valid' o₁ l x :=
  ⟨H.1.1, H.2.2.1, H.3.2.1⟩

/--
theorem `Valid'.right` / 定理 `Valid'.right`

English:
theorem Valid'.right
  given: {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂)
  statement: Valid' x r o₂
  proof: ⟨H.1.2, H.2.2.2, H.3.2.2⟩

nonrec theorem Valid.left {s l x r} (H : Valid (@node α s l x r)) : Valid l :=
  H.left.valid

nonrec theorem Valid.right {s l x r} (H : Valid (@node α s l x r)) : Valid r :=
  H.right.valid

中文:
定理 Valid'.right
  条件: {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂)
  结论: Valid' x r o₂
  证明: ⟨H.1.2, H.2.2.2, H.3.2.2⟩

nonrec theorem Valid.left {s l x r} (H : Valid (@node α s l x r)) : Valid l :=
  H.left.valid

nonrec theorem Valid.right {s l x r} (H : Valid (@node α s l x r)) : Valid r :=
  H.right.valid
-/
theorem Valid'.right {s l x r o₁ o₂} (H : Valid' o₁ (@Ordnode.node α s l x r) o₂) : Valid' x r o₂ :=
  ⟨H.1.2, H.2.2.2, H.3.2.2⟩

nonrec theorem Valid.left {s l x r} (H : Valid (@node α s l x r)) : Valid l :=
  H.left.valid

nonrec theorem Valid.right {s l x r} (H : Valid (@node α s l x r)) : Valid r :=
  H.right.valid

/--
theorem `Valid.size_eq` / 定理 `Valid.size_eq`

English:
theorem Valid.size_eq
  given: {s l x r} (H : Valid (@node α s l x r))
  proof: H.2.1

中文:
定理 Valid.size_eq
  条件: {s l x r} (H : Valid (@node α s l x r))
  证明: H.2.1
-/
theorem Valid.size_eq {s l x r} (H : Valid (@node α s l x r)) :
    size (@node α s l x r) = size l + size r + 1 :=
  H.2.1

/--
theorem `Valid'.node'` / 定理 `Valid'.node'`

English:
theorem Valid'.node'
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: hl.node hr H rfl

中文:
定理 Valid'.node'
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: hl.node hr H rfl
-/
theorem Valid'.node' {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : BalancedSz (size l) (size r)) : Valid' o₁ (@node' α l x r) o₂ :=
  hl.node hr H rfl

/--
theorem `valid'_singleton` / 定理 `valid'_singleton`

English:
theorem valid'_singleton
  given: {x : α} {o₁ o₂} (h₁ : Bounded nil o₁ x) (h₂ : Bounded nil x o₂)
  proof: (valid'_nil h₁).node (valid'_nil h₂) (Or.inl zero_le_one) rfl

中文:
定理 valid'_singleton
  条件: {x : α} {o₁ o₂} (h₁ : Bounded nil o₁ x) (h₂ : Bounded nil x o₂)
  证明: (valid'_nil h₁).node (valid'_nil h₂) (Or.inl zero_le_one) rfl
-/
theorem valid'_singleton {x : α} {o₁ o₂} (h₁ : Bounded nil o₁ x) (h₂ : Bounded nil x o₂) :
    Valid' o₁ (singleton x : Ordnode α) o₂ :=
  (valid'_nil h₁).node (valid'_nil h₂) (Or.inl zero_le_one) rfl

/--
theorem `valid_singleton` / 定理 `valid_singleton`

English:
theorem valid_singleton
  given: {x : α}
  statement: Valid (singleton x : Ordnode α)
  proof: valid'_singleton ⟨⟩ ⟨⟩

中文:
定理 valid_singleton
  条件: {x : α}
  结论: Valid (singleton x : Ordnode α)
  证明: valid'_singleton ⟨⟩ ⟨⟩

Depends on / 依赖: _singleton
-/
theorem valid_singleton {x : α} : Valid (singleton x : Ordnode α) :=
  valid'_singleton ⟨⟩ ⟨⟩

/--
theorem `Valid'.node3L` / 定理 `Valid'.node3L`

English:
theorem Valid'.node3L
  statement: {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
  proof: (hl.node' hm H1).node' hr H2

中文:
定理 Valid'.node3L
  结论: {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
  证明: (hl.node' hm H1).node' hr H2
-/
theorem Valid'.node3L {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' y r o₂) (H1 : BalancedSz (size l) (size m))
    (H2 : BalancedSz (size l + size m + 1) (size r)) : Valid' o₁ (@node3L α l x m y r) o₂ :=
  (hl.node' hm H1).node' hr H2

/--
theorem `Valid'.node3R` / 定理 `Valid'.node3R`

English:
theorem Valid'.node3R
  statement: {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
  proof: hl.node' (hm.node' hr H2) H1

中文:
定理 Valid'.node3R
  结论: {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
  证明: hl.node' (hm.node' hr H2) H1
-/
theorem Valid'.node3R {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' y r o₂) (H1 : BalancedSz (size l) (size m + size r + 1))
    (H2 : BalancedSz (size m) (size r)) : Valid' o₁ (@node3R α l x m y r) o₂ :=
  hl.node' (hm.node' hr H2) H1

/--
theorem `Valid'.node4L_lemma₁` / 定理 `Valid'.node4L_lemma₁`

English:
theorem Valid'.node4L_lemma₁
  statement: {a b c d : Nat} (lr₂ : 3 * (b + c + 1 + d) <= 16 * a + 9)
  proof: by lia

中文:
定理 Valid'.node4L_lemma₁
  结论: {a b c d : 自然数} (lr₂ : 3 * (b + c + 1 + d) <= 16 * a + 9)
  证明: by lia
-/
theorem Valid'.node4L_lemma₁ {a b c d : Nat} (lr₂ : 3 * (b + c + 1 + d) <= 16 * a + 9)
    (mr₂ : b + c + 1 <= 3 * d) (mm₁ : b <= 3 * c) : b < 3 * a + 1 := by lia

/--
theorem `Valid'.node4L_lemma₂` / 定理 `Valid'.node4L_lemma₂`

English:
theorem Valid'.node4L_lemma₂
  given: {b c d : Nat} (mr₂ : b + c + 1 <= 3 * d)
  statement: c <= 3 * d
  proof: by lia

中文:
定理 Valid'.node4L_lemma₂
  条件: {b c d : 自然数} (mr₂ : b + c + 1 <= 3 * d)
  结论: c <= 3 * d
  证明: by lia
-/
theorem Valid'.node4L_lemma₂ {b c d : Nat} (mr₂ : b + c + 1 <= 3 * d) : c <= 3 * d := by lia

/--
theorem `Valid'.node4L_lemma₃` / 定理 `Valid'.node4L_lemma₃`

English:
theorem Valid'.node4L_lemma₃
  given: {b c d : Nat} (mr₁ : 2 * d <= b + c + 1) (mm₁ : b <= 3 * c)
  proof: by lia

中文:
定理 Valid'.node4L_lemma₃
  条件: {b c d : 自然数} (mr₁ : 2 * d <= b + c + 1) (mm₁ : b <= 3 * c)
  证明: by lia
-/
theorem Valid'.node4L_lemma₃ {b c d : Nat} (mr₁ : 2 * d <= b + c + 1) (mm₁ : b <= 3 * c) :
    d <= 3 * c := by lia

/--
theorem `Valid'.node4L_lemma₄` / 定理 `Valid'.node4L_lemma₄`

English:
theorem Valid'.node4L_lemma₄
  statement: {a b c d : Nat} (lr₁ : 3 * a <= b + c + 1 + d) (mr₂ : b + c + 1 <= 3 * d)
  proof: by lia

中文:
定理 Valid'.node4L_lemma₄
  结论: {a b c d : 自然数} (lr₁ : 3 * a <= b + c + 1 + d) (mr₂ : b + c + 1 <= 3 * d)
  证明: by lia
-/
theorem Valid'.node4L_lemma₄ {a b c d : Nat} (lr₁ : 3 * a <= b + c + 1 + d) (mr₂ : b + c + 1 <= 3 * d)
    (mm₁ : b <= 3 * c) : a + b + 1 <= 3 * (c + d + 1) := by lia

/--
theorem `Valid'.node4L_lemma₅` / 定理 `Valid'.node4L_lemma₅`

English:
theorem Valid'.node4L_lemma₅
  statement: {a b c d : Nat} (lr₂ : 3 * (b + c + 1 + d) <= 16 * a + 9)
  proof: by lia

中文:
定理 Valid'.node4L_lemma₅
  结论: {a b c d : 自然数} (lr₂ : 3 * (b + c + 1 + d) <= 16 * a + 9)
  证明: by lia
-/
theorem Valid'.node4L_lemma₅ {a b c d : Nat} (lr₂ : 3 * (b + c + 1 + d) <= 16 * a + 9)
    (mr₁ : 2 * d <= b + c + 1) (mm₂ : c <= 3 * b) : c + d + 1 <= 3 * (a + b + 1) := by lia

/--
theorem `Valid'.node4L` / 定理 `Valid'.node4L`

English:
theorem Valid'.node4L
  statement: {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
  proof: by
  obtain - | ⟨s, ml, z, mr⟩ := m; · cases Hm
  suffices
    BalancedSz (size l) (size ml) ∧
      BalancedSz (size mr) (size r) ∧ BalancedSz (size l + size ml + 1) (size mr + size r + 1) from
    Valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2
  rcases H with (⟨l0, m1

中文:
定理 Valid'.node4L
  结论: {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
  证明: by
  obtain - | ⟨s, ml, z, mr⟩ := m; · cases Hm
  suffices
    BalancedSz (size l) (size ml) ∧
      BalancedSz (size mr) (size r) ∧ BalancedSz (size l + size ml + 1) (size mr + size r + 1) from
    Valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2
  rcases H with (⟨l0, m1
-/
theorem Valid'.node4L {l} {x : α} {m} {y : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hm : Valid' x m y)
    (hr : Valid' (↑y) r o₂) (Hm : 0 < size m)
    (H : size l = 0 ∧ size m = 1 ∧ size r <= 1 ∨
        0 < size l ∧
          ratio * size r <= size m ∧
            delta * size l <= size m + size r ∧
              3 * (size m + size r) <= 16 * size l + 9 ∧ size m <= delta * size r) :
    Valid' o₁ (@node4L α l x m y r) o₂ := by
  obtain - | ⟨s, ml, z, mr⟩ := m; · cases Hm
  suffices
    BalancedSz (size l) (size ml) ∧
      BalancedSz (size mr) (size r) ∧ BalancedSz (size l + size ml + 1) (size mr + size r + 1) from
    Valid'.node' (hl.node' hm.left this.1) (hm.right.node' hr this.2.1) this.2.2
  rcases H with (⟨l0, m1, r0⟩ | ⟨l0, mr₁, lr₁, lr₂, mr₂⟩)
  · rw [hm.2.size_eq, Nat.succ_inj, add_eq_zero] at m1
    rw [l0]; rw [m1.1]; rw [m1.2]; revert r0; rcases size r with (_ | _ | _) <;>
      [decide; decide; (intro r0; unfold BalancedSz delta; lia)]
  · rcases Nat.eq_zero_or_pos (size r) with r0 | r0
    · rw [r0] at mr₂; cases not_le_of_gt Hm mr₂
    rw [hm.2.size_eq] at lr₁ lr₂ mr₁ mr₂
    by_cases mm : size ml + size mr <= 1
    · dsimp [delta, ratio] at lr₁ mr₁
      have r1 : r.size = 1 := by lia
      have l1 : l.size = 1 := by lia
      rw [r1]; rw [add_assoc] at lr₁
      rw [l1]; rw [r1]
      revert mm; cases size ml <;> cases size mr <;> intro mm
      · decide
      · rw [zero_add] at mm; rcases mm with (_ | ⟨⟨⟩⟩)
        decide
      · rcases mm with (_ | ⟨⟨⟩⟩); decide
      · rw [Nat.succ_add] at mm; rcases mm with (_ | ⟨⟨⟩⟩)
    rcases hm.3.1.resolve_left mm with ⟨mm₁, mm₂⟩
    rcases Nat.eq_zero_or_pos (size ml) with ml0 | ml0
    · rw [ml0, mul_zero, Nat.le_zero] at mm₂
      rw [ml0]; rw [mm₂] at mm; cases mm (by decide)
    have : 2 * size l <= size ml + size mr + 1 := by
      have := Nat.mul_le_mul_left ratio lr₁
      rw [mul_left_comm]; rw [mul_add] at this
      have := le_trans this (add_le_add_right mr₁ _)
      rw [← Nat.succ_mul] at this
      exact (mul_le_mul_iff_right₀ (by decide)).1 this
    refine ⟨Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩, Or.inr ⟨?_, ?_⟩⟩
    · refine (mul_le_mul_iff_right₀ (by decide)).1 (le_trans this ?_)
      rw [two_mul]; rw [Nat.succ_le_iff]
      refine add_lt_add_of_lt_of_le ?_ mm₂
      simpa using! mul_lt_mul_of_pos_right (by decide : 1 < 3) ml0
    · exact Nat.le_of_lt_succ (Valid'.node4L_lemma₁ lr₂ mr₂ mm₁)
    · exact Valid'.node4L_lemma₂ mr₂
    · exact Valid'.node4L_lemma₃ mr₁ mm₁
    · exact Valid'.node4L_lemma₄ lr₁ mr₂ mm₁
    · exact Valid'.node4L_lemma₅ lr₂ mr₁ mm₂

/--
theorem `Valid'.rotateL_lemma₁` / 定理 `Valid'.rotateL_lemma₁`

English:
theorem Valid'.rotateL_lemma₁
  given: {a b c : Nat} (H2 : 3 * a <= b + c) (hb₂ : c <= 3 * b)
  statement: a <= 3 * b
  proof: by
  lia

中文:
定理 Valid'.rotateL_lemma₁
  条件: {a b c : 自然数} (H2 : 3 * a <= b + c) (hb₂ : c <= 3 * b)
  结论: a <= 3 * b
  证明: by
  lia
-/
theorem Valid'.rotateL_lemma₁ {a b c : Nat} (H2 : 3 * a <= b + c) (hb₂ : c <= 3 * b) : a <= 3 * b := by
  lia

/--
theorem `Valid'.rotateL_lemma₂` / 定理 `Valid'.rotateL_lemma₂`

English:
theorem Valid'.rotateL_lemma₂
  given: {a b c : Nat} (H3 : 2 * (b + c) <= 9 * a + 3) (h : b < 2 * c)
  proof: by lia

中文:
定理 Valid'.rotateL_lemma₂
  条件: {a b c : 自然数} (H3 : 2 * (b + c) <= 9 * a + 3) (h : b < 2 * c)
  证明: by lia
-/
theorem Valid'.rotateL_lemma₂ {a b c : Nat} (H3 : 2 * (b + c) <= 9 * a + 3) (h : b < 2 * c) :
    b < 3 * a + 1 := by lia

/--
theorem `Valid'.rotateL_lemma₃` / 定理 `Valid'.rotateL_lemma₃`

English:
theorem Valid'.rotateL_lemma₃
  given: {a b c : Nat} (H2 : 3 * a <= b + c) (h : b < 2 * c)
  statement: a + b < 3 * c
  proof: by
  lia

中文:
定理 Valid'.rotateL_lemma₃
  条件: {a b c : 自然数} (H2 : 3 * a <= b + c) (h : b < 2 * c)
  结论: a + b < 3 * c
  证明: by
  lia
-/
theorem Valid'.rotateL_lemma₃ {a b c : Nat} (H2 : 3 * a <= b + c) (h : b < 2 * c) : a + b < 3 * c := by
  lia

/--
theorem `Valid'.rotateL_lemma₄` / 定理 `Valid'.rotateL_lemma₄`

English:
theorem Valid'.rotateL_lemma₄
  given: {a b : Nat} (H3 : 2 * b <= 9 * a + 3)
  statement: 3 * b <= 16 * a + 9
  proof: by
  lia

中文:
定理 Valid'.rotateL_lemma₄
  条件: {a b : 自然数} (H3 : 2 * b <= 9 * a + 3)
  结论: 3 * b <= 16 * a + 9
  证明: by
  lia
-/
theorem Valid'.rotateL_lemma₄ {a b : Nat} (H3 : 2 * b <= 9 * a + 3) : 3 * b <= 16 * a + 9 := by
  lia

/--
theorem `Valid'.rotateL` / 定理 `Valid'.rotateL`

English:
theorem Valid'.rotateL
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: by
  obtain - | ⟨rs, rl, rx, rr⟩ := r; · cases H2
  rw [hr.2.size_eq]; rw [Nat.lt_succ_iff] at H2
  rw [hr.2.size_eq] at H3
  replace H3 : 2 * (size rl + size rr) <= 9 * size l + 3 ∨ size rl + size rr <= 2 :=
    H3.imp (@Nat.le_of_add_le_add_right _ 2 _) Nat.le_of_succ_le_succ
  have H3_0 (l0 : siz

中文:
定理 Valid'.rotateL
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: by
  obtain - | ⟨rs, rl, rx, rr⟩ := r; · cases H2
  rw [hr.2.size_eq]; rw [Nat.lt_succ_iff] at H2
  rw [hr.2.size_eq] at H3
  replace H3 : 2 * (size rl + size rr) <= 9 * size l + 3 ∨ size rl + size rr <= 2 :=
    H3.imp (@Nat.le_of_add_le_add_right _ 2 _) Nat.le_of_succ_le_succ
  have H3_0 (l0 : siz
-/
theorem Valid'.rotateL {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H1 : ¬size l + size r <= 1) (H2 : delta * size l < size r)
    (H3 : 2 * size r <= 9 * size l + 5 ∨ size r <= 3) : Valid' o₁ (@rotateL α l x r) o₂ := by
  obtain - | ⟨rs, rl, rx, rr⟩ := r; · cases H2
  rw [hr.2.size_eq]; rw [Nat.lt_succ_iff] at H2
  rw [hr.2.size_eq] at H3
  replace H3 : 2 * (size rl + size rr) <= 9 * size l + 3 ∨ size rl + size rr <= 2 :=
    H3.imp (@Nat.le_of_add_le_add_right _ 2 _) Nat.le_of_succ_le_succ
  have H3_0 (l0 : size l = 0) : size rl + size rr <= 2 := by lia
  have H3p : size l > 0 -> 2 * (size rl + size rr) <= 9 * size l + 3 := fun l0 : 1 <= size l =>
    (or_iff_left_of_imp <| by lia).1 H3
  have ablem : forall {a b : Nat}, 1 <= a -> a + b <= 2 -> b <= 1 := by lia
  have hlp : size l > 0 -> ¬size rl + size rr <= 1 := fun l0 hb =>
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
      rw [rr1]; rw [show size rl = 1 from le_antisymm (ablem rr0 H3) rl0]
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
      rw [rl0]; rw [h]; rw [Nat.le_zero]; rw [Nat.mul_eq_zero] at H2
      rw [hr.2.size_eq]; rw [rl0]; rw [h]; rw [H2.resolve_left (by decide)] at H1
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
/--
theorem `Valid'.rotateR` / 定理 `Valid'.rotateR`

English:
theorem Valid'.rotateR
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: by
  refine Valid'.dual_iff.2 ?_
  rw [dual_rotateR]
  refine hr.dual.rotateL hl.dual ?_ ?_ ?_
  · rwa [size_dual, size_dual, add_comm]
  · rwa [size_dual, size_dual]
  · rwa [size_dual, size_dual]

中文:
定理 Valid'.rotateR
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: by
  refine Valid'.dual_iff.2 ?_
  rw [dual_rotateR]
  refine hr.dual.rotateL hl.dual ?_ ?_ ?_
  · rwa [size_dual, size_dual, add_comm]
  · rwa [size_dual, size_dual]
  · rwa [size_dual, size_dual]
-/
theorem Valid'.rotateR {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H1 : ¬size l + size r <= 1) (H2 : delta * size r < size l)
    (H3 : 2 * size l <= 9 * size r + 5 ∨ size l <= 3) : Valid' o₁ (@rotateR α l x r) o₂ := by
  refine Valid'.dual_iff.2 ?_
  rw [dual_rotateR]
  refine hr.dual.rotateL hl.dual ?_ ?_ ?_
  · rwa [size_dual, size_dual, add_comm]
  · rwa [size_dual, size_dual]
  · rwa [size_dual, size_dual]

/--
theorem `Valid'.balance'_aux` / 定理 `Valid'.balance'_aux`

English:
theorem Valid'.balance'_aux
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: by
  rw [balance']; split_ifs with h h_1 h_2
  · exact hl.node' hr (Or.inl h)
  · exact hl.rotateL hr h h_1 H₁
  · exact hl.rotateR hr h h_2 H₂
  · exact hl.node' hr (Or.inr ⟨not_lt.1 h_2, not_lt.1 h_1⟩)

中文:
定理 Valid'.balance'_aux
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: by
  rw [balance']; split_ifs with h h_1 h_2
  · exact hl.node' hr (Or.inl h)
  · exact hl.rotateL hr h h_1 H₁
  · exact hl.rotateR hr h h_2 H₂
  · exact hl.node' hr (Or.inr ⟨not_lt.1 h_2, not_lt.1 h_1⟩)
-/
theorem Valid'.balance'_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : 2 * @size α r <= 9 * size l + 5 ∨ size r <= 3)
    (H₂ : 2 * @size α l <= 9 * size r + 5 ∨ size l <= 3) : Valid' o₁ (@balance' α l x r) o₂ := by
  rw [balance']; split_ifs with h h_1 h_2
  · exact hl.node' hr (Or.inl h)
  · exact hl.rotateL hr h h_1 H₁
  · exact hl.rotateR hr h h_2 H₂
  · exact hl.node' hr (Or.inr ⟨not_lt.1 h_2, not_lt.1 h_1⟩)

/--
theorem `Valid'.balance'_lemma` / 定理 `Valid'.balance'_lemma`

English:
theorem Valid'.balance'_lemma
  statement: {α l l' r r'} (H1 : BalancedSz l' r')
  proof: by
  suffices @size α r <= 3 * (size l + 1) by lia
  rcases H2 with (⟨hl, rfl⟩ | ⟨hr, rfl⟩) <;> rcases H1 with (h | ⟨_, h₂⟩)
  · exact le_trans (Nat.le_add_left _ _) (le_trans h (Nat.le_add_left _ _))
  · exact
      le_trans h₂
        (Nat.mul_le_mul_left _ <| le_trans (Nat.dist_tri_right _ _) (Na

中文:
定理 Valid'.balance'_lemma
  结论: {α l l' r r'} (H1 : BalancedSz l' r')
  证明: by
  suffices @size α r <= 3 * (size l + 1) by lia
  rcases H2 with (⟨hl, rfl⟩ | ⟨hr, rfl⟩) <;> rcases H1 with (h | ⟨_, h₂⟩)
  · exact le_trans (Nat.le_add_left _ _) (le_trans h (Nat.le_add_left _ _))
  · exact
      le_trans h₂
        (Nat.mul_le_mul_left _ <| le_trans (Nat.dist_tri_right _ _) (Na
-/
theorem Valid'.balance'_lemma {α l l' r r'} (H1 : BalancedSz l' r')
    (H2 : Nat.dist (@size α l) l' <= 1 ∧ size r = r' ∨ Nat.dist (size r) r' <= 1 ∧ size l = l') :
    2 * @size α r <= 9 * size l + 5 ∨ size r <= 3 := by
  suffices @size α r <= 3 * (size l + 1) by lia
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

/--
theorem `Valid'.balance'` / 定理 `Valid'.balance'`

English:
theorem Valid'.balance'
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: let ⟨_, _, H1, H2⟩ := H
  Valid'.balance'_aux hl hr (Valid'.balance'_lemma H1 H2) (Valid'.balance'_lemma H1.symm H2.symm)

中文:
定理 Valid'.balance'
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: let ⟨_, _, H1, H2⟩ := H
  Valid'.balance'_aux hl hr (Valid'.balance'_lemma H1 H2) (Valid'.balance'_lemma H1.symm H2.symm)
-/
theorem Valid'.balance' {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : exists l' r', BalancedSz l' r' ∧
          (Nat.dist (size l) l' <= 1 ∧ size r = r' ∨ Nat.dist (size r) r' <= 1 ∧ size l = l')) :
    Valid' o₁ (@balance' α l x r) o₂ :=
  let ⟨_, _, H1, H2⟩ := H
  Valid'.balance'_aux hl hr (Valid'.balance'_lemma H1 H2) (Valid'.balance'_lemma H1.symm H2.symm)

/--
theorem `Valid'.balance` / 定理 `Valid'.balance`

English:
theorem Valid'.balance
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: by
  rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2]; exact hl.balance' hr H

中文:
定理 Valid'.balance
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: by
  rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2]; exact hl.balance' hr H
-/
theorem Valid'.balance {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : exists l' r', BalancedSz l' r' ∧
          (Nat.dist (size l) l' <= 1 ∧ size r = r' ∨ Nat.dist (size r) r' <= 1 ∧ size l = l')) :
    Valid' o₁ (@balance α l x r) o₂ := by
  rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2]; exact hl.balance' hr H

/--
theorem `Valid'.balanceL_aux` / 定理 `Valid'.balanceL_aux`

English:
theorem Valid'.balanceL_aux
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: by
  rw [balanceL_eq_balance hl.2 hr.2 H₁ H₂]; rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2]
  refine hl.balance'_aux hr (Or.inl ?_) H₃
  rcases Nat.eq_zero_or_pos (size r) with r0 | r0
  · rw [r0]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos (size l) with l0 | l0
  · rw [l0]; exact le_trans (Nat

中文:
定理 Valid'.balanceL_aux
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: by
  rw [balanceL_eq_balance hl.2 hr.2 H₁ H₂]; rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2]
  refine hl.balance'_aux hr (Or.inl ?_) H₃
  rcases Nat.eq_zero_or_pos (size r) with r0 | r0
  · rw [r0]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos (size l) with l0 | l0
  · rw [l0]; exact le_trans (Nat
-/
theorem Valid'.balanceL_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : size l = 0 -> size r <= 1) (H₂ : 1 <= size l -> 1 <= size r -> size r <= delta * size l)
    (H₃ : 2 * @size α l <= 9 * size r + 5 ∨ size l <= 3) : Valid' o₁ (@balanceL α l x r) o₂ := by
  rw [balanceL_eq_balance hl.2 hr.2 H₁ H₂]; rw [balance_eq_balance' hl.3 hr.3 hl.2 hr.2]
  refine hl.balance'_aux hr (Or.inl ?_) H₃
  rcases Nat.eq_zero_or_pos (size r) with r0 | r0
  · rw [r0]; exact Nat.zero_le _
  rcases Nat.eq_zero_or_pos (size l) with l0 | l0
  · rw [l0]; exact le_trans (Nat.mul_le_mul_left _ (H₁ l0)) (by decide)
  replace H₂ : _ <= 3 * _ := H₂ l0 r0; lia

/--
theorem `Valid'.balanceL` / 定理 `Valid'.balanceL`

English:
theorem Valid'.balanceL
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: by
  rw [balanceL_eq_balance' hl.3 hr.3 hl.2 hr.2 H]
  refine hl.balance' hr ?_
  rcases H with (⟨l', e, H⟩ | ⟨r', e, H⟩)
  · exact ⟨_, _, H, Or.inl ⟨e.dist_le', rfl⟩⟩
  · exact ⟨_, _, H, Or.inr ⟨e.dist_le, rfl⟩⟩

中文:
定理 Valid'.balanceL
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: by
  rw [balanceL_eq_balance' hl.3 hr.3 hl.2 hr.2 H]
  refine hl.balance' hr ?_
  rcases H with (⟨l', e, H⟩ | ⟨r', e, H⟩)
  · exact ⟨_, _, H, Or.inl ⟨e.dist_le', rfl⟩⟩
  · exact ⟨_, _, H, Or.inr ⟨e.dist_le, rfl⟩⟩
-/
theorem Valid'.balanceL {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : (exists l', Raised l' (size l) ∧ BalancedSz l' (size r)) ∨
        exists r', Raised (size r) r' ∧ BalancedSz (size l) r') :
    Valid' o₁ (@balanceL α l x r) o₂ := by
  rw [balanceL_eq_balance' hl.3 hr.3 hl.2 hr.2 H]
  refine hl.balance' hr ?_
  rcases H with (⟨l', e, H⟩ | ⟨r', e, H⟩)
  · exact ⟨_, _, H, Or.inl ⟨e.dist_le', rfl⟩⟩
  · exact ⟨_, _, H, Or.inr ⟨e.dist_le, rfl⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Valid'.balanceR_aux` / 定理 `Valid'.balanceR_aux`

English:
theorem Valid'.balanceR_aux
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: by
  rw [Valid'.dual_iff]; rw [dual_balanceR]
  have := hr.dual.balanceL_aux hl.dual
  rw [size_dual]; rw [size_dual] at this
  exact this H₁ H₂ H₃

中文:
定理 Valid'.balanceR_aux
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: by
  rw [Valid'.dual_iff]; rw [dual_balanceR]
  have := hr.dual.balanceL_aux hl.dual
  rw [size_dual]; rw [size_dual] at this
  exact this H₁ H₂ H₃
-/
theorem Valid'.balanceR_aux {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H₁ : size r = 0 -> size l <= 1) (H₂ : 1 <= size r -> 1 <= size l -> size l <= delta * size r)
    (H₃ : 2 * @size α r <= 9 * size l + 5 ∨ size r <= 3) : Valid' o₁ (@balanceR α l x r) o₂ := by
  rw [Valid'.dual_iff]; rw [dual_balanceR]
  have := hr.dual.balanceL_aux hl.dual
  rw [size_dual]; rw [size_dual] at this
  exact this H₁ H₂ H₃

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Valid'.balanceR` / 定理 `Valid'.balanceR`

English:
theorem Valid'.balanceR
  statement: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: by
  rw [Valid'.dual_iff]; rw [dual_balanceR]; exact hr.dual.balanceL hl.dual (balance_sz_dual H)

中文:
定理 Valid'.balanceR
  结论: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: by
  rw [Valid'.dual_iff]; rw [dual_balanceR]; exact hr.dual.balanceL hl.dual (balance_sz_dual H)
-/
theorem Valid'.balanceR {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
    (H : (exists l', Raised (size l) l' ∧ BalancedSz l' (size r)) ∨
        exists r', Raised r' (size r) ∧ BalancedSz (size l) r') :
    Valid' o₁ (@balanceR α l x r) o₂ := by
  rw [Valid'.dual_iff]; rw [dual_balanceR]; exact hr.dual.balanceL hl.dual (balance_sz_dual H)

/--
theorem `Valid'.eraseMax_aux` / 定理 `Valid'.eraseMax_aux`

English:
theorem Valid'.eraseMax_aux
  given: {s l x r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂)
  proof: by
  have := H.2.eq_node'; rw [this] at H; clear this
  induction r generalizing l x o₁ with
  | nil => exact ⟨H.left, rfl⟩
  | node rs rl rx rr _ IHrr =>
    have := H.2.2.2.eq_node'; rw [this] at H ⊢
    rcases IHrr H.right with ⟨h, e⟩
    refine ⟨Valid'.balanceL H.left h (Or.inr ⟨_, Or.inr e, H.3

中文:
定理 Valid'.eraseMax_aux
  条件: {s l x r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂)
  证明: by
  have := H.2.eq_node'; rw [this] at H; clear this
  induction r generalizing l x o₁ with
  | nil => exact ⟨H.left, rfl⟩
  | node rs rl rx rr _ IHrr =>
    have := H.2.2.2.eq_node'; rw [this] at H ⊢
    rcases IHrr H.right with ⟨h, e⟩
    refine ⟨Valid'.balanceL H.left h (Or.inr ⟨_, Or.inr e, H.3
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
    rw [eraseMax]; rw [size_balanceL H.3.2.1 h.3 H.2.2.1 h.2 (Or.inr ⟨_]; rw [Or.inr e]; rw [H.3.1⟩)]
    rw [size_node]; rw [e]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Valid'.eraseMin_aux` / 定理 `Valid'.eraseMin_aux`

English:
theorem Valid'.eraseMin_aux
  given: {s l} {x : α} {r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂)
  proof: by
  have := H.dual.eraseMax_aux
  rwa [← dual_node', size_dual, ← dual_eraseMin, size_dual, ← Valid'.dual_iff, findMax'_dual]
    at this

中文:
定理 Valid'.eraseMin_aux
  条件: {s l} {x : α} {r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂)
  证明: by
  have := H.dual.eraseMax_aux
  rwa [← dual_node', size_dual, ← dual_eraseMin, size_dual, ← Valid'.dual_iff, findMax'_dual]
    at this
-/
theorem Valid'.eraseMin_aux {s l} {x : α} {r o₁ o₂} (H : Valid' o₁ (.node s l x r) o₂) :
    Valid' ↑(findMin' l x) (@eraseMin α (.node' l x r)) o₂ ∧
      size (.node' l x r) = size (eraseMin (.node' l x r)) + 1 := by
  have := H.dual.eraseMax_aux
  rwa [← dual_node', size_dual, ← dual_eraseMin, size_dual, ← Valid'.dual_iff, findMax'_dual]
    at this

/--
theorem `eraseMin.valid` / 定理 `eraseMin.valid`

English:
theorem eraseMin.valid
  statement: forall {t}, @Valid α _ t -> Valid (eraseMin t)

中文:
定理 eraseMin.valid
  结论: 对任意 {t}, @Valid α _ t -> Valid (eraseMin t)
-/
theorem eraseMin.valid : forall {t}, @Valid α _ t -> Valid (eraseMin t)
  | nil, _ => valid_nil
  | node _ l x r, h => by rw [h.2.eq_node']; exact h.eraseMin_aux.1.valid

set_option backward.isDefEq.respectTransparency false in
/--
theorem `eraseMax.valid` / 定理 `eraseMax.valid`

English:
theorem eraseMax.valid
  given: {t} (h : @Valid α _ t)
  statement: Valid (eraseMax t)
  proof: by
  rw [Valid.dual_iff]; rw [dual_eraseMax]; exact eraseMin.valid h.dual

中文:
定理 eraseMax.valid
  条件: {t} (h : @Valid α _ t)
  结论: Valid (eraseMax t)
  证明: by
  rw [Valid.dual_iff]; rw [dual_eraseMax]; exact eraseMin.valid h.dual

Depends on / 依赖: Valid.dual_iff, dual_eraseMax, dual_iff, eraseMin, eraseMin.valid, h.dual
-/
theorem eraseMax.valid {t} (h : @Valid α _ t) : Valid (eraseMax t) := by
  rw [Valid.dual_iff]; rw [dual_eraseMax]; exact eraseMin.valid h.dual

/--
theorem `Valid'.glue_aux` / 定理 `Valid'.glue_aux`

English:
theorem Valid'.glue_aux
  statement: {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
  proof: by
  obtain - | ⟨ls, ll, lx, lr⟩ := l; · exact ⟨hr, (zero_add _).symm⟩
  obtain - | ⟨rs, rl, rx, rr⟩ := r; · exact ⟨hl, rfl⟩
  dsimp [glue]; split_ifs
  · rw [splitMax_eq]
    · obtain ⟨v, e⟩ := Valid'.eraseMax_aux hl
      suffices H : _ by
        refine ⟨Valid'.balanceR v (hr.of_gt ?_ ?_) H, ?_⟩


中文:
定理 Valid'.glue_aux
  结论: {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
  证明: by
  obtain - | ⟨ls, ll, lx, lr⟩ := l; · exact ⟨hr, (zero_add _).symm⟩
  obtain - | ⟨rs, rl, rx, rr⟩ := r; · exact ⟨hl, rfl⟩
  dsimp [glue]; split_ifs
  · rw [splitMax_eq]
    · obtain ⟨v, e⟩ := Valid'.eraseMax_aux hl
      suffices H : _ by
        refine ⟨Valid'.balanceR v (hr.of_gt ?_ ?_) H, ?_⟩

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

/--
theorem `Valid'.glue` / 定理 `Valid'.glue`

English:
theorem Valid'.glue
  given: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  proof: Valid'.glue_aux (hl.trans_right hr.1) (hr.trans_left hl.1) (hl.1.to_sep hr.1)

中文:
定理 Valid'.glue
  条件: {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂)
  证明: Valid'.glue_aux (hl.trans_right hr.1) (hr.trans_left hl.1) (hl.1.to_sep hr.1)
-/
theorem Valid'.glue {l} {x : α} {r o₁ o₂} (hl : Valid' o₁ l x) (hr : Valid' x r o₂) :
    BalancedSz (size l) (size r) ->
      Valid' o₁ (@glue α l r) o₂ ∧ size (@glue α l r) = size l + size r :=
  Valid'.glue_aux (hl.trans_right hr.1) (hr.trans_left hl.1) (hl.1.to_sep hr.1)

/--
theorem `Valid'.merge_lemma` / 定理 `Valid'.merge_lemma`

English:
theorem Valid'.merge_lemma
  given: {a b c : Nat} (h₁ : 3 * a < b + c + 1) (h₂ : b <= 3 * c)
  proof: by lia

中文:
定理 Valid'.merge_lemma
  条件: {a b c : 自然数} (h₁ : 3 * a < b + c + 1) (h₂ : b <= 3 * c)
  证明: by lia
-/
theorem Valid'.merge_lemma {a b c : Nat} (h₁ : 3 * a < b + c + 1) (h₂ : b <= 3 * c) :
    2 * (a + b) <= 9 * c + 5 := by lia

/--
theorem `Valid'.merge_aux₁` / 定理 `Valid'.merge_aux₁`

English:
theorem Valid'.merge_aux₁
  statement: {o₁ o₂ ls ll lx lr rs rl rx rr t}
  proof: by
  rw [hl.2.1] at e
  rw [hl.2.1]; rw [hr.2.1]; rw [delta] at h
  rcases hr.3.1 with (H | ⟨hr₁, hr₂⟩); · lia
  suffices H₂ : _ by
    suffices H₁ : _ by
      refine ⟨Valid'.balanceL_aux v hr.right H₁ H₂ ?_, ?_⟩
      · rw [e]; exact Or.inl (Valid'.merge_lemma h hr₁)
      · rw [balanceL_eq_balanc

中文:
定理 Valid'.merge_aux₁
  结论: {o₁ o₂ ls ll lx lr rs rl rx rr t}
  证明: by
  rw [hl.2.1] at e
  rw [hl.2.1]; rw [hr.2.1]; rw [delta] at h
  rcases hr.3.1 with (H | ⟨hr₁, hr₂⟩); · lia
  suffices H₂ : _ by
    suffices H₁ : _ by
      refine ⟨Valid'.balanceL_aux v hr.right H₁ H₂ ?_, ?_⟩
      · rw [e]; exact Or.inl (Valid'.merge_lemma h hr₁)
      · rw [balanceL_eq_balanc
-/
theorem Valid'.merge_aux₁ {o₁ o₂ ls ll lx lr rs rl rx rr t}
    (hl : Valid' o₁ (@Ordnode.node α ls ll lx lr) o₂) (hr : Valid' o₁ (.node rs rl rx rr) o₂)
    (h : delta * ls < rs) (v : Valid' o₁ t rx) (e : size t = ls + size rl) :
    Valid' o₁ (.balanceL t rx rr) o₂ ∧ size (.balanceL t rx rr) = ls + rs := by
  rw [hl.2.1] at e
  rw [hl.2.1]; rw [hr.2.1]; rw [delta] at h
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
/--
theorem `Valid'.merge_aux` / 定理 `Valid'.merge_aux`

English:
theorem Valid'.merge_aux
  statement: {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
  proof: by
  induction l generalizing o₁ o₂ r with
  | nil => exact ⟨hr, (zero_add _).symm⟩
  | node ls ll lx lr _ IHlr => ?_
  induction r generalizing o₁ o₂ with
  | nil => exact ⟨hl, rfl⟩
  | node rs rl rx rr IHrl _ => ?_
  rw [merge_node]; split_ifs with h h_1
  · obtain ⟨v, e⟩ := IHrl (hl.of_lt hr.1.1.

中文:
定理 Valid'.merge_aux
  结论: {l r o₁ o₂} (hl : Valid' o₁ l o₂) (hr : Valid' o₁ r o₂)
  证明: by
  induction l generalizing o₁ o₂ r with
  | nil => exact ⟨hr, (zero_add _).symm⟩
  | node ls ll lx lr _ IHlr => ?_
  induction r generalizing o₁ o₂ with
  | nil => exact ⟨hl, rfl⟩
  | node rs rl rx rr IHrl _ => ?_
  rw [merge_node]; split_ifs with h h_1
  · obtain ⟨v, e⟩ := IHrl (hl.of_lt hr.1.1.
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
    rw [size_dual]; rw [add_comm]; rw [size_dual]; rw [← dual_balanceR]; rw [← Valid'.dual_iff]; rw [size_dual]; rw [add_comm rs] at this
    exact this e
  · refine Valid'.glue_aux hl hr sep (Or.inr ⟨not_lt.1 h_1, not_lt.1 h⟩)

/--
theorem `Valid.merge` / 定理 `Valid.merge`

English:
theorem Valid.merge
  statement: {l r} (hl : Valid l) (hr : Valid r)
  proof: (Valid'.merge_aux hl hr sep).1

中文:
定理 Valid.merge
  结论: {l r} (hl : Valid l) (hr : Valid r)
  证明: (Valid'.merge_aux hl hr sep).1

Depends on / 依赖: merge_aux
-/
theorem Valid.merge {l r} (hl : Valid l) (hr : Valid r)
    (sep : l.All fun x => r.All fun y => x < y) : Valid (@merge α l r) :=
  (Valid'.merge_aux hl hr sep).1

/--
theorem `insertWith.valid_aux` / 定理 `insertWith.valid_aux`

English:
theorem insertWith.valid_aux
  statement: [@Std.Total α (· <= ·)] [DecidableLE α] (f : α -> α) (x : α)
  proof: lt_of_le_not_ge ((total_of (· <= ·) _ _).resolve_left h_1) h_1
      rcases insertWith.valid_aux f x hf h.right this br with ⟨vr, e⟩
      suffices H : _ by
        refine ⟨h.left.balanceR vr H, ?_⟩
        rw [size_balanceR h.3.2.1 vr.3 h.2.2.1 vr.2 H]; rw [h.2.size_eq]
        exact (e.add_left _)

中文:
定理 insertWith.valid_aux
  结论: [@Std.Total α (· <= ·)] [DecidableLE α] (f : α -> α) (x : α)
  证明: lt_of_le_not_ge ((total_of (· <= ·) _ _).resolve_left h_1) h_1
      rcases insertWith.valid_aux f x hf h.right this br with ⟨vr, e⟩
      suffices H : _ by
        refine ⟨h.left.balanceR vr H, ?_⟩
        rw [size_balanceR h.3.2.1 vr.3 h.2.2.1 vr.2 H]; rw [h.2.size_eq]
        exact (e.add_left _)

Depends on / 依赖: lt_of_le_not_ge, resolve_left, total_of
-/
theorem insertWith.valid_aux [@Std.Total α (· <= ·)] [DecidableLE α] (f : α -> α) (x : α)
    (hf : forall y, x <= y ∧ y <= x -> x <= f y ∧ f y <= x) :
    forall {t o₁ o₂},
      Valid' o₁ t o₂ ->
        Bounded nil o₁ x ->
          Bounded nil x o₂ ->
            Valid' o₁ (insertWith f x t) o₂ ∧ Raised (size t) (size (insertWith f x t))
  | nil, _, _, _, bl, br => ⟨valid'_singleton bl br, Or.inr rfl⟩
  | node sz l y r, o₁, o₂, h, bl, br => by
    rw [insertWith]; rw [cmpLE]
    split_ifs with h_1 h_2 <;> dsimp only
    · rcases h with ⟨⟨lx, xr⟩, hs, hb⟩
      rcases hf _ ⟨h_1, h_2⟩ with ⟨xf, fx⟩
      refine
        ⟨⟨⟨lx.mono_right (le_trans h_2 xf), xr.mono_left (le_trans fx h_1)⟩, hs, hb⟩, Or.inl rfl⟩
    · rcases insertWith.valid_aux f x hf h.left bl (lt_of_le_not_ge h_1 h_2) with ⟨vl, e⟩
      suffices H : _ by
        refine ⟨vl.balanceL h.right H, ?_⟩
        rw [size_balanceL vl.3 h.3.2.2 vl.2 h.2.2.2 H]; rw [h.2.size_eq]
        exact (e.add_right _).add_right _
      exact Or.inl ⟨_, e, h.3.1⟩
    · have : y < x := lt_of_le_not_ge ((total_of (· <= ·) _ _).resolve_left h_1) h_1
      rcases insertWith.valid_aux f x hf h.right this br with ⟨vr, e⟩
      suffices H : _ by
        refine ⟨h.left.balanceR vr H, ?_⟩
        rw [size_balanceR h.3.2.1 vr.3 h.2.2.1 vr.2 H]; rw [h.2.size_eq]
        exact (e.add_left _).add_right _
      exact Or.inr ⟨_, e, h.3.1⟩

/--
theorem `insertWith.valid` / 定理 `insertWith.valid`

English:
theorem insertWith.valid
  statement: [@Std.Total α (· <= ·)] [DecidableLE α] (f : α -> α) (x : α)
  proof: (insertWith.valid_aux _ _ hf h ⟨⟩ ⟨⟩).1

中文:
定理 insertWith.valid
  结论: [@Std.Total α (· <= ·)] [DecidableLE α] (f : α -> α) (x : α)
  证明: (insertWith.valid_aux _ _ hf h ⟨⟩ ⟨⟩).1

Depends on / 依赖: insertWith, insertWith.valid_aux, valid_aux
-/
theorem insertWith.valid [@Std.Total α (· <= ·)] [DecidableLE α] (f : α -> α) (x : α)
    (hf : forall y, x <= y ∧ y <= x -> x <= f y ∧ f y <= x) {t} (h : Valid t) : Valid (insertWith f x t) :=
  (insertWith.valid_aux _ _ hf h ⟨⟩ ⟨⟩).1

/--
theorem `insert_eq_insertWith` / 定理 `insert_eq_insertWith`

English:
theorem insert_eq_insertWith
  given: [DecidableLE α] (x : α)

中文:
定理 insert_eq_insertWith
  条件: [DecidableLE α] (x : α)
-/
theorem insert_eq_insertWith [DecidableLE α] (x : α) :
    forall t, Ordnode.insert x t = insertWith (fun _ => x) x t
  | nil => rfl
  | node _ l y r => by
    unfold Ordnode.insert insertWith; cases cmpLE x y <;> simp [insert_eq_insertWith]

/--
theorem `insert.valid` / 定理 `insert.valid`

English:
theorem insert.valid
  given: [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) {t} (h : Valid t)
  proof: by
  rw [insert_eq_insertWith]; exact insertWith.valid _ _ (fun _ _ => ⟨le_rfl, le_rfl⟩) h

中文:
定理 insert.valid
  条件: [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) {t} (h : Valid t)
  证明: by
  rw [insert_eq_insertWith]; exact insertWith.valid _ _ (fun _ _ => ⟨le_rfl, le_rfl⟩) h

Depends on / 依赖: insertWith, insertWith.valid, insert_eq_insertWith, le_rfl
-/
theorem insert.valid [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) {t} (h : Valid t) :
    Valid (Ordnode.insert x t) := by
  rw [insert_eq_insertWith]; exact insertWith.valid _ _ (fun _ _ => ⟨le_rfl, le_rfl⟩) h

/--
theorem `insert'_eq_insertWith` / 定理 `insert'_eq_insertWith`

English:
theorem insert'_eq_insertWith
  given: [DecidableLE α] (x : α)

中文:
定理 insert'_eq_insertWith
  条件: [DecidableLE α] (x : α)
-/
theorem insert'_eq_insertWith [DecidableLE α] (x : α) :
    forall t, insert' x t = insertWith id x t
  | nil => rfl
  | node _ l y r => by
    unfold insert' insertWith; cases cmpLE x y <;> simp [insert'_eq_insertWith]

/--
theorem `insert'.valid` / 定理 `insert'.valid`

English:
theorem insert'.valid
  statement: [@Std.Total α (· <= ·)] [DecidableLE α]
  proof: by
  rw [insert'_eq_insertWith]; exact insertWith.valid _ _ (fun _ => id) h

中文:
定理 insert'.valid
  结论: [@Std.Total α (· <= ·)] [DecidableLE α]
  证明: by
  rw [insert'_eq_insertWith]; exact insertWith.valid _ _ (fun _ => id) h

Depends on / 依赖: _eq_insertWith, insert, insertWith, insertWith.valid
-/
theorem insert'.valid [@Std.Total α (· <= ·)] [DecidableLE α]
    (x : α) {t} (h : Valid t) : Valid (insert' x t) := by
  rw [insert'_eq_insertWith]; exact insertWith.valid _ _ (fun _ => id) h

/--
theorem `Valid'.map_aux` / 定理 `Valid'.map_aux`

English:
theorem Valid'.map_aux
  statement: {β} [Preorder β] {f : α -> β} (f_strict_mono : StrictMono f) {t a₁ a₂}
  proof: by
  induction t generalizing a₁ a₂ with
  | nil =>
    simp only [map, size_nil, and_true]; apply valid'_nil
    cases a₁; · trivial
    cases a₂; · trivial
    simp only [Option.map, Bounded]
    exact f_strict_mono h.ord
  | node _ _ _ _ t_ih_l t_ih_r =>
    have t_ih_l' := t_ih_l h.left
    have

中文:
定理 Valid'.map_aux
  结论: {β} [Preorder β] {f : α -> β} (f_strict_mono : StrictMono f) {t a₁ a₂}
  证明: by
  induction t generalizing a₁ a₂ with
  | nil =>
    simp only [map, size_nil, and_true]; apply valid'_nil
    cases a₁; · trivial
    cases a₂; · trivial
    simp only [Option.map, Bounded]
    exact f_strict_mono h.ord
  | node _ _ _ _ t_ih_l t_ih_r =>
    have t_ih_l' := t_ih_l h.left
    have
-/
theorem Valid'.map_aux {β} [Preorder β] {f : α -> β} (f_strict_mono : StrictMono f) {t a₁ a₂}
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

/--
theorem `map.valid` / 定理 `map.valid`

English:
theorem map.valid
  given: {β} [Preorder β] {f : α -> β} (f_strict_mono : StrictMono f) {t} (h : Valid t)
  proof: (Valid'.map_aux f_strict_mono h).1

中文:
定理 map.valid
  条件: {β} [Preorder β] {f : α -> β} (f_strict_mono : StrictMono f) {t} (h : Valid t)
  证明: (Valid'.map_aux f_strict_mono h).1

Depends on / 依赖: f_strict_mono, map_aux
-/
theorem map.valid {β} [Preorder β] {f : α -> β} (f_strict_mono : StrictMono f) {t} (h : Valid t) :
    Valid (map f t) :=
  (Valid'.map_aux f_strict_mono h).1

/--
theorem `Valid'.erase_aux` / 定理 `Valid'.erase_aux`

English:
theorem Valid'.erase_aux
  given: [DecidableLE α] (x : α) {t a₁ a₂} (h : Valid' a₁ t a₂)
  proof: by
  induction t generalizing a₁ a₂ with
  | nil =>
    simpa [erase, Raised]
  | node _ t_l t_x t_r t_ih_l t_ih_r =>
    simp only [erase, size_node]
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    obtain ⟨t_l_valid, t_l_size⟩ := t_ih_l'
    obtain ⟨

中文:
定理 Valid'.erase_aux
  条件: [DecidableLE α] (x : α) {t a₁ a₂} (h : Valid' a₁ t a₂)
  证明: by
  induction t generalizing a₁ a₂ with
  | nil =>
    simpa [erase, Raised]
  | node _ t_l t_x t_r t_ih_l t_ih_r =>
    simp only [erase, size_node]
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    obtain ⟨t_l_valid, t_l_size⟩ := t_ih_l'
    obtain ⟨
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

/--
theorem `erase.valid` / 定理 `erase.valid`

English:
theorem erase.valid
  given: [DecidableLE α] (x : α) {t} (h : Valid t)
  statement: Valid (erase x t)
  proof: (Valid'.erase_aux x h).1

中文:
定理 erase.valid
  条件: [DecidableLE α] (x : α) {t} (h : Valid t)
  结论: Valid (erase x t)
  证明: (Valid'.erase_aux x h).1

Depends on / 依赖: erase_aux
-/
theorem erase.valid [DecidableLE α] (x : α) {t} (h : Valid t) : Valid (erase x t) :=
  (Valid'.erase_aux x h).1

/--
theorem `size_erase_of_mem` / 定理 `size_erase_of_mem`

English:
theorem size_erase_of_mem
  statement: [DecidableLE α] {x : α} {t a₁ a₂} (h : Valid' a₁ t a₂)
  proof: by
  induction t generalizing a₁ a₂ with
  | nil =>
    contradiction
  | node _ t_l t_x t_r t_ih_l t_ih_r =>
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    dsimp only [Membership.mem, mem] at h_mem
    unfold erase
    revert h_mem; cases cmpLE x t_

中文:
定理 size_erase_of_mem
  结论: [DecidableLE α] {x : α} {t a₁ a₂} (h : Valid' a₁ t a₂)
  证明: by
  induction t generalizing a₁ a₂ with
  | nil =>
    contradiction
  | node _ t_l t_x t_r t_ih_l t_ih_r =>
    have t_ih_l' := t_ih_l h.left
    have t_ih_r' := t_ih_r h.right
    clear t_ih_l t_ih_r
    dsimp only [Membership.mem, mem] at h_mem
    unfold erase
    revert h_mem; cases cmpLE x t_

Depends on / 依赖: Membership, Membership.mem, erase_aux, generalizing, h.left, h.right, h.right.bal, h_mem, revert, size_balanceR, t_ih_l, t_ih_r, t_l_h, t_l_size, t_l_valid, t_l_valid.bal, t_l_valid.sz
-/
theorem size_erase_of_mem [DecidableLE α] {x : α} {t a₁ a₂} (h : Valid' a₁ t a₂)
    (h_mem : x in t) : size (erase x t) = size t - 1 := by
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
      rw [t_ih_l]; rw [h.sz.1]
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
      rw [t_ih_r]; rw [h.sz.1]
      have h_pos_t_r_size := pos_size_of_mem h.right.sz h_mem
      revert h_pos_t_r_size; rcases t_r.size with - | t_r_size <;> intro h_pos_t_r_size
      · cases h_pos_t_r_size
      · simp [Nat.add_assoc]

end Valid

end Ordnode

/--
Definition of `Ordset` / `Ordset` 的定义

English:
definition Ordset
  signature: (α : Type*) [Preorder α]
  body: { t : Ordnode α // t.Valid }

中文:
定义 Ordset
  签名: (α : 类型) [Preorder α]
  定义体: { t : Ordnode α // t.Valid }

Depends on / 依赖: Ordnode, t.Valid
-/
def Ordset (α : Type*) [Preorder α] :=
  { t : Ordnode α // t.Valid }

namespace Ordset

open Ordnode

variable [Preorder α]

/-- O(1). The empty set. -/
nonrec def nil : Ordset α :=
  ⟨nil, ⟨⟩, ⟨⟩, ⟨⟩⟩

/--
Definition of `size` / `size` 的定义

English:
definition size
  signature: (s : Ordset α)
  body: s.1.size

中文:
定义 size
  签名: (s : Ordset α)
  定义体: s.1.size
-/
def size (s : Ordset α) : Nat :=
  s.1.size

/--
Definition of `singleton` / `singleton` 的定义

English:
definition singleton
  signature: (a : α)
  body: ⟨singleton a, valid_singleton⟩

中文:
定义 singleton
  签名: (a : α)
  定义体: ⟨singleton a, valid_singleton⟩
-/
protected def singleton (a : α) : Ordset α :=
  ⟨singleton a, valid_singleton⟩

/--
Instance `instEmptyCollection` / 实例 `instEmptyCollection`

English:
instance instEmptyCollection
  signature: : EmptyCollection (Ordset α)
  body: ⟨nil⟩

中文:
实例 instEmptyCollection
  签名: : EmptyCollection (Ordset α)
  定义体: ⟨nil⟩
-/
instance instEmptyCollection : EmptyCollection (Ordset α) :=
  ⟨nil⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (Ordset α)
  body: ⟨nil⟩

中文:
实例 instInhabited
  签名: : Inhabited (Ordset α)
  定义体: ⟨nil⟩
-/
instance instInhabited : Inhabited (Ordset α) :=
  ⟨nil⟩

/--
Instance `instSingleton` / 实例 `instSingleton`

English:
instance instSingleton
  signature: : Singleton α (Ordset α)
  body: ⟨Ordset.singleton⟩

中文:
实例 instSingleton
  签名: : Singleton α (Ordset α)
  定义体: ⟨Ordset.singleton⟩

Depends on / 依赖: Ordset, Ordset.singleton, singleton
-/
instance instSingleton : Singleton α (Ordset α) :=
  ⟨Ordset.singleton⟩

/--
Definition of `Empty` / `Empty` 的定义

English:
definition Empty
  signature: (s : Ordset α)
  body: s = ∅

中文:
定义 Empty
  签名: (s : Ordset α)
  定义体: s = ∅
-/
def Empty (s : Ordset α) : Prop :=
  s = ∅

/--
theorem `empty_iff` / 定理 `empty_iff`

English:
theorem empty_iff
  given: {s : Ordset α}
  statement: s = ∅ ↔ s.1.empty
  proof: ⟨fun h => by cases h; exact rfl,
    fun h => by cases s with | mk s_val _ => cases s_val <;> [rfl; cases h]⟩

中文:
定理 empty_iff
  条件: {s : Ordset α}
  结论: s = ∅ ↔ s.1.empty
  证明: ⟨fun h => by cases h; exact rfl,
    fun h => by cases s with | mk s_val _ => cases s_val <;> [rfl; cases h]⟩

Depends on / 依赖: s_val
-/
theorem empty_iff {s : Ordset α} : s = ∅ ↔ s.1.empty :=
  ⟨fun h => by cases h; exact rfl,
    fun h => by cases s with | mk s_val _ => cases s_val <;> [rfl; cases h]⟩

/--
Instance `Empty.instDecidablePred` / 实例 `Empty.instDecidablePred`

English:
instance Empty.instDecidablePred
  signature: : DecidablePred (@Empty α _)
  body: fun _ => decidable_of_iff' _ empty_iff

中文:
实例 Empty.instDecidablePred
  签名: : DecidablePred (@Empty α _)
  定义体: fun _ => decidable_of_iff' _ empty_iff

Depends on / 依赖: decidable_of_iff, empty_iff
-/
instance Empty.instDecidablePred : DecidablePred (@Empty α _) :=
  fun _ => decidable_of_iff' _ empty_iff

/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) (s : Ordset α)
  body: ⟨Ordnode.insert x s.1, insert.valid _ s.2⟩

中文:
定义 insert
  签名: [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) (s : Ordset α)
  定义体: ⟨Ordnode.insert x s.1, insert.valid _ s.2⟩
-/
protected def insert [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) (s : Ordset α) :
    Ordset α :=
  ⟨Ordnode.insert x s.1, insert.valid _ s.2⟩

/--
Instance `instInsert` / 实例 `instInsert`

English:
instance instInsert
  signature: [@Std.Total α (· <= ·)] [DecidableLE α]
  body: ⟨Ordset.insert⟩

中文:
实例 instInsert
  签名: [@Std.Total α (· <= ·)] [DecidableLE α]
  定义体: ⟨Ordset.insert⟩

Depends on / 依赖: Ordset, Ordset.insert, insert
-/
instance instInsert [@Std.Total α (· <= ·)] [DecidableLE α] : Insert α (Ordset α) :=
  ⟨Ordset.insert⟩

/-- O(log n). Insert an element into the set, preserving balance and the BST property.
  If an equivalent element is already in the set, the set is returned as is. -/
nonrec def insert' [@Std.Total α (· <= ·)] [DecidableLE α] (x : α) (s : Ordset α) :
    Ordset α :=
  ⟨insert' x s.1, insert'.valid _ s.2⟩

section

variable [DecidableLE α]

/--
Definition of `mem` / `mem` 的定义

English:
definition mem
  signature: (x : α) (s : Ordset α)
  body: x in s.val

中文:
定义 mem
  签名: (x : α) (s : Ordset α)
  定义体: x in s.val

Depends on / 依赖: s.val
-/
def mem (x : α) (s : Ordset α) : Bool :=
  x in s.val

/--
Definition of `find` / `find` 的定义

English:
definition find
  signature: (x : α) (s : Ordset α)
  body: Ordnode.find x s.val

中文:
定义 find
  签名: (x : α) (s : Ordset α)
  定义体: Ordnode.find x s.val

Depends on / 依赖: Ordnode, Ordnode.find, s.val
-/
def find (x : α) (s : Ordset α) : Option α :=
  Ordnode.find x s.val

/--
Instance `instMembership` / 实例 `instMembership`

English:
instance instMembership
  signature: : Membership α (Ordset α)
  body: ⟨fun s x => mem x s⟩

中文:
实例 instMembership
  签名: : Membership α (Ordset α)
  定义体: ⟨fun s x => mem x s⟩
-/
instance instMembership : Membership α (Ordset α) :=
  ⟨fun s x => mem x s⟩

/--
Instance `mem.decidable` / 实例 `mem.decidable`

English:
instance mem.decidable
  signature: (x : α) (s : Ordset α)
  body: instDecidableEqBool _ _

中文:
实例 mem.decidable
  签名: (x : α) (s : Ordset α)
  定义体: instDecidableEqBool _ _
-/
instance mem.decidable (x : α) (s : Ordset α) : Decidable (x in s) :=
  instDecidableEqBool _ _

/--
theorem `pos_size_of_mem` / 定理 `pos_size_of_mem`

English:
theorem pos_size_of_mem
  given: {x : α} {t : Ordset α} (h_mem : x in t)
  statement: 0 < size t
  proof: by
  simp only [Membership.mem, mem, Bool.decide_eq_true] at h_mem
  apply Ordnode.pos_size_of_mem t.property.sz h_mem

中文:
定理 pos_size_of_mem
  条件: {x : α} {t : Ordset α} (h_mem : x in t)
  结论: 0 < size t
  证明: by
  simp only [Membership.mem, mem, Bool.decide_eq_true] at h_mem
  apply Ordnode.pos_size_of_mem t.property.sz h_mem

Depends on / 依赖: Bool.decide_eq_true, Membership, Membership.mem, Ordnode, Ordnode.pos_size_of_mem, decide_eq_true, h_mem, pos_size_of_mem, property, t.property.sz
-/
theorem pos_size_of_mem {x : α} {t : Ordset α} (h_mem : x in t) : 0 < size t := by
  simp only [Membership.mem, mem, Bool.decide_eq_true] at h_mem
  apply Ordnode.pos_size_of_mem t.property.sz h_mem

end

/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: [DecidableLE α] (x : α) (s : Ordset α)
  body: ⟨Ordnode.erase x s.val, Ordnode.erase.valid x s.property⟩

中文:
定义 erase
  签名: [DecidableLE α] (x : α) (s : Ordset α)
  定义体: ⟨Ordnode.erase x s.val, Ordnode.erase.valid x s.property⟩

Depends on / 依赖: Ordnode, Ordnode.erase, Ordnode.erase.valid, property, s.property, s.val
-/
def erase [DecidableLE α] (x : α) (s : Ordset α) : Ordset α :=
  ⟨Ordnode.erase x s.val, Ordnode.erase.valid x s.property⟩

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {β} [Preorder β] (f : α -> β) (f_strict_mono : StrictMono f) (s : Ordset α)
  body: ⟨Ordnode.map f s.val, Ordnode.map.valid f_strict_mono s.property⟩

中文:
定义 map
  签名: {β} [Preorder β] (f : α -> β) (f_strict_mono : StrictMono f) (s : Ordset α)
  定义体: ⟨Ordnode.map f s.val, Ordnode.map.valid f_strict_mono s.property⟩

Depends on / 依赖: Ordnode, Ordnode.map, Ordnode.map.valid, f_strict_mono, property, s.property, s.val
-/
def map {β} [Preorder β] (f : α -> β) (f_strict_mono : StrictMono f) (s : Ordset α) : Ordset β :=
  ⟨Ordnode.map f s.val, Ordnode.map.valid f_strict_mono s.property⟩

end Ordset
