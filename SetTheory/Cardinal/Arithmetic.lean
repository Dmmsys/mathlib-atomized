/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.SetTheory.Cardinal.Aleph

/-!
# Cardinal arithmetic

Arithmetic operations on cardinals are defined in `Mathlib/SetTheory/Cardinal/Order.lean`. However,
proving the important theorem `c * c = c` for infinite cardinals and its corollaries requires the
use of ordinal numbers. This is done within this file.

## Main statements

* `Cardinal.mul_eq_max` and `Cardinal.add_eq_max` state that the product (resp. sum) of two infinite
  cardinals is just their maximum. Several variations around this fact are also given.
* `Cardinal.mk_list_eq_mk`: when `α` is infinite, `α` and `List α` have the same cardinality.

## Tags

cardinal arithmetic (for infinite cardinals)
-/

public section

assert_not_exists Module Finsupp Ordinal.log

noncomputable section

open Function Set Cardinal Equiv Order Ordinal

universe u v w

namespace Cardinal

/-! ### Properties of `mul` -/
section mul

set_option backward.isDefEq.respectTransparency false in
/-- If `α` is an infinite type, then `α × α` and `α` have the same cardinality. -/
/-
**Cardinal.mul_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c = c
参数：hc : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedLT.induction`：induction {motive : α -> Prop} (a : α) (ind : f
orall x, (forall y, y < x -> motive y) -> motive x) : motive a
· 使用定理 `Cardinal.instWellFoundedLT`：WellFoundedLT Cardinal.{u}
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Cardinal.exists_ord_eq_type_lt`：exists_ord_eq_type_lt (α) : exists (_ : 
LinearOrder α) (_ : WellFoundedLT α), ord #α = typeLT α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.isSuccPrelimit_type_lt_iff`：isSuccPrelimit_type_lt_iff [LinearOr
der α] [WellFoundedLT α] : IsSuccPrelimit (typeLT α) ↔ NoMaxOrder α
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
· 使用定理 `Cardinal.isSuccLimit_ord`：isSuccLimit_ord {c} (hc : ℵ₀ <= c) : IsSuccLim
it (ord c)
· 使用定理 `RelEmbedding.isWellOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s) [IsWellOrder β s], IsWellOrder α r
· 使用定理 `Prod.Lex.instWellFoundedLTLex`：∀ {α : Type u_1} {β : Type u_2} [inst : L
T α] [inst_1 : LT β] [WellFoundedLT α] [WellFoundedLT β],   WellFoundedLT (Lex (
α × β))
· 使用定理 `Ordinal.card_le_card`：card_le_card {o₁ o₂ : Ordinal} : o₁ <= o₂ -> card 
o₁ <= card o₂
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `Ordinal.typein_surj`：typein_surj (r : α -> α -> Prop) [IsWellOrder α r] 
{o} (h : o < type r) : o in Set.range (typein r)
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Cardinal.lt_ord`：lt_ord {c o} : o < ord c ↔ o.card < c
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Function.Embedding.cardinal_le`：∀ {α β : Type u} (f : α ↪ β), Cardinal.m
k α ≤ Cardinal.mk β
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Order.Preimage.eq_1`：∀ {α : Type u_2} {β : Type u_3} (f : α → β) (s : β 
→ β → Prop) (x y : α), (f ⁻¹'o s) x y = s (f x) (f y)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_setProd`：∀ {α β : Type u} (s : Set α) (t : Set β), Cardinal.
mk ↑(s ×ˢ t) = Cardinal.mk ↑s * Cardinal.mk ↑t
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `α` is an infinite type, then `α × α` and `α` have the same cardinality.
-/
theorem mul_eq_self {c : Cardinal} (hc : ℵ₀ ≤ c) : c * c = c := by
  -- The only nontrivial part is `c * c ≤ c`. We prove it inductively.
  induction c using WellFoundedLT.induction with | ind c IH
  refine le_antisymm ?_ (by simpa using mul_le_mul_right (one_le_aleph0.trans hc) c)
  -- Consider the minimal well-order on `α` (a type with cardinality `c`).
  induction c using Cardinal.inductionOn with | mk α
  obtain ⟨_, _, hα⟩ := exists_ord_eq_type_lt α
  have : NoMaxOrder α := by
    rw [← isSuccPrelimit_type_lt_iff, ← hα]
    exact (isSuccLimit_ord hc).isSuccPrelimit
  -- Define an order `s` on `α × α`, comparing first by `max x.1 x.2`, then by `toLex (x.1, x.2)`.
  let g : α × α → α := uncurry max
  let f : α × α ↪ α ×ₗ (α ×ₗ α) := ⟨fun p ↦ toLex (g p, toLex p), fun p q ↦ congrArg Prod.snd⟩
  let s := f ⁻¹'o (· < ·)
  have : IsWellOrder _ s := (RelEmbedding.preimage ..).isWellOrder
  -- Every initial segment of `s` is contained in `β × β` for some `β` of cardinality `< c`.
  -- By the inductive hypothesis, this means `#(β × β) < c`. Thus, `α × α` must have
  -- cardinality `≤ c`.
  refine @card_le_card (type s) (typeLT α) <| le_of_forall_lt fun o h ↦ ?_
  obtain ⟨p, rfl⟩ := typein_surj s h
  obtain ⟨q, hq'⟩ := exists_gt (g p)
  rw [← hα, lt_ord]
  apply lt_of_le_of_lt (b := #(Iio q) * #(Iio q))
  · apply (Set.embeddingOfSubset { x | s x p } ..).cardinal_le.trans_eq (mk_setProd ..)
    simp [s, f, Prod.Lex.lt_iff, subset_def]
    grind
  rcases lt_or_ge #(Iio q) ℵ₀ with hq | hq
  · exact (mul_lt_aleph0 hq hq).trans_le hc
  · have := mk_Iio_lt q hα
    rwa [IH _ this hq]

/-- If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximum
of the cardinalities of `α` and `β`. -/
/-
**Cardinal.mul_eq_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) (hb : ℵ₀ <= b) : a * b = max a 
b
参数：ha : ℵ₀ <= a；hb : ℵ₀ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `Cardinal.one_le_aleph0`：one_le_aleph0 : 1 <= ℵ₀
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a

--- 原说明 ---
If `α` and `β` are infinite types, then the cardinality of `α × β` is the maximu
m
of the cardinalities of `α` and `β`.
-/
theorem mul_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : ℵ₀ ≤ b) : a * b = max a b :=
  le_antisymm
      (mul_eq_self (ha.trans (le_max_left a b)) ▸
        mul_le_mul' (le_max_left _ _) (le_max_right _ _)) <|
    max_le (by simpa only [mul_one] using mul_le_mul_right (one_le_aleph0.trans hb) a)
      (by simpa only [one_mul] using mul_le_mul_left (one_le_aleph0.trans ha) b)

@[simp]
/-
**Cardinal.mul_mk_eq_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_mk_eq_max {α β : Type u} [Infinite α] [Infinite β] : #α * #β = max #α 
#β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mul_eq_max`：mul_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) (hb : ℵ₀
 <= b) : a * b = max a b
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem mul_mk_eq_max {α β : Type u} [Infinite α] [Infinite β] : #α * #β = max #α #β :=
  mul_eq_max (aleph0_le_mk α) (aleph0_le_mk β)

@[simp]
/-
**Cardinal.aleph_mul_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_mul_aleph (o₁ o₂ : Ordinal) : ℵ_ o₁ * ℵ_ o₂ = ℵ_ (max o₁ o₂)
参数：o₁ o₂ : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mul_eq_max`：mul_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) (hb : ℵ₀
 <= b) : a * b = max a b
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
· 使用定理 `Cardinal.aleph_max`：aleph_max (o₁ o₂ : Ordinal) : ℵ_ (max o₁ o₂) = max (
ℵ_ o₁) (ℵ_ o₂)
-/
theorem aleph_mul_aleph (o₁ o₂ : Ordinal) : ℵ_ o₁ * ℵ_ o₂ = ℵ_ (max o₁ o₂) := by
  rw [Cardinal.mul_eq_max (aleph0_le_aleph o₁) (aleph0_le_aleph o₂), aleph_max]

@[simp]
/-
**Cardinal.aleph0_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ <= a) : ℵ₀ * a = a
参数：ha : ℵ₀ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mul_eq_max`：mul_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) (hb : ℵ₀
 <= b) : a * b = max a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
-/
theorem aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : ℵ₀ * a = a :=
  (mul_eq_max le_rfl ha).trans (max_eq_right ha)

@[simp]
/-
**Cardinal.mul_aleph0_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ <= a) : a * ℵ₀ = a
参数：ha : ℵ₀ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mul_eq_max`：mul_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) (hb : ℵ₀
 <= b) : a * b = max a b
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a * ℵ₀ = a :=
  (mul_eq_max ha le_rfl).trans (max_eq_left ha)
/-
**Cardinal.aleph0_mul_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_mul_mk_eq {α : Type*} [Infinite α] : ℵ₀ * #α = #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph0_mul_eq`：aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ <= a) : ℵ₀
 * a = a
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem aleph0_mul_mk_eq {α : Type*} [Infinite α] : ℵ₀ * #α = #α :=
  aleph0_mul_eq (aleph0_le_mk α)
/-
**Cardinal.mk_mul_aleph0_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_mul_aleph0_eq {α : Type*} [Infinite α] : #α * ℵ₀ = #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mul_aleph0_eq`：mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ <= a) : a 
* ℵ₀ = a
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem mk_mul_aleph0_eq {α : Type*} [Infinite α] : #α * ℵ₀ = #α :=
  mul_aleph0_eq (aleph0_le_mk α)
/-
**Cardinal.aleph0_mul_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_mul_aleph (o : Ordinal) : ℵ₀ * ℵ_ o = ℵ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.aleph0_mul_eq`：aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ <= a) : ℵ₀
 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aleph0_mul_aleph (o : Ordinal) : ℵ₀ * ℵ_ o = ℵ_ o := by
  simp
/-
**Cardinal.aleph_mul_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_mul_aleph0 (o : Ordinal) : ℵ_ o * ℵ₀ = ℵ_ o
参数：o : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mul_aleph0_eq`：mul_aleph0_eq {a : Cardinal} (ha : ℵ₀ <= a) : a 
* ℵ₀ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem aleph_mul_aleph0 (o : Ordinal) : ℵ_ o * ℵ₀ = ℵ_ o := by
  simp
/-
**Cardinal.mul_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_le_of_le {a b c : Cardinal} (hc : ℵ₀ <= c) (ha : a <= c) (hb : b <= c)
 : a * b <= c
参数：hc : ℵ₀ <= c；ha : a <= c；hb : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
-/
theorem mul_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (ha : a ≤ c) (hb : b ≤ c) : a * b ≤ c := by
  rw [← Cardinal.mul_eq_self hc]
  exact mul_le_mul' ha hb
/-
**Cardinal.mul_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (ha : a < c) (hb : b < c) :
 a * b < c
参数：hc : ℵ₀ <= c；ha : a < c；hb : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.mul_lt_aleph0`：mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb
 : b < ℵ₀) : a * b < ℵ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
-/
theorem mul_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (ha : a < c) (hb : b < c) : a * b < c := by
  apply (mul_le_mul' (le_max_left a b) (le_max_right a b)).trans_lt
  obtain h | h := lt_or_ge (max a b) ℵ₀
  · exact (mul_lt_aleph0 h h).trans_le hc
  · rw [mul_eq_self h]
    exact max_lt ha hb
/-
**Cardinal.mul_le_max_of_aleph0_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_le_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ <= a) : a * b <= max
 a b
参数：h : ℵ₀ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem mul_le_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) : a * b ≤ max a b := by
  convert! mul_le_mul' (le_max_left a b) (le_max_right a b) using 1
  rw [mul_eq_self]
  exact h.trans (le_max_left a b)
/-
**Cardinal.mul_eq_max_of_aleph0_le_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_eq_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) 
: a * b = max a b
参数：h : ℵ₀ <= a；h' : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Cardinal.mul_eq_max`：mul_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) (hb : ℵ₀
 <= b) : a * b = max a b
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Cardinal.mul_le_max_of_aleph0_le_left`：mul_le_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) : a * b <= max a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_le_mul_right`：mul_le_mul_right [MulLeftMono α] {b c : α} (bc : b <= 
c) (a : α) : a * b <= a * c
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
-/
theorem mul_eq_max_of_aleph0_le_left {a b : Cardinal} (h : ℵ₀ ≤ a) (h' : b ≠ 0) :
    a * b = max a b := by
  rcases le_or_gt ℵ₀ b with hb | hb
  · exact mul_eq_max h hb
  refine (mul_le_max_of_aleph0_le_left h).antisymm ?_
  have : b ≤ a := hb.le.trans h
  rw [max_eq_left this]
  convert! mul_le_mul_right (Cardinal.one_le_iff_ne_zero.mpr h') a
  rw [mul_one]
/-
**Cardinal.mul_le_max_of_aleph0_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_le_max_of_aleph0_le_right {a b : Cardinal} (h : ℵ₀ <= b) : a * b <= ma
x a b
参数：h : ℵ₀ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Cardinal.mul_le_max_of_aleph0_le_left`：mul_le_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) : a * b <= max a b
-/
theorem mul_le_max_of_aleph0_le_right {a b : Cardinal} (h : ℵ₀ ≤ b) : a * b ≤ max a b := by
  simpa only [mul_comm b, max_comm b] using mul_le_max_of_aleph0_le_left h
/-
**Cardinal.mul_eq_max_of_aleph0_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_eq_max_of_aleph0_le_right {a b : Cardinal} (h' : a != 0) (h : ℵ₀ <= b)
 : a * b = max a b
参数：h' : a != 0；h : ℵ₀ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_left`：mul_eq_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) : a * b = max a b
-/
theorem mul_eq_max_of_aleph0_le_right {a b : Cardinal} (h' : a ≠ 0) (h : ℵ₀ ≤ b) :
    a * b = max a b := by
  rw [mul_comm, max_comm]
  exact mul_eq_max_of_aleph0_le_left h h'
/-
**Cardinal.mul_eq_max'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_eq_max' {a b : Cardinal} (h : ℵ₀ <= a * b) : a * b = max a b
参数：h : ℵ₀ <= a * b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.aleph0_le_mul_iff`：aleph0_le_mul_iff {a b : Cardinal} : ℵ₀ <= a
 * b ↔ a != 0 ∧ b != 0 ∧ (ℵ₀ <= a ∨ ℵ₀ <= b)
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_left`：mul_eq_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) : a * b = max a b
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_right`：mul_eq_max_of_aleph0_le_right {a
 b : Cardinal} (h' : a != 0) (h : ℵ₀ <= b) : a * b = max a b
-/
theorem mul_eq_max' {a b : Cardinal} (h : ℵ₀ ≤ a * b) : a * b = max a b := by
  rcases aleph0_le_mul_iff.mp h with ⟨ha, hb, ha' | hb'⟩
  · exact mul_eq_max_of_aleph0_le_left ha' hb
  · exact mul_eq_max_of_aleph0_le_right ha hb'
/-
**Cardinal.mul_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_le_max (a b : Cardinal) : a * b <= max (max a b) ℵ₀
参数：a b : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_left`：mul_eq_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) : a * b = max a b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.mul_lt_aleph0`：mul_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb
 : b < ℵ₀) : a * b < ℵ₀
-/
theorem mul_le_max (a b : Cardinal) : a * b ≤ max (max a b) ℵ₀ := by
  rcases eq_or_ne a 0 with (rfl | ha0); · simp
  rcases eq_or_ne b 0 with (rfl | hb0); · simp
  rcases le_or_gt ℵ₀ a with ha | ha
  · rw [mul_eq_max_of_aleph0_le_left ha hb0]
    exact le_max_left _ _
  · rcases le_or_gt ℵ₀ b with hb | hb
    · rw [mul_comm, mul_eq_max_of_aleph0_le_left hb ha0, max_comm]
      exact le_max_left _ _
    · exact le_max_of_le_right (mul_lt_aleph0 ha hb).le
/-
**Cardinal.mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : b <= a) (hb' : b != 0) :
 a * b = a
参数：ha : ℵ₀ <= a；hb : b <= a；hb' : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_left`：mul_eq_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) : a * b = max a b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem mul_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) (hb' : b ≠ 0) : a * b = a := by
  rw [mul_eq_max_of_aleph0_le_left ha hb', max_eq_left hb]
/-
**Cardinal.mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_eq_right {a b : Cardinal} (hb : ℵ₀ <= b) (ha : a <= b) (ha' : a != 0) 
: a * b = b
参数：hb : ℵ₀ <= b；ha : a <= b；ha' : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.mul_eq_left`：mul_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) (hb' : b != 0) : a * b = a
-/
theorem mul_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) (ha' : a ≠ 0) : a * b = b := by
  rw [mul_comm, mul_eq_left hb ha ha']
/-
**Cardinal.le_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_mul_left {a b : Cardinal} (h : b != 0) : a <= b * a
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
-/
theorem le_mul_left {a b : Cardinal} (h : b ≠ 0) : a ≤ b * a := by
  convert! mul_le_mul_left (Cardinal.one_le_iff_ne_zero.mpr h) a
  rw [one_mul]
/-
**Cardinal.le_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：le_mul_right {a b : Cardinal} (h : b != 0) : a <= a * b
参数：h : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.le_mul_left`：le_mul_left {a b : Cardinal} (h : b != 0) : a <= b
 * a
-/
theorem le_mul_right {a b : Cardinal} (h : b ≠ 0) : a ≤ a * b := by
  rw [mul_comm]
  exact le_mul_left h
/-
**Cardinal.mul_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_eq_left_iff {a b : Cardinal} : a * b = a ↔ max ℵ₀ b <= a ∧ b != 0 ∨ b 
= 1 ∨ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LE.le.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Cardinal.aleph0_pos`：aleph0_pos : 0 < ℵ₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `and_assoc`：∀ {a b c : Prop}, (a ∧ b) ∧ c ↔ a ∧ b ∧ c
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.le_mul_left`：le_mul_left {a b : Cardinal} (h : b != 0) : a <= b
 * a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `Cardinal.mul_lt_aleph0_iff`：mul_lt_aleph0_iff {a b : Cardinal} : a * b <
 ℵ₀ ↔ a = 0 ∨ b = 0 ∨ a < ℵ₀ ∧ b < ℵ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Nat.mul_lt_mul_left`：∀ {a b c : ℕ}, 0 < a → (a * b < a * c ↔ b < c)
· 使用定理 `Nat.lt_of_succ_le`：∀ {n m : ℕ}, n.succ ≤ m → n < m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_left`：mul_eq_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) : a * b = max a b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 31 条，此处仅展示前 30 条）
-/
theorem mul_eq_left_iff {a b : Cardinal} : a * b = a ↔ max ℵ₀ b ≤ a ∧ b ≠ 0 ∨ b = 1 ∨ a = 0 := by
  rw [max_le_iff]
  refine ⟨fun h => ?_, ?_⟩
  · rcases le_or_gt ℵ₀ a with ha | ha
    · have : a ≠ 0 := by
        rintro rfl
        exact ha.not_gt aleph0_pos
      left
      rw [and_assoc]
      use ha
      constructor
      · rw [← not_lt]
        exact fun hb => ne_of_gt (hb.trans_le (le_mul_left this)) h
      · rintro rfl
        apply this
        rw [mul_zero] at h
        exact h.symm
    right
    by_cases h2a : a = 0
    · exact Or.inr h2a
    have hb : b ≠ 0 := by
      rintro rfl
      apply h2a
      rw [mul_zero] at h
      exact h.symm
    left
    rw [← h, mul_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    rcases ha with (rfl | rfl | ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩)
    · contradiction
    · contradiction
    rw [← Ne] at h2a
    rw [← Cardinal.one_le_iff_ne_zero] at h2a hb
    norm_cast at h2a hb h ⊢
    apply le_antisymm _ hb
    rw [← not_lt]
    apply fun h2b => ne_of_gt _ h
    conv_rhs => left; rw [← mul_one n]
    rw [Nat.mul_lt_mul_left]
    · exact id
    apply Nat.lt_of_succ_le h2a
  · rintro (⟨⟨ha, hab⟩, hb⟩ | rfl | rfl)
    · rw [mul_eq_max_of_aleph0_le_left ha hb, max_eq_left hab]
    all_goals simp

end mul

/-! ### Properties of `add` -/
section add

/-- If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality. -/
/-
**Cardinal.add_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_eq_self {c : Cardinal} (h : ℵ₀ <= c) : c + c = c
参数：h : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a

--- 原说明 ---
If `α` is an infinite type, then `α ⊕ α` and `α` have the same cardinality.
-/
theorem add_eq_self {c : Cardinal} (h : ℵ₀ ≤ c) : c + c = c :=
  le_antisymm
    (by simpa [two_mul, mul_eq_self h] using mul_le_mul_left (natCast_le_aleph0 (n := 2).trans h) c)
    (self_le_add_left c c)

/-- If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`. -/
/-
**Cardinal.add_eq_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b = max a b
参数：ha : ℵ₀ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Cardinal.add_eq_self`：add_eq_self {c : Cardinal} (h : ℵ₀ <= c) : c + c =
 c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a

--- 原说明 ---
If `α` is an infinite type, then the cardinality of `α ⊕ β` is the maximum
of the cardinalities of `α` and `β`.
-/
theorem add_eq_max {a b : Cardinal} (ha : ℵ₀ ≤ a) : a + b = max a b :=
  le_antisymm
      (add_eq_self (ha.trans (le_max_left a b)) ▸
        add_le_add (le_max_left _ _) (le_max_right _ _)) <|
    max_le (self_le_add_right _ _) (self_le_add_left _ _)
/-
**Cardinal.add_eq_max'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_eq_max' {a b : Cardinal} (ha : ℵ₀ <= b) : a + b = max a b
参数：ha : ℵ₀ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
-/
theorem add_eq_max' {a b : Cardinal} (ha : ℵ₀ ≤ b) : a + b = max a b := by
  rw [add_comm, max_comm, add_eq_max ha]

@[simp]
/-
**Cardinal.add_mk_eq_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_mk_eq_max {α β : Type u} [Infinite α] : #α + #β = max #α #β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem add_mk_eq_max {α β : Type u} [Infinite α] : #α + #β = max #α #β :=
  add_eq_max (aleph0_le_mk α)

@[simp]
/-
**Cardinal.add_mk_eq_max'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_mk_eq_max' {α β : Type u} [Infinite β] : #α + #β = max #α #β
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_eq_max'`：add_eq_max' {a b : Cardinal} (ha : ℵ₀ <= b) : a + 
b = max a b
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem add_mk_eq_max' {α β : Type u} [Infinite β] : #α + #β = max #α #β :=
  add_eq_max' (aleph0_le_mk β)
/-
**Cardinal.add_mk_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_mk_eq_self {α : Type*} [Infinite α] : #α + #α = #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.add_mk_eq_max`：add_mk_eq_max {α β : Type u} [Infinite α] : #α +
 #β = max #α #β
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_mk_eq_self {α : Type*} [Infinite α] : #α + #α = #α := by
  simp
/-
**Cardinal.add_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_le_max (a b : Cardinal) : a + b <= max (max a b) ℵ₀
参数：a b : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.add_lt_aleph0`：add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb
 : b < ℵ₀) : a + b < ℵ₀
-/
theorem add_le_max (a b : Cardinal) : a + b ≤ max (max a b) ℵ₀ := by
  rcases le_or_gt ℵ₀ a with ha | ha
  · rw [add_eq_max ha]
    exact le_max_left _ _
  · rcases le_or_gt ℵ₀ b with hb | hb
    · rw [add_comm, add_eq_max hb, max_comm]
      exact le_max_left _ _
    · exact le_max_of_le_right (add_lt_aleph0 ha hb).le
/-
**Cardinal.add_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_le_of_le {a b c : Cardinal} (hc : ℵ₀ <= c) (h1 : a <= c) (h2 : b <= c)
 : a + b <= c
参数：hc : ℵ₀ <= c；h1 : a <= c；h2 : b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Cardinal.add_eq_self`：add_eq_self {c : Cardinal} (h : ℵ₀ <= c) : c + c =
 c
-/
theorem add_le_of_le {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a ≤ c) (h2 : b ≤ c) : a + b ≤ c :=
  (add_le_add h1 h2).trans <| le_of_eq <| add_eq_self hc
/-
**Cardinal.add_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h1 : a < c) (h2 : b < c) :
 a + b < c
参数：hc : ℵ₀ <= c；h1 : a < c；h2 : b < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.add_lt_aleph0`：add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb
 : b < ℵ₀) : a + b < ℵ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.add_eq_self`：add_eq_self {c : Cardinal} (h : ℵ₀ <= c) : c + c =
 c
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
-/
theorem add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ ≤ c) (h1 : a < c) (h2 : b < c) : a + b < c :=
  (add_le_add (le_max_left a b) (le_max_right a b)).trans_lt <|
    (lt_or_ge (max a b) ℵ₀).elim (fun h => (add_lt_aleph0 h h).trans_le hc) fun h => by
      rw [add_eq_self h]; exact max_lt h1 h2
/-
**Cardinal.add_one_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_one_lt_of_lt {a b : Cardinal} (hb : ℵ₀ <= b) (ha : a < b) : a + 1 < b
参数：hb : ℵ₀ <= b；ha : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_lt_of_lt`：add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
1 : a < c) (h2 : b < c) : a + b < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
theorem add_one_lt_of_lt {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a < b) : a + 1 < b :=
  add_lt_of_lt hb ha (one_lt_aleph0.trans_le hb)
/-
**Cardinal.one_add_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_add_lt_of_lt {a b : Cardinal} (hb : ℵ₀ <= b) (ha : a < b) : 1 + a < b
参数：hb : ℵ₀ <= b；ha : a < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_lt_of_lt`：add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
1 : a < c) (h2 : b < c) : a + b < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
theorem one_add_lt_of_lt {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a < b) : 1 + a < b :=
  add_lt_of_lt hb (one_lt_aleph0.trans_le hb) ha
/-
**Cardinal.eq_of_add_eq_of_aleph0_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：eq_of_add_eq_of_aleph0_le {a b c : Cardinal} (h : a + b = c) (ha : a < c) 
(hc : ℵ₀ <= c) : b = c
参数：h : a + b = c；ha : a < c；hc : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Cardinal.add_lt_of_lt`：add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
1 : a < c) (h2 : b < c) : a + b < c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem eq_of_add_eq_of_aleph0_le {a b c : Cardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ ≤ c) :
    b = c := by
  apply le_antisymm
  · rw [← h]
    apply self_le_add_left
  rw [← not_lt]; intro hb
  have : a + b < c := add_lt_of_lt hc ha hb
  simp [h] at this
/-
**Cardinal.add_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : b <= a) : a + b = a
参数：ha : ℵ₀ <= a；hb : b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem add_eq_left {a b : Cardinal} (ha : ℵ₀ ≤ a) (hb : b ≤ a) : a + b = a := by
  rw [add_eq_max ha, max_eq_left hb]
/-
**Cardinal.add_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_eq_right {a b : Cardinal} (hb : ℵ₀ <= b) (ha : a <= b) : a + b = b
参数：hb : ℵ₀ <= b；ha : a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.add_eq_left`：add_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) : a + b = a
-/
theorem add_eq_right {a b : Cardinal} (hb : ℵ₀ ≤ b) (ha : a ≤ b) : a + b = b := by
  rw [add_comm, add_eq_left hb ha]
/-
**Cardinal.add_eq_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_eq_left_iff {a b : Cardinal} : a + b = a ↔ max ℵ₀ b <= a ∨ b = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `Cardinal.add_lt_aleph0_iff`：add_lt_aleph0_iff {a b : Cardinal} : a + b <
 ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem add_eq_left_iff {a b : Cardinal} : a + b = a ↔ max ℵ₀ b ≤ a ∨ b = 0 := by
  rw [max_le_iff]
  refine ⟨fun h => ?_, ?_⟩
  · rcases le_or_gt ℵ₀ a with ha | ha
    · left
      use ha
      rw [← not_lt]
      apply fun hb => ne_of_gt _ h
      intro hb
      exact hb.trans_le (self_le_add_left b a)
    right
    rw [← h, add_lt_aleph0_iff, lt_aleph0, lt_aleph0] at ha
    rcases ha with ⟨⟨n, rfl⟩, ⟨m, rfl⟩⟩
    norm_cast at h ⊢
    rw [← add_right_inj, h, add_zero]
  · rintro (⟨h1, h2⟩ | h3)
    · rw [add_eq_max h1, max_eq_left h2]
    · rw [h3, add_zero]
/-
**Cardinal.add_eq_right_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_eq_right_iff {a b : Cardinal} : a + b = b ↔ max ℵ₀ a <= b ∨ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.add_eq_left_iff`：add_eq_left_iff {a b : Cardinal} : a + b = a ↔
 max ℵ₀ b <= a ∨ b = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem add_eq_right_iff {a b : Cardinal} : a + b = b ↔ max ℵ₀ a ≤ b ∨ a = 0 := by
  rw [add_comm, add_eq_left_iff]
/-
**Cardinal.add_nat_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_nat_eq {a : Cardinal} (n : Nat) (ha : ℵ₀ <= a) : a + n = a
参数：n : Nat；ha : ℵ₀ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_eq_left`：add_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) : a + b = a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
-/
theorem add_nat_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : a + n = a :=
  add_eq_left ha (natCast_le_aleph0.trans ha)
/-
**Cardinal.nat_add_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_add_eq {a : Cardinal} (n : Nat) (ha : ℵ₀ <= a) : n + a = a
参数：n : Nat；ha : ℵ₀ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.add_nat_eq`：add_nat_eq {a : Cardinal} (n : Nat) (ha : ℵ₀ <= a) 
: a + n = a
-/
theorem nat_add_eq {a : Cardinal} (n : ℕ) (ha : ℵ₀ ≤ a) : n + a = a := by
  rw [add_comm, add_nat_eq n ha]
/-
**Cardinal.add_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_one_eq {a : Cardinal} (ha : ℵ₀ <= a) : a + 1 = a
参数：ha : ℵ₀ <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_one_of_aleph0_le`：add_one_of_aleph0_le {c} (h : ℵ₀ <= c) : 
c + 1 = c
-/
theorem add_one_eq {a : Cardinal} (ha : ℵ₀ ≤ a) : a + 1 = a :=
  add_one_of_aleph0_le ha
/-
**Cardinal.mk_add_one_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_add_one_eq {α : Type*} [Infinite α] : #α + 1 = #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_one_eq`：add_one_eq {a : Cardinal} (ha : ℵ₀ <= a) : a + 1 = 
a
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem mk_add_one_eq {α : Type*} [Infinite α] : #α + 1 = #α :=
  add_one_eq (aleph0_le_mk α)
/-
**Cardinal.mk_Iic_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Iic_lt {α : Type*} [LinearOrder α] [WellFoundedLT α] (i : α) (h : ord #
α = typeLT α) (hα : ℵ₀ <= #α) : #(Iic i) < #α
参数：i : α；h : ord #α = typeLT α；hα : ℵ₀ <= #α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Iio_insert`：Iio_insert : insert a (Iio a) = Iic a
· 使用定理 `Cardinal.mk_insert`：mk_insert {α : Type u} {s : Set α} {a : α} (h : a ∉ 
s) : #(insert a s : Set α) = #s + 1
· 使用定理 `Set.self_notMem_Iio`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∉ S
et.Iio a
· 使用定理 `Cardinal.add_one_lt_of_lt`：add_one_lt_of_lt {a b : Cardinal} (hb : ℵ₀ <=
 b) (ha : a < b) : a + 1 < b
· 使用定理 `Cardinal.mk_Iio_lt`：mk_Iio_lt [LinearOrder α] [WellFoundedLT α] (i : α) 
(h : ord #α = typeLT α) : #(Iio i) < #α
-/
theorem mk_Iic_lt {α : Type*} [LinearOrder α] [WellFoundedLT α] (i : α)
    (h : ord #α = typeLT α) (hα : ℵ₀ ≤ #α) : #(Iic i) < #α := by
  rw [← Iio_insert, mk_insert self_notMem_Iio]
  exact add_one_lt_of_lt hα (mk_Iio_lt i h)
/-
**Cardinal.mk_Ici_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_Ici_lt {α : Type*} [LinearOrder α] [WellFoundedGT α] (i : α) (h : ord #
α = typeLT αᵒᵈ) (hα : ℵ₀ <= #α) : #(Ici i) < #α
参数：i : α；h : ord #α = typeLT αᵒᵈ；hα : ℵ₀ <= #α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
· 使用定理 `Cardinal.mk_Iic_lt`：mk_Iic_lt {α : Type*} [LinearOrder α] [WellFoundedLT
 α] (i : α) (h : ord #α = typeLT α) (hα : ℵ₀ <= #α) : #(Iic i) < #α
-/
theorem mk_Ici_lt {α : Type*} [LinearOrder α] [WellFoundedGT α] (i : α)
    (h : ord #α = typeLT αᵒᵈ) (hα : ℵ₀ ≤ #α) : #(Ici i) < #α :=
  mk_Iic_lt (OrderDual.toDual i) h hα
/-
**Cardinal.eq_of_add_eq_add_left** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {a b c : Cardinal.{u_1}}, a + b = a + c → a < Cardinal.aleph0 → b = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.eq_of_add_eq_of_aleph0_le`：eq_of_add_eq_of_aleph0_le {a b c : C
ardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ <= c) : b = c
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Cardinal.add_eq_right`：add_eq_right {a b : Cardinal} (hb : ℵ₀ <= b) (ha 
: a <= b) : a + b = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `Cardinal.add_lt_aleph0`：add_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀) (hb
 : b < ℵ₀) : a + b < ℵ₀
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
protected theorem eq_of_add_eq_add_left {a b c : Cardinal} (h : a + b = a + c) (ha : a < ℵ₀) :
    b = c := by
  rcases le_or_gt ℵ₀ b with hb | hb
  · have : a < b := ha.trans_le hb
    rw [add_eq_right hb this.le, eq_comm] at h
    rw [eq_of_add_eq_of_aleph0_le h this hb]
  · have hc : c < ℵ₀ := by
      rw [← not_le]
      intro hc
      apply lt_irrefl ℵ₀
      apply (hc.trans (self_le_add_left _ a)).trans_lt
      rw [← h]
      apply add_lt_aleph0 ha hb
    rw [lt_aleph0] at *
    rcases ha with ⟨n, rfl⟩
    rcases hb with ⟨m, rfl⟩
    rcases hc with ⟨k, rfl⟩
    norm_cast at h ⊢
    apply add_left_cancel h
/-
**Cardinal.eq_of_add_eq_add_right** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {a b c : Cardinal.{u_1}}, a + b = c + b → b < Cardinal.aleph0 → a = c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.eq_of_add_eq_add_left`：∀ {a b c : Cardinal.{u_1}}, a + b = a + 
c → a < Cardinal.aleph0 → b = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
protected theorem eq_of_add_eq_add_right {a b c : Cardinal} (h : a + b = c + b) (hb : b < ℵ₀) :
    a = c := by
  rw [add_comm a b, add_comm c b] at h
  exact Cardinal.eq_of_add_eq_add_left h hb

end add

/-- Infinite types permit a relation where fewer elements than its cardinality
are missed along all verticals and fewer elements than its cardinality are hit
along all horizontals. -/
/-
**Cardinal.exists_rel_mk_fibers_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：exists_rel_mk_fibers_lt (α : Type*) [Infinite α] : exists r : α -> α -> Pr
op, (forall x, #{y // ¬ r x y} < #α) ∧ (forall y, #{x // r x y} < #α)
参数：α : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `Cardinal.exists_ord_eq_type_lt`：exists_ord_eq_type_lt (α) : exists (_ : 
LinearOrder α) (_ : WellFoundedLT α), ord #α = typeLT α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mk_Iic_lt`：mk_Iic_lt {α : Type*} [LinearOrder α] [WellFoundedLT
 α] (i : α) (h : ord #α = typeLT α) (hα : ℵ₀ <= #α) : #(Iic i) < #α
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `Cardinal.mk_Iio_lt`：mk_Iio_lt [LinearOrder α] [WellFoundedLT α] (i : α) 
(h : ord #α = typeLT α) : #(Iio i) < #α

--- 原说明 ---
Infinite types permit a relation where fewer elements than its cardinality
are missed along all verticals and fewer elements than its cardinality are hit
along all horizontals.
-/
theorem exists_rel_mk_fibers_lt (α : Type*) [Infinite α] :
    ∃ r : α → α → Prop, (∀ x, #{y // ¬ r x y} < #α) ∧ (∀ y, #{x // r x y} < #α) := by
  obtain ⟨α, _, hα⟩ := exists_ord_eq_type_lt α
  refine ⟨LT.lt, fun x ↦ ?_, fun y ↦ mk_Iio_lt _ hα⟩
  simpa using! mk_Iic_lt _ hα (aleph0_le_mk _)

/-! ### Properties of `ciSup` -/
section ciSup

variable {ι : Type u} {ι' : Type w} (f : ι → Cardinal.{v})

section add

variable [Nonempty ι] [Nonempty ι']

/-
**Cardinal.ciSup_add** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {ι : Type u} (f : ι → Cardinal.{v}) [Nonempty ι],   BddAbove (Set.range 
f) → ∀ (c : Cardinal.{v}), (⨆ i, f i) + c = ⨆ i, f i + c
参数：f : ι → Cardinal.{v}；Set.range f；c : Cardinal.{v}；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用引理 `exists_eq_ciSup_of_not_isSuccLimit`：exists_eq_ciSup_of_not_isSuccLimit (
hbdd : BddAbove (range f)) (hf : ¬ IsSuccLimit (⨆ i, f i)) : exists i, f i = ⨆ i
, f i
· 使用定理 `Cardinal.not_isSuccLimit_of_lt_aleph0`：not_isSuccLimit_of_lt_aleph0 {c :
 Cardinal} (h : c < ℵ₀) : ¬ IsSuccLimit c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `ciSup_mono`：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : fora
ll x, f x <= g x) : iSup f <= iSup g
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `self_le_add_left`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canonic
allyOrderedAdd α] (a b : α), a ≤ b + a
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
-/
protected theorem ciSup_add (hf : BddAbove (range f)) (c : Cardinal.{v}) :
    (⨆ i, f i) + c = ⨆ i, f i + c := by
  have (i : ι) : f i + c ≤ (⨆ i, f i) + c := by grw [le_ciSup hf i]
  refine le_antisymm ?_ (ciSup_le' this)
  have bdd : BddAbove (range (f · + c)) := ⟨_, forall_mem_range.mpr this⟩
  obtain hs | hs := lt_or_ge (⨆ i, f i) ℵ₀
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_not_isSuccLimit hf (not_isSuccLimit_of_lt_aleph0 hs)
    exact hi ▸ le_ciSup bdd i
  rw [add_eq_max hs, max_le_iff]
  exact ⟨ciSup_mono bdd fun i ↦ self_le_add_right _ c,
    (self_le_add_left _ _).trans (le_ciSup bdd <| Classical.arbitrary ι)⟩
/-
**Cardinal.add_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {ι : Type u} (f : ι → Cardinal.{v}) [Nonempty ι],   BddAbove (Set.range 
f) → ∀ (c : Cardinal.{v}), c + ⨆ i, f i = ⨆ i, c + f i
参数：f : ι → Cardinal.{v}；Set.range f；c : Cardinal.{v}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Cardinal.ciSup_add`：∀ {ι : Type u} (f : ι → Cardinal.{v}) [Nonempty ι], 
  BddAbove (Set.range f) → ∀ (c : Cardinal.{v}), (⨆ i, f i) + c = ⨆ i, f i + c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem add_ciSup (hf : BddAbove (range f)) (c : Cardinal.{v}) :
    c + (⨆ i, f i) = ⨆ i, c + f i := by
  rw [add_comm, Cardinal.ciSup_add f hf]; simp_rw [add_comm]
/-
**Cardinal.ciSup_add_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {ι : Type u} {ι' : Type w} (f : ι → Cardinal.{v}) [Nonempty ι] [Nonempty
 ι'],   BddAbove (Set.range f) →     ∀ (g : ι' → Cardinal.{v}), BddAbove (Set.ra
nge g) → (⨆ i, f i) + ⨆ j, g j = ⨆ i, ⨆ j, f i + g j
参数：f : ι → Cardinal.{v}；Set.range f；g : ι' → Cardinal.{v}；Set.range g；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ciSup_add`：∀ {ι : Type u} (f : ι → Cardinal.{v}) [Nonempty ι], 
  BddAbove (Set.range f) → ∀ (c : Cardinal.{v}), (⨆ i, f i) + c = ⨆ i, f i + c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.add_ciSup`：∀ {ι : Type u} (f : ι → Cardinal.{v}) [Nonempty ι], 
  BddAbove (Set.range f) → ∀ (c : Cardinal.{v}), c + ⨆ i, f i = ⨆ i, c + f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem ciSup_add_ciSup (hf : BddAbove (range f)) (g : ι' → Cardinal.{v})
    (hg : BddAbove (range g)) :
    (⨆ i, f i) + (⨆ j, g j) = ⨆ (i) (j), f i + g j := by
  simp_rw [Cardinal.ciSup_add f hf, Cardinal.add_ciSup g hg]

end add

/-
**Cardinal.ciSup_mul** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {ι : Type u} (f : ι → Cardinal.{v}) (c : Cardinal.{v}), (⨆ i, f i) * c =
 ⨆ i, f i * c
参数：f : ι → Cardinal.{v}；c : Cardinal.{v}；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ciSup_of_empty`：ciSup_of_empty [IsEmpty ι] (f : ι -> α) : ⨆ i, f i = ⊥
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ciSup_const`：ciSup_const [hι : Nonempty ι] {a : α} : ⨆ _ : ι, a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `le_ciSup`：le_ciSup {f : ι -> α} (H : BddAbove (range f)) (c : ι) : f c <
= iSup f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用引理 `exists_eq_ciSup_of_not_isSuccLimit`：exists_eq_ciSup_of_not_isSuccLimit (
hbdd : BddAbove (range f)) (hf : ¬ IsSuccLimit (⨆ i, f i)) : exists i, f i = ⨆ i
, f i
· 使用定理 `Cardinal.not_isSuccLimit_of_lt_aleph0`：not_isSuccLimit_of_lt_aleph0 {c :
 Cardinal} (h : c < ℵ₀) : ¬ IsSuccLimit c
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_left`：mul_eq_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) : a * b = max a b
· 使用定理 `max_le_iff`：∀ {α : Type u} [inst : LinearOrder α] {a b c : α}, max a b ≤
 c ↔ a ≤ c ∧ b ≤ c
· 使用定理 `exists_lt_of_lt_ciSup'`：exists_lt_of_lt_ciSup' {f : ι -> α} {a : α} (h :
 a < ⨆ i, f i) : exists i, a < f i
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
（共 45 条，此处仅展示前 30 条）
-/
protected theorem ciSup_mul (c : Cardinal.{v}) : (⨆ i, f i) * c = ⨆ i, f i * c := by
  cases isEmpty_or_nonempty ι; · simp
  obtain rfl | h0 := eq_or_ne c 0; · simp
  by_cases hf : BddAbove (range f); swap
  · have hfc : ¬ BddAbove (range (f · * c)) := fun bdd ↦ hf
      ⟨⨆ i, f i * c, forall_mem_range.mpr fun i ↦ (le_mul_right h0).trans (le_ciSup bdd i)⟩
    simp [iSup, csSup_of_not_bddAbove, hf, hfc]
  have (i : ι) : f i * c ≤ (⨆ i, f i) * c := by grw [← le_ciSup hf i]
  refine le_antisymm ?_ (ciSup_le' this)
  have bdd : BddAbove (range (f · * c)) := ⟨_, forall_mem_range.mpr this⟩
  obtain hs | hs := lt_or_ge (⨆ i, f i) ℵ₀
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_not_isSuccLimit hf (not_isSuccLimit_of_lt_aleph0 hs)
    exact hi ▸ le_ciSup bdd i
  rw [mul_eq_max_of_aleph0_le_left hs h0, max_le_iff]
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup' (one_lt_aleph0.trans_le hs)
  exact ⟨ciSup_mono bdd fun i ↦ le_mul_right h0,
    (le_mul_left (zero_lt_one.trans hi).ne').trans (le_ciSup bdd i)⟩
/-
**Cardinal.mul_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {ι : Type u} (f : ι → Cardinal.{v}) (c : Cardinal.{v}), c * ⨆ i, f i = ⨆
 i, c * f i
参数：f : ι → Cardinal.{v}；c : Cardinal.{v}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Cardinal.ciSup_mul`：∀ {ι : Type u} (f : ι → Cardinal.{v}) (c : Cardinal.
{v}), (⨆ i, f i) * c = ⨆ i, f i * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem mul_ciSup (c : Cardinal.{v}) : c * (⨆ i, f i) = ⨆ i, c * f i := by
  rw [mul_comm, Cardinal.ciSup_mul f]; simp_rw [mul_comm]
/-
**Cardinal.ciSup_mul_ciSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {ι : Type u} {ι' : Type w} (f : ι → Cardinal.{v}) (g : ι' → Cardinal.{v}
), (⨆ i, f i) * ⨆ j, g j = ⨆ i, ⨆ j, f i * g j
参数：f : ι → Cardinal.{v}；g : ι' → Cardinal.{v}；⨆ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.ciSup_mul`：∀ {ι : Type u} (f : ι → Cardinal.{v}) (c : Cardinal.
{v}), (⨆ i, f i) * c = ⨆ i, f i * c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.mul_ciSup`：∀ {ι : Type u} (f : ι → Cardinal.{v}) (c : Cardinal.
{v}), c * ⨆ i, f i = ⨆ i, c * f i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem ciSup_mul_ciSup (g : ι' → Cardinal.{v}) :
    (⨆ i, f i) * (⨆ j, g j) = ⨆ (i) (j), f i * g j := by
  simp_rw [Cardinal.ciSup_mul f, Cardinal.mul_ciSup g]
/-
**Cardinal.sum_eq_lift_iSup_of_lift_mk_le_lift_iSup** 是 Mathlib 中的一个定理，位于命名空间 `C
ardinal`。
形式化陈述：sum_eq_lift_iSup_of_lift_mk_le_lift_iSup [Small.{v} ι] {f : ι -> Cardinal.
{v}} (hι : ℵ₀ <= #ι) (h : lift.{v} #ι <= lift.{u} (⨆ i, f i)) : sum f = lift (⨆ 
i, f i)
参数：hι : ℵ₀ <= #ι；h : lift.{v} #ι <= lift.{u} (⨆ i, f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≤ b → a = b
· 使用定理 `Cardinal.lift_iSup_le_sum`：lift_iSup_le_sum {ι : Type u} [Small.{v} ι] (
f : ι -> Cardinal.{v}) : lift (⨆ i, f i) <= sum f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mul_eq_max`：mul_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) (hb : ℵ₀
 <= b) : a * b = max a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_le_lift`：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.
{v} c ↔ ℵ₀ <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.lift_iSup`：lift_iSup {ι : Type v} {f : ι -> Cardinal.{w}} (hf :
 BddAbove (range f)) : lift.{u} (iSup f) = ⨆ i, lift.{u} (f i)
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `Cardinal.sum_le_lift_mk_mul_iSup_lift`：sum_le_lift_mk_mul_iSup_lift {ι :
 Type u} (f : ι -> Cardinal.{v}) : sum f <= lift #ι * ⨆ i, lift (f i)
-/
theorem sum_eq_lift_iSup_of_lift_mk_le_lift_iSup [Small.{v} ι] {f : ι → Cardinal.{v}} (hι : ℵ₀ ≤ #ι)
    (h : lift.{v} #ι ≤ lift.{u} (⨆ i, f i)) : sum f = lift (⨆ i, f i) := by
  rw [lift_iSup bddAbove_of_small] at h
  apply (lift_iSup_le_sum f).antisymm'
  convert! sum_le_lift_mk_mul_iSup_lift f
  rw [mul_eq_max (aleph0_le_lift.mpr hι) ((aleph0_le_lift.mpr hι).trans h), max_eq_right h,
    lift_iSup bddAbove_of_small]
/-
**Cardinal.sum_eq_iSup_of_lift_mk_le_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_eq_iSup_of_lift_mk_le_iSup {f : ι -> Cardinal.{max u v}} (hι : ℵ₀ <= #
ι) (h : lift.{v} #ι <= ⨆ i, f i) : sum f = ⨆ i, f i
参数：hι : ℵ₀ <= #ι；h : lift.{v} #ι <= ⨆ i, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.sum_eq_lift_iSup_of_lift_mk_le_lift_iSup`：sum_eq_lift_iSup_of_l
ift_mk_le_lift_iSup [Small.{v} ι] {f : ι -> Cardinal.{v}} (hι : ℵ₀ <= #ι) (h : l
ift.{v} #ι <= lift.{u} (⨆ i, f i)) : su…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
-/
theorem sum_eq_iSup_of_lift_mk_le_iSup {f : ι → Cardinal.{max u v}} (hι : ℵ₀ ≤ #ι)
    (h : lift.{v} #ι ≤ ⨆ i, f i) : sum f = ⨆ i, f i := by
  rw [← lift_id'.{u, v} (iSup _)]
  apply sum_eq_lift_iSup_of_lift_mk_le_lift_iSup hι
  rwa [lift_umax, lift_id'.{u, v}]
/-
**Cardinal.sum_eq_iSup_of_mk_le_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_eq_iSup_of_mk_le_iSup {f : ι -> Cardinal.{u}} (hι : ℵ₀ <= #ι) (h : #ι 
<= iSup f) : sum f = ⨆ i, f i
参数：hι : ℵ₀ <= #ι；h : #ι <= iSup f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.sum_eq_iSup_of_lift_mk_le_iSup`：sum_eq_iSup_of_lift_mk_le_iSup 
{f : ι -> Cardinal.{max u v}} (hι : ℵ₀ <= #ι) (h : lift.{v} #ι <= ⨆ i, f i) : su
m f = ⨆ i, f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem sum_eq_iSup_of_mk_le_iSup {f : ι → Cardinal.{u}} (hι : ℵ₀ ≤ #ι) (h : #ι ≤ iSup f) :
    sum f = ⨆ i, f i :=
  sum_eq_iSup_of_lift_mk_le_iSup hι ((lift_id #ι).symm ▸ h)

end ciSup

/-! ### Properties of `aleph` -/
section aleph

@[simp]
/-
**Cardinal.aleph_add_aleph** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph_add_aleph (o₁ o₂ : Ordinal) : ℵ_ o₁ + ℵ_ o₂ = ℵ_ (max o₁ o₂)
参数：o₁ o₂ : Ordinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `Cardinal.aleph0_le_aleph`：aleph0_le_aleph (o : Ordinal) : ℵ₀ <= ℵ_ o
· 使用定理 `Cardinal.aleph_max`：aleph_max (o₁ o₂ : Ordinal) : ℵ_ (max o₁ o₂) = max (
ℵ_ o₁) (ℵ_ o₂)
-/
theorem aleph_add_aleph (o₁ o₂ : Ordinal) : ℵ_ o₁ + ℵ_ o₂ = ℵ_ (max o₁ o₂) := by
  rw [Cardinal.add_eq_max (aleph0_le_aleph o₁), aleph_max]
/-
**Cardinal.add_right_inj_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_right_inj_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < aleph0) : α + γ = 
β + γ ↔ α = β
参数：γ₀ : γ < aleph0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.eq_of_add_eq_add_right`：∀ {a b c : Cardinal.{u_1}}, a + b = c +
 b → b < Cardinal.aleph0 → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem add_right_inj_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β :=
  ⟨fun h => Cardinal.eq_of_add_eq_add_right h γ₀, fun h => congr_arg (· + γ) h⟩

@[simp]
/-
**Cardinal.add_nat_inj** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_nat_inj {α β : Cardinal} (n : Nat) : α + n = β + n ↔ α = β
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_right_inj_of_lt_aleph0`：add_right_inj_of_lt_aleph0 {α β γ :
 Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem add_nat_inj {α β : Cardinal} (n : ℕ) : α + n = β + n ↔ α = β :=
  add_right_inj_of_lt_aleph0 natCast_lt_aleph0

@[simp]
/-
**Cardinal.add_one_inj** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_one_inj {α β : Cardinal} : α + 1 = β + 1 ↔ α = β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_right_inj_of_lt_aleph0`：add_right_inj_of_lt_aleph0 {α β γ :
 Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
theorem add_one_inj {α β : Cardinal} : α + 1 = β + 1 ↔ α = β :=
  add_right_inj_of_lt_aleph0 one_lt_aleph0
/-
**Cardinal.add_le_add_iff_of_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_le_add_iff_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < ℵ₀) : α + γ <= β 
+ γ ↔ α <= β
参数：γ₀ : γ < ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.add_right_inj_of_lt_aleph0`：add_right_inj_of_lt_aleph0 {α β γ :
 Cardinal} (γ₀ : γ < aleph0) : α + γ = β + γ ↔ α = β
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem add_le_add_iff_of_lt_aleph0 {α β γ : Cardinal} (γ₀ : γ < ℵ₀) :
    α + γ ≤ β + γ ↔ α ≤ β := by
  refine ⟨fun h => ?_, fun h => by gcongr⟩
  contrapose h
  rw [not_le, lt_iff_le_and_ne, Ne] at h ⊢
  exact ⟨by grw [h.1], mt (add_right_inj_of_lt_aleph0 γ₀).1 h.2⟩

@[simp]
/-
**Cardinal.add_nat_le_add_nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_nat_le_add_nat_iff {α β : Cardinal} (n : Nat) : α + n <= β + n ↔ α <= 
β
参数：n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_le_add_iff_of_lt_aleph0`：add_le_add_iff_of_lt_aleph0 {α β γ
 : Cardinal} (γ₀ : γ < ℵ₀) : α + γ <= β + γ ↔ α <= β
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem add_nat_le_add_nat_iff {α β : Cardinal} (n : ℕ) : α + n ≤ β + n ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 natCast_lt_aleph0

@[simp]
/-
**Cardinal.add_one_le_add_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_one_le_add_one_iff {α β : Cardinal} : α + 1 <= β + 1 ↔ α <= β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.add_le_add_iff_of_lt_aleph0`：add_le_add_iff_of_lt_aleph0 {α β γ
 : Cardinal} (γ₀ : γ < ℵ₀) : α + γ <= β + γ ↔ α <= β
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
theorem add_one_le_add_one_iff {α β : Cardinal} : α + 1 ≤ β + 1 ↔ α ≤ β :=
  add_le_add_iff_of_lt_aleph0 one_lt_aleph0
/-
**Cardinal.add_lt_add_iff_of_right_lt_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal
`。
形式化陈述：add_lt_add_iff_of_right_lt_aleph0 {a b c : Cardinal} (hc : c < ℵ₀) : a + c
 < b + c ↔ a < b
参数：hc : c < ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.add_le_add_iff_of_lt_aleph0`：add_le_add_iff_of_lt_aleph0 {α β γ
 : Cardinal} (γ₀ : γ < ℵ₀) : α + γ <= β + γ ↔ α <= β
-/
lemma add_lt_add_iff_of_right_lt_aleph0 {a b c : Cardinal} (hc : c < ℵ₀) :
    a + c < b + c ↔ a < b := by
  constructor <;> contrapose! <;> simp [add_le_add_iff_of_lt_aleph0 hc]
/-
**Cardinal.add_lt_add_iff_of_left_lt_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`
。
形式化陈述：add_lt_add_iff_of_left_lt_aleph0 {a b c : Cardinal} (hc : c < ℵ₀) : c + a 
< c + b ↔ a < b
参数：hc : c < ℵ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Cardinal.add_lt_add_iff_of_right_lt_aleph0`：add_lt_add_iff_of_right_lt_a
leph0 {a b c : Cardinal} (hc : c < ℵ₀) : a + c < b + c ↔ a < b
-/
lemma add_lt_add_iff_of_left_lt_aleph0 {a b c : Cardinal} (hc : c < ℵ₀) :
    c + a < c + b ↔ a < b := by
  simpa [add_comm] using add_lt_add_iff_of_right_lt_aleph0 (a := a) (b := b) hc
/-
**Cardinal.add_lt_add** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {κ₁ κ₂ μ₁ μ₂ : Cardinal.{u_1}}, κ₁ < κ₂ → μ₁ < μ₂ → κ₁ + μ₁ < κ₂ + μ₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Cardinal.add_lt_of_lt`：add_lt_of_lt {a b c : Cardinal} (hc : ℵ₀ <= c) (h
1 : a < c) (h2 : b < c) : a + b < c
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.add_lt_aleph0_iff`：add_lt_aleph0_iff {a b : Cardinal} : a + b <
 ℵ₀ ↔ a < ℵ₀ ∧ b < ℵ₀
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.add_le_add_iff_of_lt_aleph0`：add_le_add_iff_of_lt_aleph0 {α β γ
 : Cardinal} (γ₀ : γ < ℵ₀) : α + γ <= β + γ ↔ α <= β
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Cardinal.add_lt_add_iff_of_right_lt_aleph0`：add_lt_add_iff_of_right_lt_a
leph0 {a b c : Cardinal} (hc : c < ℵ₀) : a + c < b + c ↔ a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected lemma add_lt_add {κ₁ κ₂ μ₁ μ₂ : Cardinal}
    (hκ : κ₁ < κ₂) (hμ : μ₁ < μ₂) : κ₁ + μ₁ < κ₂ + μ₂ := by
  rcases le_or_gt ℵ₀ (κ₂ + μ₂) with hinf | hfin
  · refine add_lt_of_lt hinf ?_ ?_ <;> apply lt_of_lt_of_le <;> solve | assumption | simp
  · have hfin_ : κ₂ < ℵ₀ ∧ μ₂ < ℵ₀ := add_lt_aleph0_iff.1 hfin
    apply lt_of_le_of_lt
    · exact (add_le_add_iff_of_lt_aleph0 (hμ.trans hfin_.right)).mpr hκ.le
    · simpa [add_comm] using (add_lt_add_iff_of_right_lt_aleph0 hfin_.left).mpr hμ

end aleph

section mul_strictMono

variable {n : ℕ} {a b : Cardinal}

/-
**Cardinal.natCast_mul_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：natCast_mul_strictMono {n : Nat} (hn : n != 0) : StrictMono fun a : Cardin
al => n * a
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natCast_mul_strictMono {n : ℕ} (hn : n ≠ 0) : StrictMono fun a : Cardinal ↦ n * a := by
  match n, hn with
  | 1, _ => simpa using! strictMono_id
  | (n + 1) + 1, hneq1 =>
    intro a μ hlt
    push_cast
    conv_lhs => rw [add_mul, one_mul]
    conv_rhs => rw [add_mul, one_mul]
    refine Cardinal.add_lt_add ?_ hlt
    simpa using! (natCast_mul_strictMono (Nat.succ_ne_zero n) hlt)
/-
**Cardinal.mul_natCast_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mul_natCast_strictMono (hn : n != 0) : StrictMono fun a : Cardinal => a * 
n
参数：hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Cardinal.natCast_mul_strictMono`：natCast_mul_strictMono {n : Nat} (hn : 
n != 0) : StrictMono fun a : Cardinal => n * a
-/
lemma mul_natCast_strictMono (hn : n ≠ 0) : StrictMono fun a : Cardinal ↦ a * n :=
  fun _ _ hlt => by simpa [mul_comm] using natCast_mul_strictMono hn hlt

@[simp]
/-
**Cardinal.natCast_mul_inj** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：natCast_mul_inj (hn : n != 0) : n * a = n * b ↔ a = b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Cardinal.natCast_mul_strictMono`：natCast_mul_strictMono {n : Nat} (hn : 
n != 0) : StrictMono fun a : Cardinal => n * a
-/
lemma natCast_mul_inj (hn : n ≠ 0) : n * a = n * b ↔ a = b :=
  (natCast_mul_strictMono hn).injective.eq_iff

@[simp]
/-
**Cardinal.mul_natCast_inj** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mul_natCast_inj (hn : n != 0) : a * n = b * n ↔ a = b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `Cardinal.mul_natCast_strictMono`：mul_natCast_strictMono (hn : n != 0) : 
StrictMono fun a : Cardinal => a * n
-/
lemma mul_natCast_inj (hn : n ≠ 0) : a * n = b * n ↔ a = b :=
  (mul_natCast_strictMono hn).injective.eq_iff

@[simp]
/-
**Cardinal.natCast_mul_le_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：natCast_mul_le_natCast_mul (hn : n != 0) : n * a <= n * b ↔ a <= b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Cardinal.natCast_mul_strictMono`：natCast_mul_strictMono {n : Nat} (hn : 
n != 0) : StrictMono fun a : Cardinal => n * a
-/
lemma natCast_mul_le_natCast_mul (hn : n ≠ 0) : n * a ≤ n * b ↔ a ≤ b :=
  (natCast_mul_strictMono hn).le_iff_le

@[simp]
/-
**Cardinal.mul_natCast_le_mul_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mul_natCast_le_mul_natCast (hn : n != 0) : a * n <= b * n ↔ a <= b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Cardinal.mul_natCast_strictMono`：mul_natCast_strictMono (hn : n != 0) : 
StrictMono fun a : Cardinal => a * n
-/
lemma mul_natCast_le_mul_natCast (hn : n ≠ 0) : a * n ≤ b * n ↔ a ≤ b :=
  (mul_natCast_strictMono hn).le_iff_le

@[simp]
/-
**Cardinal.natCast_mul_lt_natCast_mul** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：natCast_mul_lt_natCast_mul (hn : n != 0) : n * a < n * b ↔ a < b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Cardinal.natCast_mul_strictMono`：natCast_mul_strictMono {n : Nat} (hn : 
n != 0) : StrictMono fun a : Cardinal => n * a
-/
lemma natCast_mul_lt_natCast_mul (hn : n ≠ 0) : n * a < n * b ↔ a < b :=
  (natCast_mul_strictMono hn).lt_iff_lt

@[simp]
/-
**Cardinal.mul_natCast_lt_mul_natCast** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：mul_natCast_lt_mul_natCast (hn : n != 0) : a * n < b * n ↔ a < b
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Cardinal.mul_natCast_strictMono`：mul_natCast_strictMono (hn : n != 0) : 
StrictMono fun a : Cardinal => a * n
-/
lemma mul_natCast_lt_mul_natCast (hn : n ≠ 0) : a * n < b * n ↔ a < b :=
  (mul_natCast_strictMono hn).lt_iff_lt

end mul_strictMono

/-! ### Properties about `power` -/
section power

set_option backward.isDefEq.respectTransparency false in
/-
**Cardinal.pow_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ <= κ) (H2 : μ < ℵ₀) : κ ^ μ <= κ
参数：H1 : ℵ₀ <= κ；H2 : μ < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0`：lt_aleph0 {c : Cardinal} : c < ℵ₀ ↔ exists n : Nat, 
c = n
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Cardinal.power_zero`：power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Cardinal.power_add`：power_add (a b c : Cardinal) : a ^ (b + c) = a ^ b *
 a ^ c
· 使用定理 `Cardinal.power_one`：power_one (a : Cardinal.{u}) : a ^ (1 : Cardinal) = 
a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `CanonicallyOrderedAdd.toMulLeftMono`：∀ {R : Type u} [inst : NonUnitalNon
AssocSemiring R] [inst_1 : LE R] [CanonicallyOrderedAdd R], MulLeftMono R
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : μ < ℵ₀) : κ ^ μ ≤ κ :=
  let ⟨n, H3⟩ := lt_aleph0.1 H2
  H3.symm ▸
    Quotient.inductionOn κ
      (fun α H1 =>
        Nat.recOn n
          (by grw [Nat.cast_zero, power_zero, one_lt_aleph0, H1])
          fun n ih => by grw [Nat.cast_succ, power_add, power_one, ih, mul_eq_self H1])
      H1
/-
**Cardinal.pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：pow_eq {κ μ : Cardinal.{u}} (H1 : ℵ₀ <= κ) (H2 : 1 <= μ) (H3 : μ < ℵ₀) : κ
 ^ μ = κ
参数：H1 : ℵ₀ <= κ；H2 : 1 <= μ；H3 : μ < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Cardinal.pow_le`：pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ <= κ) (H2 : μ < ℵ₀
) : κ ^ μ <= κ
· 使用定理 `Cardinal.self_le_power`：self_le_power (a : Cardinal) {b : Cardinal} (hb 
: 1 <= b) : a <= a ^ b
-/
theorem pow_eq {κ μ : Cardinal.{u}} (H1 : ℵ₀ ≤ κ) (H2 : 1 ≤ μ) (H3 : μ < ℵ₀) : κ ^ μ = κ :=
  (pow_le H1 H3).antisymm <| self_le_power κ H2
/-
**Cardinal.power_self_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_self_eq {c : Cardinal} (h : ℵ₀ <= c) : c ^ c = 2 ^ c
参数：h : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.power_le_power_right`：power_le_power_right {a b c : Cardinal} :
 a <= b -> a ^ c <= b ^ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.cantor`：cantor (a : Cardinal.{u}) : a < 2 ^ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.power_mul`：power_mul {a b c : Cardinal} : a ^ (b * c) = (a ^ b)
 ^ c
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
-/
theorem power_self_eq {c : Cardinal} (h : ℵ₀ ≤ c) : c ^ c = 2 ^ c := by
  apply ((power_le_power_right <| (cantor c).le).trans _).antisymm
  · exact power_le_power_right (natCast_le_aleph0.trans h)
  · rw [← power_mul, mul_eq_self h]
/-
**Cardinal.prod_eq_two_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι -> Cardinal.{v}} (h₁ : 
forall i, 2 <= c i) (h₂ : forall i, lift.{u} (c i) <= lift.{v} #ι) : prod c = 2 
^ lift.{v} #ι
参数：h₁ : forall i, 2 <= c i；h₂ : forall i, lift.{u} (c i) <= lift.{v} #ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_prod`：lift_prod {ι : Type u} (c : ι -> Cardinal.{v}) : lif
t.{w} (prod c) = prod fun i => lift.{w} (c i)
· 使用定理 `Cardinal.lift_two_power`：lift_two_power (a : Cardinal) : lift.{v} (2 ^ a
) = 2 ^ lift.{v} a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Cardinal.prod_le_prod`：prod_le_prod {ι} (f g : ι -> Cardinal) (H : foral
l i, f i <= g i) : prod f <= prod g
· 使用定理 `Cardinal.prod_const`：prod_const (ι : Type u) (a : Cardinal.{v}) : (prod 
fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_power`：lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) 
= lift.{v} a ^ lift.{v} b
· 使用定理 `Cardinal.power_self_eq`：power_self_eq {c : Cardinal} (h : ℵ₀ <= c) : c ^
 c = 2 ^ c
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.prod_const'`：prod_const' (ι : Type u) (a : Cardinal.{u}) : (pro
d fun _ : ι => a) = a ^ #ι
· 使用定理 `Cardinal.lift_two`：lift_two : lift.{u, v} 2 = 2
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem prod_eq_two_power {ι : Type u} [Infinite ι] {c : ι → Cardinal.{v}} (h₁ : ∀ i, 2 ≤ c i)
    (h₂ : ∀ i, lift.{u} (c i) ≤ lift.{v} #ι) : prod c = 2 ^ lift.{v} #ι := by
  rw [← lift_id'.{u, v} (prod.{u, v} c), lift_prod, ← lift_two_power]
  apply le_antisymm
  · refine (prod_le_prod _ _ h₂).trans_eq ?_
    rw [prod_const, lift_lift, ← lift_power, power_self_eq (aleph0_le_mk ι), lift_umax.{u, v}]
  · rw [← prod_const', lift_prod]
    refine prod_le_prod _ _ fun i => ?_
    rw [lift_two, ← lift_two.{u, v}, lift_le]
    exact h₁ i
/-
**Cardinal.power_eq_two_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ℵ₀ <= c₁) (h₂ : 2 <= c₂) (h₂' 
: c₂ <= c₁) : c₂ ^ c₁ = 2 ^ c₁
参数：h₁ : ℵ₀ <= c₁；h₂ : 2 <= c₂；h₂' : c₂ <= c₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.power_le_power_right`：power_le_power_right {a b c : Cardinal} :
 a <= b -> a ^ c <= b ^ c
· 使用定理 `Cardinal.power_self_eq`：power_self_eq {c : Cardinal} (h : ℵ₀ <= c) : c ^
 c = 2 ^ c
-/
theorem power_eq_two_power {c₁ c₂ : Cardinal} (h₁ : ℵ₀ ≤ c₁) (h₂ : 2 ≤ c₂) (h₂' : c₂ ≤ c₁) :
    c₂ ^ c₁ = 2 ^ c₁ :=
  le_antisymm (power_self_eq h₁ ▸ power_le_power_right h₂') (power_le_power_right h₂)
/-
**Cardinal.nat_power_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nat_power_eq {c : Cardinal.{u}} (h : ℵ₀ <= c) {n : Nat} (hn : 2 <= n) : (n
 : Cardinal.{u}) ^ c = 2 ^ c
参数：h : ℵ₀ <= c；hn : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.power_eq_two_power`：power_eq_two_power {c₁ c₂ : Cardinal} (h₁ :
 ℵ₀ <= c₁) (h₂ : 2 <= c₂) (h₂' : c₂ <= c₁) : c₂ ^ c₁ = 2 ^ c₁
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.natCast_le_aleph0`：∀ {n : ℕ}, ↑n ≤ Cardinal.aleph0
-/
theorem nat_power_eq {c : Cardinal.{u}} (h : ℵ₀ ≤ c) {n : ℕ} (hn : 2 ≤ n) :
    (n : Cardinal.{u}) ^ c = 2 ^ c :=
  power_eq_two_power h (by assumption_mod_cast) (natCast_le_aleph0.trans h)
/-
**Cardinal.power_nat_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_nat_le {c : Cardinal.{u}} {n : Nat} (h : ℵ₀ <= c) : c ^ n <= c
参数：h : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.pow_le`：pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ <= κ) (H2 : μ < ℵ₀
) : κ ^ μ <= κ
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem power_nat_le {c : Cardinal.{u}} {n : ℕ} (h : ℵ₀ ≤ c) : c ^ n ≤ c :=
  pow_le h natCast_lt_aleph0
/-
**Cardinal.power_nat_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_nat_eq {c : Cardinal.{u}} {n : Nat} (h1 : ℵ₀ <= c) (h2 : 1 <= n) : c
 ^ n = c
参数：h1 : ℵ₀ <= c；h2 : 1 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.pow_eq`：pow_eq {κ μ : Cardinal.{u}} (H1 : ℵ₀ <= κ) (H2 : 1 <= μ
) (H3 : μ < ℵ₀) : κ ^ μ = κ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem power_nat_eq {c : Cardinal.{u}} {n : ℕ} (h1 : ℵ₀ ≤ c) (h2 : 1 ≤ n) : c ^ n = c :=
  pow_eq h1 (mod_cast h2) natCast_lt_aleph0
/-
**Cardinal.power_nat_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_nat_le_max {c : Cardinal.{u}} {n : Nat} : c ^ (n : Cardinal.{u}) <= 
max c ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `Cardinal.power_nat_le`：power_nat_le {c : Cardinal.{u}} {n : Nat} (h : ℵ₀
 <= c) : c ^ n <= c
· 使用定理 `le_max_of_le_right`：le_max_of_le_right : a <= c -> a <= max b c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.power_lt_aleph0`：power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀)
 (hb : b < ℵ₀) : a ^ b < ℵ₀
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem power_nat_le_max {c : Cardinal.{u}} {n : ℕ} : c ^ (n : Cardinal.{u}) ≤ max c ℵ₀ := by
  rcases le_or_gt ℵ₀ c with hc | hc
  · exact le_max_of_le_left (power_nat_le hc)
  · exact le_max_of_le_right (power_lt_aleph0 hc natCast_lt_aleph0).le
/-
**Cardinal.power_le_aleph0** 是 Mathlib 中的一个引理，位于命名空间 `Cardinal`。
形式化陈述：power_le_aleph0 {a b : Cardinal.{u}} (ha : a <= ℵ₀) (hb : b < ℵ₀) : a ^ b 
<= ℵ₀
参数：ha : a <= ℵ₀；hb : b < ℵ₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `Cardinal.power_nat_le_max`：power_nat_le_max {c : Cardinal.{u}} {n : Nat}
 : c ^ (n : Cardinal.{u}) <= max c ℵ₀
-/
lemma power_le_aleph0 {a b : Cardinal.{u}} (ha : a ≤ ℵ₀) (hb : b < ℵ₀) : a ^ b ≤ ℵ₀ := by
  lift b to ℕ using hb; simpa [ha] using power_nat_le_max (c := a)
/-
**Cardinal.powerlt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_aleph0 {c : Cardinal} (h : ℵ₀ <= c) : c ^< ℵ₀ = c
参数：h : ℵ₀ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.powerlt_le`：powerlt_le {a b c : Cardinal.{u}} : a ^< b <= c ↔ f
orall x < b, a ^ x <= c
· 使用定理 `Cardinal.pow_le`：pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ <= κ) (H2 : μ < ℵ₀
) : κ ^ μ <= κ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.power_one`：power_one (a : Cardinal.{u}) : a ^ (1 : Cardinal) = 
a
· 使用定理 `Cardinal.le_powerlt`：le_powerlt {b c : Cardinal.{u}} (a) (h : c < b) : (
a ^ c) <= a ^< b
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀
-/
theorem powerlt_aleph0 {c : Cardinal} (h : ℵ₀ ≤ c) : c ^< ℵ₀ = c := by
  apply le_antisymm
  · rw [powerlt_le]
    exact fun _ a ↦ pow_le h a
  convert! le_powerlt c one_lt_aleph0; rw [power_one]
/-
**Cardinal.powerlt_aleph0_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：powerlt_aleph0_le (c : Cardinal) : c ^< ℵ₀ <= max c ℵ₀
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.powerlt_aleph0`：powerlt_aleph0 {c : Cardinal} (h : ℵ₀ <= c) : c
 ^< ℵ₀ = c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Cardinal.powerlt_le`：powerlt_le {a b c : Cardinal.{u}} : a ^< b <= c ↔ f
orall x < b, a ^ x <= c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.power_lt_aleph0`：power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀)
 (hb : b < ℵ₀) : a ^ b < ℵ₀
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem powerlt_aleph0_le (c : Cardinal) : c ^< ℵ₀ ≤ max c ℵ₀ := by
  rcases le_or_gt ℵ₀ c with h | h
  · rw [powerlt_aleph0 h]
    apply le_max_left
  rw [powerlt_le]
  exact fun c' hc' => (power_lt_aleph0 h hc').le.trans (le_max_right _ _)

end power

/-! ### Computing cardinality of various types -/
section computing

section Function

variable {α β : Type u} {β' : Type v}

/-
**Cardinal.mk_equiv_eq_zero_iff_lift_ne** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_equiv_eq_zero_iff_lift_ne : #(α ≃ β') = 0 ↔ lift.{v} #α != lift.{u} #β'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_equiv_eq_zero_iff_lift_ne : #(α ≃ β') = 0 ↔ lift.{v} #α ≠ lift.{u} #β' := by
  rw [mk_eq_zero_iff, ← not_nonempty_iff, ← lift_mk_eq']
/-
**Cardinal.mk_equiv_eq_zero_iff_ne** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_equiv_eq_zero_iff_ne : #(α ≃ β) = 0 ↔ #α != #β
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_equiv_eq_zero_iff_lift_ne`：mk_equiv_eq_zero_iff_lift_ne : #(
α ≃ β') = 0 ↔ lift.{v} #α != lift.{u} #β'
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_equiv_eq_zero_iff_ne : #(α ≃ β) = 0 ↔ #α ≠ #β := by
  rw [mk_equiv_eq_zero_iff_lift_ne, lift_id, lift_id]

/-- This lemma makes lemmas assuming `Infinite α` applicable to the situation where we have
  `Infinite β` instead. -/
/-
**Cardinal.mk_equiv_comm** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_equiv_comm : #(α ≃ β') = #(β' ≃ α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.symm_bijective`：symm_bijective : Function.Bijective (Equiv.symm : 
(α ≃ β) -> β ≃ α)

--- 原说明 ---
This lemma makes lemmas assuming `Infinite α` applicable to the situation where 
we have
  `Infinite β` instead.
-/
theorem mk_equiv_comm : #(α ≃ β') = #(β' ≃ α) :=
  (ofBijective _ symm_bijective).cardinal_eq
/-
**Cardinal.mk_embedding_eq_zero_iff_lift_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
形式化陈述：mk_embedding_eq_zero_iff_lift_lt : #(α ↪ β') = 0 ↔ lift.{u} #β' < lift.{v}
 #α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_embedding_eq_zero_iff_lift_lt : #(α ↪ β') = 0 ↔ lift.{u} #β' < lift.{v} #α := by
  rw [mk_eq_zero_iff, ← not_nonempty_iff, ← lift_mk_le', not_le]
/-
**Cardinal.mk_embedding_eq_zero_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_embedding_eq_zero_iff_lt : #(α ↪ β) = 0 ↔ #β < #α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_embedding_eq_zero_iff_lift_lt`：mk_embedding_eq_zero_iff_lift
_lt : #(α ↪ β') = 0 ↔ lift.{u} #β' < lift.{v} #α
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_embedding_eq_zero_iff_lt : #(α ↪ β) = 0 ↔ #β < #α := by
  rw [mk_embedding_eq_zero_iff_lift_lt, lift_lt]
/-
**Cardinal.mk_arrow_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_arrow_eq_zero_iff : #(α -> β') = 0 ↔ #α != 0 ∧ #β' = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_arrow_eq_zero_iff : #(α → β') = 0 ↔ #α ≠ 0 ∧ #β' = 0 := by
  simp_rw [mk_eq_zero_iff, mk_ne_zero_iff, isEmpty_fun]
/-
**Cardinal.mk_surjective_eq_zero_iff_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_surjective_eq_zero_iff_lift : #{f : α -> β' | Surjective f} = 0 ↔ lift.
{v} #α < lift.{u} #β' ∨ (#α != 0 ∧ #β' = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Tactic.Push.not_and_or_eq`：not_and_or_eq : (¬ (p ∧ q)) = (¬ p ∨ 
¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk_surjective_eq_zero_iff_lift :
    #{f : α → β' | Surjective f} = 0 ↔ lift.{v} #α < lift.{u} #β' ∨ (#α ≠ 0 ∧ #β' = 0) := by
  contrapose! +distrib
  rw [lift_mk_le', and_comm]
  simp_rw [mk_ne_zero_iff, mk_eq_zero_iff, nonempty_coe_sort,
    Set.Nonempty, mem_ofPred, exists_surjective_iff, nonempty_fun]
/-
**Cardinal.mk_surjective_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_surjective_eq_zero_iff : #{f : α -> β | Surjective f} = 0 ↔ #α < #β ∨ (
#α != 0 ∧ #β = 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_surjective_eq_zero_iff_lift`：mk_surjective_eq_zero_iff_lift 
: #{f : α -> β' | Surjective f} = 0 ↔ lift.{v} #α < lift.{u} #β' ∨ (#α != 0 ∧ #β
' = 0)
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_surjective_eq_zero_iff :
    #{f : α → β | Surjective f} = 0 ↔ #α < #β ∨ (#α ≠ 0 ∧ #β = 0) := by
  rw [mk_surjective_eq_zero_iff_lift, lift_lt]

variable (α β')
/-
**Cardinal.mk_equiv_le_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_equiv_le_embedding : #(α ≃ β') <= #(α ↪ β')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.toEmbedding_injective`：toEmbedding_injective : Function.Injective 
(Equiv.toEmbedding : (α ≃ β) -> (α ↪ β))
-/
theorem mk_equiv_le_embedding : #(α ≃ β') ≤ #(α ↪ β') := ⟨⟨_, Equiv.toEmbedding_injective⟩⟩
/-
**Cardinal.mk_embedding_le_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_embedding_le_arrow : #(α ↪ β') <= #(α -> β')
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem mk_embedding_le_arrow : #(α ↪ β') ≤ #(α → β') := ⟨⟨_, DFunLike.coe_injective⟩⟩

variable [Infinite α] {α β'}
/-
**Cardinal.mk_perm_eq_self_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_perm_eq_self_power : #(Equiv.Perm α) = #α ^ #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_equiv_le_embedding`：mk_equiv_le_embedding : #(α ≃ β') <= #(α
 ↪ β')
· 使用定理 `Cardinal.mk_embedding_le_arrow`：mk_embedding_le_arrow : #(α ↪ β') <= #(α
 -> β')
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Bool.xor_self`：∀ (x : Bool), (x ^^ x) = false
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.false_xor`：∀ (x : Bool), (false ^^ x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Bool.xor_false`：∀ (x : Bool), (x ^^ false) = x
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_ofNat`：lift_ofNat (n : Nat) [n.AtLeastTwo] : lift.{u} (ofN
at(n) : Cardinal.{v}) = OfNat.ofNat n
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Cardinal.add_mk_eq_max`：add_mk_eq_max {α β : Type u} [Infinite α] : #α +
 #β = max #α #β
· 使用定理 `max_self`：∀ {α : Type u_1} [inst : LinearOrder α] (a : α), max a a = a
· 使用定理 `Cardinal.power_def`：power_def (α β : Type u) : #α ^ #β = #(β -> α)
· 使用定理 `Cardinal.power_self_eq`：power_self_eq {c : Cardinal} (h : ℵ₀ <= c) : c ^
 c = 2 ^ c
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Cardinal.mk_pi`：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = pro
d fun i => #(α i)
· 使用定理 `Cardinal.prod_const`：prod_const (ι : Type u) (a : Cardinal.{v}) : (prod 
fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι
-/
theorem mk_perm_eq_self_power : #(Equiv.Perm α) = #α ^ #α :=
  ((mk_equiv_le_embedding α α).trans (mk_embedding_le_arrow α α)).antisymm <| by
    suffices Nonempty ((α → Bool) ↪ Equiv.Perm (α × Bool)) by
      obtain ⟨e⟩ : Nonempty (α ≃ α × Bool) := by simp [← Cardinal.eq, mul_two]
      simp only [← le_def, mk_pi, mk_fintype, Fintype.card_bool, Nat.cast_ofNat,
        prod_const, lift_ofNat, lift_uzero] at this
      rwa [← power_def, power_self_eq (aleph0_le_mk α), e.permCongr.cardinal_eq]
    refine ⟨⟨fun f ↦ Involutive.toPerm (fun x ↦ ⟨x.1, xor (f x.1) x.2⟩) fun x ↦ ?_, fun f g h ↦ ?_⟩⟩
    · simp_rw [← Bool.xor_assoc, Bool.xor_self, Bool.false_xor]
    · ext a; rw [← (f a).xor_false, ← (g a).xor_false]; exact congr(($h ⟨a, false⟩).2)
/-
**Cardinal.mk_perm_eq_two_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_perm_eq_two_power : #(Equiv.Perm α) = 2 ^ #α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_perm_eq_self_power`：mk_perm_eq_self_power : #(Equiv.Perm α) 
= #α ^ #α
· 使用定理 `Cardinal.power_self_eq`：power_self_eq {c : Cardinal} (h : ℵ₀ <= c) : c ^
 c = 2 ^ c
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem mk_perm_eq_two_power : #(Equiv.Perm α) = 2 ^ #α := by
  rw [mk_perm_eq_self_power, power_self_eq (aleph0_le_mk α)]
/-
**Cardinal.mk_equiv_eq_arrow_of_lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_equiv_eq_arrow_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') : #(α ≃ β'
) = #(α -> β')
参数：leq : lift.{v} #α = lift.{u} #β'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.mk_perm_eq_self_power`：mk_perm_eq_self_power : #(Equiv.Perm α) 
= #α ^ #α
· 使用定理 `Cardinal.power_def`：power_def (α β : Type u) : #α ^ #β = #(β -> α)
-/
theorem mk_equiv_eq_arrow_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') :
    #(α ≃ β') = #(α → β') := by
  obtain ⟨e⟩ := lift_mk_eq'.mp leq
  have e₁ := lift_mk_eq'.mpr ⟨.equivCongr (.refl α) e⟩
  have e₂ := lift_mk_eq'.mpr ⟨.arrowCongr (.refl α) e⟩
  rw [lift_id'.{u, v}] at e₁ e₂
  rw [← e₁, ← e₂, lift_inj, mk_perm_eq_self_power, power_def]
/-
**Cardinal.mk_equiv_eq_arrow_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_equiv_eq_arrow_of_eq (eq : #α = #β) : #(α ≃ β) = #(α -> β)
参数：eq : #α = #β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_equiv_eq_arrow_of_lift_eq`：mk_equiv_eq_arrow_of_lift_eq (leq
 : lift.{v} #α = lift.{u} #β') : #(α ≃ β') = #(α -> β')
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem mk_equiv_eq_arrow_of_eq (eq : #α = #β) : #(α ≃ β) = #(α → β) :=
  mk_equiv_eq_arrow_of_lift_eq congr(lift $eq)
/-
**Cardinal.mk_equiv_of_lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_equiv_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') : #(α ≃ β') = 2 ^ l
ift.{v} #α
参数：leq : lift.{v} #α = lift.{u} #β'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_equiv_eq_arrow_of_lift_eq`：mk_equiv_eq_arrow_of_lift_eq (leq
 : lift.{v} #α = lift.{u} #β') : #(α ≃ β') = #(α -> β')
· 使用定理 `Cardinal.mk_pi`：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = pro
d fun i => #(α i)
· 使用定理 `Cardinal.prod_const`：prod_const (ι : Type u) (a : Cardinal.{v}) : (prod 
fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.power_self_eq`：power_self_eq {c : Cardinal} (h : ℵ₀ <= c) : c ^
 c = 2 ^ c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_equiv_of_lift_eq (leq : lift.{v} #α = lift.{u} #β') : #(α ≃ β') = 2 ^ lift.{v} #α := by
  simp [mk_equiv_eq_arrow_of_lift_eq leq, ← leq, power_self_eq]
/-
**Cardinal.mk_equiv_of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_equiv_of_eq (eq : #α = #β) : #(α ≃ β) = 2 ^ #α
参数：eq : #α = #β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_equiv_of_lift_eq`：mk_equiv_of_lift_eq (leq : lift.{v} #α = l
ift.{u} #β') : #(α ≃ β') = 2 ^ lift.{v} #α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem mk_equiv_of_eq (eq : #α = #β) : #(α ≃ β) = 2 ^ #α := by
  rw [mk_equiv_of_lift_eq (lift_inj.mpr eq), lift_id]
/-
**Cardinal.mk_embedding_eq_arrow_of_lift_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
形式化陈述：mk_embedding_eq_arrow_of_lift_le (lle : lift.{u} #β' <= lift.{v} #α) : #(β
' ↪ α) = #(β' -> α)
参数：lle : lift.{u} #β' <= lift.{v} #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Cardinal.mk_embedding_le_arrow`：mk_embedding_le_arrow : #(α ↪ β') <= #(α
 -> β')
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
· 使用定理 `Cardinal.mul_eq_self`：mul_eq_self {c : Cardinal} (hc : ℵ₀ <= c) : c * c 
= c
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `Cardinal.lift_mk_le'`：lift_mk_le' {α : Type u} {β : Type v} : lift.{v} #
α <= lift.{u} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem mk_embedding_eq_arrow_of_lift_le (lle : lift.{u} #β' ≤ lift.{v} #α) :
    #(β' ↪ α) = #(β' → α) :=
  (mk_embedding_le_arrow _ _).antisymm <| by
    conv_rhs => rw [← (Equiv.embeddingCongr (.refl _)
      (Cardinal.eq.mp <| mul_eq_self <| aleph0_le_mk α).some).cardinal_eq]
    obtain ⟨e⟩ := lift_mk_le'.mp lle
    exact ⟨⟨fun f ↦ ⟨fun b ↦ ⟨e b, f b⟩, fun _ _ h ↦ e.injective congr(Prod.fst $h)⟩,
      fun f g h ↦ funext fun b ↦ congr(Prod.snd <| $h b)⟩⟩
/-
**Cardinal.mk_embedding_eq_arrow_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_embedding_eq_arrow_of_le (le : #β <= #α) : #(β ↪ α) = #(β -> α)
参数：le : #β <= #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_embedding_eq_arrow_of_lift_le`：mk_embedding_eq_arrow_of_lift
_le (lle : lift.{u} #β' <= lift.{v} #α) : #(β' ↪ α) = #(β' -> α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem mk_embedding_eq_arrow_of_le (le : #β ≤ #α) : #(β ↪ α) = #(β → α) :=
  mk_embedding_eq_arrow_of_lift_le (lift_le.mpr le)
/-
**Cardinal.mk_surjective_eq_arrow_of_lift_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal
`。
形式化陈述：mk_surjective_eq_arrow_of_lift_le (lle : lift.{u} #β' <= lift.{v} #α) : #{
f : α -> β' | Surjective f} = #(α -> β')
参数：lle : lift.{u} #β' <= lift.{v} #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Cardinal.mk_set_le`：mk_set_le (s : Set α) : #s <= #α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Cardinal.add_eq_left`：add_eq_left {a b : Cardinal} (ha : ℵ₀ <= a) (hb : 
b <= a) : a + b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_le_lift`：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.
{v} c ↔ ℵ₀ <= c
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem mk_surjective_eq_arrow_of_lift_le (lle : lift.{u} #β' ≤ lift.{v} #α) :
    #{f : α → β' | Surjective f} = #(α → β') :=
  (mk_set_le _).antisymm <|
    have ⟨e⟩ : Nonempty (α ≃ α ⊕ β') := by
      simp_rw [← lift_mk_eq', mk_sum, lift_add, lift_lift]; rw [lift_umax.{u, v}, eq_comm]
      exact add_eq_left (aleph0_le_lift.mpr <| aleph0_le_mk α) lle
    ⟨⟨fun f ↦ ⟨fun a ↦ (e a).elim f id, fun b ↦ ⟨e.symm (.inr b), congr_arg _ (e.right_inv _)⟩⟩,
      fun f g h ↦ funext fun a ↦ by
        simpa only [e.apply_symm_apply] using! congr_fun (Subtype.ext_iff.mp h) (e.symm <| .inl a)⟩⟩
/-
**Cardinal.mk_surjective_eq_arrow_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_surjective_eq_arrow_of_le (le : #β <= #α) : #{f : α -> β | Surjective f
} = #(α -> β)
参数：le : #β <= #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_surjective_eq_arrow_of_lift_le`：mk_surjective_eq_arrow_of_li
ft_le (lle : lift.{u} #β' <= lift.{v} #α) : #{f : α -> β' | Surjective f} = #(α 
-> β')
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem mk_surjective_eq_arrow_of_le (le : #β ≤ #α) : #{f : α → β | Surjective f} = #(α → β) :=
  mk_surjective_eq_arrow_of_lift_le (lift_le.mpr le)

end Function

@[simp]
/-
**Cardinal.mk_list_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_list_eq_mk (α : Type u) [Infinite α] : #(List α) = #α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.le_def`：le_def (α β : Type u) : #α <= #β ↔ Nonempty (α ↪ β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Cardinal.mk_list_eq_sum_pow`：mk_list_eq_sum_pow (α : Type u) : #(List α)
 = sum fun n => #α ^ n
· 使用定理 `Cardinal.sum_le_sum`：sum_le_sum {ι} (f g : ι -> Cardinal) (H : forall i,
 f i <= g i) : sum f <= sum g
· 使用定理 `Cardinal.pow_le`：pow_le {κ μ : Cardinal.{u}} (H1 : ℵ₀ <= κ) (H2 : μ < ℵ₀
) : κ ^ μ <= κ
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.aleph0_mul_eq`：aleph0_mul_eq {a : Cardinal} (ha : ℵ₀ <= a) : ℵ₀
 * a = a
-/
theorem mk_list_eq_mk (α : Type u) [Infinite α] : #(List α) = #α :=
  have H1 : ℵ₀ ≤ #α := aleph0_le_mk α
  Eq.symm <|
    le_antisymm ((le_def _ _).2 ⟨⟨fun a => [a], fun _ => by simp⟩⟩) <|
      calc
        #(List α) = sum fun n : ℕ => #α ^ (n : Cardinal.{u}) := mk_list_eq_sum_pow α
        _ ≤ sum fun _ : ℕ => #α := sum_le_sum _ _ fun n => pow_le H1 natCast_lt_aleph0
        _ = #α := by simp [H1]
/-
**Cardinal.mk_list_eq_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_list_eq_aleph0 (α : Type u) [Countable α] [Nonempty α] : #(List α) = ℵ₀
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Cardinal.mk_le_aleph0`：mk_le_aleph0 [Countable α] : #α <= ℵ₀
· 使用定理 `List.countable`：∀ {α : Type u_2} [Countable α], Countable (List α)
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `instInfiniteListOfNonempty`：∀ {α : Type u_1} [Nonempty α], Infinite (Lis
t α)
-/
theorem mk_list_eq_aleph0 (α : Type u) [Countable α] [Nonempty α] : #(List α) = ℵ₀ :=
  mk_le_aleph0.antisymm (aleph0_le_mk _)
/-
**Cardinal.mk_list_eq_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_list_eq_max (α : Type u) [Nonempty α] : #(List α) = max ℵ₀ #α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_list_eq_aleph0`：mk_list_eq_aleph0 (α : Type u) [Countable α]
 [Nonempty α] : #(List α) = ℵ₀
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
· 使用定理 `Cardinal.mk_le_aleph0`：mk_le_aleph0 [Countable α] : #α <= ℵ₀
· 使用定理 `Cardinal.mk_list_eq_mk`：mk_list_eq_mk (α : Type u) [Infinite α] : #(List
 α) = #α
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem mk_list_eq_max (α : Type u) [Nonempty α] : #(List α) = max ℵ₀ #α := by
  cases finite_or_infinite α
  · rw [mk_list_eq_aleph0, eq_comm, max_eq_left]
    exact mk_le_aleph0
  · rw [mk_list_eq_mk, eq_comm, max_eq_right]
    exact aleph0_le_mk α

-- TODO: standardize whether we write `max ℵ₀ x` or `max x ℵ₀`.
/-
**Cardinal.mk_list_eq_max_mk_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_list_eq_max_mk_aleph0 (α : Type u) [Nonempty α] : #(List α) = max #α ℵ₀
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_list_eq_max`：mk_list_eq_max (α : Type u) [Nonempty α] : #(Li
st α) = max ℵ₀ #α
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
-/
theorem mk_list_eq_max_mk_aleph0 (α : Type u) [Nonempty α] : #(List α) = max #α ℵ₀ := by
  rw [mk_list_eq_max, max_comm]
/-
**Cardinal.sum_pow_eq_max_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_pow_eq_max_aleph0 {x : Cardinal} (h : x != 0) : sum (fun n => x ^ n) =
 max ℵ₀ x
参数：h : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.nonempty_out`：nonempty_out {x : Cardinal} (h : x != 0) : Nonemp
ty x.out
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.mk_list_eq_sum_pow`：mk_list_eq_sum_pow (α : Type u) : #(List α)
 = sum fun n => #α ^ n
· 使用定理 `Cardinal.mk_list_eq_max`：mk_list_eq_max (α : Type u) [Nonempty α] : #(Li
st α) = max ℵ₀ #α
-/
theorem sum_pow_eq_max_aleph0 {x : Cardinal} (h : x ≠ 0) : sum (fun n ↦ x ^ n) = max ℵ₀ x := by
  have := nonempty_out h
  conv_lhs => rw [← x.mk_out, ← mk_list_eq_sum_pow, mk_list_eq_max, mk_out]
/-
**Cardinal.mk_list_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_list_le_max (α : Type u) : #(List α) <= max ℵ₀ #α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_le_aleph0`：mk_le_aleph0 [Countable α] : #α <= ℵ₀
· 使用定理 `List.countable`：∀ {α : Type u_2} [Countable α], Countable (List α)
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_list_eq_mk`：mk_list_eq_mk (α : Type u) [Infinite α] : #(List
 α) = #α
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem mk_list_le_max (α : Type u) : #(List α) ≤ max ℵ₀ #α := by
  cases finite_or_infinite α
  · exact mk_le_aleph0.trans (le_max_left _ _)
  · rw [mk_list_eq_mk]
    apply le_max_right
/-
**Cardinal.sum_pow_le_max_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_pow_le_max_aleph0 (x : Cardinal) : sum (fun n => x ^ n) <= max ℵ₀ x
参数：x : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.mk_list_eq_sum_pow`：mk_list_eq_sum_pow (α : Type u) : #(List α)
 = sum fun n => #α ^ n
· 使用定理 `Cardinal.mk_list_le_max`：mk_list_le_max (α : Type u) : #(List α) <= max 
ℵ₀ #α
-/
theorem sum_pow_le_max_aleph0 (x : Cardinal) : sum (fun n ↦ x ^ n) ≤ max ℵ₀ x := by
  rw [← x.mk_out, ← mk_list_eq_sum_pow]
  exact mk_list_le_max _

@[simp]
/-
**Cardinal.mk_finset_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finset_of_infinite (α : Type u) [Infinite α] : #(Finset α) = #α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.singleton_inj`：singleton_inj : ({a} : Finset α) = {b} ↔ a = b
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用定理 `List.toFinset_surjective`：toFinset_surjective : Surjective (toFinset : L
ist α -> Finset α)
· 使用定理 `Cardinal.mk_list_eq_mk`：mk_list_eq_mk (α : Type u) [Infinite α] : #(List
 α) = #α
-/
theorem mk_finset_of_infinite (α : Type u) [Infinite α] : #(Finset α) = #α := by
  classical
  exact Eq.symm <|
    le_antisymm (mk_le_of_injective fun _ _ => Finset.singleton_inj.1) <|
      calc
        #(Finset α) ≤ #(List α) := mk_le_of_surjective List.toFinset_surjective
        _ = #α := mk_list_eq_mk α
/-
**Cardinal.mk_bounded_set_le_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_bounded_set_le_of_infinite (α : Type u) [Infinite α] (c : Cardinal) : #
{ t : Set α // #t <= c } <= #α ^ c
参数：α : Type u；c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.add_one_eq`：add_one_eq {a : Cardinal} (ha : ℵ₀ <= a) : a + 1 = 
a
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.mk_le_of_surjective`：mk_le_of_surjective {α β : Type u} {f : α 
-> β} (hf : Surjective f) : #β <= #α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Cardinal.mk_preimage_of_injective`：mk_preimage_of_injective (f : α -> β)
 (s : Set β) (h : Injective f) : #(f ⁻¹' s) <= #s
· 使用定理 `Sum.inl.inj`：∀ {α : Type u} {β : Type v} {val val_1 : α}, Sum.inl val = 
Sum.inl val_1 → val = val_1
· 使用定理 `Cardinal.mk_range_le`：mk_range_le {α β : Type u} {f : α -> β} : #(range 
f) <= #α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem mk_bounded_set_le_of_infinite (α : Type u) [Infinite α] (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ #α ^ c := by
  rw [← add_one_eq (aleph0_le_mk α)]
  induction c using Cardinal.inductionOn with | _ β
  fapply mk_le_of_surjective
  · intro f
    use Sum.inl ⁻¹' range f
    refine le_trans (mk_preimage_of_injective _ _ fun x y => Sum.inl.inj) ?_
    apply mk_range_le
  rintro ⟨s, ⟨g⟩⟩
  classical
  use fun y => if h : ∃ x : s, g x = y then Sum.inl (Classical.choose h).val
               else Sum.inr (ULift.up 0)
  apply Subtype.ext; ext x
  constructor
  · rintro ⟨y, h⟩
    dsimp only at h
    by_cases h' : ∃ z : s, g z = y
    · rw [dif_pos h'] at h
      cases Sum.inl.inj h
      exact (Classical.choose h').2
    · rw [dif_neg h'] at h
      cases h
  · intro h
    have : ∃ z : s, g z = g ⟨x, h⟩ := ⟨⟨x, h⟩, rfl⟩
    use g ⟨x, h⟩
    dsimp only
    rw [dif_pos this]
    congr
    suffices Classical.choose this = ⟨x, h⟩ from congr_arg Subtype.val this
    apply g.2
    exact Classical.choose_spec this
/-
**Cardinal.mk_bounded_set_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_bounded_set_le (α : Type u) (c : Cardinal) : #{ t : Set α // #t <= c } 
<= max #α ℵ₀ ^ c
参数：α : Type u；c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inr.inj`：∀ {α : Type u} {β : Type v} {val val_1 : β}, Sum.inr val = 
Sum.inr val_1 → val = val_1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_image_le`：mk_image_le {α β : Type u} {f : α -> β} {s : Set α
} : #(f '' s) <= #s
· 使用定理 `Cardinal.mk_bounded_set_le_of_infinite`：mk_bounded_set_le_of_infinite (α
 : Type u) [Infinite α] (c : Cardinal) : #{ t : Set α // #t <= c } <= #α ^ c
· 使用定理 `instInfiniteULift`：∀ {α : Type v} [Infinite α], Infinite (ULift.{u, v} α
)
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_comm`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), max a b = m
ax b a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.add_eq_max`：add_eq_max {a b : Cardinal} (ha : ℵ₀ <= a) : a + b 
= max a b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mk_bounded_set_le (α : Type u) (c : Cardinal) :
    #{ t : Set α // #t ≤ c } ≤ max #α ℵ₀ ^ c := by
  trans #{ t : Set ((ULift.{u} ℕ) ⊕ α) // #t ≤ c }
  · refine ⟨Embedding.subtypeMap ?_ ?_⟩
    · apply Embedding.image
      use Sum.inr
      apply Sum.inr.inj
    intro s hs
    exact mk_image_le.trans hs
  apply (mk_bounded_set_le_of_infinite ((ULift.{u} ℕ) ⊕ α) c).trans
  rw [max_comm, ← add_eq_max] <;> rfl
/-
**Cardinal.mk_bounded_subset_le** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) : #{ t : 
Set α // t subseteq s ∧ #t <= c } <= max #s ℵ₀ ^ c
参数：s : Set α；c : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.preimage_eq_preimage'`：preimage_eq_preimage' {s t : Set α} {f : β ->
 α} (hs : s subseteq range f) (ht : t subseteq range f) : f ⁻¹' s = f ⁻¹' t ↔ s 
= t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mk_preimage_of_injective`：mk_preimage_of_injective (f : α -> β)
 (s : Set β) (h : Injective f) : #(f ⁻¹' s) <= #s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Cardinal.mk_bounded_set_le`：mk_bounded_set_le (α : Type u) (c : Cardinal
) : #{ t : Set α // #t <= c } <= max #α ℵ₀ ^ c
-/
theorem mk_bounded_subset_le {α : Type u} (s : Set α) (c : Cardinal.{u}) :
    #{ t : Set α // t ⊆ s ∧ #t ≤ c } ≤ max #s ℵ₀ ^ c := by
  refine le_trans ?_ (mk_bounded_set_le s c)
  refine ⟨Embedding.codRestrict _ ?_ ?_⟩
  · use fun t => (↑) ⁻¹' t.1
    rintro ⟨t, ht1, ht2⟩ ⟨t', h1t', h2t'⟩ h
    apply Subtype.ext
    dsimp only at h ⊢
    refine (preimage_eq_preimage' ?_ ?_).1 h <;> rw [Subtype.range_coe] <;> assumption
  rintro ⟨t, _, h2t⟩; exact (mk_preimage_of_injective _ _ Subtype.val_injective).trans h2t

end computing

/-! ### Properties of `compl` -/
section compl

/-
**Cardinal.mk_compl_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_compl_of_infinite {α : Type*} [Infinite α] (s : Set α) (h2 : #s < #α) :
 #(sᶜ : Set α) = #α
参数：s : Set α；h2 : #s < #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.eq_of_add_eq_of_aleph0_le`：eq_of_add_eq_of_aleph0_le {a b c : C
ardinal} (h : a + b = c) (ha : a < c) (hc : ℵ₀ <= c) : b = c
· 使用定理 `Cardinal.mk_sum_compl`：mk_sum_compl {α} (s : Set α) : #s + #(sᶜ : Set α)
 = #α
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem mk_compl_of_infinite {α : Type*} [Infinite α] (s : Set α) (h2 : #s < #α) :
    #(sᶜ : Set α) = #α := by
  refine eq_of_add_eq_of_aleph0_le ?_ h2 (aleph0_le_mk α)
  exact mk_sum_compl s
/-
**Cardinal.mk_compl_finset_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_compl_finset_of_infinite {α : Type*} [Infinite α] (s : Finset α) : #((↑
s)ᶜ : Set α) = #α
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_compl_of_infinite`：mk_compl_of_infinite {α : Type*} [Infinit
e α] (s : Set α) (h2 : #s < #α) : #(sᶜ : Set α) = #α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Cardinal.finset_card_lt_aleph0`：finset_card_lt_aleph0 (s : Finset α) : #
(↑s : Set α) < ℵ₀
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
-/
theorem mk_compl_finset_of_infinite {α : Type*} [Infinite α] (s : Finset α) :
    #((↑s)ᶜ : Set α) = #α := by
  apply mk_compl_of_infinite
  exact (finset_card_lt_aleph0 s).trans_le (aleph0_le_mk α)
/-
**Cardinal.mk_compl_eq_mk_compl_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_compl_eq_mk_compl_infinite {α : Type*} [Infinite α] {s t : Set α} (hs :
 #s < #α) (ht : #t < #α) : #(sᶜ : Set α) = #(tᶜ : Set α)
参数：hs : #s < #α；ht : #t < #α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_compl_of_infinite`：mk_compl_of_infinite {α : Type*} [Infinit
e α] (s : Set α) (h2 : #s < #α) : #(sᶜ : Set α) = #α
-/
theorem mk_compl_eq_mk_compl_infinite {α : Type*} [Infinite α] {s t : Set α} (hs : #s < #α)
    (ht : #t < #α) : #(sᶜ : Set α) = #(tᶜ : Set α) := by
  rw [mk_compl_of_infinite s hs, mk_compl_of_infinite t ht]
/-
**Cardinal.mk_compl_eq_mk_compl_finite_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
形式化陈述：mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [Finite α] {s :
 Set α} {t : Set β} (h1 : (lift.{v, u} #α) = (lift.{u, v} #β)) (h2 : lift.{v, u}
 #s = lift.{u, v} #t) : lift.{v} #(sᶜ : Set α) = lift.{u} #(tᶜ : Set β)
参数：h1 : (lift.{v, u} #α) = (lift.{u, v} #β)；h2 : lift.{v, u} #s = lift.{u, v} #t
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.ofEquiv_card`：ofEquiv_card [Fintype α] (f : α ≃ β) : @card β (of
Equiv α f) = card α
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.instCanLiftFinsetCoeFinite`：∀ {α : Type u}, CanLift (Set α) (Finset 
α) SetLike.coe Set.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_coe_finset`：mk_coe_finset {α : Type u} {s : Finset α} : #s =
 ↑(Finset.card s)
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_compl_eq_mk_compl_finite_lift {α : Type u} {β : Type v} [Finite α] {s : Set α}
    {t : Set β} (h1 : (lift.{v, u} #α) = (lift.{u, v} #β))
    (h2 : lift.{v, u} #s = lift.{u, v} #t) :
    lift.{v} #(sᶜ : Set α) = lift.{u} #(tᶜ : Set β) := by
  cases nonempty_fintype α
  rcases lift_mk_eq'.1 h1 with ⟨e⟩; let : Fintype β := Fintype.ofEquiv α e
  replace h1 : Fintype.card α = Fintype.card β := (Fintype.ofEquiv_card _).symm
  classical
    lift s to Finset α using s.toFinite
    lift t to Finset β using t.toFinite
    simp only [Finset.coe_sort_coe, mk_fintype, Fintype.card_coe, lift_natCast, Nat.cast_inj] at h2
    simp only [← Finset.coe_compl, Finset.coe_sort_coe, mk_coe_finset, Finset.card_compl,
      lift_natCast, h1, h2]
/-
**Cardinal.mk_compl_eq_mk_compl_finite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_compl_eq_mk_compl_finite {α β : Type u} [Finite α] {s : Set α} {t : Set
 β} (h1 : #α = #β) (h : #s = #t) : #(sᶜ : Set α) = #(tᶜ : Set β)
参数：h1 : #α = #β；h : #s = #t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.mk_compl_eq_mk_compl_finite_lift`：mk_compl_eq_mk_compl_finite_l
ift {α : Type u} {β : Type v} [Finite α] {s : Set α} {t : Set β} (h1 : (lift.{v,
 u} #α) = (lift.{u, v} #β)) (h2…
-/
theorem mk_compl_eq_mk_compl_finite {α β : Type u} [Finite α] {s : Set α} {t : Set β}
    (h1 : #α = #β) (h : #s = #t) : #(sᶜ : Set α) = #(tᶜ : Set β) := by
  rw [← lift_inj.{u, u}]
  apply mk_compl_eq_mk_compl_finite_lift.{u, u}
  <;> rwa [lift_inj]
/-
**Cardinal.mk_compl_eq_mk_compl_finite_same** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`
。
形式化陈述：mk_compl_eq_mk_compl_finite_same {α : Type u} [Finite α] {s t : Set α} (h 
: #s = #t) : #(sᶜ : Set α) = #(tᶜ : Set α)
参数：h : #s = #t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_compl_eq_mk_compl_finite`：mk_compl_eq_mk_compl_finite {α β :
 Type u} [Finite α] {s : Set α} {t : Set β} (h1 : #α = #β) (h : #s = #t) : #(sᶜ 
: Set α) = #(tᶜ : Set β)
-/
theorem mk_compl_eq_mk_compl_finite_same {α : Type u} [Finite α] {s t : Set α} (h : #s = #t) :
    #(sᶜ : Set α) = #(tᶜ : Set α) :=
  mk_compl_eq_mk_compl_finite.{u} rfl h

end compl

/-! ### Extending an injection to an equiv -/
section extend

/-
**Cardinal.extend_function** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：extend_function {α β : Type*} {s : Set α} (f : s ↪ β) (h : Nonempty ((sᶜ :
 Set α) ≃ ((range f)ᶜ : Set β))) : exists g : α ≃ β, forall x : s, g x = f x
参数：f : s ↪ β；h : Nonempty ((sᶜ : Set α) ≃ ((range f)ᶜ : Set β))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Set.sumCompl_symm_apply_of_mem`：sumCompl_symm_apply_of_mem {α : Ty
pe u} {s : Set α} [DecidablePred (· in s)] {x : α} (hx : x in s) : (Equiv.Set.su
mCompl s).symm x = Sum.inl…
· 使用定理 `Equiv.sumCongr_apply`：∀ {α₁ : Type u_9} {α₂ : Type u_10} {β₁ : Type u_11
} {β₂ : Type u_12} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (a : α₁ ⊕ β₁),   (ea.sumCongr e
b) a = Sum…
· 使用定理 `Equiv.ofInjective_apply`：∀ {α : Sort u_3} {β : Type u_4} (f : α → β) (hf
 : Function.Injective f) (a : α), (Equiv.ofInjective f hf) a = ⟨f a, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem extend_function {α β : Type*} {s : Set α} (f : s ↪ β)
    (h : Nonempty ((sᶜ : Set α) ≃ ((range f)ᶜ : Set β))) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  classical
  have := h; obtain ⟨g⟩ := this
  let h : α ≃ β :=
    (Set.sumCompl (s : Set α)).symm.trans
      ((sumCongr (Equiv.ofInjective f f.2) g).trans (Set.sumCompl (range f)))
  refine ⟨h, ?_⟩; rintro ⟨x, hx⟩; simp [h, Set.sumCompl_symm_apply_of_mem, hx]
/-
**Cardinal.extend_function_finite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：extend_function_finite {α : Type u} {β : Type v} [Finite α] {s : Set α} (f
 : s ↪ β) (h : Nonempty (α ≃ β)) : exists g : α ≃ β, forall x : s, g x = f x
参数：f : s ↪ β；h : Nonempty (α ≃ β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.extend_function`：extend_function {α β : Type*} {s : Set α} (f :
 s ↪ β) (h : Nonempty ((sᶜ : Set α) ≃ ((range f)ᶜ : Set β))) : exists g : α ≃ β,
 forall x : s,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Cardinal.mk_compl_eq_mk_compl_finite_lift`：mk_compl_eq_mk_compl_finite_l
ift {α : Type u} {β : Type v} [Finite α] {s : Set α} {t : Set β} (h1 : (lift.{v,
 u} #α) = (lift.{u, v} #β)) (h2…
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem extend_function_finite {α : Type u} {β : Type v} [Finite α] {s : Set α} (f : s ↪ β)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  apply extend_function.{u, v} f
  rw [← lift_mk_eq'] at h
  rw [← lift_mk_eq', mk_compl_eq_mk_compl_finite_lift h]
  rw [mk_range_eq_of_injective]; exact f.2
/-
**Cardinal.extend_function_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：extend_function_of_lt {α β : Type*} {s : Set α} (f : s ↪ β) (hs : #s < #α)
 (h : Nonempty (α ≃ β)) : exists g : α ≃ β, forall x : s, g x = f x
参数：f : s ↪ β；hs : #s < #α；h : Nonempty (α ≃ β)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.extend_function_finite`：extend_function_finite {α : Type u} {β 
: Type v} [Finite α] {s : Set α} (f : s ↪ β) (h : Nonempty (α ≃ β)) : exists g :
 α ≃ β, forall x : s,…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Cardinal.extend_function`：extend_function {α β : Type*} {s : Set α} (f :
 s ↪ β) (h : Nonempty ((sᶜ : Set α) ≃ ((range f)ᶜ : Set β))) : exists g : α ≃ β,
 forall x : s,…
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Cardinal.mk_compl_of_infinite`：mk_compl_of_infinite {α : Type*} [Infinit
e α] (s : Set α) (h2 : #s < #α) : #(sᶜ : Set α) = #α
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
-/
theorem extend_function_of_lt {α β : Type*} {s : Set α} (f : s ↪ β) (hs : #s < #α)
    (h : Nonempty (α ≃ β)) : ∃ g : α ≃ β, ∀ x : s, g x = f x := by
  cases fintypeOrInfinite α
  · exact extend_function_finite f h
  · apply extend_function f
    obtain ⟨g⟩ := id h
    have := Infinite.of_injective _ g.injective
    rw [← lift_mk_eq'] at h ⊢
    rwa [mk_compl_of_infinite s hs, mk_compl_of_infinite]
    rwa [← lift_lt, mk_range_eq_of_injective f.injective, ← h, lift_lt]

end extend
end Cardinal

