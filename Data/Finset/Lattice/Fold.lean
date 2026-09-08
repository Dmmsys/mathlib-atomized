/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Fold
public import Mathlib.Data.Finset.Sum
public import Mathlib.Data.Multiset.Lattice
public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Order.Hom.BoundedLattice
public import Mathlib.Order.Nat

/-!
# Lattice operations on finsets

This file is concerned with folding binary lattice operations over finsets.

For the special case of maximum and minimum of a finset, see Max.lean.

See also `Mathlib/Order/CompleteLattice/Finset.lean`, which is instead concerned with how big
lattice or set operations behave when indexed by a finset.
-/

@[expose] public section

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset

/-! ### sup and inf -/


section Sup

-- TODO: define with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c` -/
@[to_dual /-- Infimum of a finite set: `inf {a, b, c} f = f a ⊓ f b ⊓ f c` -/]
/-
**Finset.sup** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：sup (s : Finset β) (f : β -> α) : α
参数：s : Finset β；f : β -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2

--- 原说明 ---
Supremum of a finite set: `sup {a, b, c} f = f a ⊔ f b ⊔ f c`
-/
def sup (s : Finset β) (f : β → α) : α :=
  s.fold (· ⊔ ·) ⊥ f

variable {s s₁ s₂ : Finset β} {f g : β → α} {a : α}

@[to_dual]
/-
**Finset.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_def : s.sup f = (s.1.map f).sup
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_def : s.sup f = (s.1.map f).sup :=
  rfl

@[to_dual (attr := simp)]
/-
**Finset.sup_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_empty : (∅ : Finset β).sup f = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_empty`：fold_empty : (∅ : Finset α).fold op b f = b
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
-/
theorem sup_empty : (∅ : Finset β).sup f = ⊥ :=
  fold_empty

@[to_dual (attr := simp)]
/-
**Finset.sup_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f
参数：h : b ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_cons`：fold_cons (h : a ∉ s) : (cons a s h).fold op b f = f a
 * s.fold op b f
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
-/
theorem sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b ⊔ s.sup f :=
  fold_cons h

@[to_dual (attr := simp, grind =)]
/-
**Finset.sup_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_insert [DecidableEq β] {b : β} : (insert b s : Finset β).sup f = f b ⊔
 s.sup f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_insert_idem`：fold_insert_idem [DecidableEq α] [hi : Std.Idem
potentOp op] : (insert a s).fold op b f = f a * s.fold op b f
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
-/
theorem sup_insert [DecidableEq β] {b : β} : (insert b s : Finset β).sup f = f b ⊔ s.sup f :=
  fold_insert_idem

@[to_dual (attr := simp)]
/-
**Finset.sup_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) (g : β -> α) : (s.im
age f).sup g = s.sup (g ∘ f)
参数：s : Finset γ；f : γ -> β；g : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_image_idem`：fold_image_idem [DecidableEq α] {g : γ -> α} {s 
: Finset γ} [hi : Std.IdempotentOp op] : (image g s).fold op b f = s.fold op b (
f ∘ g)
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
-/
theorem sup_image [DecidableEq β] (s : Finset γ) (f : γ → β) (g : β → α) :
    (s.image f).sup g = s.sup (g ∘ f) :=
  fold_image_idem

@[to_dual (attr := simp)]
/-
**Finset.sup_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map f).sup g = s.sup 
(g ∘ f)
参数：s : Finset γ；f : γ ↪ β；g : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_map`：fold_map {g : γ ↪ α} {s : Finset γ} : (s.map g).fold op
 b f = s.fold op b (f ∘ g)
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
-/
theorem sup_map (s : Finset γ) (f : γ ↪ β) (g : β → α) : (s.map f).sup g = s.sup (g ∘ f) :=
  fold_map

@[to_dual (attr := simp)]
/-
**Finset.sup_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_singleton {b : β} : ({b} : Finset β).sup f = f b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sup_singleton`：sup_singleton {a : α} : ({a} : Multiset α).sup =
 a
-/
theorem sup_singleton {b : β} : ({b} : Finset β).sup f = f b :=
  Multiset.sup_singleton

@[to_dual]
/-
**Finset.sup_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_sup : s.sup (f ⊔ g) = s.sup f ⊔ s.sup g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `sup_sup_sup_comm`：sup_sup_sup_comm (a b c d : α) : a ⊔ b ⊔ (c ⊔ d) = a ⊔
 c ⊔ (b ⊔ d)
-/
theorem sup_sup : s.sup (f ⊔ g) = s.sup f ⊔ s.sup g := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, sup_empty, bot_sup_eq]
  | cons _ _ _ ih =>
    rw [sup_cons, sup_cons, sup_cons, ih]
    exact sup_sup_sup_comm _ _ _ _

@[to_dual]
/-
**Finset.sup_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_congr {f g : β -> α} (hs : s₁ = s₂) (hfg : forall a in s₂, f a = g a) 
: s₁.sup f = s₂.sup g
参数：hs : s₁ = s₂；hfg : forall a in s₂, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_congr`：fold_congr {g : α -> β} (H : forall x in s, f x = g x
) : s.fold op b f = s.fold op b g
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
-/
theorem sup_congr {f g : β → α} (hs : s₁ = s₂) (hfg : ∀ a ∈ s₂, f a = g a) :
    s₁.sup f = s₂.sup g := by
  subst hs
  exact Finset.fold_congr hfg

@[to_dual (attr := simp)]
/-
**Finset._root_.map_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.map_finset_sup [SemilatticeSup β] [OrderBot β]
    [FunLike F α β] [SupBotHomClass F α β]
    (f : F) (s : Finset ι) (g : ι → α) : f (s.sup g) = s.sup (f ∘ g) :=
  Finset.cons_induction_on s (map_bot f) fun i s _ h => by
    rw [sup_cons, sup_cons, map_sup, h, Function.comp_apply]

@[to_dual (attr := simp) le_inf_iff]
/-
**Finset.sup_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] [inst_1 : OrderB
ot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀ b ∈ s, f b ≤ a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.sup_le`：sup_le {s : Multiset α} {a : α} : s.sup <= a ↔ forall b
 in s, b <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
protected theorem sup_le_iff {a : α} : s.sup f ≤ a ↔ ∀ b ∈ s, f b ≤ a := by
  apply Iff.trans Multiset.sup_le
  simp only [Multiset.mem_map, and_imp, exists_imp]
  exact ⟨fun k b hb => k _ _ hb rfl, fun k a' b hb h => h ▸ k _ hb⟩

@[to_dual le_inf] protected alias ⟨_, sup_le⟩ := Finset.sup_le_iff

@[to_dual le_inf_const]
/-
**Finset.sup_const_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_const_le : (s.sup fun _ => a) <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sup_const_le : (s.sup fun _ => a) ≤ a :=
  Finset.sup_le fun _ _ => le_rfl

@[deprecated (since := "2026-03-25")] alias le_inf_const_le := le_inf_const

@[to_dual inf_le]
/-
**Finset.le_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_sup {b : β} (hb : b in s) : f b <= s.sup f
参数：hb : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_sup {b : β} (hb : b ∈ s) : f b ≤ s.sup f :=
  Finset.sup_le_iff.1 le_rfl _ hb

@[to_dual]
/-
**Finset.isLUB_sup** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：isLUB_sup : IsLUB (f '' s) (s.sup f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma isLUB_sup : IsLUB (f '' s) (s.sup f) := by
  simp +contextual [IsLUB, IsLeast, upperBounds, lowerBounds, le_sup]

@[to_dual]
/-
**Finset.isLUB_sup_id** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：isLUB_sup_id {s : Finset α} : IsLUB s (s.sup id)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用引理 `Finset.isLUB_sup`：isLUB_sup : IsLUB (f '' s) (s.sup f)
-/
lemma isLUB_sup_id {s : Finset α} : IsLUB s (s.sup id) := by simpa using isLUB_sup (f := id)

@[to_dual inf_le_of_le]
/-
**Finset.le_sup_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_sup_of_le {b : β} (hb : b in s) (h : a <= f b) : a <= s.sup f
参数：hb : b in s；h : a <= f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem le_sup_of_le {b : β} (hb : b ∈ s) (h : a ≤ f b) : a ≤ s.sup f := h.trans <| le_sup hb

@[to_dual (attr := grind _=_)]
/-
**Finset.sup_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.sup f ⊔ s₂.sup f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_union [DecidableEq β] : (s₁ ∪ s₂).sup f = s₁.sup f ⊔ s₂.sup f :=
  eq_of_forall_ge_iff fun c => by simp [or_imp, forall_and]

@[to_dual]
/-
**Finset.sup_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.sup fun _ => c) = c
参数：h : s.Nonempty；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `Finset.Nonempty.forall_const`：∀ {α : Type u_1} {s : Finset α}, s.Nonempt
y → ∀ {p : Prop}, (∀ x ∈ s, p) ↔ p
-/
theorem sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s.sup fun _ => c) = c :=
  eq_of_forall_ge_iff (fun _ => Finset.sup_le_iff.trans h.forall_const)

@[to_dual (attr := simp)]
/-
**Finset.sup_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α)
参数：s : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_const`：sup_const {s : Finset β} (h : s.Nonempty) (c : α) : (s
.sup fun _ => c) = c
-/
theorem sup_bot (s : Finset β) : (s.sup fun _ => ⊥) = (⊥ : α) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · exact sup_empty
  · exact sup_const hs _

@[to_dual]
/-
**Finset.sup_ite** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_ite (p : β -> Prop) [DecidablePred p] : (s.sup fun i => ite (p i) (f i
) (g i)) = (s.filter p).sup f ⊔ (s.filter fun i => ¬p i).sup g
参数：p : β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.fold_ite`：fold_ite [Std.IdempotentOp op] {g : α -> β} (p : α -> P
rop) [DecidablePred p] : Finset.fold op b (fun i => ite (p i) (f i) (g i)) s = o
p (Fi…
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
-/
theorem sup_ite (p : β → Prop) [DecidablePred p] :
    (s.sup fun i => ite (p i) (f i) (g i)) = (s.filter p).sup f ⊔ (s.filter fun i => ¬p i).sup g :=
  fold_ite _

@[to_dual (attr := gcongr, grind ←)]
/-
**Finset.sup_mono_fun** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_mono_fun {g : β -> α} (h : forall b in s, f b <= g b) : s.sup f <= s.s
up g
参数：h : forall b in s, f b <= g b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem sup_mono_fun {g : β → α} (h : ∀ b ∈ s, f b ≤ g b) : s.sup f ≤ s.sup g :=
  Finset.sup_le fun b hb => le_trans (h b hb) (le_sup hb)

@[to_dual (attr := gcongr, grind ←)]
/-
**Finset.sup_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
参数：h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem sup_mono (h : s₁ ⊆ s₂) : s₁.sup f ≤ s₂.sup f :=
  Finset.sup_le (fun _ hb => le_sup (h hb))

@[to_dual]
/-
**Finset.sup_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] [
inst_1 : OrderBot α] (s : Finset β)   (t : Finset γ) (f : β → γ → α), (s.sup fun
 b => t.sup (f b)) = t.sup fun c => s.sup fun b => f b c
参数：s : Finset β；t : Finset γ；f : β → γ → α；s.sup fun b => t.sup (f b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
protected theorem sup_comm (s : Finset β) (t : Finset γ) (f : β → γ → α) :
    (s.sup fun b => t.sup (f b)) = t.sup fun c => s.sup fun b => f b c :=
  eq_of_forall_ge_iff fun a => by simpa using forall₂_comm

@[to_dual (attr := simp)]
/-
**Finset.sup_attach** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_attach (s : Finset β) (f : β -> α) : (s.attach.sup fun x => f x) = s.s
up f
参数：s : Finset β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup_map`：sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map
 f).sup g = s.sup (g ∘ f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `Finset.attach_map_val`：attach_map_val {s : Finset α} : s.attach.map (Emb
edding.subtype _) = s
-/
theorem sup_attach (s : Finset β) (f : β → α) : (s.attach.sup fun x => f x) = s.sup f :=
  (s.attach.sup_map (Function.Embedding.subtype _) f).symm.trans <| congr_arg _ attach_map_val

@[to_dual (attr := simp)]
/-
**Finset.sup_erase_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup 
id
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
-/
theorem sup_erase_bot [DecidableEq α] (s : Finset α) : (s.erase ⊥).sup id = s.sup id := by
  refine (sup_mono (s.erase_subset _)).antisymm (Finset.sup_le_iff.2 fun a ha => ?_)
  obtain rfl | ha' := eq_or_ne a ⊥
  · exact bot_le
  · exact le_sup (mem_erase.2 ⟨ha', ha⟩)
/-
**Finset.sup_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_sdiff_right {α β : Type*} [GeneralizedBooleanAlgebra α] (s : Finset β)
 (f : β -> α) (a : α) : (s.sup fun b => f b \ a) = s.sup f \ a
参数：s : Finset β；f : β -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `bot_sdiff`：∀ {α : Type u_2} [inst : GeneralizedCoheytingAlgebra α] {a : 
α}, ⊥ \ a = ⊥
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `sup_sdiff`：sup_sdiff : (a ⊔ b) \ c = a \ c ⊔ b \ c
-/
theorem sup_sdiff_right {α β : Type*} [GeneralizedBooleanAlgebra α] (s : Finset β) (f : β → α)
    (a : α) : (s.sup fun b => f b \ a) = s.sup f \ a := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, sup_empty, bot_sdiff]
  | cons _ _ _ h => rw [sup_cons, sup_cons, h, sup_sdiff]

@[to_dual]
/-
**Finset.apply_sup_eq_sup_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：apply_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : 
β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥)
 : g (s.sup f) = s.sup (g ∘ f)
参数：g : α -> γ；g_sup : forall x y, g (x ⊔ y) = g x ⊔ g y；bot : g ⊥ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem apply_sup_eq_sup_comp [SemilatticeSup γ] [OrderBot γ] {s : Finset β} {f : β → α} (g : α → γ)
    (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  Finset.cons_induction_on s bot fun c t hc ih => by
    rw [sup_cons, sup_cons, g_sup, ih, Function.comp_apply]

@[deprecated (since := "2026-05-29")]
alias comp_sup_eq_sup_comp := apply_sup_eq_sup_comp

@[deprecated (since := "2026-05-29")]
alias comp_inf_eq_inf_comp := apply_inf_eq_inf_comp

/-- Computing `sup` in a subtype (closed under `sup`) is the same as computing it in `α`. -/
@[to_dual (rename := Pbot → Ptop, Psup → Pinf)
/-- Computing `inf` in a subtype (closed under `inf`) is the same as computing it in `α`. -/]
/-
**Finset.sup_coe** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_coe {P : α -> Prop} {Pbot : P ⊥} {Psup : forall ⦃x y⦄, P x -> P y -> P
 (x ⊔ y)} (t : Finset β) (f : β -> { x : α // P x }) : letI
参数：x ⊔ y；t : Finset β；f : β -> { x : α // P x }。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
-/
theorem sup_coe {P : α → Prop} {Pbot : P ⊥} {Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)} (t : Finset β)
    (f : β → { x : α // P x }) :
    letI := Subtype.semilatticeSup Psup
    letI := Subtype.orderBot Pbot
    (t.sup f).val = t.sup fun x => ↑(f x) := by
  let := Subtype.semilatticeSup Psup
  let := Subtype.orderBot Pbot
  apply apply_sup_eq_sup_comp Subtype.val <;> intros <;> rfl

@[simp]
/-
**Finset.sup_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_toFinset {α β} [DecidableEq β] (s : Finset α) (f : α -> Multiset β) : 
(s.sup f).toFinset = s.sup fun x => (f x).toFinset
参数：s : Finset α；f : α -> Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
· 使用定理 `Multiset.toFinset_union`：toFinset_union (s t : Multiset α) : (s union t)
.toFinset = s.toFinset union t.toFinset
-/
theorem sup_toFinset {α β} [DecidableEq β] (s : Finset α) (f : α → Multiset β) :
    (s.sup f).toFinset = s.sup fun x => (f x).toFinset :=
  apply_sup_eq_sup_comp Multiset.toFinset toFinset_union rfl

@[to_dual]
/-
**Finset._root_.List.foldr_sup_eq_sup_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finset
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.List.foldr_sup_eq_sup_toFinset [DecidableEq α] (l : List α) :
    l.foldr (· ⊔ ·) ⊥ = l.toFinset.sup id := by
  rw [← coe_fold_r, ← Multiset.fold_dedup_idem, sup_def, ← List.toFinset_coe, toFinset_val,
    Multiset.map_id]
  rfl
/-
**Finset.subset_range_sup_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：subset_range_sup_succ (s : Finset Nat) : s subseteq range (s.sup id).succ
参数：s : Finset Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem subset_range_sup_succ (s : Finset ℕ) : s ⊆ range (s.sup id).succ := fun _ hn =>
  mem_range.2 <| Nat.lt_succ_of_le <| @le_sup _ _ _ _ _ id _ hn

@[to_dual]
/-
**Finset.sup_induction** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_induction {p : α -> Prop} (hb : p ⊥) (hp : forall a₁, p a₁ -> forall a
₂, p a₂ -> p (a₁ ⊔ a₂)) (hs : forall b in s, p (f b)) : p (s.sup f)
参数：hb : p ⊥；hp : forall a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂)；hs : forall b
 in s, p (f b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sup_induction {p : α → Prop} (hb : p ⊥) (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup f) := by
  induction s using Finset.cons_induction with
  | empty => exact hb
  | cons _ _ _ ih =>
    simp only [sup_cons, forall_mem_cons] at hs ⊢
    exact hp _ hs.1 _ (ih hs.2)

@[to_dual le_inf_of_directed_le]
/-
**Finset.sup_le_of_le_directed** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_le_of_le_directed {α : Type*} [SemilatticeSup α] [OrderBot α] (s : Set
 α) (hs : s.Nonempty) (hdir : DirectedOn (· <= ·) s) (t : Finset α) : (forall x 
in t, exists y in s, x <= y) -> exists x in s, t.sup id <= x
参数：s : Set α；hs : s.Nonempty；hdir : DirectedOn (· <= ·) s；t : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Finset.coe_subset`：coe_subset {s₁ s₂ : Finset α} : (s₁ : Set α) subseteq
 s₂ ↔ s₁ subseteq s₂
· 使用定理 `Finset.subset_insert`：∀ {α : Type u_1} [inst : DecidableEq α] (a : α) (s
 : Finset α), s ⊆ insert a s
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
theorem sup_le_of_le_directed {α : Type*} [SemilatticeSup α] [OrderBot α] (s : Set α)
    (hs : s.Nonempty) (hdir : DirectedOn (· ≤ ·) s) (t : Finset α) :
    (∀ x ∈ t, ∃ y ∈ s, x ≤ y) → ∃ x ∈ s, t.sup id ≤ x := by
  classical
    induction t using Finset.induction_on with
    | empty =>
      simpa only [forall_prop_of_true, and_true, forall_prop_of_false, bot_le, not_false_iff,
        sup_empty, forall_true_iff, notMem_empty]
    | insert a r _ ih =>
      intro h
      have incs : (r : Set α) ⊆ ↑(insert a r) := by
        rw [Finset.coe_subset]
        apply Finset.subset_insert
      -- x ∈ s is above the sup of r
      obtain ⟨x, ⟨hxs, hsx_sup⟩⟩ := ih fun x hx => h x <| incs hx
      -- y ∈ s is above a
      obtain ⟨y, hys, hay⟩ := h a (Finset.mem_insert_self a r)
      -- z ∈ s is above x and y
      obtain ⟨z, hzs, ⟨hxz, hyz⟩⟩ := hdir x hxs y hys
      use z, hzs
      rw [sup_insert, id, sup_le_iff]
      exact ⟨le_trans hay hyz, le_trans hsx_sup hxz⟩

-- If we acquire sublattices
-- the hypotheses should be reformulated as `s : SubsemilatticeSupBot`
@[to_dual]
/-
**Finset.sup_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_mem (s : Set α) (w₁ : ⊥ in s) (w₂ : forallᵉ (x in s) (y in s), x ⊔ y i
n s) {ι : Type*} (t : Finset ι) (p : ι -> α) (h : forall i in t, p i in s) : t.s
up p in s
参数：s : Set α；w₁ : ⊥ in s；w₂ : forallᵉ (x in s) (y in s), x ⊔ y in s；t : Finset ι
；p : ι -> α；h : forall i in t, p i in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_induction`：sup_induction {p : α -> Prop} (hb : p ⊥) (hp : for
all a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂)) (hs : forall b in s, p (f b)) : 
p (s.sup f…
-/
theorem sup_mem (s : Set α) (w₁ : ⊥ ∈ s) (w₂ : ∀ᵉ (x ∈ s) (y ∈ s), x ⊔ y ∈ s)
    {ι : Type*} (t : Finset ι) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup p ∈ s :=
  @sup_induction _ _ _ _ _ _ (· ∈ s) w₁ w₂ h

@[to_dual (attr := simp)]
/-
**Finset.sup_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] [inst_1 : OrderB
ot α] (f : β → α) (S : Finset β),   S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥
参数：f : β → α；S : Finset β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
-/
protected theorem sup_eq_bot_iff (f : β → α) (S : Finset β) : S.sup f = ⊥ ↔ ∀ s ∈ S, f s = ⊥ := by
  classical induction S using Finset.induction <;> simp [*]

@[to_additive (attr := simp)]
/-
**Finset.sup_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_eq_one [One α] [IsBotOneClass α] : s.sup f = 1 ↔ forall i in s, f i = 
1
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
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sup_eq_one [One α] [IsBotOneClass α] : s.sup f = 1 ↔ ∀ i ∈ s, f i = 1 := by
  simp [← bot_eq_one]

@[to_dual (attr := simp)]
/-
**Finset.sup_disjSum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_disjSum (s : Finset β) (t : Finset γ) (f : β oplus γ -> α) : (s.disjSu
m t).sup f = (s.sup fun x => f (.inl x)) ⊔ (t.sup fun x => f (.inr x))
参数：s : Finset β；t : Finset γ；f : β oplus γ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用引理 `Finset.fold_disjSum`：fold_disjSum (s : Finset α) (t : Finset β) (f : α o
plus β -> γ) (b₁ b₂ : γ) (op : γ -> γ -> γ) [Std.Commutative op] [Std.Associativ
e op] : (…
-/
lemma sup_disjSum (s : Finset β) (t : Finset γ) (f : β ⊕ γ → α) :
    (s.disjSum t).sup f = (s.sup fun x ↦ f (.inl x)) ⊔ (t.sup fun x ↦ f (.inr x)) :=
  congr(fold _ $(bot_sup_eq _ |>.symm) _ _).trans (fold_disjSum _ _ _ _ _ _)

@[to_dual (attr := simp)]
/-
**Finset.sup_eq_bot_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_eq_bot_of_isEmpty [IsEmpty β] (f : β -> α) (S : Finset β) : S.sup f = 
⊥
参数：f : β -> α；S : Finset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_bot_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatti
ceSup α] [inst_1 : OrderBot α] (f : β → α) (S : Finset β),   S.sup f = ⊥ ↔ ∀ s ∈
 S, f s = ⊥
· 使用定理 `IsEmpty.false`：∀ {α : Sort u} [self : IsEmpty α] (a : α), False
-/
theorem sup_eq_bot_of_isEmpty [IsEmpty β] (f : β → α) (S : Finset β) : S.sup f = ⊥ := by
  rw [Finset.sup_eq_bot_iff]
  exact fun x _ => False.elim <| IsEmpty.false x

@[to_dual inf_dite_pos_le]
/-
**Finset.le_sup_dite_pos** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_sup_dite_pos (p : β -> Prop) [DecidablePred p] {f : (b : β) -> p b -> α
} {g : (b : β) -> ¬p b -> α} {b : β} (h₀ : b in s) (h₁ : p b) : f b h₁ <= s.sup 
fun i => if h : p i then f i h else g i h
参数：p : β -> Prop；b : β；b : β；h₀ : b in s；h₁ : p b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_sup_dite_pos (p : β → Prop) [DecidablePred p]
    {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β} (h₀ : b ∈ s) (h₁ : p b) :
    f b h₁ ≤ s.sup fun i ↦ if h : p i then f i h else g i h := by
  grind [le_sup_of_le]

@[to_dual inf_dite_neg_le]
/-
**Finset.le_sup_dite_neg** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_sup_dite_neg (p : β -> Prop) [DecidablePred p] {f : (b : β) -> p b -> α
} {g : (b : β) -> ¬p b -> α} {b : β} (h₀ : b in s) (h₁ : ¬p b) : g b h₁ <= s.sup
 fun i => if h : p i then f i h else g i h
参数：p : β -> Prop；b : β；b : β；h₀ : b in s；h₁ : ¬p b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_sup_dite_neg (p : β → Prop) [DecidablePred p]
    {f : (b : β) → p b → α} {g : (b : β) → ¬p b → α} {b : β} (h₀ : b ∈ s) (h₁ : ¬p b) :
    g b h₁ ≤ s.sup fun i ↦ if h : p i then f i h else g i h := by
  grind [le_sup_of_le]

end Sup

@[to_dual]
/-
**Finset.sup_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : α -> β) : s.sup f = ⨆ 
a in s, f a
参数：s : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : α → β) : s.sup f = ⨆ a ∈ s, f a :=
  le_antisymm
    (Finset.sup_le (fun a ha => le_iSup_of_le a <| le_iSup (fun _ => f a) ha))
    (iSup_le fun _ => iSup_le fun ha => le_sup ha)

@[to_dual]
/-
**Finset.sup_id_eq_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_id_eq_sSup [CompleteLattice α] (s : Finset α) : s.sup id = sSup s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `sSup_eq_iSup`：sSup_eq_iSup {s : Set α} : sSup s = ⨆ a in s, a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_id_eq_sSup [CompleteLattice α] (s : Finset α) : s.sup id = sSup s := by
  simp [sSup_eq_iSup, sup_eq_iSup]
/-
**Finset.sup_id_set_eq_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_id_set_eq_sUnion (s : Finset (Set α)) : s.sup id = ⋃₀ ↑s
参数：s : Finset (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
-/
theorem sup_id_set_eq_sUnion (s : Finset (Set α)) : s.sup id = ⋃₀ ↑s :=
  sup_id_eq_sSup _
/-
**Finset.inf_id_set_eq_sInter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_id_set_eq_sInter (s : Finset (Set α)) : s.inf id = ⋂₀ ↑s
参数：s : Finset (Set α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_id_eq_sInf`：∀ {α : Type u_2} [inst : CompleteLattice α] (s : 
Finset α), s.inf id = sInf ↑s
-/
theorem inf_id_set_eq_sInter (s : Finset (Set α)) : s.inf id = ⋂₀ ↑s :=
  inf_id_eq_sInf _

@[simp]
/-
**Finset.sup_set_eq_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_set_eq_biUnion (s : Finset α) (f : α -> Set β) : s.sup f = ⋃ x in s, f
 x
参数：s : Finset α；f : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
-/
theorem sup_set_eq_biUnion (s : Finset α) (f : α → Set β) : s.sup f = ⋃ x ∈ s, f x :=
  sup_eq_iSup _ _

@[simp]
/-
**Finset.inf_set_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_set_eq_iInter (s : Finset α) (f : α -> Set β) : s.inf f = ⋂ x in s, f 
x
参数：s : Finset α；f : α -> Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a
-/
theorem inf_set_eq_iInter (s : Finset α) (f : α → Set β) : s.inf f = ⋂ x ∈ s, f x :=
  inf_eq_iInf _ _

@[to_dual]
/-
**Finset.sup_eq_sSup_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_eq_sSup_image [CompleteLattice β] (s : Finset α) (f : α -> β) : s.sup 
f = sSup (f '' s)
参数：s : Finset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)
· 使用定理 `Function.id_comp`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), id ∘ f = 
f
-/
theorem sup_eq_sSup_image [CompleteLattice β] (s : Finset α) (f : α → β) :
    s.sup f = sSup (f '' s) := by
  classical rw [← Finset.coe_image, ← sup_id_eq_sSup, sup_image, Function.id_comp]

@[to_dual exists_inf_le]
/-
**Finset.exists_sup_ge** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_sup_ge [SemilatticeSup β] [OrderBot β] [WellFoundedGT β] (f : α -> 
β) : exists t : Finset α, forall a, f a <= t.sup f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `wellFounded_gt`：∀ {α : Type u} [inst : LT α] [WellFoundedGT α], WellFoun
ded fun x1 x2 => x2 < x1
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `right_lt_sup`：right_lt_sup : b < a ⊔ b ↔ ¬a <= b
-/
theorem exists_sup_ge [SemilatticeSup β] [OrderBot β] [WellFoundedGT β] (f : α → β) :
    ∃ t : Finset α, ∀ a, f a ≤ t.sup f := by
  cases isEmpty_or_nonempty α
  · exact ⟨⊥, isEmptyElim⟩
  obtain ⟨_, ⟨t, rfl⟩, ht⟩ := wellFounded_gt.has_min _ (Set.range_nonempty (sup · f))
  refine ⟨t, fun a ↦ ?_⟩
  classical
  have := ht (f a ⊔ t.sup f) ⟨insert a t, by simp⟩
  rwa [right_lt_sup, not_not] at this

@[to_dual]
/-
**Finset.exists_sup_eq_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_sup_eq_iSup [CompleteLattice β] [WellFoundedGT β] (f : α -> β) : ex
ists t : Finset α, t.sup f = ⨆ a, f a
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_sup_ge`：exists_sup_ge [SemilatticeSup β] [OrderBot β] [Wel
lFoundedGT β] (f : α -> β) : exists t : Finset α, forall a, f a <= t.sup f
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
-/
theorem exists_sup_eq_iSup [CompleteLattice β] [WellFoundedGT β] (f : α → β) :
    ∃ t : Finset α, t.sup f = ⨆ a, f a :=
  have ⟨t, ht⟩ := exists_sup_ge f
  ⟨t, (Finset.sup_le fun _ _ ↦ le_iSup ..).antisymm <| iSup_le ht⟩

@[to_dual (attr := simp)]
/-
**Finset.toDual_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toDual_sup [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β -> α) : t
oDual (s.sup f) = s.inf (toDual ∘ f)
参数：s : Finset β；f : β -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toDual_sup [SemilatticeSup α] [OrderBot α] (s : Finset β) (f : β → α) :
    toDual (s.sup f) = s.inf (toDual ∘ f) :=
  rfl

@[to_dual (attr := simp)]
/-
**Finset.ofDual_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ofDual_sup [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β -> αᵒᵈ) :
 ofDual (s.sup f) = s.inf (ofDual ∘ f)
参数：s : Finset β；f : β -> αᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofDual_sup [SemilatticeInf α] [OrderTop α] (s : Finset β) (f : β → αᵒᵈ) :
    ofDual (s.sup f) = s.inf (ofDual ∘ f) :=
  rfl

section DistribLattice

variable [DistribLattice α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α} {a : α}

@[to_dual]
/-
**Finset.sup_inf_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_inf_distrib_left (s : Finset ι) (f : ι -> α) (a : α) : a ⊓ s.sup f = s
.sup fun i => a ⊓ f i
参数：s : Finset ι；f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
-/
theorem sup_inf_distrib_left (s : Finset ι) (f : ι → α) (a : α) :
    a ⊓ s.sup f = s.sup fun i => a ⊓ f i := by
  induction s using Finset.cons_induction with
  | empty => simp_rw [Finset.sup_empty, inf_bot_eq]
  | cons _ _ _ h => rw [sup_cons, sup_cons, inf_sup_left, h]

@[to_dual]
/-
**Finset.sup_inf_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_inf_distrib_right (s : Finset ι) (f : ι -> α) (a : α) : s.sup f ⊓ a = 
s.sup fun i => f i ⊓ a
参数：s : Finset ι；f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Finset.sup_inf_distrib_left`：sup_inf_distrib_left (s : Finset ι) (f : ι 
-> α) (a : α) : a ⊓ s.sup f = s.sup fun i => a ⊓ f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup_inf_distrib_right (s : Finset ι) (f : ι → α) (a : α) :
    s.sup f ⊓ a = s.sup fun i => f i ⊓ a := by
  rw [_root_.inf_comm, s.sup_inf_distrib_left]
  simp_rw [_root_.inf_comm]

@[to_dual]
/-
**Finset.disjoint_sup_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : DistribLattice α] [inst_1 : OrderB
ot α] {s : Finset ι} {f : ι → α} {a : α},   Disjoint a (s.sup f) ↔ ∀ ⦃i : ι⦄, i 
∈ s → Disjoint a (f i)
参数：s.sup f。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_inf_distrib_left`：sup_inf_distrib_left (s : Finset ι) (f : ι 
-> α) (a : α) : a ⊓ s.sup f = s.sup fun i => a ⊓ f i
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem disjoint_sup_right : Disjoint a (s.sup f) ↔ ∀ ⦃i⦄, i ∈ s → Disjoint a (f i) := by
  simp only [disjoint_iff, sup_inf_distrib_left, Finset.sup_eq_bot_iff]

@[to_dual]
/-
**Finset.disjoint_sup_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : DistribLattice α] [inst_1 : OrderB
ot α] {s : Finset ι} {f : ι → α} {a : α},   Disjoint (s.sup f) a ↔ ∀ ⦃i : ι⦄, i 
∈ s → Disjoint (f i) a
参数：s.sup f。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_inf_distrib_right`：sup_inf_distrib_right (s : Finset ι) (f : 
ι -> α) (a : α) : s.sup f ⊓ a = s.sup fun i => f i ⊓ a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
protected theorem disjoint_sup_left : Disjoint (s.sup f) a ↔ ∀ ⦃i⦄, i ∈ s → Disjoint (f i) a := by
  simp only [disjoint_iff, sup_inf_distrib_right, Finset.sup_eq_bot_iff]

end OrderBot

end DistribLattice

section BooleanAlgebra

variable [BooleanAlgebra α] {s : Finset ι}

/-
**Finset.sup_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_sdiff_left (s : Finset ι) (f : ι -> α) (a : α) : (s.sup fun b => a \ f
 b) = a \ s.inf f
参数：s : Finset ι；f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `Finset.inf_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] [inst_1 : OrderTop α] {f : β → α}, ∅.inf f = ⊤
· 使用定理 `sdiff_top`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), a \ ⊤ =
 ⊥
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `Finset.inf_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf 
α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β}   (h : b ∉ s), (Fins
et.co…
· 使用定理 `sdiff_inf`：sdiff_inf : a \ (b ⊓ c) = a \ b ⊔ a \ c
-/
theorem sup_sdiff_left (s : Finset ι) (f : ι → α) (a : α) :
    (s.sup fun b => a \ f b) = a \ s.inf f := by
  induction s using Finset.cons_induction with
  | empty => rw [sup_empty, inf_empty, sdiff_top]
  | cons _ _ _ h => rw [sup_cons, inf_cons, h, sdiff_inf]
/-
**Finset.inf_sdiff_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_sdiff_left (hs : s.Nonempty) (f : ι -> α) (a : α) : (s.inf fun b => a 
\ f b) = a \ s.sup f
参数：hs : s.Nonempty；f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `Finset.inf_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eInf α] [inst_1 : OrderTop α] {f : β → α} {b : β}, {b}.inf f = f b
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `Finset.inf_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf 
α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β}   (h : b ∉ s), (Fins
et.co…
· 使用定理 `sdiff_sup`：sdiff_sup : y \ (x ⊔ z) = y \ x ⊓ y \ z
-/
theorem inf_sdiff_left (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.inf fun b => a \ f b) = a \ s.sup f := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [sup_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [sup_cons, inf_cons, ih, sdiff_sup]
/-
**Finset.inf_sdiff_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_sdiff_right (hs : s.Nonempty) (f : ι -> α) (a : α) : (s.inf fun b => f
 b \ a) = s.inf f \ a
参数：hs : s.Nonempty；f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.inf_singleton`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eInf α] [inst_1 : OrderTop α] {f : β → α} {b : β}, {b}.inf f = f b
· 使用定理 `Finset.inf_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf 
α] [inst_1 : OrderTop α] {s : Finset β} {f : β → α} {b : β}   (h : b ∉ s), (Fins
et.co…
· 使用定理 `inf_sdiff`：inf_sdiff : (x ⊓ y) \ z = x \ z ⊓ y \ z
-/
theorem inf_sdiff_right (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.inf fun b => f b \ a) = s.inf f \ a := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => rw [inf_singleton, inf_singleton]
  | cons _ _ _ _ ih => rw [inf_cons, inf_cons, ih, inf_sdiff]
/-
**Finset.inf_himp_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：inf_himp_right (s : Finset ι) (f : ι -> α) (a : α) : (s.inf fun b => f b ⇨
 a) = s.sup f ⇨ a
参数：s : Finset ι；f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup_sdiff_left`：sup_sdiff_left (s : Finset ι) (f : ι -> α) (a : α
) : (s.sup fun b => a \ f b) = a \ s.inf f
-/
theorem inf_himp_right (s : Finset ι) (f : ι → α) (a : α) :
    (s.inf fun b => f b ⇨ a) = s.sup f ⇨ a :=
  @sup_sdiff_left αᵒᵈ _ _ _ _ _
/-
**Finset.sup_himp_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_himp_right (hs : s.Nonempty) (f : ι -> α) (a : α) : (s.sup fun b => f 
b ⇨ a) = s.inf f ⇨ a
参数：hs : s.Nonempty；f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_sdiff_left`：inf_sdiff_left (hs : s.Nonempty) (f : ι -> α) (a 
: α) : (s.inf fun b => a \ f b) = a \ s.sup f
-/
theorem sup_himp_right (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.sup fun b => f b ⇨ a) = s.inf f ⇨ a :=
  @inf_sdiff_left αᵒᵈ _ _ _ hs _ _
/-
**Finset.sup_himp_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_himp_left (hs : s.Nonempty) (f : ι -> α) (a : α) : (s.sup fun b => a ⇨
 f b) = a ⇨ s.sup f
参数：hs : s.Nonempty；f : ι -> α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.inf_sdiff_right`：inf_sdiff_right (hs : s.Nonempty) (f : ι -> α) (
a : α) : (s.inf fun b => f b \ a) = s.inf f \ a
-/
theorem sup_himp_left (hs : s.Nonempty) (f : ι → α) (a : α) :
    (s.sup fun b => a ⇨ f b) = a ⇨ s.sup f :=
  @inf_sdiff_right αᵒᵈ _ _ _ hs _ _

@[simp]
/-
**Finset.compl_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : BooleanAlgebra α] (s : Finset ι) (
f : ι → α), (s.sup f)ᶜ = s.inf fun i => (f i)ᶜ
参数：s : Finset ι；f : ι → α；s.sup f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeSup α] [inst_1 : OrderBot α]   [inst_2 : SemilatticeSup
 β] …
· 使用定理 `OrderIsoClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : OrderBot
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
protected theorem compl_sup (s : Finset ι) (f : ι → α) : (s.sup f)ᶜ = s.inf fun i => (f i)ᶜ :=
  map_finset_sup (OrderIso.compl α) _ _

@[simp]
/-
**Finset.compl_inf** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : BooleanAlgebra α] (s : Finset ι) (
f : ι → α), (s.inf f)ᶜ = s.sup fun i => (f i)ᶜ
参数：s : Finset ι；f : ι → α；s.inf f；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_inf`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Type
 u_5} [inst : SemilatticeInf α] [inst_1 : OrderTop α]   [inst_2 : SemilatticeInf
 β] …
· 使用定理 `OrderIsoClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : OrderTop
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
protected theorem compl_inf (s : Finset ι) (f : ι → α) : (s.inf f)ᶜ = s.sup fun i => (f i)ᶜ :=
  map_finset_inf (OrderIso.compl α) _ _

end BooleanAlgebra

section LinearOrder

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {s : Finset ι} {f : ι → α} {a : α}

@[to_dual]
/-
**Finset.apply_sup_eq_sup_comp_of_linearOrder** 是 Mathlib 中的一个定理，位于命名空间 `Finset`
。
形式化陈述：apply_sup_eq_sup_comp_of_linearOrder [SemilatticeSup β] [OrderBot β] (g : 
α -> β) (mono_g : Monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f)
参数：g : α -> β；mono_g : Monotone g；bot : g ⊥ = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
· 使用定理 `Monotone.map_sup`：map_sup [SemilatticeSup β] {f : α -> β} (hf : Monotone
 f) (x y : α) : f (x ⊔ y) = f x ⊔ f y
-/
theorem apply_sup_eq_sup_comp_of_linearOrder [SemilatticeSup β] [OrderBot β] (g : α → β)
    (mono_g : Monotone g) (bot : g ⊥ = ⊥) : g (s.sup f) = s.sup (g ∘ f) :=
  apply_sup_eq_sup_comp g mono_g.map_sup bot

@[deprecated (since := "2026-05-29")]
alias comp_sup_eq_sup_comp_of_is_total := apply_sup_eq_sup_comp_of_linearOrder

@[deprecated (since := "2026-05-29")]
alias comp_inf_eq_inf_comp_of_is_total := apply_inf_eq_inf_comp_of_linearOrder

@[to_dual (attr := simp) inf_le_iff]
/-
**Finset.le_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α] [inst_1 : OrderBot 
α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b
)
参数：a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `le_sup_iff`：le_sup_iff : a <= b ⊔ c ↔ a <= b ∨ a <= c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
protected theorem le_sup_iff (ha : ⊥ < a) : a ≤ s.sup f ↔ ∃ b ∈ s, a ≤ f b := by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · (not_le_of_gt ha))
    | cons c t hc ih =>
      rw [sup_cons, le_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hle⟩ := ih h; ⟨b, mem_cons.2 (Or.inr hb), hle⟩
  · exact fun ⟨b, hb, hle⟩ => le_trans hle (le_sup hb)

@[to_dual]
/-
**Finset.sup_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_5} {α : Type u_7} [inst : LinearOrder α] [inst_1 : BoundedOr
der α] [Nontrivial α] {s : Finset ι}   {f : ι → α}, s.sup f = ⊤ ↔ ∃ b ∈ s, f b =
 ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.le_sup_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (a ≤ s.sup
 f ↔ ∃ …
· 使用定理 `bot_lt_top`：bot_lt_top : (⊥ : α) < ⊤
-/
protected theorem sup_eq_top_iff {α : Type*} [LinearOrder α] [BoundedOrder α] [Nontrivial α]
    {s : Finset ι} {f : ι → α} : s.sup f = ⊤ ↔ ∃ b ∈ s, f b = ⊤ := by
  simp only [← top_le_iff]
  exact Finset.le_sup_iff bot_lt_top

@[to_dual]
/-
**Finset.Nonempty.sup_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Nonempty`。
形式化陈述：∀ {ι : Type u_5} {α : Type u_7} [inst : LinearOrder α] [inst_1 : BoundedOr
der α] {s : Finset ι} {f : ι → α},   s.Nonempty → (s.sup f = ⊤ ↔ ∃ b ∈ s, f b = 
⊤)
参数：s.sup f = ⊤ ↔ ∃ b ∈ s, f b = ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Finset.sup_eq_top_iff`：∀ {ι : Type u_5} {α : Type u_7} [inst : LinearOrd
er α] [inst_1 : BoundedOrder α] [Nontrivial α] {s : Finset ι}   {f : ι → α}, s.s
up f = ⊤ ↔ …
-/
protected theorem Nonempty.sup_eq_top_iff {α : Type*} [LinearOrder α] [BoundedOrder α]
    {s : Finset ι} {f : ι → α} (hs : s.Nonempty) : s.sup f = ⊤ ↔ ∃ b ∈ s, f b = ⊤ := by
  cases subsingleton_or_nontrivial α
  · simpa [Subsingleton.elim _ (⊤ : α)]
  · exact Finset.sup_eq_top_iff

@[to_dual (attr := simp) inf_lt_iff]
/-
**Finset.lt_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α] [inst_1 : OrderBot 
α] {s : Finset ι} {f : ι → α} {a : α},   a < s.sup f ↔ ∃ b ∈ s, a < f b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `lt_sup_iff`：lt_sup_iff : a < b ⊔ c ↔ a < b ∨ a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
protected theorem lt_sup_iff : a < s.sup f ↔ ∃ b ∈ s, a < f b := by
  apply Iff.intro
  · induction s using cons_induction with
    | empty => exact (absurd · not_lt_bot)
    | cons c t hc ih =>
      rw [sup_cons, lt_sup_iff]
      exact fun
      | Or.inl h => ⟨c, mem_cons.2 (Or.inl rfl), h⟩
      | Or.inr h => let ⟨b, hb, hlt⟩ := ih h; ⟨b, mem_cons.2 (Or.inr hb), hlt⟩
  · exact fun ⟨b, hb, hlt⟩ => lt_of_lt_of_le hlt (le_sup hb)

@[to_dual (attr := simp) lt_inf_iff]
/-
**Finset.sup_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α] [inst_1 : OrderBot 
α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f < a ↔ ∀ b ∈ s, f b < a
)
参数：s.sup f < a ↔ ∀ b ∈ s, f b < a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
-/
protected theorem sup_lt_iff (ha : ⊥ < a) : s.sup f < a ↔ ∀ b ∈ s, f b < a :=
  ⟨fun hs _ hb => lt_of_le_of_lt (le_sup hb) hs,
    Finset.cons_induction_on s (fun _ => ha) fun c t hc => by
      simpa only [sup_cons, sup_lt_iff, mem_cons, forall_eq_or_imp] using And.imp_right⟩

@[to_dual]
/-
**Finset.sup_mem_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_mem_of_nonempty (hs : s.Nonempty) : s.sup f in f '' s
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
-/
theorem sup_mem_of_nonempty (hs : s.Nonempty) : s.sup f ∈ f '' s := by
  classical
  induction s using Finset.induction with
  | empty => simp only [Finset.not_nonempty_empty] at hs
  | insert a s _ h =>
    rw [Finset.sup_insert (b := a) (s := s) (f := f)]
    cases s.eq_empty_or_nonempty with
    | inl hs => simp [hs]
    | inr hs =>
      simp only [Finset.coe_insert]
      rcases le_total (f a) (s.sup f) with (ha | ha)
      · rw [sup_eq_right.mpr ha]
        exact Set.image_mono (Set.subset_insert a s) (h hs)
      · rw [sup_eq_left.mpr ha]
        apply Set.mem_image_of_mem _ (Set.mem_insert a ↑s)

end OrderBot

end LinearOrder

section Sup'

variable [SemilatticeSup α]

@[to_dual]
/-
**Finset.sup_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_of_mem {s : Finset β} (f : β -> α) {b : β} (h : b in s) : exists a : α
, s.sup ((↑) ∘ f : β -> WithBot α) = ↑a
参数：f : β -> α；h : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.le_iff_forall`：le_iff_forall : x <= y ↔ forall a : α, x = ↑a -> 
exists b : α, y = ↑b ∧ a <= b
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem sup_of_mem {s : Finset β} (f : β → α) {b : β} (h : b ∈ s) :
    ∃ a : α, s.sup ((↑) ∘ f : β → WithBot α) = ↑a :=
  (WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) (f b) rfl).imp fun _ ↦ And.left

/-- Given nonempty finset `s` then `s.sup' H f` is the supremum of its image under `f` in (possibly
unbounded) join-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a bottom element
you may instead use `Finset.sup` which does not require `s` nonempty. -/
@[to_dual
/-- Given nonempty finset `s` then `s.inf' H f` is the infimum of its image under `f` in (possibly
unbounded) meet-semilattice `α`, where `H` is a proof of nonemptiness. If `α` has a top element you
may instead use `Finset.inf` which does not require `s` nonempty. -/]
/-
**Finset.sup'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonempty f = f 1
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def sup' (s : Finset β) (H : s.Nonempty) (f : β → α) : α :=
  WithBot.unbot (s.sup ((↑) ∘ f)) (by simpa using! H)

variable {s : Finset β} (H : s.Nonempty) (f : β → α)

@[to_dual (attr := simp)]
/-
**Finset.coe_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'.eq_1`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] (s : Finset β) (H : s.Nonempty) (f : β → α),   s.sup' H f = (s.sup (WithBot.
some ∘…
· 使用定理 `WithBot.coe_unbot`：∀ {α : Type u_1} (x : WithBot α) (hx : x ≠ ⊥), ↑(x.un
bot hx) = x
-/
theorem coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) ∘ f) := by
  rw [sup', WithBot.coe_unbot]

@[to_dual (attr := simp)]
/-
**Finset.sup'_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} (
H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.cons b s hb).sup' ⋯ 
f = f b ⊔ s.sup' H f
参数：H : s.Nonempty；f : β → α；Finset.cons b s hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup'_cons {b : β} {hb : b ∉ s} :
    (cons b s hb).sup' (cons_nonempty hb) f = f b ⊔ s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[to_dual (attr := simp)]
/-
**Finset.sup'_insert** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} (
H : s.Nonempty) (f : β → α)   [inst_1 : DecidableEq β] {b : β}, (insert b s).sup
' ⋯ f = f b ⊔ s.sup' H f
参数：H : s.Nonempty；f : β → α；insert b s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.insert_nonempty`：insert_nonempty (a : α) (s : Finset α) : (insert
 a s).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup'_insert [DecidableEq β] {b : β} :
    (insert b s).sup' (insert_nonempty _ _) f = f b ⊔ s.sup' H f := by
  rw [← WithBot.coe_eq_coe]
  simp [WithBot.coe_sup]

@[to_dual (attr := simp)]
/-
**Finset.sup'_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] (f : β → α) {b :
 β}, {b}.sup' ⋯ f = f b
参数：f : β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
-/
theorem sup'_singleton {b : β} : ({b} : Finset β).sup' (singleton_nonempty _) f = f b :=
  rfl

@[to_dual (attr := simp) le_inf'_iff]
/-
**Finset.sup'_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} (
H : s.Nonempty) (f : β → α) {a : α},   s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a
参数：H : s.Nonempty；f : β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sup'_le_iff {a : α} : s.sup' H f ≤ a ↔ ∀ b ∈ s, f b ≤ a := by
  simp_rw [← @WithBot.coe_le_coe α, coe_sup', Finset.sup_le_iff]; rfl

@[to_dual le_inf'] alias ⟨_, sup'_le⟩ := sup'_le_iff

@[to_dual inf'_le]
/-
**Finset.le_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
参数：h : b in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   s.sup' H f ≤ a ↔ ∀ 
b ∈ s, f…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_sup' {b : β} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f :=
  (sup'_le_iff ⟨b, h⟩ f).1 le_rfl b h

@[to_dual]
/-
**Finset.isLUB_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：isLUB_sup' {s : Finset α} (hs : s.Nonempty) : IsLUB s (sup' s hs id)
参数：hs : s.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
-/
theorem isLUB_sup' {s : Finset α} (hs : s.Nonempty) : IsLUB s (sup' s hs id) :=
  ⟨fun x h => id_eq x ▸ le_sup' id h, fun _ h => Finset.sup'_le hs id h⟩

@[to_dual inf'_le_of_le]
/-
**Finset.le_sup'_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} (
f : β → α) {a : α} {b : β} (hb : b ∈ s),   a ≤ f b → a ≤ s.sup' ⋯ f
参数：f : β → α；hb : b ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
-/
theorem le_sup'_of_le {a : α} {b : β} (hb : b ∈ s) (h : a ≤ f b) : a ≤ s.sup' ⟨b, hb⟩ f :=
  h.trans <| le_sup' _ hb

@[to_dual]
/-
**Finset.sup'_eq_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} (
H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b = a) → s.sup' H f = a
参数：H : s.Nonempty；f : β → α；∀ b ∈ s, f b = a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.le_sup'_of_le`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eSup α] {s : Finset β} (f : β → α) {a : α} {b : β} (hb : b ∈ s),   a ≤ f b → a ≤
 s.sup' ⋯ …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma sup'_eq_of_forall {a : α} (h : ∀ b ∈ s, f b = a) : s.sup' H f = a :=
  le_antisymm (sup'_le _ _ (fun _ hb ↦ (h _ hb).le))
    (le_sup'_of_le _ H.choose_spec (h _ H.choose_spec).ge)

@[to_dual (attr := simp)]
/-
**Finset.sup'_const** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} (
H : s.Nonempty) (a : α),   (s.sup' H fun x => a) = a
参数：H : s.Nonempty；a : α；s.sup' H fun x => a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_eq_of_forall`：∀ {α : Type u_2} {β : Type u_3} [inst : Semila
tticeSup α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b
 = a) → s.sup'…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem sup'_const (a : α) : s.sup' H (fun _ => a) = a :=
  sup'_eq_of_forall H (fun _ ↦ a) fun _ ↦ congrFun rfl

@[to_dual]
/-
**Finset.sup'_union** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] [inst_1 : Decida
bleEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty)   (h₂ : s₂.Nonempty) (f : β → α),
 (s₁ ∪ s₂).sup' ⋯ f = s₁.sup' h₁ f ⊔ s₂.sup' h₂ f
参数：h₁ : s₁.Nonempty；h₂ : s₂.Nonempty；f : β → α；s₁ ∪ s₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.mono`：∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.Nonem
pty → t.Nonempty
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup'_union [DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
    (f : β → α) :
    (s₁ ∪ s₂).sup' (h₁.mono subset_union_left) f = s₁.sup' h₁ f ⊔ s₂.sup' h₂ f :=
  eq_of_forall_ge_iff fun a => by simp [or_imp, forall_and]

@[to_dual]
/-
**Finset.sup'_comm** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] {
s : Finset β} {t : Finset γ} (hs : s.Nonempty)   (ht : t.Nonempty) (f : β → γ → 
α), (s.sup' hs fun b => t.sup' ht (f b)) = t.sup' ht fun c => s.sup' hs fun b =>
 f b c
参数：hs : s.Nonempty；ht : t.Nonempty；f : β → γ → α；s.sup' hs fun b => t.sup' ht (f
 b)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall₂_comm`：forall₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ -> Sort*} {κ₂ : ι₂ -
> Sort*} {p : forall i₁, κ₁ i₁ -> forall i₂, κ₂ i₂ -> Prop} : (forall i₁ j₁ i₂ j
₂,…
-/
protected theorem sup'_comm {t : Finset γ} (hs : s.Nonempty) (ht : t.Nonempty) (f : β → γ → α) :
    (s.sup' hs fun b => t.sup' ht (f b)) = t.sup' ht fun c => s.sup' hs fun b => f b c :=
  eq_of_forall_ge_iff fun a => by simpa using forall₂_comm

@[to_dual]
/-
**Finset.sup'_induction** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} (
H : s.Nonempty) (f : β → α) {p : α → Prop},   (∀ (a₁ : α), p a₁ → ∀ (a₂ : α), p 
a₂ → p (a₁ ⊔ a₂)) → (∀ b ∈ s, p (f b)) → p (s.sup' H f)
参数：H : s.Nonempty；f : β → α；∀ (a₁ : α), p a₁ → ∀ (a₂ : α), p a₂ → p (a₁ ⊔ a₂)；∀ 
b ∈ s, p (f b)；s.sup' H f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.sup_induction`：sup_induction {p : α -> Prop} (hb : p ⊥) (hp : for
all a₁, p a₁ -> forall a₂, p a₂ -> p (a₁ ⊔ a₂)) (hs : forall b in s, p (f b)) : 
p (s.sup f…
· 使用定理 `trivial`：True
· 使用定理 `bot_sup_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), ⊥ ⊔ a = a
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
theorem sup'_induction {p : α → Prop} (hp : ∀ a₁, p a₁ → ∀ a₂, p a₂ → p (a₁ ⊔ a₂))
    (hs : ∀ b ∈ s, p (f b)) : p (s.sup' H f) := by
  change @WithBot.recBotCoe α (fun _ => Prop) True p ↑(s.sup' H f)
  rw [coe_sup']
  refine sup_induction trivial (fun a₁ h₁ a₂ h₂ ↦ ?_) hs
  match a₁, a₂ with
  | ⊥, _ => rwa [bot_sup_eq]
  | (a₁ : α), ⊥ => rwa [sup_bot_eq]
  | (a₁ : α), (a₂ : α) => exact hp a₁ h₁ a₂ h₂

@[to_dual]
/-
**Finset.sup'_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} [inst : SemilatticeSup α] (s : Set α),   (∀ x ∈ s, ∀ y ∈ 
s, x ⊔ y ∈ s) →     ∀ {ι : Type u_7} (t : Finset ι) (H : t.Nonempty) (p : ι → α)
, (∀ i ∈ t, p i ∈ s) → t.sup' H p ∈ s
参数：s : Set α；∀ x ∈ s, ∀ y ∈ s, x ⊔ y ∈ s；t : Finset ι；H : t.Nonempty；p : ι → α；∀
 i ∈ t, p i ∈ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_induction`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatti
ceSup α] {s : Finset β} (H : s.Nonempty) (f : β → α) {p : α → Prop},   (∀ (a₁ : 
α), p a₁ → …
-/
theorem sup'_mem (s : Set α) (w : ∀ᵉ (x ∈ s) (y ∈ s), x ⊔ y ∈ s) {ι : Type*}
    (t : Finset ι) (H : t.Nonempty) (p : ι → α) (h : ∀ i ∈ t, p i ∈ s) : t.sup' H p ∈ s :=
  sup'_induction H p w h

@[to_dual (attr := congr)]
/-
**Finset.sup'_congr** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} (
H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t), (∀ x ∈ s, f x = g x
) → s.sup' H f = t.sup' ⋯ g
参数：H : s.Nonempty；h₁ : s = t；∀ x ∈ s, f x = g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup'_congr {t : Finset β} {f g : β → α} (h₁ : s = t) (h₂ : ∀ x ∈ s, f x = g x) :
    s.sup' H f = t.sup' (h₁ ▸ H) g := by
  subst s
  refine eq_of_forall_ge_iff fun c => ?_
  simp +contextual only [sup'_le_iff, h₂]

@[to_dual]
/-
**Finset.apply_sup'_eq_sup'_comp** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] [
inst_1 : SemilatticeSup γ] {s : Finset β}   (H : s.Nonempty) {f : β → α} (g : α 
→ γ), (∀ (x y : α), g (x ⊔ y) = g x ⊔ g y) → g (s.sup' H f) = s.sup' H (g ∘ f)
参数：H : s.Nonempty；g : α → γ；∀ (x y : α), g (x ⊔ y) = g x ⊔ g y；s.sup' H f；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
-/
theorem apply_sup'_eq_sup'_comp [SemilatticeSup γ] {s : Finset β} (H : s.Nonempty) {f : β → α}
    (g : α → γ) (g_sup : ∀ x y, g (x ⊔ y) = g x ⊔ g y) : g (s.sup' H f) = s.sup' H (g ∘ f) := by
  refine H.cons_induction ?_ ?_ <;> intros <;> simp [*]

@[deprecated (since := "2026-05-29")]
alias comp_sup'_eq_sup'_comp := apply_sup'_eq_sup'_comp

@[deprecated (since := "2026-05-29")]
alias comp_inf'_eq_inf'_comp := apply_sup'_eq_sup'_comp

@[to_dual (attr := simp)]
/-
**Finset._root_.map_finset_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.map_finset_sup' [SemilatticeSup β] [FunLike F α β] [SupHomClass F α β]
    (f : F) {s : Finset ι} (hs) (g : ι → α) :
    f (s.sup' hs g) = s.sup' hs (f ∘ g) := by
  refine hs.cons_induction ?_ ?_ <;> intros <;> simp [*]

/-- To rewrite from right to left, use `Finset.sup'_comp_eq_image`. -/
@[to_dual (attr := simp) /-- To rewrite from right to left, use `Finset.inf'_comp_eq_image`. -/]
/-
**Finset.sup'_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] [
inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : (Finset.image f s).No
nempty) (g : β → α), (Finset.image f s).sup' hs g = s.sup' ⋯ (g ∘ f)
参数：hs : (Finset.image f s).Nonempty；g : β → α；Finset.image f s；g ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.sup_image`：sup_image [DecidableEq β] (s : Finset γ) (f : γ -> β) 
(g : β -> α) : (s.image f).sup g = s.sup (g ∘ f)

--- 原说明 ---
To rewrite from right to left, use `Finset.sup'_comp_eq_image`.
-/
theorem sup'_image [DecidableEq β] {s : Finset γ} {f : γ → β} (hs : (s.image f).Nonempty)
    (g : β → α) :
    (s.image f).sup' hs g = s.sup' hs.of_image (g ∘ f) := by
  rw [← WithBot.coe_eq_coe]; simp only [coe_sup', sup_image]; rfl

/-- A version of `Finset.sup'_image` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/
@[to_dual /-- A version of `Finset.inf'_image` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/]
/-
**Finset.sup'_comp_eq_image** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] [
inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : s.Nonempty) (g : β → 
α), s.sup' hs (g ∘ f) = (Finset.image f s).sup' ⋯ g
参数：hs : s.Nonempty；g : β → α；g ∘ f；Finset.image f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `Finset.sup'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeSup α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
-/
lemma sup'_comp_eq_image [DecidableEq β] {s : Finset γ} {f : γ → β} (hs : s.Nonempty) (g : β → α) :
    s.sup' hs (g ∘ f) = (s.image f).sup' (hs.image f) g :=
  .symm <| sup'_image _ _

/-- To rewrite from right to left, use `Finset.sup'_comp_eq_map`. -/
@[to_dual (attr := simp) /-- To rewrite from right to left, use `Finset.inf'_comp_eq_map`. -/]
/-
**Finset.sup'_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] {
s : Finset γ} {f : γ ↪ β} (g : β → α)   (hs : (Finset.map f s).Nonempty), (Finse
t.map f s).sup' hs g = s.sup' ⋯ (g ∘ ⇑f)
参数：g : β → α；hs : (Finset.map f s).Nonempty；Finset.map f s；g ∘ ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.map_nonempty`：map_nonempty : (s.map f).Nonempty ↔ s.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithBot.coe_eq_coe`：coe_eq_coe : (a : WithBot α) = b ↔ a = b
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.sup_map`：sup_map (s : Finset γ) (f : γ ↪ β) (g : β -> α) : (s.map
 f).sup g = s.sup (g ∘ f)

--- 原说明 ---
To rewrite from right to left, use `Finset.sup'_comp_eq_map`.
-/
theorem sup'_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : (s.map f).Nonempty) :
    (s.map f).sup' hs g = s.sup' (map_nonempty.1 hs) (g ∘ f) := by
  rw [← WithBot.coe_eq_coe, coe_sup', sup_map, coe_sup']
  rfl

/-- A version of `Finset.sup'_map` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/
@[to_dual /-- A version of `Finset.inf'_map` with LHS and RHS reversed.
Also, this lemma assumes that `s` is nonempty instead of assuming that its image is nonempty. -/]
/-
**Finset.sup'_comp_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : SemilatticeSup α] {
s : Finset γ} {f : γ ↪ β} (g : β → α)   (hs : s.Nonempty), s.sup' hs (g ∘ ⇑f) = 
(Finset.map f s).sup' ⋯ g
参数：g : β → α；hs : s.Nonempty；g ∘ ⇑f；Finset.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.map_nonempty`：map_nonempty : (s.map f).Nonempty ↔ s.Nonempty
· 使用定理 `Finset.sup'_map`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : 
SemilatticeSup α] {s : Finset γ} {f : γ ↪ β} (g : β → α)   (hs : (Finset.map f s
).Non…
-/
lemma sup'_comp_eq_map {s : Finset γ} {f : γ ↪ β} (g : β → α) (hs : s.Nonempty) :
    s.sup' hs (g ∘ f) = (s.map f).sup' (map_nonempty.2 hs) g :=
  .symm <| sup'_map _ _


@[to_dual (attr := gcongr)]
/-
**Finset.sup'_mono** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] (f : β → α) {s₁ 
s₂ : Finset β} (h : s₁ ⊆ s₂)   (h₁ : s₁.Nonempty), s₁.sup' h₁ f ≤ s₂.sup' ⋯ f
参数：f : β → α；h : s₁ ⊆ s₂；h₁ : s₁.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.Nonempty.mono`：∀ {α : Type u_1} {s t : Finset α}, s ⊆ t → s.Nonem
pty → t.Nonempty
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
-/
theorem sup'_mono {s₁ s₂ : Finset β} (h : s₁ ⊆ s₂) (h₁ : s₁.Nonempty) :
    s₁.sup' h₁ f ≤ s₂.sup' (h₁.mono h) f :=
  Finset.sup'_le h₁ _ (fun _ hb => le_sup' _ (h hb))

@[to_dual (attr := gcongr)]
/-
**Finset.sup'_mono_fun** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] {s : Finset β} {
hs : s.Nonempty} {f g : β → α},   (∀ b ∈ s, f b ≤ g b) → s.sup' hs f ≤ s.sup' hs
 g
参数：∀ b ∈ s, f b ≤ g b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
-/
lemma sup'_mono_fun {hs : s.Nonempty} {f g : β → α} (h : ∀ b ∈ s, f b ≤ g b) :
    s.sup' hs f ≤ s.sup' hs g := sup'_le _ _ fun b hb ↦ (h b hb).trans (le_sup' _ hb)

end Sup'

section Sup

variable [SemilatticeSup α] [OrderBot α] {s : Finset β} {f : β → α}

@[to_dual]
/-
**Finset.sup'_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] [inst_1 : OrderB
ot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup' H f = s.sup f
参数：H : s.Nonempty；f : β → α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
-/
theorem sup'_eq_sup (H : s.Nonempty) (f : β → α) : s.sup' H f = s.sup f :=
  le_antisymm (sup'_le H f fun _ => le_sup) (Finset.sup_le fun _ => le_sup' f)

@[to_additive (attr := simp)]
/-
**Finset.sup'_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α] [OrderBot α] {s 
: Finset β} {f : β → α} [inst_2 : One α]   [IsBotOneClass α] (hs : s.Nonempty), 
s.sup' hs f = 1 ↔ ∀ i ∈ s, f i = 1
参数：hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sup'_eq_one [One α] [IsBotOneClass α] (hs) : s.sup' hs f = 1 ↔ ∀ i ∈ s, f i = 1 := by
  simp [sup'_eq_sup]

@[to_dual]
/-
**Finset.coe_sup_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：coe_sup_of_nonempty (h : s.Nonempty) (f : β -> α) : (↑(s.sup f) : WithBot 
α) = s.sup ((↑) ∘ f)
参数：h : s.Nonempty；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_sup_of_nonempty (h : s.Nonempty) (f : β → α) :
    (↑(s.sup f) : WithBot α) = s.sup ((↑) ∘ f) := by simp only [← sup'_eq_sup h, coe_sup' h]

end Sup

@[to_dual (attr := simp)]
/-
**Finset.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [inst : (b : β) → Semil
atticeSup (C b)]   [inst_1 : (b : β) → OrderBot (C b)] (s : Finset α) (f : α → (
b : β) → C b) (b : β), s.sup f b = s.sup fun a => f a b
参数：b : β；C b；b : β；C b；s : Finset α；f : α → (b : β) → C b；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
-/
protected theorem sup_apply {C : β → Type*} [∀ b : β, SemilatticeSup (C b)]
    [∀ b : β, OrderBot (C b)] (s : Finset α) (f : α → ∀ b : β, C b) (b : β) :
    s.sup f b = s.sup fun a => f a b :=
  apply_sup_eq_sup_comp (fun x : ∀ b : β, C b => x b) (fun _ _ => rfl) rfl

@[to_dual (attr := simp)]
/-
**Finset.sup'_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {C : β → Type u_7} [inst : (b : β) → Semil
atticeSup (C b)] {s : Finset α}   (H : s.Nonempty) (f : α → (b : β) → C b) (b : 
β), s.sup' H f b = s.sup' H fun a => f a b
参数：b : β；C b；H : s.Nonempty；f : α → (b : β) → C b；b : β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup'_eq_sup'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
-/
protected theorem sup'_apply {C : β → Type*} [∀ b : β, SemilatticeSup (C b)]
    {s : Finset α} (H : s.Nonempty) (f : α → ∀ b : β, C b) (b : β) :
    s.sup' H f b = s.sup' H fun a => f a b :=
  apply_sup'_eq_sup'_comp H (fun x : ∀ b : β, C b => x b) fun _ _ => rfl

@[to_dual (attr := simp)]
/-
**Finset.toDual_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：toDual_sup' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι -> 
α) : toDual (s.sup' hs f) = s.inf' hs (toDual ∘ f)
参数：hs : s.Nonempty；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
-/
theorem toDual_sup' [SemilatticeSup α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) :
    toDual (s.sup' hs f) = s.inf' hs (toDual ∘ f) :=
  rfl

@[to_dual (attr := simp)]
/-
**Finset.ofDual_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：ofDual_sup' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι -> 
αᵒᵈ) : ofDual (s.sup' hs f) = s.inf' hs (ofDual ∘ f)
参数：hs : s.Nonempty；f : ι -> αᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
-/
theorem ofDual_sup' [SemilatticeInf α] {s : Finset ι} (hs : s.Nonempty) (f : ι → αᵒᵈ) :
    ofDual (s.sup' hs f) = s.inf' hs (ofDual ∘ f) :=
  rfl

section DistribLattice
variable [DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty) (ht : t.Nonempty)
  {f : ι → α} {g : κ → α} {a : α}

@[to_dual]
/-
**Finset.sup'_inf_distrib_left** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : DistribLattice α] {s : Finset ι} (
hs : s.Nonempty) (f : ι → α) (a : α),   a ⊓ s.sup' hs f = s.sup' hs fun i => a ⊓
 f i
参数：hs : s.Nonempty；f : ι → α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_sup_left`：inf_sup_left (a b c : α) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem sup'_inf_distrib_left (f : ι → α) (a : α) :
    a ⊓ s.sup' hs f = s.sup' hs fun i ↦ a ⊓ f i := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton => simp
  | cons _ _ _ hs ih => simp_rw [sup'_cons hs, inf_sup_left, ih]

@[to_dual]
/-
**Finset.sup'_inf_distrib_right** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : DistribLattice α] {s : Finset ι} (
hs : s.Nonempty) (f : ι → α) (a : α),   s.sup' hs f ⊓ a = s.sup' hs fun i => f i
 ⊓ a
参数：hs : s.Nonempty；f : ι → α；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b : α), a ⊓ b = b 
⊓ a
· 使用定理 `Finset.sup'_inf_distrib_left`：∀ {α : Type u_2} {ι : Type u_5} [inst : Di
stribLattice α] {s : Finset ι} (hs : s.Nonempty) (f : ι → α) (a : α),   a ⊓ s.su
p' hs f = s.sup' h…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sup'_inf_distrib_right (f : ι → α) (a : α) :
    s.sup' hs f ⊓ a = s.sup' hs fun i => f i ⊓ a := by
  rw [inf_comm, sup'_inf_distrib_left]; simp_rw [inf_comm]

end DistribLattice

section LinearOrder

variable [LinearOrder α] {s : Finset ι} (H : s.Nonempty) {f : ι → α} {a : α}

@[to_dual]
/-
**Finset.apply_sup_eq_sup_comp_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：apply_sup_eq_sup_comp_of_nonempty [OrderBot α] [SemilatticeSup β] [OrderBo
t β] {g : α -> β} (mono_g : Monotone g) (H : s.Nonempty) : g (s.sup f) = s.sup (
g ∘ f)
参数：mono_g : Monotone g；H : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.apply_sup'_eq_sup'_comp`：∀ {α : Type u_2} {β : Type u_3} {γ : Typ
e u_4} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup γ] {s : Finset β}   (H
 : s.Nonempty) {f : …
· 使用定理 `Monotone.map_sup`：map_sup [SemilatticeSup β] {f : α -> β} (hf : Monotone
 f) (x y : α) : f (x ⊔ y) = f x ⊔ f y
-/
theorem apply_sup_eq_sup_comp_of_nonempty [OrderBot α] [SemilatticeSup β] [OrderBot β]
    {g : α → β} (mono_g : Monotone g) (H : s.Nonempty) : g (s.sup f) = s.sup (g ∘ f) := by
  rw [← Finset.sup'_eq_sup H, ← Finset.sup'_eq_sup H]
  exact Finset.apply_sup'_eq_sup'_comp H g (fun x y ↦ Monotone.map_sup mono_g x y)

@[deprecated (since := "2026-03-25")]
alias comp_sup_eq_sup_comp_of_nonempty := apply_sup_eq_sup_comp_of_nonempty

@[to_dual (attr := simp) inf'_le_iff]
/-
**Finset.le_sup'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α] {s : Finset ι} (H :
 s.Nonempty) {f : ι → α} {a : α},   a ≤ s.sup' H f ↔ ∃ b ∈ s, a ≤ f b
参数：H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.le_sup_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (a ≤ s.sup
 f ↔ ∃ …
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
-/
theorem le_sup'_iff : a ≤ s.sup' H f ↔ ∃ b ∈ s, a ≤ f b := by
  rw [← WithBot.coe_le_coe, coe_sup', Finset.le_sup_iff (WithBot.bot_lt_coe a)]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_le_coe)

@[to_dual (attr := simp) inf'_lt_iff]
/-
**Finset.lt_sup'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α] {s : Finset ι} (H :
 s.Nonempty) {f : ι → α} {a : α},   a < s.sup' H f ↔ ∃ b ∈ s, a < f b
参数：H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.lt_sup_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   a < s.sup f ↔ ∃ b 
∈ s, a …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `and_congr_right'`：∀ {b c a : Prop}, (b ↔ c) → (a ∧ b ↔ a ∧ c)
-/
theorem lt_sup'_iff : a < s.sup' H f ↔ ∃ b ∈ s, a < f b := by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.lt_sup_iff]
  exact exists_congr (fun _ => and_congr_right' WithBot.coe_lt_coe)

@[to_dual (attr := simp) lt_inf'_iff]
/-
**Finset.sup'_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α] {s : Finset ι} (H :
 s.Nonempty) {f : ι → α} {a : α},   s.sup' H f < a ↔ ∀ i ∈ s, f i < a
参数：H : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
-/
theorem sup'_lt_iff : s.sup' H f < a ↔ ∀ i ∈ s, f i < a := by
  rw [← WithBot.coe_lt_coe, coe_sup', Finset.sup_lt_iff (WithBot.bot_lt_coe a)]
  exact forall₂_congr (fun _ _ => WithBot.coe_lt_coe)

@[to_dual]
/-
**Finset.exists_mem_eq_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_mem_eq_sup' (f : ι -> α) : exists i, i in s ∧ s.sup' H f = f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.singleton_nonempty`：singleton_nonempty (a : α) : ({a} : Finset α)
.Nonempty
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_cons`：mem_cons {h} : b in s.cons a h ↔ b = a ∨ b in s
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
-/
theorem exists_mem_eq_sup' (f : ι → α) : ∃ i, i ∈ s ∧ s.sup' H f = f i := by
  induction H using Finset.Nonempty.cons_induction with
  | singleton c => exact ⟨c, mem_singleton_self c, rfl⟩
  | cons c s hcs hs ih =>
    rcases ih with ⟨b, hb, h'⟩
    rw [sup'_cons hs, h']
    cases le_total (f b) (f c) with
    | inl h => exact ⟨c, mem_cons.2 (Or.inl rfl), sup_eq_left.2 h⟩
    | inr h => exact ⟨b, mem_cons.2 (Or.inr hb), sup_eq_right.2 h⟩

@[to_dual]
/-
**Finset.exists_mem_eq_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：exists_mem_eq_sup [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι -> α
) : exists i, i in s ∧ s.sup f = f i
参数：s : Finset ι；h : s.Nonempty；f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.exists_mem_eq_sup'`：exists_mem_eq_sup' (f : ι -> α) : exists i, i
 in s ∧ s.sup' H f = f i
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
-/
theorem exists_mem_eq_sup [OrderBot α] (s : Finset ι) (h : s.Nonempty) (f : ι → α) :
    ∃ i, i ∈ s ∧ s.sup f = f i :=
  sup'_eq_sup h f ▸ exists_mem_eq_sup' h f

end LinearOrder

end Finset

namespace Multiset

/-
**Multiset.map_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_finset_sup [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ -> Mu
ltiset β) (g : β -> α) (hg : Function.Injective g) : map g (s.sup f) = s.sup (ma
p g ∘ f)
参数：s : Finset γ；f : γ -> Multiset β；g : β -> α；hg : Function.Injective g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
· 使用引理 `Multiset.map_union`：map_union [DecidableEq β] {f : α -> β} (finj : Funct
ion.Injective f) {s t : Multiset α} : map f (s union t) = map f s union map f t
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
-/
theorem map_finset_sup [DecidableEq α] [DecidableEq β] (s : Finset γ) (f : γ → Multiset β)
    (g : β → α) (hg : Function.Injective g) : map g (s.sup f) = s.sup (map g ∘ f) :=
  Finset.apply_sup_eq_sup_comp _ (fun _ _ => map_union hg) (map_zero _)
/-
**Multiset.count_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_finset_sup [DecidableEq β] (s : Finset α) (f : α -> Multiset β) (b :
 β) : count b (s.sup f) = s.sup fun a => count b (f a)
参数：s : Finset α；f : α -> Multiset β；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Multiset.count_zero`：count_zero (a : α) : count a 0 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `Multiset.sup_eq_union`：∀ {α : Type u_1} [inst : DecidableEq α] (s t : Mu
ltiset α), s ⊔ t = s ∪ t
· 使用引理 `Multiset.count_union`：count_union (a : α) (s t : Multiset α) : count a (
s union t) = max (count a s) (count a t)
-/
theorem count_finset_sup [DecidableEq β] (s : Finset α) (f : α → Multiset β) (b : β) :
    count b (s.sup f) = s.sup fun a => count b (f a) := by
  let := Classical.decEq α
  refine s.induction ?_ ?_
  · exact count_zero _
  · intro i s _ ih
    rw [Finset.sup_insert, sup_eq_union, count_union, Finset.sup_insert, ih]
/-
**Multiset.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α -> Multiset β} {x : β}
 : x in s.sup f ↔ exists v in s, x in f v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
-/
theorem mem_sup {α β} [DecidableEq β] {s : Finset α} {f : α → Multiset β} {x : β} :
    x ∈ s.sup f ↔ ∃ v ∈ s, x ∈ f v := by
  induction s using Finset.cons_induction <;> simp [*]

end Multiset

namespace Finset
variable [DecidableEq α] {s : Finset ι} {f : ι → Finset α} {a : α}

/-
**Finset.mem_sup'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : DecidableEq α] {s : Finset ι} {f :
 ι → Finset α} {a : α} (hs : s.Nonempty),   a ∈ s.sup' hs f ↔ ∃ i ∈ s, a ∈ f i
参数：hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sup'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
-/
@[simp] lemma mem_sup' (hs) : a ∈ s.sup' hs f ↔ ∃ i ∈ s, a ∈ f i := by
  induction hs using Nonempty.cons_induction <;> simp [*]
/-
**Finset.mem_inf'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : DecidableEq α] {s : Finset ι} {f :
 ι → Finset α} {a : α} (hs : s.Nonempty),   a ∈ s.inf' hs f ↔ ∀ i ∈ s, a ∈ f i
参数：hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.cons_induction`：∀ {α : Type u_3} {motive : (s : Finset α
) → s.Nonempty → Prop},   (∀ (a : α), motive {a} ⋯) →     (∀ (a : α) (s : Finset
 α) (h : a ∉ s) (hs …
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.cons_nonempty`：cons_nonempty (h : a ∉ s) : (cons a s h).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.inf'_cons`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf
 α] {s : Finset β} (H : s.Nonempty) (f : β → α) {b : β}   {hb : b ∉ s}, (Finset.
cons b…
-/
@[simp] lemma mem_inf' (hs) : a ∈ s.inf' hs f ↔ ∀ i ∈ s, a ∈ f i := by
  induction hs using Nonempty.cons_induction <;> simp [*]
/-
**Finset.mem_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_2} {ι : Type u_5} [inst : DecidableEq α] {s : Finset ι} {f :
 ι → Finset α} {a : α},   a ∈ s.sup f ↔ ∃ i ∈ s, a ∈ f i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Finset.sup_cons`：sup_cons {b : β} (h : b ∉ s) : (cons b s h).sup f = f b
 ⊔ s.sup f
-/
@[simp] lemma mem_sup : a ∈ s.sup f ↔ ∃ i ∈ s, a ∈ f i := by
  induction s using cons_induction <;> simp [*]

@[simp]
/-
**Finset.sup_singleton_apply** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_singleton_apply (s : Finset β) (f : β -> α) : (s.sup fun b => {f b}) =
 s.image f
参数：s : Finset β；f : β -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.mem_sup`：∀ {α : Type u_2} {ι : Type u_5} [inst : DecidableEq α] {
s : Finset ι} {f : ι → Finset α} {a : α},   a ∈ s.sup f ↔ ∃ i ∈ s, a ∈ f i
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sup_singleton_apply (s : Finset β) (f : β → α) :
    (s.sup fun b => {f b}) = s.image f := by
  ext a
  rw [mem_sup, mem_image]
  simp only [mem_singleton, eq_comm]

@[simp]
/-
**Finset.sup_singleton_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sup_singleton_eq_self (s : Finset α) : s.sup singleton = s
参数：s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sup_singleton_apply`：sup_singleton_apply (s : Finset β) (f : β ->
 α) : (s.sup fun b => {f b}) = s.image f
· 使用定理 `Finset.image_id`：image_id [DecidableEq α] : s.image id = s
-/
theorem sup_singleton_eq_self (s : Finset α) : s.sup singleton = s :=
  (s.sup_singleton_apply _).trans image_id

end Finset

