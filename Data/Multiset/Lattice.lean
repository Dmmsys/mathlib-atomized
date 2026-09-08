/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.FinsetOps
public import Mathlib.Data.Multiset.Fold

/-!
# Lattice operations on multisets

This file defines `Multiset.sup` and derives the dual `Multiset.inf` and their basic lemmas
via `to_dual`.
-/

@[expose] public section


namespace Multiset

variable {α : Type*}

-- `sup` can be defined with just `[Bot α]` where some lemmas hold without requiring `[OrderBot α]`
-- `inf` can be defined with just `[Top α]` where some lemmas hold without requiring `[OrderTop α]`
variable [SemilatticeSup α] [OrderBot α]

/-- Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c` -/
@[to_dual /-- Infimum of a multiset: `inf {a, b, c} = a ⊓ b ⊓ c` -/]
/-
**Multiset.sup** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：sup (s : Multiset α) : α
参数：s : Multiset α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2

--- 原说明 ---
Supremum of a multiset: `sup {a, b, c} = a ⊔ b ⊔ c`
-/
def sup (s : Multiset α) : α :=
  s.fold (· ⊔ ·) ⊥

@[to_dual (attr := simp)]
/-
**Multiset.sup_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_coe (l : List α) : sup (l : Multiset α) = l.foldr (· ⊔ ·) ⊥
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_coe (l : List α) : sup (l : Multiset α) = l.foldr (· ⊔ ·) ⊥ :=
  rfl

@[to_dual (attr := simp)]
/-
**Multiset.sup_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_zero : (0 : Multiset α).sup = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.fold_zero`：fold_zero (b : α) : (0 : Multiset α).fold op b = b
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
-/
theorem sup_zero : (0 : Multiset α).sup = ⊥ :=
  fold_zero _ _

@[to_dual (attr := simp)]
/-
**Multiset.sup_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a ⊔ s.sup
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
-/
theorem sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a ⊔ s.sup :=
  fold_cons_left _ _ _ _

@[to_dual (attr := simp)]
/-
**Multiset.sup_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_singleton {a : α} : ({a} : Multiset α).sup = a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
theorem sup_singleton {a : α} : ({a} : Multiset α).sup = a := sup_bot_eq _

@[to_dual (attr := simp)]
/-
**Multiset.sup_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.fold.congr_simp`：∀ {α : Type u_1} (op op_1 : α → α → α) (e_op :
 op = op_1) [hc : Std.Commutative op] [ha : Std.Associative op]   (a a_1 : α), a
 = a_1 → ∀ (a_…
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.fold_add`：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂)
.fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂
-/
theorem sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup ⊔ s₂.sup :=
  Eq.trans (by simp [sup]) (fold_add _ _ _ _ _)

@[to_dual (attr := simp) le_inf]
/-
**Multiset.sup_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_le {s : Multiset α} {a : α} : s.sup <= a ↔ forall b in s, b <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.sup_zero`：sup_zero : (0 : Multiset α).sup = ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.sup_cons`：sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a
 ⊔ s.sup
-/
theorem sup_le {s : Multiset α} {a : α} : s.sup ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [or_imp, forall_and])

@[to_dual inf_le]
/-
**Multiset.le_sup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_sup {s : Multiset α} {a : α} (h : a in s) : a <= s.sup
参数：h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.sup_le`：sup_le {s : Multiset α} {a : α} : s.sup <= a ↔ forall b
 in s, b <= a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem le_sup {s : Multiset α} {a : α} (h : a ∈ s) : a ≤ s.sup :=
  sup_le.1 le_rfl _ h

@[to_dual (attr := gcongr)]
/-
**Multiset.sup_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_mono {s₁ s₂ : Multiset α} (h : s₁ subseteq s₂) : s₁.sup <= s₂.sup
参数：h : s₁ subseteq s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.sup_le`：sup_le {s : Multiset α} {a : α} : s.sup <= a ↔ forall b
 in s, b <= a
· 使用定理 `Multiset.le_sup`：le_sup {s : Multiset α} {a : α} (h : a in s) : a <= s.s
up
-/
theorem sup_mono {s₁ s₂ : Multiset α} (h : s₁ ⊆ s₂) : s₁.sup ≤ s₂.sup :=
  sup_le.2 fun _ hb => le_sup (h hb)

variable [DecidableEq α]

@[to_dual (attr := simp)]
/-
**Multiset.sup_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_dedup (s : Multiset α) : (dedup s).sup = s.sup
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.fold_dedup_idem`：fold_dedup_idem [DecidableEq α] [hi : Std.Idem
potentOp op] (s : Multiset α) (b : α) : (dedup s).fold op b = s.fold op b
· 使用定理 `instCommutativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Commutative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instAssociativeMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], St
d.Associative fun x1 x2 => x1 ⊔ x2
· 使用定理 `instIdempotentOpMax_mathlib`：∀ {α : Type u} [inst : SemilatticeSup α], S
td.IdempotentOp fun x1 x2 => x1 ⊔ x2
-/
theorem sup_dedup (s : Multiset α) : (dedup s).sup = s.sup :=
  fold_dedup_idem _ _ _

@[to_dual (attr := simp)]
/-
**Multiset.sup_ndunion** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.sup_dedup`：sup_dedup (s : Multiset α) : (dedup s).sup = s.sup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.sup_add`：sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup 
⊔ s₂.sup
-/
theorem sup_ndunion (s₁ s₂ : Multiset α) : (ndunion s₁ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add]; simp

@[to_dual (attr := simp)]
/-
**Multiset.sup_union** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_union (s₁ s₂ : Multiset α) : (s₁ union s₂).sup = s₁.sup ⊔ s₂.sup
参数：s₁ s₂ : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.sup_dedup`：sup_dedup (s : Multiset α) : (dedup s).sup = s.sup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.sup_add`：sup_add (s₁ s₂ : Multiset α) : (s₁ + s₂).sup = s₁.sup 
⊔ s₂.sup
-/
theorem sup_union (s₁ s₂ : Multiset α) : (s₁ ∪ s₂).sup = s₁.sup ⊔ s₂.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_add]; simp

@[to_dual (attr := simp)]
/-
**Multiset.sup_ndinsert** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sup_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).sup = a ⊔ s.sup
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.sup_dedup`：sup_dedup (s : Multiset α) : (dedup s).sup = s.sup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.dedup_ext`：dedup_ext {s t : Multiset α} : dedup s = dedup t ↔ f
orall a, a in s ↔ a in t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Multiset.sup_cons`：sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a
 ⊔ s.sup
-/
theorem sup_ndinsert (a : α) (s : Multiset α) : (ndinsert a s).sup = a ⊔ s.sup := by
  rw [← sup_dedup, dedup_ext.2, sup_dedup, sup_cons]; simp
/-
**Multiset.nodup_sup_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_sup_iff {α : Type*} [DecidableEq α] {m : Multiset (Multiset α)} : m.
sup.Nodup ↔ forall a : Multiset α, a in m -> a.Nodup
参数：Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sup_zero`：sup_zero : (0 : Multiset α).sup = ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Multiset.sup_cons`：sup_cons (a : α) (s : Multiset α) : (a ::ₘ s).sup = a
 ⊔ s.sup
-/
theorem nodup_sup_iff {α : Type*} [DecidableEq α] {m : Multiset (Multiset α)} :
    m.sup.Nodup ↔ ∀ a : Multiset α, a ∈ m → a.Nodup := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons _ _ h => simp [h]

end Multiset

