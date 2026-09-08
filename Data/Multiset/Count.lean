/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Multiset.ZeroCons

/-!
# Counting multiplicity in a multiset

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

section

variable (p : α → Prop) [DecidablePred p]


/-! ### countP -/


/-- `countP p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`. -/
/-
**Multiset.countP** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：countP (s : Multiset α) : Nat
参数：s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`countP p s` counts the number of elements of `s` (with multiplicity) that
  satisfy `p`.
-/
def countP (s : Multiset α) : ℕ :=
  Quot.liftOn s (List.countP p) fun _l₁ _l₂ => Perm.countP_eq (p ·)

@[simp]
/-
**Multiset.coe_countP** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_countP (l : List α) : countP p l = l.countP p
参数：l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_countP (l : List α) : countP p l = l.countP p :=
  rfl

@[simp]
/-
**Multiset.countP_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_zero : countP p 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem countP_zero : countP p 0 = 0 :=
  rfl

variable {p}

@[simp]
/-
**Multiset.countP_cons_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_cons_of_pos {a : α} (s) : p a -> countP p (a ::ₘ s) = countP p s + 
1
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.countP_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.countP p (a :: l) = List.countP p l + 1
-/
theorem countP_cons_of_pos {a : α} (s) : p a → countP p (a ::ₘ s) = countP p s + 1 :=
  Quot.inductionOn s <| by simpa using fun _ => List.countP_cons_of_pos (p := (p ·))

@[simp]
/-
**Multiset.countP_cons_of_neg** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_cons_of_neg {a : α} (s) : ¬p a -> countP p (a ::ₘ s) = countP p s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.countP_cons_of_neg`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, ¬p a = true → List.countP p (a :: l) = List.countP p l
-/
theorem countP_cons_of_neg {a : α} (s) : ¬p a → countP p (a ::ₘ s) = countP p s :=
  Quot.inductionOn s <| by simpa using fun _ => List.countP_cons_of_neg (p := (p ·))

variable (p)
/-
**Multiset.countP_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_cons (b : α) (s) : countP p (b ::ₘ s) = countP p s + if p b then 1 
else 0
参数：b : α；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.countP_cons`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : List α}, 
  List.countP p (a :: l) = List.countP p l + if p a = true then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem countP_cons (b : α) (s) : countP p (b ::ₘ s) = countP p s + if p b then 1 else 0 :=
  Quot.inductionOn s <| by simp [List.countP_cons]
/-
**Multiset.countP_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_le_card (s) : countP p s <= card s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.countP_le_length`：∀ {α : Type u_1} {p : α → Bool} {l : List α}, Lis
t.countP p l ≤ l.length
-/
theorem countP_le_card (s) : countP p s ≤ card s :=
  Quot.inductionOn s fun _l => countP_le_length (p := (p ·))
/-
**Multiset.card_eq_countP_add_countP** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_eq_countP_add_countP (s) : card s = countP p s + countP (fun x => ¬p 
x) s
参数：s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_eq_countP_add_countP`：∀ {α : Type u_1} (p : α → Bool) {l : L
ist α}, l.length = List.countP p l + List.countP (fun a => decide ¬p a = true) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `decide_not`：∀ {p : Prop} [g : Decidable p] [h : Decidable ¬p], (decide ¬
p) = !decide p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_eq_countP_add_countP (s) : card s = countP p s + countP (fun x => ¬p x) s :=
  Quot.inductionOn s fun l => by simp [l.length_eq_countP_add_countP p]

@[gcongr]
/-
**Multiset.countP_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_le_of_le {s t} (h : s <= t) : countP p s <= countP p t
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.Sublist.countP_le`：∀ {α : Type u_1} {p : α → Bool} {l₁ l₂ : List α}
, l₁.Sublist l₂ → List.countP p l₁ ≤ List.countP p l₂
-/
theorem countP_le_of_le {s t} (h : s ≤ t) : countP p s ≤ countP p t :=
  leInductionOn h fun s => s.countP_le

@[simp]
/-
**Multiset.countP_True** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_True {s : Multiset α} : countP (fun _ => True) s = card s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.countP_true`：∀ {α : Type u_1}, (List.countP fun x => true) = List.l
ength
-/
theorem countP_True {s : Multiset α} : countP (fun _ => True) s = card s :=
  Quot.inductionOn s fun _l => congrFun List.countP_true _

@[simp]
/-
**Multiset.countP_False** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_False {s : Multiset α} : countP (fun _ => False) s = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.countP_false`：∀ {α : Type u_1}, (List.countP fun x => false) = Func
tion.const (List α) 0
-/
theorem countP_False {s : Multiset α} : countP (fun _ => False) s = 0 :=
  Quot.inductionOn s fun _l => congrFun List.countP_false _
/-
**Multiset.countP_attach** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：countP_attach (s : Multiset α) : s.attach.countP (fun a : {a // a in s} =>
 p a) = s.countP p
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.countP_attach`：∀ {α : Type u_1} {l : List α} {p : α → Bool}, List.c
ountP (fun a => p ↑a) l.attach = List.countP p l
-/
lemma countP_attach (s : Multiset α) : s.attach.countP (fun a : {a // a ∈ s} ↦ p a) = s.countP p :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, coe_countP, coe_attach, coe_countP, ← List.countP_attach (l := l)]
    rfl

variable {p}
/-
**Multiset.countP_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_pos {s} : 0 < countP p s ↔ exists a in s, p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem countP_pos {s} : 0 < countP p s ↔ ∃ a ∈ s, p a :=
  Quot.inductionOn s fun _l => by simp
/-
**Multiset.countP_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_eq_zero {s} : countP p s = 0 ↔ forall a in s, ¬p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
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
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem countP_eq_zero {s} : countP p s = 0 ↔ ∀ a ∈ s, ¬p a :=
  Quot.inductionOn s fun _l => by simp [List.countP_eq_zero]
/-
**Multiset.countP_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_eq_card {s} : countP p s = card s ↔ forall a in s, p a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
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
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem countP_eq_card {s} : countP p s = card s ↔ ∀ a ∈ s, p a :=
  Quot.inductionOn s fun _l => by simp [List.countP_eq_length]
/-
**Multiset.countP_pos_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_pos_of_mem {s a} (h : a in s) (pa : p a) : 0 < countP p s
参数：h : a in s；pa : p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.countP_pos`：countP_pos {s} : 0 < countP p s ↔ exists a in s, p 
a
-/
theorem countP_pos_of_mem {s a} (h : a ∈ s) (pa : p a) : 0 < countP p s :=
  countP_pos.2 ⟨_, h, pa⟩

@[congr]
/-
**Multiset.countP_congr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：countP_congr {s s' : Multiset α} (hs : s = s') {p p' : α -> Prop} [Decidab
lePred p] [DecidablePred p'] (hp : forall x in s, p x = p' x) : s.countP p = s'.
countP p'
参数：hs : s = s'；hp : forall x in s, p x = p' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on₂`：∀ {α : Sort u_1} {β : Sort u_2} {r : α → α → Prop} {
s : β → β → Prop} {δ : Quot r → Quot s → Prop} (q₁ : Quot r)   (q₂ : Quot s), (∀
 (a : α)…
· 使用定理 `List.Perm.countP_congr`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.Perm l₂ 
→ ∀ {p p' : α → Bool}, (∀ x ∈ l₁, p x = p' x) → List.countP p l₁ = List.countP p
' l₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem countP_congr {s s' : Multiset α} (hs : s = s')
    {p p' : α → Prop} [DecidablePred p] [DecidablePred p']
    (hp : ∀ x ∈ s, p x = p' x) : s.countP p = s'.countP p' := by
  revert hs hp
  exact Quot.induction_on₂ s s'
    (fun l l' hs hp => by
      simp only [quot_mk_to_coe'', coe_eq_coe] at hs
      apply hs.countP_congr
      simpa using hp)

end

/-! ### Multiplicity of an element -/


section

variable [DecidableEq α] {s t u : Multiset α}

/-- `count a s` is the multiplicity of `a` in `s`. -/
/-
**Multiset.count** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：count (a : α) : Multiset α -> Nat
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`count a s` is the multiplicity of `a` in `s`.
-/
def count (a : α) : Multiset α → ℕ :=
  countP (a = ·)

@[simp]
/-
**Multiset.coe_count** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_count (a : α) (l : List α) : count a (ofList l) = l.count a
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem coe_count (a : α) (l : List α) : count a (ofList l) = l.count a := by
  simp_rw [count, List.count, coe_countP (a = ·) l, @eq_comm _ a]
  rfl

@[simp]
/-
**Multiset.count_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_zero (a : α) : count a 0 = 0
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem count_zero (a : α) : count a 0 = 0 :=
  rfl

@[simp]
/-
**Multiset.count_cons_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_cons_self (a : α) (s : Multiset α) : count a (a ::ₘ s) = count a s +
 1
参数：a : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.countP_cons_of_pos`：countP_cons_of_pos {a : α} (s) : p a -> cou
ntP p (a ::ₘ s) = countP p s + 1
-/
theorem count_cons_self (a : α) (s : Multiset α) : count a (a ::ₘ s) = count a s + 1 :=
  countP_cons_of_pos _ <| rfl

@[simp]
/-
**Multiset.count_cons_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_cons_of_ne {a b : α} (h : a != b) (s : Multiset α) : count a (b ::ₘ 
s) = count a s
参数：h : a != b；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.countP_cons_of_neg`：countP_cons_of_neg {a : α} (s) : ¬p a -> co
untP p (a ::ₘ s) = countP p s
-/
theorem count_cons_of_ne {a b : α} (h : a ≠ b) (s : Multiset α) : count a (b ::ₘ s) = count a s :=
  countP_cons_of_neg _ <| h
/-
**Multiset.count_le_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_le_card (a : α) (s) : count a s <= card s
参数：a : α；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.countP_le_card`：countP_le_card (s) : countP p s <= card s
-/
theorem count_le_card (a : α) (s) : count a s ≤ card s :=
  countP_le_card _ _

@[gcongr]
/-
**Multiset.count_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_le_of_le (a : α) {s t} : s <= t -> count a s <= count a t
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.countP_le_of_le`：countP_le_of_le {s t} (h : s <= t) : countP p 
s <= countP p t
-/
theorem count_le_of_le (a : α) {s t} : s ≤ t → count a s ≤ count a t :=
  countP_le_of_le _
/-
**Multiset.count_le_count_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_le_count_cons (a b : α) (s : Multiset α) : count a s <= count a (b :
:ₘ s)
参数：a b : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.count_le_of_le`：count_le_of_le (a : α) {s t} : s <= t -> count 
a s <= count a t
· 使用定理 `Multiset.le_cons_self`：le_cons_self (s : Multiset α) (a : α) : s <= a ::
ₘ s
-/
theorem count_le_count_cons (a b : α) (s : Multiset α) : count a s ≤ count a (b ::ₘ s) :=
  count_le_of_le _ (le_cons_self _ _)
/-
**Multiset.count_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_cons (a b : α) (s : Multiset α) : count a (b ::ₘ s) = count a s + if
 a = b then 1 else 0
参数：a b : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.countP_cons`：countP_cons (b : α) (s) : countP p (b ::ₘ s) = cou
ntP p s + if p b then 1 else 0
-/
theorem count_cons (a b : α) (s : Multiset α) :
    count a (b ::ₘ s) = count a s + if a = b then 1 else 0 :=
  countP_cons (a = ·) _ _
/-
**Multiset.count_singleton_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_singleton_self (a : α) : count a ({a} : Multiset α) = 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.nodup_singleton`：nodup_singleton (a : α) : Nodup [a]
· 使用定理 `Multiset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Mu
ltiset α)
-/
theorem count_singleton_self (a : α) : count a ({a} : Multiset α) = 1 :=
  count_eq_one_of_mem (nodup_singleton a) <| mem_singleton_self a
/-
**Multiset.count_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_singleton (a b : α) : count a ({b} : Multiset α) = if a = b then 1 e
lse 0
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_cons`：count_cons (a b : α) (s : Multiset α) : count a (b 
::ₘ s) = count a s + if a = b then 1 else 0
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem count_singleton (a b : α) : count a ({b} : Multiset α) = if a = b then 1 else 0 := by
  simp only [count_cons, ← cons_zero, count_zero, Nat.zero_add]

@[simp]
/-
**Multiset.count_attach** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：count_attach (a : {x // x in s}) : s.attach.count a = s.count ↑a
参数：a : {x // x in s}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.countP_congr`：countP_congr {s s' : Multiset α} (hs : s = s') {p
 p' : α -> Prop} [DecidablePred p] [DecidablePred p'] (hp : forall x in s, p x =
 p' x) : s.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Multiset.countP_attach`：countP_attach (s : Multiset α) : s.attach.countP
 (fun a : {a // a in s} => p a) = s.countP p
-/
lemma count_attach (a : {x // x ∈ s}) : s.attach.count a = s.count ↑a :=
  Eq.trans (countP_congr rfl fun _ _ => by simp [Subtype.ext_iff]) <| countP_attach _ _
/-
**Multiset.count_pos** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem count_pos {a : α} {s : Multiset α} : 0 < count a s ↔ a ∈ s := by simp [count, countP_pos]
/-
**Multiset.one_le_count_iff_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：one_le_count_iff_mem {a : α} {s : Multiset α} : 1 <= count a s ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem one_le_count_iff_mem {a : α} {s : Multiset α} : 1 ≤ count a s ↔ a ∈ s := by
  rw [succ_le_iff, count_pos]

@[simp]
/-
**Multiset.count_eq_zero_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_eq_zero_of_notMem {a : α} {s : Multiset α} (h : a ∉ s) : count a s =
 0
参数：h : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem count_eq_zero_of_notMem {a : α} {s : Multiset α} (h : a ∉ s) : count a s = 0 :=
  by_contradiction fun h' => h <| count_pos.1 (Nat.pos_of_ne_zero h')
/-
**Multiset.count_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：count_ne_zero {a : α} : count a s != 0 ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
-/
lemma count_ne_zero {a : α} : count a s ≠ 0 ↔ a ∈ s := Nat.pos_iff_ne_zero.symm.trans count_pos
/-
**Multiset.count_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multiset α} {a : α}, Multiset
.count a s = 0 ↔ a ∉ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not_right`：Iff.not_right (h : ¬a ↔ b) : a ↔ ¬b
· 使用引理 `Multiset.count_ne_zero`：count_ne_zero {a : α} : count a s != 0 ↔ a in s
-/
@[simp] lemma count_eq_zero {a : α} : count a s = 0 ↔ a ∉ s := count_ne_zero.not_right
/-
**Multiset.count_eq_card** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_eq_card {a : α} {s} : count a s = card s ↔ forall x in s, a = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.countP_congr`：countP_congr {s s' : Multiset α} (hs : s = s') {p
 p' : α -> Prop} [DecidablePred p] [DecidablePred p'] (hp : forall x in s, p x =
 p' x) : s.…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem count_eq_card {a : α} {s} : count a s = card s ↔ ∀ x ∈ s, a = x := by
  simp [countP_eq_card, count, @eq_comm _ a]
/-
**Multiset.ext** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ext {s t : Multiset α} : s = t ↔ forall a, count a s = count a t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `List.perm_iff_count`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {l₁ l
₂ : List α},   l₁.Perm l₂ ↔ ∀ (a : α), List.count a l₁ = List.count a l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem ext {s t : Multiset α} : s = t ↔ ∀ a, count a s = count a t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => Quotient.eq.trans <| by
    simp only [quot_mk_to_coe, coe_count]
    apply perm_iff_count

@[ext]
/-
**Multiset.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：ext' {s t : Multiset α} : (forall a, count a s = count a t) -> s = t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.ext`：ext {s t : Multiset α} : s = t ↔ forall a, count a s = cou
nt a t
-/
theorem ext' {s t : Multiset α} : (∀ a, count a s = count a t) → s = t :=
  ext.2
/-
**Multiset.count_injective** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：count_injective : Injective fun (s : Multiset α) a => s.count a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
lemma count_injective : Injective fun (s : Multiset α) a ↦ s.count a :=
  fun _s _t hst ↦ ext' <| congr_fun hst
/-
**Multiset.le_iff_count** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_iff_count {s t : Multiset α} : s <= t ↔ forall a, count a s <= count a 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_iff_count {s t : Multiset α} : s ≤ t ↔ ∀ a, count a s ≤ count a t :=
  Quotient.inductionOn₂ s t fun _ _ ↦ by simp [subperm_iff_count]

end

/-! ### Lift a relation to `Multiset`s -/

section Rel

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

/-
**Multiset.Rel.countP_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Rel`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [IsTrans α r] [Std.Symm r] {s t : Mult
iset α} (x : α) [inst : DecidablePred (r x)],   Multiset.Rel r s t → Multiset.co
untP (r x) s = Multiset.countP (r x) t
参数：r : α → α → Prop；x : α；r x；r x；r x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.rel_zero_left`：rel_zero_left {b : Multiset β} : Rel r 0 b ↔ b =
 0
· 使用定理 `Multiset.rel_cons_left`：rel_cons_left {a as bs} : Rel r (a ::ₘ as) bs ↔ 
exists b bs', r a b ∧ Rel r as bs' ∧ bs = b ::ₘ bs'
· 使用定理 `Multiset.countP_cons`：countP_cons (b : α) (s) : countP p (b ::ₘ s) = cou
ntP p s + if p b then 1 else 0
· 使用定理 `if_congr`：if_congr (h_c : P ↔ Q) (h_t : x = u) (h_e : y = v) : ite P x y
 = ite Q u v
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Rel.countP_eq (r : α → α → Prop) [IsTrans α r] [Std.Symm r] {s t : Multiset α} (x : α)
    [DecidablePred (r x)] (h : Rel r s t) : countP (r x) s = countP (r x) t := by
  induction s using Multiset.induction_on generalizing t with
  | empty => rw [rel_zero_left.mp h]
  | cons y s ih =>
    obtain ⟨b, bs, hb1, hb2, rfl⟩ := rel_cons_left.mp h
    rw [countP_cons, countP_cons, ih hb2]
    simp only [Nat.add_right_inj]
    exact (if_congr ⟨fun h => _root_.trans h hb1, fun h => _root_.trans h (symm hb1)⟩ rfl rfl)

end Rel

section Nodup

variable {s : Multiset α} {a : α}

/-
**Multiset.nodup_iff_count_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_iff_count_le_one [DecidableEq α] {s : Multiset α} : Nodup s ↔ forall
 a, count a s <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem nodup_iff_count_le_one [DecidableEq α] {s : Multiset α} : Nodup s ↔ ∀ a, count a s ≤ 1 :=
  Quot.induction_on s fun _l => by
    simp only [quot_mk_to_coe'', coe_nodup, coe_count]
    exact List.nodup_iff_count_le_one
/-
**Multiset.nodup_iff_count_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_iff_count_eq_one [DecidableEq α] : Nodup s ↔ forall a in s, count a 
s = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.coe_count`：coe_count (a : α) (l : List α) : count a (ofList l) 
= l.count a
· 使用定理 `List.nodup_iff_count_eq_one`：nodup_iff_count_eq_one [BEq α] [LawfulBEq α
] : Nodup l ↔ forall a in l, count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
-/
theorem nodup_iff_count_eq_one [DecidableEq α] : Nodup s ↔ ∀ a ∈ s, count a s = 1 :=
  Quot.induction_on s fun _l => by simpa using List.nodup_iff_count_eq_one

@[simp]
/-
**Multiset.count_eq_one_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_eq_one_of_mem [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s)
 (h : a in s) : count a s = 1
参数：d : Nodup s；h : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.nodup_iff_count_eq_one`：nodup_iff_count_eq_one [DecidableEq α] 
: Nodup s ↔ forall a in s, count a s = 1
-/
theorem count_eq_one_of_mem [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) (h : a ∈ s) :
    count a s = 1 :=
  nodup_iff_count_eq_one.mp d a h
/-
**Multiset.count_eq_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_eq_of_nodup [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) :
 count a s = if a in s then 1 else 0
参数：d : Nodup s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Multiset.count_eq_one_of_mem`：count_eq_one_of_mem [DecidableEq α] {a : α
} {s : Multiset α} (d : Nodup s) (h : a in s) : count a s = 1
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
-/
theorem count_eq_of_nodup [DecidableEq α] {a : α} {s : Multiset α} (d : Nodup s) :
    count a s = if a ∈ s then 1 else 0 := by
  split_ifs with h
  · exact count_eq_one_of_mem d h
  · exact count_eq_zero_of_notMem h

end Nodup

end Multiset

