/-
Copyright (c) 2025 Joseph Myers, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yaël Dillies
-/
module

public import Mathlib.Tactic.MkIffOfInductiveProp
public import Batteries.Data.List.Lemmas

/-!
# Triplewise predicates on list.

## Main definitions

* `List.Triplewise` says that a predicate applies to all ordered triples of elements of a list.

-/

public section


namespace List

variable {α β : Type*}

/-- Whether a predicate holds for all ordered triples of elements of a list. -/
@[mk_iff]
/-
**List.Triplewise** 是 Mathlib 中的一个归纳类型，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → α → α → Prop) → List α → Prop
参数：α → α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whether a predicate holds for all ordered triples of elements of a list.
-/
inductive Triplewise (p : α → α → α → Prop) : List α → Prop
  | nil : [].Triplewise p
  | cons {a : α} {l : List α} : l.Pairwise (p a) → l.Triplewise p → (a :: l).Triplewise p

attribute [simp, grind ←] Triplewise.nil

variable {a b c : α} {l l₁ l₂ : List α} {p q : α → α → α → Prop} {f : α → β} {p' : β → β → β → Prop}

@[grind =]
/-
**List.triplewise_cons** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：triplewise_cons : (a :: l).Triplewise p ↔ l.Pairwise (p a) ∧ l.Triplewise 
p
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triplewise_cons : (a :: l).Triplewise p ↔ l.Pairwise (p a) ∧ l.Triplewise p := by
  grind [triplewise_iff]

variable (a b p)
/-
**List.triplewise_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (a : α) (p : α → α → α → Prop), List.Triplewise p [a]
参数：a : α；p : α → α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma triplewise_singleton : [a].Triplewise p := by
  simp [triplewise_cons]
/-
**List.triplewise_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (a b : α) (p : α → α → α → Prop), List.Triplewise p [a, b
]
参数：a b : α；p : α → α → α → Prop。
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
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma triplewise_pair : [a, b].Triplewise p := by
  simp [triplewise_cons]

variable {a b p}
/-
**List.triplewise_triple** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {a b c : α} {p : α → α → α → Prop}, List.Triplewise p [a,
 b, c] ↔ p a b c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma triplewise_triple : [a, b, c].Triplewise p ↔ p a b c := by
  simp [triplewise_cons]
/-
**List.Triplewise.imp** 是 Mathlib 中的一个定理，位于命名空间 `List.Triplewise`。
形式化陈述：∀ {α : Type u_1} {l : List α} {p q : α → α → α → Prop},   (∀ {a b c : α}, 
p a b c → q a b c) → List.Triplewise p l → List.Triplewise q l
参数：∀ {a b c : α}, p a b c → q a b c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
-/
lemma Triplewise.imp (h : ∀ {a b c}, p a b c → q a b c) (hl : l.Triplewise p) :
    l.Triplewise q := by
  induction hl with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.imp h) ih
/-
**List.triplewise_map** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：triplewise_map : (l.map f).Triplewise p' ↔ l.Triplewise (fun a b c => p' (
f a) (f b) (f c))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma triplewise_map :
    (l.map f).Triplewise p' ↔ l.Triplewise (fun a b c ↦ p' (f a) (f b) (f c)) := by
  induction l with
  | nil => simp
  | cons h t ih => simp [map, triplewise_cons, ih, pairwise_map]
/-
**List.Triplewise.of_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Triplewise`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : List α} {p : α → α → α → Prop} {f : α
 → β} {p' : β → β → β → Prop},   (∀ {a b c : α}, p' (f a) (f b) (f c) → p a b c)
 → List.Triplewise p' (List.map f l) → List.Triplewise p l
参数：∀ {a b c : α}, p' (f a) (f b) (f c) → p a b c；List.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Triplewise.imp`：∀ {α : Type u_1} {l : List α} {p q : α → α → α → Pr
op},   (∀ {a b c : α}, p a b c → q a b c) → List.Triplewise p l → List.Triplewis
e q l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `List.triplewise_map`：triplewise_map : (l.map f).Triplewise p' ↔ l.Triple
wise (fun a b c => p' (f a) (f b) (f c))
-/
lemma Triplewise.of_map
    (h : ∀ {a b c}, p' (f a) (f b) (f c) → p a b c) (hl : (l.map f).Triplewise p') :
    l.Triplewise p := by
  rw [triplewise_map] at hl
  exact hl.imp h
/-
**List.Triplewise.map** 是 Mathlib 中的一个定理，位于命名空间 `List.Triplewise`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : List α} {p : α → α → α → Prop} {f : α
 → β} {p' : β → β → β → Prop},   (∀ {a b c : α}, p a b c → p' (f a) (f b) (f c))
 → List.Triplewise p l → List.Triplewise p' (List.map f l)
参数：∀ {a b c : α}, p a b c → p' (f a) (f b) (f c)；List.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `List.triplewise_map`：triplewise_map : (l.map f).Triplewise p' ↔ l.Triple
wise (fun a b c => p' (f a) (f b) (f c))
· 使用定理 `List.Triplewise.imp`：∀ {α : Type u_1} {l : List α} {p q : α → α → α → Pr
op},   (∀ {a b c : α}, p a b c → q a b c) → List.Triplewise p l → List.Triplewis
e q l
-/
lemma Triplewise.map (h : ∀ {a b c}, p a b c → p' (f a) (f b) (f c)) (hl : l.Triplewise p) :
    (l.map f).Triplewise p' :=
  triplewise_map.2 (hl.imp h)
/-
**List.triplewise_iff_getElem** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：triplewise_iff_getElem : l.Triplewise p ↔ forall i j k (hij : i < j) (hjk 
: j < k) (hk : k < l.length), p l[i] l[j] l[k]
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
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `forall_false`：∀ (p : False → Prop), (∀ (h : False), p h) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma triplewise_iff_getElem : l.Triplewise p ↔ ∀ i j k (hij : i < j) (hjk : j < k)
    (hk : k < l.length), p l[i] l[j] l[k] := by
  induction l with
  | nil => simp
  | cons head tail ih =>
    simp only [triplewise_cons, length_cons, pairwise_iff_getElem, ih]
    refine ⟨fun ⟨hh, ht⟩ i j k hij hjk hk ↦ ?_,
            fun h ↦ ⟨fun i j hi hj hij ↦ ?_, fun i j k hij hjk hk ↦ ?_⟩⟩
    · grind
    · simpa using! h 0 (i + 1) (j + 1) (by lia) (by lia) (by lia)
    · simpa using! h (i + 1) (j + 1) (k + 1) (by lia) (by lia) (by lia)
/-
**List.triplewise_append** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：triplewise_append : (l₁ ++ l₂).Triplewise p ↔ l₁.Triplewise p ∧ l₂.Triplew
ise p ∧ (forall a in l₁, l₂.Pairwise (p a)) ∧ forall a in l₂, l₁.Pairwise fun x 
y => p x y a
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma triplewise_append : (l₁ ++ l₂).Triplewise p ↔ l₁.Triplewise p ∧ l₂.Triplewise p ∧
    (∀ a ∈ l₁, l₂.Pairwise (p a)) ∧ ∀ a ∈ l₂, l₁.Pairwise fun x y ↦ p x y a := by
  induction l₁ with grind [pairwise_cons]
/-
**List.triplewise_reverse** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：triplewise_reverse : l.reverse.Triplewise p ↔ l.Triplewise fun a b c => p 
c b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `false_implies`：∀ (p : Prop), (False → p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma triplewise_reverse : l.reverse.Triplewise p ↔ l.Triplewise fun a b c ↦ p c b a := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [triplewise_append, pairwise_reverse, triplewise_cons, ih, and_comm]

end List

