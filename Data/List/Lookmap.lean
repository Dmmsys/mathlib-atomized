/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Batteries.Data.List.Basic
public import Mathlib.Init

/-! ### lookmap -/

public section

variable {α β : Type*}

namespace List

variable (f : α → Option α)

/-
**List.lookmap.go_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem lookmap.go_append (l : List α) (acc : Array α) :
    lookmap.go f l acc = acc.toListAppend (lookmap f l) := by
  cases l with
  | nil => simp [go, lookmap]
  | cons hd tl =>
    rw [lookmap, go, go]
    cases f hd with
    | none =>
      simp only [go_append tl _, Array.toListAppend_eq, append_assoc, Array.toList_push]
      rfl
    | some a => simp

@[simp, grind =]
/-
**List.lookmap_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookmap_nil : [].lookmap f = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookmap_nil : [].lookmap f = [] :=
  rfl

@[simp]
/-
**List.lookmap_cons_none** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookmap_cons_none {a : α} (l : List α) (h : f a = none) : (a :: l).lookmap
 f = a :: l.lookmap f
参数：l : List α；h : f a = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Array.toListAppend_eq`：∀ {α : Type u_1} {xs : Array α} {l : List α}, xs.
toListAppend l = xs.toList ++ l
· 使用定理 `_private.Mathlib.Data.List.Lookmap.0.List.lookmap.go_append`：∀ {α : Type
 u_1} (f : α → Option α) (l : List α) (acc : Array α),   List.lookmap.go f l acc
 = acc.toListAppend (List.lookmap f l)
· 使用定理 `List.lookmap.eq_1`：∀ {α : Type u_1} (f : α → Option α) (l : List α), Lis
t.lookmap f l = List.lookmap.go f l #[]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.push_toArray`：∀ {α : Type u_1} (l : List α) (a : α), l.toArray.push
 a = (l ++ [a]).toArray
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lookmap_cons_none {a : α} (l : List α) (h : f a = none) :
    (a :: l).lookmap f = a :: l.lookmap f := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, nil_append]
  rw [lookmap.go_append, lookmap, h]; simp

@[simp]
/-
**List.lookmap_cons_some** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) : (a :: l).loo
kmap f = b :: l
参数：l : List α；h : f a = some b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Array.toListAppend_eq`：∀ {α : Type u_1} {xs : Array α} {l : List α}, xs.
toListAppend l = xs.toList ++ l
-/
theorem lookmap_cons_some {a b : α} (l : List α) (h : f a = some b) :
    (a :: l).lookmap f = b :: l := by
  simp only [lookmap, lookmap.go, Array.toListAppend_eq, nil_append]
  rw [h]

@[grind =]
/-
**List.lookmap_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookmap_cons {a : α} {l : List α} : (a :: l).lookmap f = match f a with | 
none => a :: l.lookmap f | some b => b :: l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.lookmap_cons_none`：lookmap_cons_none {a : α} (l : List α) (h : f a 
= none) : (a :: l).lookmap f = a :: l.lookmap f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.lookmap_cons_some`：lookmap_cons_some {a b : α} (l : List α) (h : f 
a = some b) : (a :: l).lookmap f = b :: l
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem lookmap_cons {a : α} {l : List α} :
    (a :: l).lookmap f = match f a with
    | none => a :: l.lookmap f
    | some b => b :: l := by
  cases h : f a <;> simp_all
/-
**List.lookmap_some** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α), List.lookmap some l = l
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.lookmap_cons_some`：lookmap_cons_some {a b : α} (l : List α) (h : f 
a = some b) : (a :: l).lookmap f = b :: l
-/
theorem lookmap_some : ∀ l : List α, l.lookmap some = l
  | [] => rfl
  | _ :: rest => lookmap_cons_some some rest rfl
/-
**List.lookmap_none** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (l : List α), List.lookmap (fun x => none) l = l
参数：l : List α；fun x => none。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookmap_none : ∀ l : List α, (l.lookmap fun _ => none) = l
  | [] => rfl
  | a :: l => (lookmap_cons_none _ l rfl).trans (congrArg (cons a) (lookmap_none l))
/-
**List.lookmap_congr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookmap_congr {f g : α -> Option α} : forall {l : List α}, (forall a in l,
 f a = g a) -> l.lookmap f = l.lookmap g | [], _ => rfl | a :: l, H => by obtain
 ⟨H₁, H₂⟩
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookmap_congr {f g : α → Option α} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.lookmap f = l.lookmap g
  | [], _ => rfl
  | a :: l, H => by
    obtain ⟨H₁, H₂⟩ := forall_mem_cons.1 H
    rcases h : g a with - | b
    · simp [h, H₁.trans h, lookmap_congr H₂]
    · simp [lookmap_cons_some _ _ h, lookmap_cons_some _ _ (H₁.trans h)]
/-
**List.lookmap_of_forall_not** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookmap_of_forall_not {l : List α} (H : forall a in l, f a = none) : l.loo
kmap f = l
参数：H : forall a in l, f a = none。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.lookmap_congr`：lookmap_congr {f g : α -> Option α} : forall {l : Li
st α}, (forall a in l, f a = g a) -> l.lookmap f = l.lookmap g | [], _ => rfl | 
a :: l, …
· 使用定理 `List.lookmap_none`：∀ {α : Type u_1} (l : List α), List.lookmap (fun x =>
 none) l = l
-/
theorem lookmap_of_forall_not {l : List α} (H : ∀ a ∈ l, f a = none) : l.lookmap f = l :=
  (lookmap_congr H).trans (lookmap_none l)
/-
**List.lookmap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → Option α) (g : α → β),   (∀ (a b 
: α), b ∈ f a → g a = g b) → ∀ (l : List α), List.map g (List.lookmap f l) = Lis
t.map g l
参数：f : α → Option α；g : α → β；∀ (a b : α), b ∈ f a → g a = g b；l : List α；List.l
ookmap f l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lookmap_map_eq (g : α → β) (h : ∀ (a), ∀ b ∈ f a, g a = g b) :
    ∀ l : List α, map g (l.lookmap f) = map g l
  | [] => rfl
  | a :: l => by
    rcases h' : f a with - | b
    · simpa [h'] using lookmap_map_eq _ h l
    · simp [lookmap_cons_some _ _ h', h _ _ h']
/-
**List.lookmap_id'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：lookmap_id' (h : forall (a), forall b in f a, a = b) (l : List α) : l.look
map f = l
参数：h : forall (a), forall b in f a, a = b；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
· 使用定理 `List.lookmap_map_eq`：∀ {α : Type u_1} {β : Type u_2} (f : α → Option α) 
(g : α → β),   (∀ (a b : α), b ∈ f a → g a = g b) → ∀ (l : List α), List.map g (
List.look…
-/
theorem lookmap_id' (h : ∀ (a), ∀ b ∈ f a, a = b) (l : List α) : l.lookmap f = l := by
  rw [← map_id (l.lookmap f), lookmap_map_eq, map_id]; exact h

@[simp, grind =]
/-
**List.length_lookmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_lookmap (l : List α) : length (l.lookmap f) = length l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.lookmap_map_eq`：∀ {α : Type u_1} {β : Type u_2} (f : α → Option α) 
(g : α → β),   (∀ (a b : α), b ∈ f a → g a = g b) → ∀ (l : List α), List.map g (
List.look…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem length_lookmap (l : List α) : length (l.lookmap f) = length l := by
  rw [← length_map, lookmap_map_eq _ fun _ => (), length_map]; simp

open Perm in
/-
**List.perm_lookmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_lookmap (f : α -> Option α) {l₁ l₂ : List α} (H : Pairwise (fun a b =
> forall c in f a, forall d in f b, a = b ∧ c = d) l₁) (p : l₁ ~ l₂) : lookmap f
 l₁ ~ lookmap f l₂
参数：f : α -> Option α；H : Pairwise (fun a b => forall c in f a, forall d in f b, 
a = b ∧ c = d) l₁；p : l₁ ~ l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.lookmap_cons_none`：lookmap_cons_none {a : α} (l : List α) (h : f a 
= none) : (a :: l).lookmap f = a :: l.lookmap f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.lookmap_cons_some`：lookmap_cons_some {a b : α} (l : List α) (h : f 
a = some b) : (a :: l).lookmap f = b :: l
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `List.Perm.pairwise_iff`：∀ {α : Type u_1} {R : α → α → Prop},   (∀ {x y :
 α}, R x y → R y x) → ∀ {l₁ l₂ : List α}, l₁.Perm l₂ → (List.Pairwise R l₁ ↔ Lis
t.Pairwise R…
-/
theorem perm_lookmap (f : α → Option α) {l₁ l₂ : List α}
    (H : Pairwise (fun a b => ∀ c ∈ f a, ∀ d ∈ f b, a = b ∧ c = d) l₁) (p : l₁ ~ l₂) :
    lookmap f l₁ ~ lookmap f l₂ := by
  induction p with
  | nil => simp
  | cons a p IH =>
    cases h : f a
    · simpa [h] using IH (pairwise_cons.1 H).2
    · simp [lookmap_cons_some _ _ h, p]
  | swap a b l =>
    rcases h₁ : f a with - | c <;> rcases h₂ : f b with - | d
    · simpa [h₁, h₂] using Perm.swap _ _ _
    · simpa [h₁, lookmap_cons_some _ _ h₂] using Perm.swap _ _ _
    · simpa [lookmap_cons_some _ _ h₁, h₂] using Perm.swap _ _ _
    · rcases (pairwise_cons.1 H).1 _ (mem_cons.2 (Or.inl rfl)) _ h₂ _ h₁ with ⟨rfl, rfl⟩
      exact Perm.refl _
  | trans p₁ _ IH₁ IH₂ =>
    refine (IH₁ H).trans (IH₂ ((p₁.pairwise_iff ?_).1 H))
    grind

end List

