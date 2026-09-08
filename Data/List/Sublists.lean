/-
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.List.Perm.Subperm
public import Mathlib.Data.List.Lex
public import Mathlib.Data.List.Induction
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Prod.Basic
public import Mathlib.Tactic.Finiteness.Attr

/-! # sublists

`List.Sublists` gives a list of all (not necessarily contiguous) sublists of a list.

This file contains basic results on this function.
-/

@[expose] public section

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

open Nat

namespace List

/-! ### sublists -/

@[simp]
/-
**List.sublists'_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u}, [].sublists' = [[]]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]

--- 原说明 ---
### sublists
-/
theorem sublists'_nil : sublists' (@nil α) = [[]] :=
  rfl

@[simp]
/-
**List.sublists'_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (a : α), [a].sublists' = [[], [a]]
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
-/
theorem sublists'_singleton (a : α) : sublists' [a] = [[], [a]] :=
  rfl

/-- Auxiliary helper definition for `sublists'` -/
/-
**List.sublists'Aux** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u} → α → List (List α) → List (List α) → List (List α)
参数：List α；List α；List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary helper definition for `sublists'`
-/
def sublists'Aux (a : α) (r₁ r₂ : List (List α)) : List (List α) :=
  r₁.foldl (init := r₂) fun r l => r ++ [a :: l]
/-
**List.sublists'Aux_eq_array_foldl** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (a : α) (r₁ r₂ : List (List α)),   List.sublists'Aux a r₁ r
₂ = (Array.foldl (fun r l => r.push (a :: l)) r₂.toArray r₁.toArray).toList
参数：a : α；r₁ r₂ : List (List α)；Array.foldl (fun r l => r.push (a :: l)) r₂.toArr
ay r₁.toArray。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'Aux.eq_1`：∀ {α : Type u} (a : α) (r₁ r₂ : List (List α)), 
List.sublists'Aux a r₁ r₂ = List.foldl (fun r l => r ++ [a :: l]) r₂ r₁
· 使用定理 `Array.foldl_toList`：∀ {β : Type u_1} {α : Type u_2} (f : β → α → β) {ini
t : β} {xs : Array α},   List.foldl f init xs.toList = Array.foldl f init xs
· 使用定理 `List.foldl_hom`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} (f : α₁
 → α₂) {g₁ : α₁ → β → α₁} {g₂ : α₂ → β → α₂} {l : List β}   {init : α₁}, (∀ (x :
 α₁)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Array.toList_push`：∀ {α : Type u_1} {xs : Array α} {x : α}, (xs.push x).
toList = xs.toList ++ [x]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Array.foldl_congr`：∀ {α : Type u_1} {β : Type u_2} {as bs : Array α},   
as = bs →     ∀ {f g : β → α → β},       f = g →         ∀ {a b : β},           
a = b →…
· 使用定理 `List.size_toArray`：∀ {α : Type u} {as : List α}, as.toArray.size = as.le
ngth
· 使用定理 `List.foldl_toArray'`：∀ {β : Type u_1} {α : Type u_2} {stop : ℕ} (f : β →
 α → β) (init : β) (l : List α),   stop = l.toArray.size → Array.foldl f init l.
toArray 0…
· 使用定理 `List.foldl_append_eq_append`：∀ {α : Type u_1} {β : Type u_2} {l : List α
} {f : α → List β} {l' : List β},   List.foldl (fun x1 x2 => x1 ++ f x2) l' l = 
l' ++ (List.map f…
· 使用定理 `List.foldl_push_eq_append`：∀ {α : Type u_1} {β : Type u_2} {l : List α} 
{f : α → β} {xs : Array β},   List.foldl (fun xs x => xs.push (f x)) xs l = xs +
+ (List.map f l…
· 使用定理 `List.append_toArray`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁.toArray ++ l₂
.toArray = (l₁ ++ l₂).toArray
· 使用定理 `List.append_cancel_left_eq`：∀ {α : Type u_1} (as bs cs : List α), (as ++
 bs = as ++ cs) = (bs = cs)
-/
theorem sublists'Aux_eq_array_foldl (a : α) : ∀ (r₁ r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = ((r₁.toArray).foldl (init := r₂.toArray)
      (fun r l => r.push (a :: l))).toList := by
  intro r₁ r₂
  rw [sublists'Aux, Array.foldl_toList]
  have := List.foldl_hom Array.toList (g₁ := fun r l => r.push (a :: l))
    (g₂ := fun r l => r ++ [a :: l]) (l := r₁) (init := r₂.toArray) (by simp)
  simpa using this
/-
**List.sublists'_eq_sublists'Aux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), l.sublists' = List.foldr (fun a r => List.sub
lists'Aux a r r) [[]] l
参数：l : List α；fun a r => List.sublists'Aux a r r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.sublists'Aux_eq_array_foldl`：∀ {α : Type u} (a : α) (r₁ r₂ : List (
List α)),   List.sublists'Aux a r₁ r₂ = (Array.foldl (fun r l => r.push (a :: l)
) r₂.toArray r₁.toArra…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.foldr_hom`：∀ {β₁ : Type u_1} {β₂ : Type u_2} {α : Type u_3} (f : β₁
 → β₂) {g₁ : α → β₁ → β₁} {g₂ : α → β₂ → β₂} {l : List α}   {init : β₁}, (∀ (x :
 α) …
-/
theorem sublists'_eq_sublists'Aux (l : List α) :
    sublists' l = l.foldr (fun a r => sublists'Aux a r r) [[]] := by
  simp only [sublists', sublists'Aux_eq_array_foldl]
  rw [← List.foldr_hom Array.toList]
  · intros; congr
/-
**List.sublists'Aux_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (a : α) (r₁ r₂ : List (List α)), List.sublists'Aux a r₁ r₂ 
= r₂ ++ List.map (List.cons a) r₁
参数：a : α；r₁ r₂ : List (List α)；List.cons a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_singleton`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : α},
 List.map f [a] = [f a]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.sublists'Aux.eq_1`：∀ {α : Type u} (a : α) (r₁ r₂ : List (List α)), 
List.sublists'Aux a r₁ r₂ = List.foldl (fun r l => r ++ [a :: l]) r₂ r₁
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `List.foldl.eq_2`：∀ {α : Type u} {β : Type v} (f : α → β → α) (x : α) (b 
: β) (l : List β),   List.foldl f x (b :: l) = List.foldl f (f x b) l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.foldl_append_eq_append`：∀ {α : Type u_1} {β : Type u_2} {l : List α
} {f : α → List β} {l' : List β},   List.foldl (fun x1 x2 => x1 ++ f x2) l' l = 
l' ++ (List.map f…
-/
theorem sublists'Aux_eq_map (a : α) (r₁ : List (List α)) : ∀ (r₂ : List (List α)),
    sublists'Aux a r₁ r₂ = r₂ ++ map (cons a) r₁ :=
  List.reverseRecOn r₁ (fun _ => by simp [sublists'Aux]) fun r₁ l ih r₂ => by
    rw [map_append, map_singleton, ← append_assoc, ← ih, sublists'Aux, foldl_append, foldl]
    simp [sublists'Aux]

@[simp 900]
/-
**List.sublists'_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (a : α) (l : List α), (a :: l).sublists' = l.sublists' ++ L
ist.map (List.cons a) l.sublists'
参数：a : α；l : List α；a :: l；List.cons a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'_eq_sublists'Aux`：∀ {α : Type u} (l : List α), l.sublists'
 = List.foldr (fun a r => List.sublists'Aux a r r) [[]] l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.sublists'Aux_eq_map`：∀ {α : Type u} (a : α) (r₁ r₂ : List (List α))
, List.sublists'Aux a r₁ r₂ = r₂ ++ List.map (List.cons a) r₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sublists'_cons (a : α) (l : List α) :
    sublists' (a :: l) = sublists' l ++ map (cons a) (sublists' l) := by
  simp [sublists'_eq_sublists'Aux, foldr_cons, sublists'Aux_eq_map]

@[simp]
/-
**List.mem_sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_sublists' {s t : List α} : s in sublists' t ↔ s <+ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `List.eq_nil_of_sublist_nil`：∀ {α : Type u_1} {l : List α}, l.Sublist [] 
→ l = []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.sublist_cons_of_sublist`：sublist_cons_of_sublist (a : α) (h : l₁ <+
 l₂) : l₁ <+ a :: l₂
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem mem_sublists' {s t : List α} : s ∈ sublists' t ↔ s <+ t := by
  induction t generalizing s with
  | nil =>
    simp only [sublists'_nil, mem_singleton]
    exact ⟨fun h => by rw [h], eq_nil_of_sublist_nil⟩
  | cons a t IH => ?_
  simp only [sublists'_cons, mem_append, IH, mem_map]
  constructor <;> intro h
  · rcases h with (h | ⟨s, h, rfl⟩)
    · exact sublist_cons_of_sublist _ h
    · exact h.cons_cons _
  · obtain - | ⟨-, h⟩ | ⟨-, h⟩ := h
    · exact Or.inl h
    · exact Or.inr ⟨_, h, rfl⟩

@[simp]
/-
**List.length_sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), l.sublists'.length = 2 ^ l.length
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
-/
theorem length_sublists' : ∀ l : List α, length (sublists' l) = 2 ^ length l
  | [] => rfl
  | a :: l => by
    simp +arith only [sublists'_cons, length_append, length_sublists' l,
      length_map, length, Nat.pow_succ']

@[simp]
/-
**List.sublists_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_nil : sublists (@nil α) = [[]]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublists_nil : sublists (@nil α) = [[]] :=
  rfl

@[simp]
/-
**List.sublists_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_singleton (a : α) : sublists [a] = [[], [a]]
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublists_singleton (a : α) : sublists [a] = [[], [a]] :=
  rfl

/-- Auxiliary helper function for `sublists` -/
/-
**List.sublistsAux** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：sublistsAux (a : α) (r : List (List α)) : List (List α)
参数：a : α；r : List (List α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary helper function for `sublists`
-/
def sublistsAux (a : α) (r : List (List α)) : List (List α) :=
  r.foldl (init := []) fun r l => r ++ [l, a :: l]
/-
**List.sublistsAux_eq_array_foldl** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsAux_eq_array_foldl : sublistsAux = fun (a : α) (r : List (List α))
 => (r.toArray.foldl (init
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.foldl_hom`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} (f : α₁
 → α₂) {g₁ : α₁ → β → α₁} {g₂ : α₂ → β → α₂} {l : List β}   {init : α₁}, (∀ (x :
 α₁)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Array.toList_push`：∀ {α : Type u_1} {xs : Array α} {x : α}, (xs.push x).
toList = xs.toList ++ [x]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.foldl_append_eq_append`：∀ {α : Type u_1} {β : Type u_2} {l : List α
} {f : α → List β} {l' : List β},   List.foldl (fun x1 x2 => x1 ++ f x2) l' l = 
l' ++ (List.map f…
· 使用定理 `Array.foldl_congr`：∀ {α : Type u_1} {β : Type u_2} {as bs : Array α},   
as = bs →     ∀ {f g : β → α → β},       f = g →         ∀ {a b : β},           
a = b →…
· 使用定理 `List.size_toArray`：∀ {α : Type u} {as : List α}, as.toArray.size = as.le
ngth
· 使用定理 `List.foldl_toArray'`：∀ {β : Type u_1} {α : Type u_2} {stop : ℕ} (f : β →
 α → β) (init : β) (l : List α),   stop = l.toArray.size → Array.foldl f init l.
toArray 0…
-/
theorem sublistsAux_eq_array_foldl :
    sublistsAux = fun (a : α) (r : List (List α)) =>
      (r.toArray.foldl (init := #[])
        fun r l => (r.push l).push (a :: l)).toList := by
  funext a r
  simp only [sublistsAux]
  have := foldl_hom Array.toList (g₁ := fun r l => (r.push l).push (a :: l))
    (g₂ := fun r l => r ++ [l, a :: l]) (l := r) (init := #[]) (by simp)
  simpa using this
/-
**List.sublistsAux_eq_flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsAux_eq_flatMap : sublistsAux = fun (a : α) (r : List (List α)) => 
r.flatMap fun l => [l, a :: l]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatMap_nil`：∀ {α : Type u} {β : Type v} {f : α → List β}, List.fla
tMap f [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.flatMap_append`：∀ {α : Type u} {β : Type v} {xs ys : List α} {f : α
 → List β},   List.flatMap f (xs ++ ys) = List.flatMap f xs ++ List.flatMap f ys
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.flatMap_singleton`：∀ {α : Type u_1} {β : Type u_2} (f : α → List β)
 (x : α), List.flatMap f [x] = f x
· 使用定理 `List.sublistsAux.eq_1`：∀ {α : Type u} (a : α) (r : List (List α)), List.
sublistsAux a r = List.foldl (fun r l => r ++ [l, a :: l]) [] r
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.foldl_append_eq_append`：∀ {α : Type u_1} {β : Type u_2} {l : List α
} {f : α → List β} {l' : List β},   List.foldl (fun x1 x2 => x1 ++ f x2) l' l = 
l' ++ (List.map f…
-/
theorem sublistsAux_eq_flatMap :
    sublistsAux = fun (a : α) (r : List (List α)) => r.flatMap fun l => [l, a :: l] :=
  funext fun a => funext fun r =>
  List.reverseRecOn r
    (by simp [sublistsAux])
    (fun r l ih => by
      rw [flatMap_append, ← ih, flatMap_singleton, sublistsAux, foldl_append]
      simp [sublistsAux])
/-
**List.sublists_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_append (l₁ l₂ : List α) : sublists (l₁ ++ l₂) = (sublists l₂) >>=
 (fun x => (sublists l₁).map (· ++ x))
参数：l₁ l₂ : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {b : 
β} {l l' : List α},   List.foldr f b (l ++ l') = List.foldr f (List.foldr f b l'
) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.flatMap_singleton'`：∀ {α : Type u_1} (l : List α), List.flatMap (fu
n x => [x]) l = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.foldr_cons`：∀ {α : Type u} {β : Type v} {a : α} {l : List α} {f : α
 → β → β} {b : β},   List.foldr f b (a :: l) = f a (List.foldr f b l)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_flatten`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {L : List 
(List α)},   List.map f L.flatten = (List.map (List.map f) L).flatten
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.flatten_flatten`：∀ {α : Type u_1} {L : List (List (List α))}, L.fla
tten.flatten = (List.map List.flatten L).flatten
-/
theorem sublists_append (l₁ l₂ : List α) :
    sublists (l₁ ++ l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (· ++ x)) := by
  simp only [sublists, foldr_append]
  induction l₁ with
  | nil => simp
  | cons a l₁ ih =>
    rw [foldr_cons, ih]
    simp [List.flatMap, flatten_flatten, Function.comp_def]
/-
**List.sublists_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_cons (a : α) (l : List α) : sublists (a :: l) = sublists l >>= (f
un x => [x, a :: x])
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists_append`：sublists_append (l₁ l₂ : List α) : sublists (l₁ ++
 l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (· ++ x))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sublists_cons (a : α) (l : List α) :
    sublists (a :: l) = sublists l >>= (fun x => [x, a :: x]) :=
  show sublists ([a] ++ l) = _ by
  rw [sublists_append]
  simp only [sublists_singleton, map_cons, bind_eq_flatMap, nil_append, cons_append, map_nil]

@[simp]
/-
**List.sublists_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_concat (l : List α) (a : α) : sublists (l ++ [a]) = sublists l ++
 map (fun x => x ++ [a]) (sublists l)
参数：l : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists_append`：sublists_append (l₁ l₂ : List α) : sublists (l₁ ++
 l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (· ++ x))
· 使用定理 `List.sublists_singleton`：sublists_singleton (a : α) : sublists [a] = [[]
, [a]]
· 使用定理 `List.bind_eq_flatMap`：bind_eq_flatMap {α β} (f : α -> List β) (l : List 
α) : l >>= f = l.flatMap f
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `List.flatMap_nil`：∀ {α : Type u} {β : Type v} {f : α → List β}, List.fla
tMap f [] = []
· 使用定理 `List.map_id''`：∀ {α : Type u_1} {f : α → α}, (∀ (x : α), f x = x) → ∀ (l
 : List α), List.map f l = l
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
-/
theorem sublists_concat (l : List α) (a : α) :
    sublists (l ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l) := by
  rw [sublists_append, sublists_singleton, bind_eq_flatMap, flatMap_cons, flatMap_cons, flatMap_nil,
     map_id'' append_nil, append_nil]
/-
**List.sublists_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_reverse (l : List α) : sublists (reverse l) = map reverse (sublis
ts' l)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.sublists_append`：sublists_append (l₁ l₂ : List α) : sublists (l₁ ++
 l₂) = (sublists l₂) >>= (fun x => (sublists l₁).map (· ++ x))
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.flatMap_nil`：∀ {α : Type u} {β : Type v} {f : α → List β}, List.fla
tMap f [] = []
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sublists_reverse (l : List α) : sublists (reverse l) = map reverse (sublists' l) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    simp only [reverse_cons, sublists_append, sublists'_cons, map_append, ih, sublists_singleton,
      bind_eq_flatMap, map_map, flatMap_cons, append_nil, flatMap_nil, Function.comp_def]
/-
**List.sublists_eq_sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_eq_sublists' (l : List α) : sublists l = map reverse (sublists' (
reverse l))
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.sublists_reverse`：sublists_reverse (l : List α) : sublists (reverse
 l) = map reverse (sublists' l)
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
theorem sublists_eq_sublists' (l : List α) : sublists l = map reverse (sublists' (reverse l)) := by
  rw [← sublists_reverse, reverse_reverse]
/-
**List.sublists'_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), l.reverse.sublists' = List.map List.reverse l
.sublists
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists_eq_sublists'`：sublists_eq_sublists' (l : List α) : sublist
s l = map reverse (sublists' (reverse l))
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.map_id''`：∀ {α : Type u_1} {f : α → α}, (∀ (x : α), f x = x) → ∀ (l
 : List α), List.map f l = l
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sublists'_reverse (l : List α) : sublists' (reverse l) = map reverse (sublists l) := by
  simp only [sublists_eq_sublists', map_map, map_id'' reverse_reverse, Function.comp_def]
/-
**List.sublists'_eq_sublists** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), l.sublists' = List.map List.reverse l.reverse
.sublists
参数：l : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.sublists'_reverse`：∀ {α : Type u} (l : List α), l.reverse.sublists'
 = List.map List.reverse l.sublists
· 使用定理 `List.reverse_reverse`：∀ {α : Type u_1} (as : List α), as.reverse.reverse
 = as
-/
theorem sublists'_eq_sublists (l : List α) : sublists' l = map reverse (sublists (reverse l)) := by
  rw [← sublists'_reverse, reverse_reverse]

@[simp]
/-
**List.mem_sublists** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_sublists {s t : List α} : s in sublists t ↔ s <+ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.reverse_sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.reverse.Subl
ist l₂.reverse ↔ l₁.Sublist l₂
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.mem_sublists'`：mem_sublists' {s t : List α} : s in sublists' t ↔ s 
<+ t
· 使用定理 `List.sublists'_reverse`：∀ {α : Type u} (l : List α), l.reverse.sublists'
 = List.map List.reverse l.sublists
· 使用定理 `List.mem_map_of_injective`：mem_map_of_injective {f : α -> β} (H : Inject
ive f) {a : α} {l : List α} : f a in map f l ↔ a in l
· 使用定理 `List.reverse_injective`：reverse_injective : Injective (@reverse α)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_sublists {s t : List α} : s ∈ sublists t ↔ s <+ t := by
  rw [← reverse_sublist, ← mem_sublists', sublists'_reverse,
    mem_map_of_injective reverse_injective]

@[simp]
/-
**List.length_sublists** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_sublists (l : List α) : length (sublists l) = 2 ^ length l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.sublists_eq_sublists'`：sublists_eq_sublists' (l : List α) : sublist
s l = map reverse (sublists' (reverse l))
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_sublists'`：∀ {α : Type u} (l : List α), l.sublists'.length =
 2 ^ l.length
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_sublists (l : List α) : length (sublists l) = 2 ^ length l := by
  simp only [sublists_eq_sublists', length_map, length_sublists', length_reverse]
/-
**List.map_pure_sublist_sublists** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_pure_sublist_sublists (l : List α) : map pure l <+ sublists l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.sublists_concat`：sublists_concat (l : List α) (a : α) : sublists (l
 ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l)
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.append_sublist_append_left`：∀ {α : Type u_1} {l₁ l₂ : List α} (l : 
List α), (l ++ l₁).Sublist (l ++ l₂) ↔ l₁.Sublist l₂
· 使用定理 `List.singleton_sublist`：∀ {α : Type u_1} {a : α} {l : List α}, [a].Subli
st l ↔ a ∈ l
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `List.mem_sublists`：mem_sublists {s t : List α} : s in sublists t ↔ s <+ 
t
· 使用定理 `List.nil_sublist`：∀ {α : Type u_1} (l : List α), [].Sublist l
· 使用定理 `List.append_sublist_append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (l :
 List α), (l₁ ++ l).Sublist (l₂ ++ l) ↔ l₁.Sublist l₂
-/
theorem map_pure_sublist_sublists (l : List α) : map pure l <+ sublists l := by
  induction l using reverseRecOn <;> simp only [map, map_append, sublists_concat]
  · simp only [sublists_nil, sublist_cons_self]
  case append_singleton l a ih =>
    exact ((append_sublist_append_left _).2 <|
              singleton_sublist.2 <| mem_map.2 ⟨[], mem_sublists.2 (nil_sublist _), by rfl⟩).trans
          ((append_sublist_append_right _).2 ih)

/-! ### sublistsLen -/

/-- Auxiliary function to construct the list of all sublists of a given length. Given an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns the list made of
`f` applied to all sublists of `l` of length `n`, concatenated with `L`. -/
/-
**List.sublistsLenAux** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u} → {β : Type v} → ℕ → List α → (List α → β) → List β → List β
参数：List α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function to construct the list of all sublists of a given length. Give
n an
integer `n`, a list `l`, a function `f` and an auxiliary list `L`, it returns th
e list made of
`f` applied to all sublists of `l` of length `n`, concatenated with `L`.
-/
def sublistsLenAux : ℕ → List α → (List α → β) → List β → List β
  | 0, _, f, r => f [] :: r
  | _ + 1, [], _, r => r
  | n + 1, a :: l, f, r => sublistsLenAux (n + 1) l f (sublistsLenAux n l (f ∘ List.cons a) r)

/-- The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`. -/
/-
**List.sublistsLen** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：sublistsLen (n : Nat) (l : List α) : List (List α)
参数：n : Nat；l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The list of all sublists of a list `l` that are of length `n`. For instance, for
`l = [0, 1, 2, 3]` and `n = 2`, one gets
`[[2, 3], [1, 3], [1, 2], [0, 3], [0, 2], [0, 1]]`.
-/
def sublistsLen (n : ℕ) (l : List α) : List (List α) :=
  sublistsLenAux n l id []
/-
**List.sublistsLenAux_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} {γ : Type w} (n : ℕ) (l : List α) (f : List α 
→ β) (g : β → γ) (r : List β) (s : List γ),   List.sublistsLenAux n l (g ∘ f) (L
ist.map g r ++ s) = List.map g (List.sublistsLenAux n l f r) ++ s
参数：n : ℕ；l : List α；f : List α → β；g : β → γ；r : List β；s : List γ；g ∘ f；List.ma
p g r ++ s；List.sublistsLenAux n l f r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublistsLenAux_append :
    ∀ (n : ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ),
      sublistsLenAux n l (g ∘ f) (r.map g ++ s) = (sublistsLenAux n l f r).map g ++ s
  | 0, l, f, g, r, s => by unfold sublistsLenAux; simp
  | _ + 1, [], _, _, _, _ => rfl
  | n + 1, a :: l, f, g, r, s => by
    unfold sublistsLenAux
    simp only [show (g ∘ f) ∘ List.cons a = g ∘ f ∘ List.cons a by rfl,
      sublistsLenAux_append]
/-
**List.sublistsLenAux_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsLenAux_eq (l : List α) (n) (f : List α -> β) (r) : sublistsLenAux 
n l f r = (sublistsLen n l).map f ++ r
参数：l : List α；n；f : List α -> β；r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublistsLen.eq_1`：∀ {α : Type u} (n : ℕ) (l : List α), List.sublist
sLen n l = List.sublistsLenAux n l id []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.sublistsLenAux_append`：∀ {α : Type u} {β : Type v} {γ : Type w} (n 
: ℕ) (l : List α) (f : List α → β) (g : β → γ) (r : List β) (s : List γ),   List
.sublistsLenAux …
-/
theorem sublistsLenAux_eq (l : List α) (n) (f : List α → β) (r) :
    sublistsLenAux n l f r = (sublistsLen n l).map f ++ r := by
  rw [sublistsLen, ← sublistsLenAux_append]; rfl
/-
**List.sublistsLenAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsLenAux_zero (l : List α) (f : List α -> β) (r) : sublistsLenAux 0 
l f r = f [] :: r
参数：l : List α；f : List α -> β；r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sublistsLenAux_zero (l : List α) (f : List α → β) (r) :
    sublistsLenAux 0 l f r = f [] :: r := by cases l <;> rfl

@[simp]
/-
**List.sublistsLen_zero** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsLen_zero (l : List α) : sublistsLen 0 l = [[]]
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublistsLenAux_zero`：sublistsLenAux_zero (l : List α) (f : List α -
> β) (r) : sublistsLenAux 0 l f r = f [] :: r
-/
theorem sublistsLen_zero (l : List α) : sublistsLen 0 l = [[]] :=
  sublistsLenAux_zero _ _ _

@[simp]
/-
**List.sublistsLen_succ_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsLen_succ_nil (n) : sublistsLen (n + 1) (@nil α) = []
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublistsLen_succ_nil (n) : sublistsLen (n + 1) (@nil α) = [] :=
  rfl

@[simp]
/-
**List.sublistsLen_succ_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsLen_succ_cons (n) (a : α) (l) : sublistsLen (n + 1) (a :: l) = sub
listsLen (n + 1) l ++ (sublistsLen n l).map (cons a)
参数：n；a : α；l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublistsLen.eq_1`：∀ {α : Type u} (n : ℕ) (l : List α), List.sublist
sLen n l = List.sublistsLenAux n l id []
· 使用定理 `List.sublistsLenAux.eq_3`：∀ {α : Type u} {β : Type v} (x : List α → β) (
x_1 : List β) (n : ℕ) (a : α) (l : List α),   List.sublistsLenAux n.succ (a :: l
) x x_1 =     …
· 使用定理 `List.sublistsLenAux_eq`：sublistsLenAux_eq (l : List α) (n) (f : List α -
> β) (r) : sublistsLenAux n l f r = (sublistsLen n l).map f ++ r
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
-/
theorem sublistsLen_succ_cons (n) (a : α) (l) :
    sublistsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons a) := by
  rw [sublistsLen, sublistsLenAux, sublistsLenAux_eq, sublistsLenAux_eq, map_id,
      append_nil]; rfl
/-
**List.sublistsLen_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsLen_one (l : List α) : sublistsLen 1 l = l.reverse.map ([·])
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublistsLen_succ_nil`：sublistsLen_succ_nil (n) : sublistsLen (n + 1
) (@nil α) = []
· 使用定理 `List.reverse_nil`：∀ {α : Type u}, [].reverse = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.sublistsLen_succ_cons`：sublistsLen_succ_cons (n) (a : α) (l) : subl
istsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons 
a)
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.sublistsLen_zero`：sublistsLen_zero (l : List α) : sublistsLen 0 l =
 [[]]
-/
theorem sublistsLen_one (l : List α) : sublistsLen 1 l = l.reverse.map ([·]) :=
  l.rec (by rw [sublistsLen_succ_nil, reverse_nil, map_nil]) fun a s ih ↦ by
    rw [sublistsLen_succ_cons, ih, reverse_cons, map_append, sublistsLen_zero]; rfl

@[simp]
/-
**List.length_sublistsLen** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (n : ℕ) (l : List α), (List.sublistsLen n l).length = l.len
gth.choose n
参数：n : ℕ；l : List α；List.sublistsLen n l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_sublistsLen :
    ∀ (n) (l : List α), length (sublistsLen n l) = Nat.choose (length l) n
  | 0, l => by simp
  | _ + 1, [] => by simp
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons, length_append, length_sublistsLen (n + 1) l,
      length_map, length_sublistsLen n l, length_cons, Nat.choose_succ_succ, Nat.add_comm]
/-
**List.sublistsLen_sublist_sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (n : ℕ) (l : List α), (List.sublistsLen n l).Sublist l.subl
ists'
参数：n : ℕ；l : List α；List.sublistsLen n l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
-/
theorem sublistsLen_sublist_sublists' :
    ∀ (n) (l : List α), sublistsLen n l <+ sublists' l
  | 0, l => by simp
  | _ + 1, [] => nil_sublist _
  | n + 1, a :: l => by
    rw [sublistsLen_succ_cons, sublists'_cons]
    exact (sublistsLen_sublist_sublists' _ _).append ((sublistsLen_sublist_sublists' _ _).map _)
/-
**List.sublistsLen_sublist_of_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsLen_sublist_of_sublist (n) {l₁ l₂ : List α} (h : l₁ <+ l₂) : subli
stsLen n l₁ <+ sublistsLen n l₂
参数：n；h : l₁ <+ l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublistsLen_zero`：sublistsLen_zero (l : List α) : sublistsLen 0 l =
 [[]]
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.sublistsLen_succ_cons`：sublistsLen_succ_cons (n) (a : α) (l) : subl
istsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons 
a)
· 使用定理 `List.sublist_append_left`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁.Sublist 
(l₁ ++ l₂)
· 使用定理 `List.Sublist.append`：∀ {α : Type u_1} {l₁ l₂ r₁ r₂ : List α}, l₁.Sublist
 l₂ → r₁.Sublist r₂ → (l₁ ++ r₁).Sublist (l₂ ++ r₂)
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
-/
theorem sublistsLen_sublist_of_sublist (n) {l₁ l₂ : List α} (h : l₁ <+ l₂) :
    sublistsLen n l₁ <+ sublistsLen n l₂ := by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction h with
  | slnil => rfl
  | cons a _ IH =>
    refine IH.trans ?_
    rw [sublistsLen_succ_cons]
    apply sublist_append_left
  | cons_cons a s IH => simpa only [sublistsLen_succ_cons] using IH.append ((IHn s).map _)
/-
**List.length_of_sublistsLen** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {n : ℕ} {l l' : List α}, l' ∈ List.sublistsLen n l → l'.len
gth = n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_of_sublistsLen :
    ∀ {n} {l l' : List α}, l' ∈ sublistsLen n l → length l' = n
  | 0, l, l', h => by simp_all
  | n + 1, a :: l, l', h => by
    rw [sublistsLen_succ_cons, mem_append, mem_map] at h
    rcases h with (h | ⟨l', h, rfl⟩)
    · exact length_of_sublistsLen h
    · exact congr_arg (· + 1) (length_of_sublistsLen h)
/-
**List.mem_sublistsLen_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_sublistsLen_self {l l' : List α} (h : l' <+ l) : l' in sublistsLen (le
ngth l') l
参数：h : l' <+ l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublistsLen_zero`：sublistsLen_zero (l : List α) : sublistsLen 0 l =
 [[]]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `List.length.eq_2`：∀ {α : Type u_1} (head : α) (tail : List α), (head :: 
tail).length = tail.length + 1
· 使用定理 `List.sublistsLen_succ_cons`：sublistsLen_succ_cons (n) (a : α) (l) : subl
istsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons 
a)
· 使用定理 `List.mem_append_left`：∀ {α : Type u} {a : α} {as : List α} (bs : List α)
, a ∈ as → a ∈ as ++ bs
· 使用定理 `List.mem_append_right`：∀ {α : Type u} {b : α} (as : List α) {bs : List α
}, b ∈ bs → b ∈ as ++ bs
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
-/
theorem mem_sublistsLen_self {l l' : List α} (h : l' <+ l) :
    l' ∈ sublistsLen (length l') l := by
  induction h with
  | slnil => simp
  | @cons l₁ l₂ a s IH =>
    rcases l₁ with - | ⟨b, l₁⟩
    · simp
    · rw [length, sublistsLen_succ_cons]
      exact mem_append_left _ IH
  | cons_cons a s IH =>
    rw [length, sublistsLen_succ_cons]
    exact mem_append_right _ (mem_map.2 ⟨_, IH, rfl⟩)

@[simp]
/-
**List.mem_sublistsLen** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_sublistsLen {n} {l l' : List α} : l' in sublistsLen n l ↔ l' <+ l ∧ le
ngth l' = n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.mem_sublists'`：mem_sublists' {s t : List α} : s in sublists' t ↔ s 
<+ t
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `List.sublistsLen_sublist_sublists'`：∀ {α : Type u} (n : ℕ) (l : List α),
 (List.sublistsLen n l).Sublist l.sublists'
· 使用定理 `List.length_of_sublistsLen`：∀ {α : Type u} {n : ℕ} {l l' : List α}, l' ∈
 List.sublistsLen n l → l'.length = n
· 使用定理 `List.mem_sublistsLen_self`：mem_sublistsLen_self {l l' : List α} (h : l' 
<+ l) : l' in sublistsLen (length l') l
-/
theorem mem_sublistsLen {n} {l l' : List α} :
    l' ∈ sublistsLen n l ↔ l' <+ l ∧ length l' = n :=
  ⟨fun h =>
    ⟨mem_sublists'.1 ((sublistsLen_sublist_sublists' _ _).subset h), length_of_sublistsLen h⟩,
    fun ⟨h₁, h₂⟩ => h₂ ▸ mem_sublistsLen_self h₁⟩
/-
**List.sublistsLen_of_length_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublistsLen_of_length_lt {n} {l : List α} (h : l.length < n) : sublistsLen
 n l = []
参数：h : l.length < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.eq_nil_iff_forall_not_mem`：∀ {α : Type u_1} {l : List α}, l = [] ↔ 
∀ (a : α), a ∉ l
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `List.mem_sublistsLen`：mem_sublistsLen {n} {l l' : List α} : l' in sublis
tsLen n l ↔ l' <+ l ∧ length l' = n
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Sublist.length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂
 → l₁.length ≤ l₂.length
-/
theorem sublistsLen_of_length_lt {n} {l : List α} (h : l.length < n) : sublistsLen n l = [] :=
  eq_nil_iff_forall_not_mem.mpr fun _ =>
    mem_sublistsLen.not.mpr fun ⟨hs, hl⟩ => (h.trans_eq hl.symm).not_ge (Sublist.length_le hs)

@[simp]
/-
**List.sublistsLen_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} (l : List α), List.sublistsLen l.length l = [l]
参数：l : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublistsLen_length : ∀ l : List α, sublistsLen l.length l = [l]
  | [] => rfl
  | a :: l => by
    simp only [length, sublistsLen_succ_cons, sublistsLen_length, map,
      sublistsLen_of_length_lt (lt_succ_self _), nil_append]

open Function
/-
**List.Pairwise.sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u} {R : α → α → Prop} {l : List α},   List.Pairwise R l → List
.Pairwise (List.Lex (Function.swap R)) l.sublists'
参数：List.Lex (Function.swap R)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.Pairwise.brecOn`：∀ {α : Type u} {R : α → α → Prop} {motive : (a : L
ist α) → List.Pairwise R a → Prop} {a : List α}   (t : List.Pairwise R a), (∀ (a
 : List α)…
· 使用定理 `List.pairwise_singleton`：∀ {α : Type u_1} (R : α → α → Prop) (a : α), Li
st.Pairwise R [a]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
-/
theorem Pairwise.sublists' {R} :
    ∀ {l : List α}, Pairwise R l → Pairwise (Lex (Function.swap R)) (sublists' l)
  | _, Pairwise.nil => pairwise_singleton _ _
  | _, @Pairwise.cons _ _ a l H₁ H₂ => by
    simp only [sublists'_cons, pairwise_append, pairwise_map, mem_sublists', mem_map, exists_imp,
      and_imp]
    refine ⟨H₂.sublists', H₂.sublists'.imp fun l₁ => Lex.cons l₁, ?_⟩
    rintro l₁ sl₁ x l₂ _ rfl
    rcases l₁ with - | ⟨b, l₁⟩; · constructor
    exact Lex.rel (H₁ _ <| sl₁.subset mem_cons_self)
/-
**List.pairwise_sublists** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_sublists {R} {l : List α} (H : Pairwise R l) : Pairwise (Lex R on
 reverse) (sublists l)
参数：H : Pairwise R l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.Pairwise.sublists'`：∀ {α : Type u} {R : α → α → Prop} {l : List α},
   List.Pairwise R l → List.Pairwise (List.Lex (Function.swap R)) l.sublists'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_reverse`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise R l.reverse ↔ List.Pairwise (fun a b => R b a) l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.pairwise_map`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {R : 
α_1 → α_1 → Prop} {l : List α},   List.Pairwise R (List.map f l) ↔ List.Pairwise
 (fun a…
· 使用定理 `List.sublists'_reverse`：∀ {α : Type u} (l : List α), l.reverse.sublists'
 = List.map List.reverse l.sublists
-/
theorem pairwise_sublists {R} {l : List α} (H : Pairwise R l) :
    Pairwise (Lex R on reverse) (sublists l) := by
  have := (pairwise_reverse.2 H).sublists'
  rwa [sublists'_reverse, pairwise_map] at this

@[simp]
/-
**List.nodup_sublists** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_sublists {l : List α} : Nodup (sublists l) ↔ Nodup l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.map_pure_sublist_sublists`：map_pure_sublist_sublists (l : List α) :
 map pure l <+ sublists l
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Lex.to_ne`：∀ {α : Type u} {l₁ l₂ : List α}, List.Lex (fun x1 x2 => 
x1 ≠ x2) l₁ l₂ → l₁ ≠ l₂
· 使用定理 `List.pairwise_sublists`：pairwise_sublists {R} {l : List α} (H : Pairwise
 R l) : Pairwise (Lex R on reverse) (sublists l)
-/
theorem nodup_sublists {l : List α} : Nodup (sublists l) ↔ Nodup l :=
  ⟨fun h => (h.sublist (map_pure_sublist_sublists _)).of_map _, fun h =>
    (pairwise_sublists h).imp @fun l₁ l₂ h => by simpa using h.to_ne⟩

@[simp]
/-
**List.nodup_sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_sublists' {l : List α} : Nodup (sublists' l) ↔ Nodup l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'_eq_sublists`：∀ {α : Type u} (l : List α), l.sublists' = L
ist.map List.reverse l.reverse.sublists
· 使用定理 `List.nodup_map_iff`：nodup_map_iff {f : α -> β} {l : List α} (hf : Inject
ive f) : Nodup (map f l) ↔ Nodup l
· 使用定理 `List.reverse_injective`：reverse_injective : Injective (@reverse α)
· 使用定理 `List.nodup_sublists`：nodup_sublists {l : List α} : Nodup (sublists l) ↔ 
Nodup l
· 使用定理 `List.nodup_reverse`：nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nod
up l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nodup_sublists' {l : List α} : Nodup (sublists' l) ↔ Nodup l := by
  rw [sublists'_eq_sublists, nodup_map_iff reverse_injective, nodup_sublists, nodup_reverse]

protected alias ⟨Nodup.of_sublists, Nodup.sublists⟩ := nodup_sublists

protected alias ⟨Nodup.of_sublists', _⟩ := nodup_sublists'
/-
**List.nodup_sublistsLen** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_sublistsLen (n : Nat) {l : List α} (h : Nodup l) : (sublistsLen n l)
.Nodup
参数：n : Nat；h : Nodup l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `List.Lex.to_ne`：∀ {α : Type u} {l₁ l₂ : List α}, List.Lex (fun x1 x2 => 
x1 ≠ x2) l₁ l₂ → l₁ ≠ l₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.Pairwise.sublists'`：∀ {α : Type u} {R : α → α → Prop} {l : List α},
   List.Pairwise R l → List.Pairwise (List.Lex (Function.swap R)) l.sublists'
· 使用定理 `List.Pairwise.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α} {R : α → α → Pr
op}, l₁.Sublist l₂ → List.Pairwise R l₂ → List.Pairwise R l₁
· 使用定理 `List.sublistsLen_sublist_sublists'`：∀ {α : Type u} (n : ℕ) (l : List α),
 (List.sublistsLen n l).Sublist l.sublists'
-/
theorem nodup_sublistsLen (n : ℕ) {l : List α} (h : Nodup l) : (sublistsLen n l).Nodup := by
  have : Pairwise (· ≠ ·) l.sublists' := Pairwise.imp
    (fun h => Lex.to_ne (by convert! h using 3; simp [eq_comm])) h.sublists'
  exact this.sublist (sublistsLen_sublist_sublists' _ _)
/-
**List.sublists_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α → β) (l : List α), (List.map f l).subli
sts = List.map (List.map f) l.sublists
参数：f : α → β；l : List α；List.map f l；List.map f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublists_map (f : α → β) : ∀ (l : List α),
    sublists (map f l) = map (map f) (sublists l)
  | [] => by simp
  | a::l => by
    rw [map_cons, sublists_cons, bind_eq_flatMap, sublists_map f l, sublists_cons,
      bind_eq_flatMap, map_eq_flatMap, map_eq_flatMap]
    induction sublists l <;> simp [*]
/-
**List.sublists'_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α → β) (l : List α), (List.map f l).subli
sts' = List.map (List.map f) l.sublists'
参数：f : α → β；l : List α；List.map f l；List.map f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
-/
theorem sublists'_map (f : α → β) : ∀ (l : List α),
    sublists' (map f l) = map (map f) (sublists' l)
  | [] => by simp
  | a::l => by simp [map_cons, sublists'_cons, sublists'_map f l, Function.comp]
/-
**List.sublists_perm_sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_perm_sublists' (l : List α) : sublists l ~ sublists' l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_get_finRange`：∀ {α : Type u_1} (l : List α), List.map l.get (Li
st.finRange l.length) = l
· 使用定理 `List.sublists_map`：∀ {α : Type u} {β : Type v} (f : α → β) (l : List α),
 (List.map f l).sublists = List.map (List.map f) l.sublists
· 使用定理 `List.sublists'_map`：∀ {α : Type u} {β : Type v} (f : α → β) (l : List α)
, (List.map f l).sublists' = List.map (List.map f) l.sublists'
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.perm_ext_iff_of_nodup`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup 
→ l₂.Nodup → (l₁.Perm l₂ ↔ ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.nodup_sublists`：nodup_sublists {l : List α} : Nodup (sublists l) ↔ 
Nodup l
· 使用定理 `List.nodup_finRange`：∀ (n : ℕ), (List.finRange n).Nodup
· 使用定理 `List.nodup_sublists'`：nodup_sublists' {l : List α} : Nodup (sublists' l)
 ↔ Nodup l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sublists_perm_sublists' (l : List α) : sublists l ~ sublists' l := by
  rw [← map_get_finRange l, sublists_map, sublists'_map]
  apply Perm.map
  apply (perm_ext_iff_of_nodup _ _).mpr
  · simp
  · exact nodup_sublists.mpr (nodup_finRange _)
  · exact (nodup_sublists'.mpr (nodup_finRange _))
/-
**List.Sublist.sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Sublist l₂ → l₁.sublists'.Sublist l₂.s
ublists'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.sublist_append_left`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁.Sublist 
(l₁ ++ l₂)
· 使用定理 `List.Sublist.append`：∀ {α : Type u_1} {l₁ l₂ r₁ r₂ : List α}, l₁.Sublist
 l₂ → r₁.Sublist r₂ → (l₁ ++ r₁).Sublist (l₂ ++ r₂)
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
-/
theorem Sublist.sublists' {l₁ l₂ : List α}
    (sublist : l₁ <+ l₂) :
    l₁.sublists' <+ l₂.sublists' := by
  induction sublist with
  | slnil => exact .refl _
  | cons a _ ih =>
    rw [sublists'_cons]
    exact ih.trans (List.sublist_append_left ..)
  | cons_cons a _ ih =>
    rw [sublists'_cons, sublists'_cons]
    exact ih.append (ih.map _)

@[simp]
/-
**List.sublists'_sublist_sublists'_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁.sublists'.Sublist l₂.sublists' ↔ l₁.Su
blist l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_sublists'`：mem_sublists' {s t : List α} : s in sublists' t ↔ s 
<+ t
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `List.Sublist.sublists'`：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.sublists'.Sublist l₂.sublists'
-/
theorem sublists'_sublist_sublists'_iff {l₁ l₂ : List α} :
    l₁.sublists' <+ l₂.sublists' ↔ l₁ <+ l₂ where
  mpr := Sublist.sublists'
  mp sublist := mem_sublists'.mp <| sublist.subset <| mem_sublists'.mpr <| .refl _
/-
**List.subperm_of_sublists'_subperm_sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁.sublists'.Subperm l₂.sublists' → l₁.Su
bperm l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_sublists'`：mem_sublists' {s t : List α} : s in sublists' t ↔ s 
<+ t
· 使用定理 `List.Subperm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Subperm l₂ → 
l₁ ⊆ l₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
-/
theorem subperm_of_sublists'_subperm_sublists' {l₁ l₂ : List α}
    (subperm : l₁.sublists' <+~ l₂.sublists') : l₁ <+~ l₂ :=
  Sublist.subperm <| mem_sublists'.mp <| subperm.subset <| mem_sublists'.mpr <| .refl _
/-
**List.sublists_cons_perm_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublists_cons_perm_append (a : α) (l : List α) : sublists (a :: l) ~ subli
sts l ++ map (cons a) (sublists l)
参数：a : α；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `List.sublists_perm_sublists'`：sublists_perm_sublists' (l : List α) : sub
lists l ~ sublists' l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
-/
theorem sublists_cons_perm_append (a : α) (l : List α) :
    sublists (a :: l) ~ sublists l ++ map (cons a) (sublists l) :=
  Perm.trans (sublists_perm_sublists' _) <| by
  rw [sublists'_cons]
  exact Perm.append (sublists_perm_sublists' _).symm (Perm.map _ (sublists_perm_sublists' _).symm)
/-
**List.revzip_sublists** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：revzip_sublists (l l₁ l₂ : List α) (h : (l₁, l₂) in revzip l.sublists) : l
₁ ++ l₂ ~ l
参数：l l₁ l₂ : List α；h : (l₁, l₂) in revzip l.sublists。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.zip_nil_right`：∀ {α : Type u} {β : Type v} {l : List α}, l.zip [] =
 []
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.zip_map_left`：∀ {α : Type u_1} {γ : Type u_2} {β : Type u_3} {f : α
 → γ} {l₁ : List α} {l₂ : List β},   (List.map f l₁).zip l₂ = List.map (Prod.map
 f id) …
· 使用定理 `List.zip_map_right`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : 
β → γ} {l₁ : List α} {l₂ : List β},   l₁.zip (List.map f l₂) = List.map (Prod.ma
p id f) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.zip_append`：∀ {α : Type u_1} {β : Type u_2} {l₁ r₁ : List α} {l₂ r₂
 : List β},   l₁.length = l₂.length → (l₁ ++ r₁).zip (l₂ ++ r₂) = l₁.zip l₂ ++ r
₁.zip…
· 使用定理 `List.length_sublists`：length_sublists (l : List α) : length (sublists l)
 = 2 ^ length l
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.sublists_concat`：sublists_concat (l : List α) (a : α) : sublists (l
 ++ [a]) = sublists l ++ map (fun x => x ++ [a]) (sublists l)
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.Perm.append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (t₁ : List α),
 l₁.Perm l₂ → (l₁ ++ t₁).Perm (l₂ ++ t₁)
· 使用定理 `List.Perm.append_left`：∀ {α : Type u_1} {t₁ t₂ : List α} (l : List α), t
₁.Perm t₂ → (l ++ t₁).Perm (l ++ t₂)
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
· 使用定理 `List.revzip.eq_1`：∀ {α : Type u_1} (l : List α), l.revzip = l.zip l.reve
rse
-/
theorem revzip_sublists (l l₁ l₂ : List α) (h : (l₁, l₂) ∈ revzip l.sublists) : l₁ ++ l₂ ~ l := by
  rw [revzip] at h
  induction l using List.reverseRecOn generalizing l₁ l₂ with
  | nil =>
    have : l₁ = [] ∧ l₂ = [] := by simpa using h
    simp [this]
  | append_singleton l' a ih =>
    rw [sublists_concat, reverse_append, zip_append (by simp), ← map_reverse, zip_map_right,
      zip_map_left] at *
    simp only [Prod.mk_inj, mem_map, mem_append, Prod.map_apply, Prod.exists] at h
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', l₂, h, rfl, rfl⟩)
    · rw [← append_assoc]
      exact (ih _ _ h).append_right _
    · rw [append_assoc]
      apply (perm_append_comm.append_left _).trans
      rw [← append_assoc]
      exact (ih _ _ h).append_right _
/-
**List.revzip_sublists'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：revzip_sublists' (l l₁ l₂ : List α) (h : (l₁, l₂) in revzip l.sublists') :
 l₁ ++ l₂ ~ l
参数：l l₁ l₂ : List α；h : (l₁, l₂) in revzip l.sublists'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.zip_nil_right`：∀ {α : Type u} {β : Type v} {l : List α}, l.zip [] =
 []
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.zip_map_left`：∀ {α : Type u_1} {γ : Type u_2} {β : Type u_3} {f : α
 → γ} {l₁ : List α} {l₂ : List β},   (List.map f l₁).zip l₂ = List.map (Prod.map
 f id) …
· 使用定理 `List.zip_map_right`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : 
β → γ} {l₁ : List α} {l₂ : List β},   l₁.zip (List.map f l₂) = List.map (Prod.ma
p id f) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_reverse`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α}, List.map f l.reverse = (List.map f l).reverse
· 使用定理 `List.zip_append`：∀ {α : Type u_1} {β : Type u_2} {l₁ r₁ : List α} {l₂ r₂
 : List β},   l₁.length = l₂.length → (l₁ ++ r₁).zip (l₂ ++ r₂) = l₁.zip l₂ ++ r
₁.zip…
· 使用定理 `List.length_sublists'`：∀ {α : Type u} (l : List α), l.sublists'.length =
 2 ^ l.length
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `List.perm_middle`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, (l₁ ++ a ::
 l₂).Perm (a :: (l₁ ++ l₂))
· 使用定理 `List.revzip.eq_1`：∀ {α : Type u_1} (l : List α), l.revzip = l.zip l.reve
rse
-/
theorem revzip_sublists' (l l₁ l₂ : List α) (h : (l₁, l₂) ∈ revzip l.sublists') : l₁ ++ l₂ ~ l := by
  rw [revzip] at h
  induction l generalizing l₁ l₂ with
  | nil =>
    simp_all only [sublists'_nil, reverse_cons, reverse_nil, nil_append, zip_cons_cons,
      zip_nil_right, mem_singleton, Prod.mk.injEq, append_nil, Perm.refl]
  | cons a l IH =>
    rw [sublists'_cons, reverse_append, zip_append, ← map_reverse, zip_map_right, zip_map_left] at *
      <;> [simp only [mem_append, mem_map, Prod.map_apply, id_eq, Prod.mk.injEq, Prod.exists,
        exists_eq_right_right] at h; simp]
    rcases h with (⟨l₁, l₂', h, rfl, rfl⟩ | ⟨l₁', h, rfl⟩)
    · exact perm_middle.trans ((IH _ _ h).cons _)
    · exact (IH _ _ h).cons _
/-
**List.range_bind_sublistsLen_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：range_bind_sublistsLen_perm (l : List α) : ((List.range (l.length + 1)).fl
atMap fun n => sublistsLen n l) ~ sublists' l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublists'`：sublists'_nil : sublists' (@nil α) = [[]]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `List.range_succ`：∀ {n : ℕ}, List.range n.succ = List.range n ++ [n]
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.sublistsLen_zero`：sublistsLen_zero (l : List α) : sublistsLen 0 l =
 [[]]
· 使用定理 `List.flatMap_nil`：∀ {α : Type u} {β : Type v} {f : α → List β}, List.fla
tMap f [] = []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.range_succ_eq_map`：∀ {n : ℕ}, List.range (n + 1) = 0 :: List.map Na
t.succ (List.range n)
· 使用定理 `List.flatMap_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α 
→ β) (g : β → List γ) (l : List α),   List.flatMap g (List.map f l) = List.flatM
ap (fu…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.sublistsLen_succ_cons`：sublistsLen_succ_cons (n) (a : α) (l) : subl
istsLen (n + 1) (a :: l) = sublistsLen (n + 1) l ++ (sublistsLen n l).map (cons 
a)
· 使用定理 `List.sublists'_cons`：∀ {α : Type u} (a : α) (l : List α), (a :: l).subli
sts' = l.sublists' ++ List.map (List.cons a) l.sublists'
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.flatMap_append_perm`：flatMap_append_perm (l : List α) (f g : α -> L
ist β) : l.flatMap f ++ l.flatMap g ~ l.flatMap fun x => f x ++ g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.flatMap_append`：∀ {α : Type u} {β : Type v} {xs ys : List α} {f : α
 → List β},   List.flatMap f (xs ++ ys) = List.flatMap f xs ++ List.flatMap f ys
· 使用定理 `List.flatMap_singleton`：∀ {α : Type u_1} {β : Type u_2} (f : α → List β)
 (x : α), List.flatMap f [x] = f x
· 使用定理 `List.sublistsLen_of_length_lt`：sublistsLen_of_length_lt {n} {l : List α}
 (h : l.length < n) : sublistsLen n l = []
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
-/
theorem range_bind_sublistsLen_perm (l : List α) :
    ((List.range (l.length + 1)).flatMap fun n => sublistsLen n l) ~ sublists' l := by
  induction l with
  | nil => simp [range_succ]
  | cons h tl l_ih =>
    simp_rw [range_succ_eq_map, length, flatMap_cons, flatMap_map, sublistsLen_succ_cons,
      sublists'_cons, List.sublistsLen_zero, List.singleton_append]
    refine ((flatMap_append_perm (range (tl.length + 1)) _ _).symm.cons _).trans ?_
    simp_rw [← List.map_flatMap, ← cons_append]
    rw [← List.singleton_append, ← List.sublistsLen_zero tl]
    refine Perm.append ?_ (l_ih.map _)
    rw [List.range_succ, flatMap_append, flatMap_singleton,
      sublistsLen_of_length_lt (Nat.lt_succ_self _), append_nil,
      ← List.flatMap_map Nat.succ fun n => sublistsLen n tl,
      ← flatMap_cons (f := fun n => sublistsLen n tl), ← range_succ_eq_map]
    exact l_ih

end List

