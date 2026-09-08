/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Duplicate
public import Mathlib.Data.List.InsertIdx
public import Mathlib.Data.List.Induction
public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Tactic.Finiteness.Attr

/-!
# Permutations of a list

In this file we prove properties about `List.Permutations`, a list of all permutations of a list. It
is defined in `Data.List.Defs`.

## Order of the permutations

Designed for performance, the order in which the permutations appear in `List.Permutations` is
rather intricate and not very amenable to induction. That's why we also provide `List.Permutations'`
as a less efficient but more straightforward way of listing permutations.

### `List.Permutations`

TODO. In the meantime, you can try decrypting the docstrings.

### `List.Permutations'`

The list of partitions is built by recursion. The permutations of `[]` are `[[]]`. Then, the
permutations of `a :: l` are obtained by taking all permutations of `l` in order and adding `a` in
all positions. Hence, to build `[0, 1, 2, 3].permutations'`, it does
* `[[]]`
* `[[3]]`
* `[[2, 3], [3, 2]]]`
* `[[1, 2, 3], [2, 1, 3], [2, 3, 1], [1, 3, 2], [3, 1, 2], [3, 2, 1]]`
* `[[0, 1, 2, 3], [1, 0, 2, 3], [1, 2, 0, 3], [1, 2, 3, 0],`
   `[0, 2, 1, 3], [2, 0, 1, 3], [2, 1, 0, 3], [2, 1, 3, 0],`
   `[0, 2, 3, 1], [2, 0, 3, 1], [2, 3, 0, 1], [2, 3, 1, 0],`
   `[0, 1, 3, 2], [1, 0, 3, 2], [1, 3, 0, 2], [1, 3, 2, 0],`
   `[0, 3, 1, 2], [3, 0, 1, 2], [3, 1, 0, 2], [3, 1, 2, 0],`
   `[0, 3, 2, 1], [3, 0, 2, 1], [3, 2, 0, 1], [3, 2, 1, 0]]`
-/

public section

-- Make sure we don't import algebra
assert_not_exists Monoid

open Nat Function

variable {α β : Type*}

namespace List

/-
**List.permutationsAux2_fst** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (t : α) (ts : List α) (r : List β) (ys : L
ist α) (f : List α → β),   (List.permutationsAux2 t ts r ys f).1 = ys ++ ts
参数：t : α；ts : List α；r : List β；ys : List α；f : List α → β；List.permutationsAux2
 t ts r ys f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem permutationsAux2_fst (t : α) (ts : List α) (r : List β) :
    ∀ (ys : List α) (f : List α → β), (permutationsAux2 t ts r ys f).1 = ys ++ ts
  | [], _ => rfl
  | y :: ys, f => by simp [permutationsAux2, permutationsAux2_fst t _ _ ys]

@[simp]
/-
**List.permutationsAux2_snd_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutationsAux2_snd_nil (t : α) (ts : List α) (r : List β) (f : List α ->
 β) : (permutationsAux2 t ts r [] f).2 = r
参数：t : α；ts : List α；r : List β；f : List α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem permutationsAux2_snd_nil (t : α) (ts : List α) (r : List β) (f : List α → β) :
    (permutationsAux2 t ts r [] f).2 = r :=
  rfl

@[simp]
/-
**List.permutationsAux2_snd_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutationsAux2_snd_cons (t : α) (ts : List α) (r : List β) (y : α) (ys :
 List α) (f : List α -> β) : (permutationsAux2 t ts r (y :: ys) f).2 = f (t :: y
 :: ys ++ ts) :: (permutationsAux2 t ts r ys fun x : List α => f (y :: x)).2
参数：t : α；ts : List α；r : List β；y : α；ys : List α；f : List α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.permutationsAux2_fst`：∀ {α : Type u_1} {β : Type u_2} (t : α) (ts :
 List α) (r : List β) (ys : List α) (f : List α → β),   (List.permutationsAux2 t
 ts r ys f).1 =…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem permutationsAux2_snd_cons (t : α) (ts : List α) (r : List β) (y : α) (ys : List α)
    (f : List α → β) :
    (permutationsAux2 t ts r (y :: ys) f).2 =
      f (t :: y :: ys ++ ts) :: (permutationsAux2 t ts r ys fun x : List α => f (y :: x)).2 := by
  simp [permutationsAux2, permutationsAux2_fst t _ _ ys]

/-- The `r` argument to `permutationsAux2` is the same as appending. -/
/-
**List.permutationsAux2_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutationsAux2_append (t : α) (ts : List α) (r : List β) (ys : List α) (
f : List α -> β) : (permutationsAux2 t ts nil ys f).2 ++ r = (permutationsAux2 t
 ts r ys f).2
参数：t : α；ts : List α；r : List β；ys : List α；f : List α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.permutationsAux2_snd_cons`：permutationsAux2_snd_cons (t : α) (ts : 
List α) (r : List β) (y : α) (ys : List α) (f : List α -> β) : (permutationsAux2
 t ts r (y :: ys) f)…

--- 原说明 ---
The `r` argument to `permutationsAux2` is the same as appending.
-/
theorem permutationsAux2_append (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts nil ys f).2 ++ r = (permutationsAux2 t ts r ys f).2 := by
  induction ys generalizing f <;> simp [*]

/-- The `ts` argument to `permutationsAux2` can be folded into the `f` argument. -/
/-
**List.permutationsAux2_comp_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutationsAux2_comp_append {t : α} {ts ys : List α} {r : List β} (f : Li
st α -> β) : ((permutationsAux2 t [] r ys) fun x => f (x ++ ts)).2 = (permutatio
nsAux2 t ts r ys f).2
参数：f : List α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux2_snd_cons`：permutationsAux2_snd_cons (t : α) (ts : 
List α) (r : List β) (y : α) (ys : List α) (f : List α -> β) : (permutationsAux2
 t ts r (y :: ys) f)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as

--- 原说明 ---
The `ts` argument to `permutationsAux2` can be folded into the `f` argument.
-/
theorem permutationsAux2_comp_append {t : α} {ts ys : List α} {r : List β} (f : List α → β) :
    ((permutationsAux2 t [] r ys) fun x => f (x ++ ts)).2 = (permutationsAux2 t ts r ys f).2 := by
  induction ys generalizing f with
  | nil => simp
  | cons ys_hd _ ys_ih => simp [ys_ih fun xs => f (ys_hd :: xs)]
/-
**List.map_permutationsAux2'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_permutationsAux2' {α' β'} (g : α -> α') (g' : β -> β') (t : α) (ts ys 
: List α) (r : List β) (f : List α -> β) (f' : List α' -> β') (H : forall a, g' 
(f a) = f' (map g a)) : map g' (permutationsAux2 t ts r ys f).2 = (permutationsA
ux2 (g t) (map g ts) (map g' r) (map g ys) f').2
参数：g : α -> α'；g' : β -> β'；t : α；ts ys : List α；r : List β；f : List α -> β；f' :
 List α' -> β'；H : forall a, g' (f a) = f' (map g a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.permutationsAux2_snd_cons`：permutationsAux2_snd_cons (t : α) (ts : 
List α) (r : List β) (y : α) (ys : List α) (f : List α -> β) : (permutationsAux2
 t ts r (y :: ys) f)…
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
-/
theorem map_permutationsAux2' {α' β'} (g : α → α') (g' : β → β') (t : α) (ts ys : List α)
    (r : List β) (f : List α → β) (f' : List α' → β') (H : ∀ a, g' (f a) = f' (map g a)) :
    map g' (permutationsAux2 t ts r ys f).2 =
      (permutationsAux2 (g t) (map g ts) (map g' r) (map g ys) f').2 := by
  induction ys generalizing f f' with
  | nil => simp
  | cons ys_hd _ ys_ih =>
    simp only [map, permutationsAux2_snd_cons, cons_append, cons.injEq]
    rw [ys_ih]
    · refine ⟨?_, rfl⟩
      simp only [← map_cons, ← map_append]; apply H
    · intro a; apply H

/-- The `f` argument to `permutationsAux2` when `r = []` can be eliminated. -/
/-
**List.map_permutationsAux2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α -> β)
 : (permutationsAux2 t ts [] ys id).2.map f = (permutationsAux2 t ts [] ys f).2
参数：t : α；ts : List α；ys : List α；f : List α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_permutationsAux2'`：map_permutationsAux2' {α' β'} (g : α -> α') 
(g' : β -> β') (t : α) (ts ys : List α) (r : List β) (f : List α -> β) (f' : Lis
t α' -> β') (H :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `List.map_id_fun`：∀ {α : Type u_1}, List.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l

--- 原说明 ---
The `f` argument to `permutationsAux2` when `r = []` can be eliminated.
-/
theorem map_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts [] ys id).2.map f = (permutationsAux2 t ts [] ys f).2 := by
  rw [map_permutationsAux2' id, map_id, map_id]
  · rfl
  simp

/-- An expository lemma to show how all of `ts`, `r`, and `f` can be eliminated from
`permutationsAux2`.

`(permutationsAux2 t [] [] ys id).2`, which appears on the RHS, is a list whose elements are
produced by inserting `t` into every non-terminal position of `ys` in order. As an example:
```lean
#eval permutationsAux2 1 [] [] [2, 3, 4] id
-- [[1, 2, 3, 4], [2, 1, 3, 4], [2, 3, 1, 4]]
```
-/
/-
**List.permutationsAux2_snd_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutationsAux2_snd_eq (t : α) (ts : List α) (r : List β) (ys : List α) (
f : List α -> β) : (permutationsAux2 t ts r ys f).2 = ((permutationsAux2 t [] []
 ys id).2.map fun x => f (x ++ ts)) ++ r
参数：t : α；ts : List α；r : List β；ys : List α；f : List α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.permutationsAux2_append`：permutationsAux2_append (t : α) (ts : List
 α) (r : List β) (ys : List α) (f : List α -> β) : (permutationsAux2 t ts nil ys
 f).2 ++ r = (perm…
· 使用定理 `List.map_permutationsAux2`：map_permutationsAux2 (t : α) (ts : List α) (y
s : List α) (f : List α -> β) : (permutationsAux2 t ts [] ys id).2.map f = (perm
utationsAux2 t …
· 使用定理 `List.permutationsAux2_comp_append`：permutationsAux2_comp_append {t : α} 
{ts ys : List α} {r : List β} (f : List α -> β) : ((permutationsAux2 t [] r ys) 
fun x => f (x ++ ts)).2…

--- 原说明 ---
An expository lemma to show how all of `ts`, `r`, and `f` can be eliminated from
`permutationsAux2`.

`(permutationsAux2 t [] [] ys id).2`, which appears on the RHS, is a list whose 
elements are
produced by inserting `t` into every non-terminal position of `ys` in order. As 
an example:
```lean
#eval permutationsAux2 1 [] [] [2, 3, 4] id
-- [[1, 2, 3, 4], [2, 1, 3, 4], [2, 3, 1, 4]]
```
-/
theorem permutationsAux2_snd_eq (t : α) (ts : List α) (r : List β) (ys : List α) (f : List α → β) :
    (permutationsAux2 t ts r ys f).2 =
      ((permutationsAux2 t [] [] ys id).2.map fun x => f (x ++ ts)) ++ r := by
  rw [← permutationsAux2_append, map_permutationsAux2, permutationsAux2_comp_append]
/-
**List.map_map_permutationsAux2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_map_permutationsAux2 {α'} (g : α -> α') (t : α) (ts ys : List α) : map
 (map g) (permutationsAux2 t ts [] ys id).2 = (permutationsAux2 (g t) (map g ts)
 [] (map g ys) id).2
参数：g : α -> α'；t : α；ts ys : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_permutationsAux2'`：map_permutationsAux2' {α' β'} (g : α -> α') 
(g' : β -> β') (t : α) (ts ys : List α) (r : List β) (f : List α -> β) (f' : Lis
t α' -> β') (H :…
-/
theorem map_map_permutationsAux2 {α'} (g : α → α') (t : α) (ts ys : List α) :
    map (map g) (permutationsAux2 t ts [] ys id).2 =
      (permutationsAux2 (g t) (map g ts) [] (map g ys) id).2 :=
  map_permutationsAux2' _ _ _ _ _ _ _ _ fun _ => rfl
/-
**List.map_map_permutations'Aux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (t : α) (ts : List α),   List.
map (List.map f) (List.permutations'Aux t ts) = List.permutations'Aux (f t) (Lis
t.map f ts)
参数：f : α → β；t : α；ts : List α；List.map f；List.permutations'Aux t ts；f t；List.ma
p f ts。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.permutations'Aux.eq_2`：∀ {α : Type u_1} (t a : α) (tail : List α), 
  List.permutations'Aux t (a :: tail) = (t :: a :: tail) :: List.map (List.cons 
a) (List.permuta…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map_permutations'Aux (f : α → β) (t : α) (ts : List α) :
    map (map f) (permutations'Aux t ts) = permutations'Aux (f t) (map f ts) := by
  induction ts with
  | nil => rfl
  | cons a ts ih => simp only [permutations'Aux, map_cons, map_map, ← ih, Function.comp_def]
/-
**List.permutations'Aux_eq_permutationsAux2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (t : α) (ts : List α), List.permutations'Aux t ts = (List
.permutationsAux2 t [] [ts ++ [t]] ts id).2
参数：t : α；ts : List α；List.permutationsAux2 t [] [ts ++ [t]] ts id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux2_snd_cons`：permutationsAux2_snd_cons (t : α) (ts : 
List α) (r : List β) (y : α) (ys : List α) (f : List α -> β) : (permutationsAux2
 t ts r (y :: ys) f)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_permutationsAux2`：map_permutationsAux2 (t : α) (ts : List α) (y
s : List α) (f : List α -> β) : (permutationsAux2 t ts [] ys id).2.map f = (perm
utationsAux2 t …
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
-/
theorem permutations'Aux_eq_permutationsAux2 (t : α) (ts : List α) :
    permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2 := by
  induction ts with | nil => rfl | cons a ts ih => ?_
  simp only [permutations'Aux, ih, cons_append, permutationsAux2_snd_cons, append_nil, id_eq,
    cons.injEq, true_and]
  simp +singlePass only [← permutationsAux2_append]
  simp [map_permutationsAux2]
/-
**List.mem_permutationsAux2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_permutationsAux2 {t : α} {ts : List α} {ys : List α} {l l' : List α} :
 l' in (permutationsAux2 t ts [] ys (l ++ ·)).2 ↔ exists l₁ l₂, l₂ != [] ∧ ys = 
l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.permutationsAux2_snd_cons`：permutationsAux2_snd_cons (t : α) (ts : 
List α) (r : List β) (y : α) (ys : List α) (f : List α -> β) : (permutationsAux2
 t ts r (y :: ys) f)…
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.append_cancel_left_eq`：∀ {α : Type u_1} (as bs cs : List α), (as ++
 bs = as ++ cs) = (bs = cs)
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem mem_permutationsAux2 {t : α} {ts : List α} {ys : List α} {l l' : List α} :
    l' ∈ (permutationsAux2 t ts [] ys (l ++ ·)).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l' = l ++ l₁ ++ t :: l₂ ++ ts := by
  induction ys generalizing l with
  | nil => simp +contextual
  | cons y ys ih => ?_
  rw [permutationsAux2_snd_cons,
    show (fun x : List α => l ++ y :: x) = (l ++ [y] ++ ·) by simp, mem_cons, ih]
  constructor
  · rintro (rfl | ⟨l₁, l₂, l0, rfl, rfl⟩)
    · exact ⟨[], y :: ys, by simp⟩
    · exact ⟨y :: l₁, l₂, l0, by simp⟩
  · rintro ⟨_ | ⟨y', l₁⟩, l₂, l0, ye, rfl⟩
    · simp [ye]
    · simp only [cons_append] at ye
      rcases ye with ⟨rfl, rfl⟩
      exact Or.inr ⟨l₁, l₂, l0, by simp⟩
/-
**List.mem_permutationsAux2'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_permutationsAux2' {t : α} {ts : List α} {ys : List α} {l : List α} : l
 in (permutationsAux2 t ts [] ys id).2 ↔ exists l₁ l₂, l₂ != [] ∧ ys = l₁ ++ l₂ 
∧ l = l₁ ++ t :: l₂ ++ ts
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.mem_permutationsAux2`：mem_permutationsAux2 {t : α} {ts : List α} {y
s : List α} {l l' : List α} : l' in (permutationsAux2 t ts [] ys (l ++ ·)).2 ↔ e
xists l₁ l₂, l₂…
-/
theorem mem_permutationsAux2' {t : α} {ts : List α} {ys : List α} {l : List α} :
    l ∈ (permutationsAux2 t ts [] ys id).2 ↔
      ∃ l₁ l₂, l₂ ≠ [] ∧ ys = l₁ ++ l₂ ∧ l = l₁ ++ t :: l₂ ++ ts := by
  rw [show @id (List α) = ([] ++ ·) by funext _; rfl]; apply mem_permutationsAux2
/-
**List.length_permutationsAux2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α ->
 β) : length (permutationsAux2 t ts [] ys f).2 = length ys
参数：t : α；ts : List α；ys : List α；f : List α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux2_snd_cons`：permutationsAux2_snd_cons (t : α) (ts : 
List α) (r : List β) (y : α) (ys : List α) (f : List α -> β) : (permutationsAux2
 t ts r (y :: ys) f)…
-/
theorem length_permutationsAux2 (t : α) (ts : List α) (ys : List α) (f : List α → β) :
    length (permutationsAux2 t ts [] ys f).2 = length ys := by
  induction ys generalizing f <;> simp [*]
/-
**List.foldr_permutationsAux2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) : foldr
 (fun y r => (permutationsAux2 t ts r y id).2) r L = (L.flatMap fun y => (permut
ationsAux2 t ts [] y id).2) ++ r
参数：t : α；ts : List α；r L : List (List α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.permutationsAux2_append`：permutationsAux2_append (t : α) (ts : List
 α) (r : List β) (ys : List α) (f : List α -> β) : (permutationsAux2 t ts nil ys
 f).2 ++ r = (perm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    foldr (fun y r => (permutationsAux2 t ts r y id).2) r L =
      (L.flatMap fun y => (permutationsAux2 t ts [] y id).2) ++ r := by
  induction L with
  | nil => rfl
  | cons l L ih => simp_rw [foldr_cons, ih, flatMap_cons, append_assoc, permutationsAux2_append]
/-
**List.mem_foldr_permutationsAux2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_foldr_permutationsAux2 {t : α} {ts : List α} {r L : List (List α)} {l'
 : List α} : l' in foldr (fun y r => (permutationsAux2 t ts r y id).2) r L ↔ l' 
in r ∨ exists l₁ l₂, l₁ ++ l₂ in L ∧ l₂ != [] ∧ l' = l₁ ++ t :: l₂ ++ ts
参数：List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_permutationsAux2`：foldr_permutationsAux2 (t : α) (ts : List α
) (r L : List (List α)) : foldr (fun y r => (permutationsAux2 t ts r y id).2) r 
L = (L.flatMap fu…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_foldr_permutationsAux2 {t : α} {ts : List α} {r L : List (List α)} {l' : List α} :
    l' ∈ foldr (fun y r => (permutationsAux2 t ts r y id).2) r L ↔
      l' ∈ r ∨ ∃ l₁ l₂, l₁ ++ l₂ ∈ L ∧ l₂ ≠ [] ∧ l' = l₁ ++ t :: l₂ ++ ts := by
  have :
    (∃ a : List α,
        a ∈ L ∧ ∃ l₁ l₂ : List α, ¬l₂ = nil ∧ a = l₁ ++ l₂ ∧ l' = l₁ ++ t :: (l₂ ++ ts)) ↔
      ∃ l₁ l₂ : List α, ¬l₂ = nil ∧ l₁ ++ l₂ ∈ L ∧ l' = l₁ ++ t :: (l₂ ++ ts) :=
    ⟨fun ⟨_, aL, l₁, l₂, l0, e, h⟩ => ⟨l₁, l₂, l0, e ▸ aL, h⟩, fun ⟨l₁, l₂, l0, aL, h⟩ =>
      ⟨_, aL, l₁, l₂, l0, rfl, h⟩⟩
  rw [foldr_permutationsAux2]
  simp only [mem_permutationsAux2', ← this, or_comm, and_left_comm, mem_append, mem_flatMap,
    append_assoc, cons_append]
/-
**List.length_foldr_permutationsAux2** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) 
: length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) = (map length
 L).sum + length r
参数：t : α；ts : List α；r L : List (List α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.foldr_permutationsAux2`：foldr_permutationsAux2 (t : α) (ts : List α
) (r L : List (List α)) : foldr (fun y r => (permutationsAux2 t ts r y id).2) r 
L = (L.flatMap fu…
· 使用定理 `List.length_append`：∀ {α : Type u} {as bs : List α}, (as ++ bs).length =
 as.length + bs.length
· 使用定理 `List.length_flatMap`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {f : α
 → List β},   (List.flatMap f l).length = (List.map (fun a => (f a).length) l).s
um
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.length_permutationsAux2`：length_permutationsAux2 (t : α) (ts : List
 α) (ys : List α) (f : List α -> β) : length (permutationsAux2 t ts [] ys f).2 =
 length ys
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_foldr_permutationsAux2 (t : α) (ts : List α) (r L : List (List α)) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) =
      (map length L).sum + length r := by
  simp [foldr_permutationsAux2, length_permutationsAux2, length_flatMap]
/-
**List.length_foldr_permutationsAux2'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_foldr_permutationsAux2' (t : α) (ts : List α) (r L : List (List α))
 (n) (H : forall l in L, length l = n) : length (foldr (fun y r => (permutations
Aux2 t ts r y id).2) r L) = n * length L + length r
参数：t : α；ts : List α；r L : List (List α)；n；H : forall l in L, length l = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_foldr_permutationsAux2`：length_foldr_permutationsAux2 (t : α
) (ts : List α) (r L : List (List α)) : length (foldr (fun y r => (permutationsA
ux2 t ts r y id).2) r L)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
-/
theorem length_foldr_permutationsAux2' (t : α) (ts : List α) (r L : List (List α)) (n)
    (H : ∀ l ∈ L, length l = n) :
    length (foldr (fun y r => (permutationsAux2 t ts r y id).2) r L) = n * length L + length r := by
  rw [length_foldr_permutationsAux2, (_ : (map length L).sum = n * length L)]
  induction L with
  | nil => simp
  | cons l L ih =>
    have sum_map : (map length L).sum = n * length L := ih fun l m => H l (mem_cons_of_mem _ m)
    have length_l : length l = n := H _ mem_cons_self
    simp [sum_map, length_l, Nat.add_comm, mul_succ]

@[simp]
/-
**List.permutationsAux_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutationsAux_nil (is : List α) : permutationsAux [] is = []
参数：is : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux.eq_1`：∀ {α : Type u_1} (l₁ l₂ : List α),   l₁.permu
tationsAux l₂ =     List.permutationsAux.rec (fun x => [])       (fun t ts is IH
1 IH2 => List.f…
· 使用定理 `List.permutationsAux.rec.eq_1`：∀ {α : Type u_1} {C : List α → List α → S
ort v} (H0 : (is : List α) → C [] is)   (H1 : (t : α) → (ts is : List α) → C ts 
(t :: is) → C is []…
-/
theorem permutationsAux_nil (is : List α) : permutationsAux [] is = [] := by
  rw [permutationsAux, permutationsAux.rec]

@[simp]
/-
**List.permutationsAux_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutationsAux_cons (t : α) (ts is : List α) : permutationsAux (t :: ts) 
is = foldr (fun y r => (permutationsAux2 t ts r y id).2) (permutationsAux ts (t 
:: is)) (permutations is)
参数：t : α；ts is : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux.eq_1`：∀ {α : Type u_1} (l₁ l₂ : List α),   l₁.permu
tationsAux l₂ =     List.permutationsAux.rec (fun x => [])       (fun t ts is IH
1 IH2 => List.f…
· 使用定理 `List.permutationsAux.rec.eq_2`：∀ {α : Type u_1} {C : List α → List α → S
ort v} (H0 : (is : List α) → C [] is)   (H1 : (t : α) → (ts is : List α) → C ts 
(t :: is) → C is []…
-/
theorem permutationsAux_cons (t : α) (ts is : List α) :
    permutationsAux (t :: ts) is =
      foldr (fun y r => (permutationsAux2 t ts r y id).2) (permutationsAux ts (t :: is))
        (permutations is) := by
  rw [permutationsAux, permutationsAux.rec]; rfl

@[simp]
/-
**List.permutations_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutations_nil : permutations ([] : List α) = [[]]
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutations.eq_1`：∀ {α : Type u_1} (l : List α), l.permutations = 
l :: l.permutationsAux []
· 使用定理 `List.permutationsAux_nil`：permutationsAux_nil (is : List α) : permutatio
nsAux [] is = []
-/
theorem permutations_nil : permutations ([] : List α) = [[]] := by
  rw [permutations, permutationsAux_nil]
/-
**List.map_permutationsAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_permutationsAux (f : α -> β) : forall ts is : List α, map (map f) (per
mutationsAux ts is) = permutationsAux (map f ts) (map f is)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux_nil`：permutationsAux_nil (is : List α) : permutatio
nsAux [] is = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.permutationsAux_cons`：permutationsAux_cons (t : α) (ts is : List α)
 : permutationsAux (t :: ts) is = foldr (fun y r => (permutationsAux2 t ts r y i
d).2) (permutat…
· 使用定理 `List.foldr_permutationsAux2`：foldr_permutationsAux2 (t : α) (ts : List α
) (r L : List (List α)) : foldr (fun y r => (permutationsAux2 t ts r y id).2) r 
L = (L.flatMap fu…
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_map_permutationsAux2`：map_map_permutationsAux2 {α'} (g : α -> α
') (t : α) (ts ys : List α) : map (map g) (permutationsAux2 t ts [] ys id).2 = (
permutationsAux2 (g…
· 使用定理 `List.map_flatMap`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : β 
→ γ} {g : α → List β} {l : List α},   List.map f (List.flatMap g l) = List.flatM
ap (fu…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β), List.map f [
] = []
· 使用定理 `List.flatMap_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α 
→ β) (g : β → List γ) (l : List α),   List.flatMap g (List.map f l) = List.flatM
ap (fu…
-/
theorem map_permutationsAux (f : α → β) :
    ∀ ts is :
    List α, map (map f) (permutationsAux ts is) = permutationsAux (map f ts) (map f is) := by
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2; rw [map] at IH2
  simp only [foldr_permutationsAux2, map_append, map, map_map_permutationsAux2, permutations,
    flatMap_map, IH1, append_assoc, permutationsAux_cons, flatMap_cons, ← IH2, map_flatMap]
/-
**List.map_permutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_permutations (f : α -> β) (ts : List α) : map (map f) (permutations ts
) = permutations (map f ts)
参数：f : α -> β；ts : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutations.eq_1`：∀ {α : Type u_1} (l : List α), l.permutations = 
l :: l.permutationsAux []
· 使用定理 `List.map.eq_2`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (head : α) (t
ail : List α),   List.map f (head :: tail) = f head :: List.map f tail
· 使用定理 `List.map_permutationsAux`：map_permutationsAux (f : α -> β) : forall ts i
s : List α, map (map f) (permutationsAux ts is) = permutationsAux (map f ts) (ma
p f is)
· 使用定理 `List.map.eq_1`：∀ {α : Type u_1} {β : Type u_2} (f : α → β), List.map f [
] = []
-/
theorem map_permutations (f : α → β) (ts : List α) :
    map (map f) (permutations ts) = permutations (map f ts) := by
  rw [permutations, permutations, map, map_permutationsAux, map]
/-
**List.map_permutations'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_permutations' (f : α -> β) (ts : List α) : map (map f) (permutations' 
ts) = permutations' (map f ts)
参数：f : α -> β；ts : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.permutations'`：permutations'Aux_eq_permutationsAux2 (t : α) (ts : L
ist α) : permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_flatMap`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : β 
→ γ} {g : α → List β} {l : List α},   List.map f (List.flatMap g l) = List.flatM
ap (fu…
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.permutations'.eq_2`：∀ {α : Type u_1} (a : α) (tail : List α),   (a 
:: tail).permutations' = List.flatMap (List.permutations'Aux a) tail.permutation
s'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.flatMap_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α 
→ β) (g : β → List γ) (l : List α),   List.flatMap g (List.map f l) = List.flatM
ap (fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_permutations' (f : α → β) (ts : List α) :
    map (map f) (permutations' ts) = permutations' (map f ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [← ih, map_flatMap, ← map_map_permutations'Aux, flatMap_map]
/-
**List.permutationsAux_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutationsAux_append (is is' ts : List α) : permutationsAux (is ++ ts) i
s' = (permutationsAux is is').map (· ++ ts) ++ permutationsAux ts (is.reverse ++
 is')
参数：is is' ts : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.permutationsAux_nil`：permutationsAux_nil (is : List α) : permutatio
nsAux [] is = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.permutationsAux_cons`：permutationsAux_cons (t : α) (ts is : List α)
 : permutationsAux (t :: ts) is = foldr (fun y r => (permutationsAux2 t ts r y i
d).2) (permutat…
· 使用定理 `List.foldr_permutationsAux2`：foldr_permutationsAux2 (t : α) (ts : List α
) (r L : List (List α)) : foldr (fun y r => (permutationsAux2 t ts r y id).2) r 
L = (L.flatMap fu…
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
· 使用定理 `List.map_flatMap`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : β 
→ γ} {g : α → List β} {l : List α},   List.map f (List.flatMap g l) = List.flatM
ap (fu…
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_permutationsAux2`：map_permutationsAux2 (t : α) (ts : List α) (y
s : List α) (f : List α -> β) : (permutationsAux2 t ts [] ys id).2.map f = (perm
utationsAux2 t …
-/
theorem permutationsAux_append (is is' ts : List α) :
    permutationsAux (is ++ ts) is' =
      (permutationsAux is is').map (· ++ ts) ++ permutationsAux ts (is.reverse ++ is') := by
  induction is generalizing is' with | nil => simp | cons t is ih =>
  simp only [foldr_permutationsAux2, ih, map_flatMap, cons_append, permutationsAux_cons, map_append,
    reverse_cons, append_assoc]
  congr 2
  funext _
  rw [map_permutationsAux2]
  simp +singlePass only [← permutationsAux2_comp_append]
  simp only [id, append_assoc]
/-
**List.permutations_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutations_append (is ts : List α) : permutations (is ++ ts) = (permutat
ions is).map (· ++ ts) ++ permutationsAux ts is.reverse
参数：is ts : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux_append`：permutationsAux_append (is is' ts : List α)
 : permutationsAux (is ++ ts) is' = (permutationsAux is is').map (· ++ ts) ++ pe
rmutationsAux ts …
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem permutations_append (is ts : List α) :
    permutations (is ++ ts) = (permutations is).map (· ++ ts) ++ permutationsAux ts is.reverse := by
  simp [permutations, permutationsAux_append]
/-
**List.perm_of_mem_permutationsAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_of_mem_permutationsAux : forall {ts is l : List α}, l in permutations
Aux ts is -> l ~ ts ++ is
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux_nil`：permutationsAux_nil (is : List α) : permutatio
nsAux [] is = []
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.mem_foldr_permutationsAux2`：mem_foldr_permutationsAux2 {t : α} {ts 
: List α} {r L : List (List α)} {l' : List α} : l' in foldr (fun y r => (permuta
tionsAux2 t ts r y id…
· 使用定理 `List.permutations.eq_1`：∀ {α : Type u_1} (l : List α), l.permutations = 
l :: l.permutationsAux []
· 使用定理 `List.permutationsAux_cons`：permutationsAux_cons (t : α) (ts is : List α)
 : permutationsAux (t :: ts) is = foldr (fun y r => (permutationsAux2 t ts r y i
d).2) (permutat…
· 使用定理 `List.perm_middle`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, (l₁ ++ a ::
 l₂).Perm (a :: (l₁ ++ l₂))
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.Perm.append_right`：∀ {α : Type u_1} {l₁ l₂ : List α} (t₁ : List α),
 l₁.Perm l₂ → (l₁ ++ t₁).Perm (l₂ ++ t₁)
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem perm_of_mem_permutationsAux :
    ∀ {ts is l : List α}, l ∈ permutationsAux ts is → l ~ ts ++ is := by
  show ∀ (ts is l : List α), l ∈ permutationsAux ts is → l ~ ts ++ is
  refine permutationsAux.rec (by simp) ?_
  introv IH1 IH2 m
  rw [permutationsAux_cons, permutations, mem_foldr_permutationsAux2] at m
  rcases m with (m | ⟨l₁, l₂, m, _, rfl⟩)
  · exact (IH1 _ m).trans perm_middle
  · have p : l₁ ++ l₂ ~ is := by
      simp only [mem_cons] at m
      rcases m with e | m
      · simp [e]
      exact is.append_nil ▸ IH2 _ m
    exact ((perm_middle.trans (p.cons _)).append_right _).trans (perm_append_comm.cons _)
/-
**List.perm_of_mem_permutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_of_mem_permutations {l₁ l₂ : List α} (h : l₁ in permutations l₂) : l₁
 ~ l₂
参数：h : l₁ in permutations l₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `List.eq_or_mem_of_mem_cons`：∀ {α : Type u_1} {a b : α} {l : List α}, a ∈
 b :: l → a = b ∨ a ∈ l
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `List.perm_of_mem_permutationsAux`：perm_of_mem_permutationsAux : forall {
ts is l : List α}, l in permutationsAux ts is -> l ~ ts ++ is
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
-/
theorem perm_of_mem_permutations {l₁ l₂ : List α} (h : l₁ ∈ permutations l₂) : l₁ ~ l₂ :=
  (eq_or_mem_of_mem_cons h).elim (fun e => e ▸ Perm.refl _) fun m =>
    append_nil l₂ ▸ perm_of_mem_permutationsAux m
/-
**List.length_permutationsAux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_permutationsAux : forall ts is : List α, length (permutationsAux ts
 is) + is.length ! = (length ts + length is)!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.permutationsAux_nil`：permutationsAux_nil (is : List α) : permutatio
nsAux [] is = []
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.permutationsAux_cons`：permutationsAux_cons (t : α) (ts is : List α)
 : permutationsAux (t :: ts) is = foldr (fun y r => (permutationsAux2 t ts r y i
d).2) (permutat…
· 使用定理 `List.length_foldr_permutationsAux2'`：length_foldr_permutationsAux2' (t :
 α) (ts : List α) (r L : List (List α)) (n) (H : forall l in L, length l = n) : 
length (foldr (fun y r =>…
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `List.perm_of_mem_permutations`：perm_of_mem_permutations {l₁ l₂ : List α}
 (h : l₁ in permutations l₂) : l₁ ~ l₂
· 使用定理 `List.permutations.eq_1`：∀ {α : Type u_1} (l : List α), l.permutations = 
l :: l.permutationsAux []
· 使用定理 `List.length.eq_2`：∀ {α : Type u_1} (head : α) (tail : List α), (head :: 
tail).length = tail.length + 1
· 使用定理 `Nat.succ_add`：∀ (n m : ℕ), n.succ + m = (n + m).succ
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.mul_comm`：∀ (n m : ℕ), n * m = m * n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_eq_add_one`：∀ (n : ℕ), n.succ = n + 1
· 使用定理 `Nat.factorial.eq_2`：∀ (n : ℕ), n.succ.factorial = n.succ * n.factorial
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
· 使用定理 `Nat.mul_succ`：∀ (n m : ℕ), n * m.succ = n * m + n
-/
theorem length_permutationsAux :
    ∀ ts is : List α, length (permutationsAux ts is) + is.length ! = (length ts + length is)! := by
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2
  have IH2 : length (permutationsAux is nil) + 1 = is.length ! := by simpa using IH2
  simp only [List.length_cons, factorial, Nat.mul_comm, add_eq] at IH1
  rw [permutationsAux_cons,
    length_foldr_permutationsAux2' _ _ _ _ _ fun l m => (perm_of_mem_permutations m).length_eq,
    permutations, length, length, IH2, Nat.succ_add, Nat.factorial_succ, Nat.mul_comm (_ + 1),
    ← Nat.succ_eq_add_one, ← IH1, Nat.add_comm (_ * _), Nat.add_assoc, Nat.mul_succ, Nat.mul_comm]
/-
**List.length_permutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_permutations (l : List α) : length (permutations l) = (length l)!
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_permutationsAux`：length_permutationsAux : forall ts is : Lis
t α, length (permutationsAux ts is) + is.length ! = (length ts + length is)!
-/
theorem length_permutations (l : List α) : length (permutations l) = (length l)! :=
  length_permutationsAux l []
/-
**List.mem_permutations_of_perm_lemma** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_permutations_of_perm_lemma {is l : List α} (H : l ~ [] ++ is -> (exist
s (ts' : _) (_ : ts' ~ []), l = ts' ++ is) ∨ l in permutationsAux is []) : l ~ i
s -> l in permutations is
参数：H : l ~ [] ++ is -> (exists (ts' : _) (_ : ts' ~ []), l = ts' ++ is) ∨ l in p
ermutationsAux is []。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem mem_permutations_of_perm_lemma {is l : List α}
    (H : l ~ [] ++ is → (∃ (ts' : _) (_ : ts' ~ []), l = ts' ++ is) ∨ l ∈ permutationsAux is []) :
    l ~ is → l ∈ permutations is := by simpa [permutations, perm_nil] using H
/-
**List.mem_permutationsAux_of_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_permutationsAux_of_perm : forall {ts is l : List α}, l ~ is ++ ts -> (
exists (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l in permutationsAux ts is
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.permutationsAux_nil`：permutationsAux_nil (is : List α) : permutatio
nsAux [] is = []
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `List.permutationsAux_cons`：permutationsAux_cons (t : α) (ts is : List α)
 : permutationsAux (t :: ts) is = foldr (fun y r => (permutationsAux2 t ts r y i
d).2) (permutat…
· 使用定理 `List.mem_foldr_permutationsAux2`：mem_foldr_permutationsAux2 {t : α} {ts 
: List α} {r L : List (List α)} {l' : List α} : l' in foldr (fun y r => (permuta
tionsAux2 t ts r y id…
· 使用定理 `List.perm_middle`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, (l₁ ++ a ::
 l₂).Perm (a :: (l₁ ++ l₂))
· 使用定理 `List.append_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ s t
, l = s ++ a :: t
· 使用定理 `List.Perm.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁ ⊆ l
₂
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.Perm.cons_inv`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, (a :: l₁)
.Perm (a :: l₂) → l₁.Perm l₂
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `List.mem_permutations_of_perm_lemma`：mem_permutations_of_perm_lemma {is 
l : List α} (H : l ~ [] ++ is -> (exists (ts' : _) (_ : ts' ~ []), l = ts' ++ is
) ∨ l in permutationsAux …
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
（共 31 条，此处仅展示前 30 条）
-/
theorem mem_permutationsAux_of_perm :
    ∀ {ts is l : List α},
      l ~ is ++ ts → (∃ (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is := by
  show ∀ (ts is l : List α),
      l ~ is ++ ts → (∃ (is' : _) (_ : is' ~ is), l = is' ++ ts) ∨ l ∈ permutationsAux ts is
  refine permutationsAux.rec (by simp) ?_
  intro t ts is IH1 IH2 l p
  rw [permutationsAux_cons, mem_foldr_permutationsAux2]
  rcases IH1 _ (p.trans perm_middle) with (⟨is', p', e⟩ | m)
  · clear p
    subst e
    rcases append_of_mem (p'.symm.subset mem_cons_self) with ⟨l₁, l₂, e⟩
    subst is'
    have p := (perm_middle.symm.trans p').cons_inv
    rcases l₂ with - | ⟨a, l₂'⟩
    · exact Or.inl ⟨l₁, by simpa using p⟩
    · exact Or.inr (Or.inr ⟨l₁, a :: l₂', mem_permutations_of_perm_lemma (IH2 _) p, by simp⟩)
  · exact Or.inr (Or.inl m)

@[simp]
/-
**List.mem_permutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_permutations {s t : List α} : s in permutations t ↔ s ~ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.perm_of_mem_permutations`：perm_of_mem_permutations {l₁ l₂ : List α}
 (h : l₁ in permutations l₂) : l₁ ~ l₂
· 使用定理 `List.mem_permutations_of_perm_lemma`：mem_permutations_of_perm_lemma {is 
l : List α} (H : l ~ [] ++ is -> (exists (ts' : _) (_ : ts' ~ []), l = ts' ++ is
) ∨ l in permutationsAux …
· 使用定理 `List.mem_permutationsAux_of_perm`：mem_permutationsAux_of_perm : forall {
ts is l : List α}, l ~ is ++ ts -> (exists (is' : _) (_ : is' ~ is), l = is' ++ 
ts) ∨ l in permutation…
-/
theorem mem_permutations {s t : List α} : s ∈ permutations t ↔ s ~ t :=
  ⟨perm_of_mem_permutations, mem_permutations_of_perm_lemma mem_permutationsAux_of_perm⟩

/-- A list is a permutation of the pair `[a, b]` if and only if it is equal to `[a, b]` or to
`[b, a]`. -/
/-
**List.perm_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_pair {a b : α} {l : List α} : l ~ [a, b] ↔ l = [a, b] ∨ l = [b, a]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutations.eq_1`：∀ {α : Type u_1} (l : List α), l.permutations = 
l :: l.permutationsAux []
· 使用定理 `List.permutationsAux.eq_1`：∀ {α : Type u_1} (l₁ l₂ : List α),   l₁.permu
tationsAux l₂ =     List.permutationsAux.rec (fun x => [])       (fun t ts is IH
1 IH2 => List.f…
· 使用定理 `List.permutationsAux.rec.eq_2`：∀ {α : Type u_1} {C : List α → List α → S
ort v} (H0 : (is : List α) → C [] is)   (H1 : (t : α) → (ts is : List α) → C ts 
(t :: is) → C is []…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.permutationsAux.rec.eq_1`：∀ {α : Type u_1} {C : List α → List α → S
ort v} (H0 : (is : List α) → C [] is)   (H1 : (t : α) → (ts is : List α) → C ts 
(t :: is) → C is []…
· 使用定理 `List.foldr.eq_2`：∀ {α : Type u} {β : Type v} (f : α → β → β) (init : β) 
(a : α) (as : List α),   List.foldr f init (a :: as) = f a (List.foldr f init as
)
· 使用定理 `List.foldr.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β → β) (init : β),
 List.foldr f init [] = init
· 使用定理 `List.permutationsAux2.eq_1`：∀ {α : Type u_1} {β : Type u_2} (t : α) (ts 
: List α) (r : List β) (x : List α → β),   List.permutationsAux2 t ts r [] x = (
ts, r)
· 使用定理 `Prod.snd.eq_1`：∀ (α : Type u) (β : Type v) (self : α × β), self.2 = self
.2
· 使用定理 `List.permutationsAux2.eq_2`：∀ {α : Type u_1} {β : Type u_2} (t : α) (ts 
: List α) (r : List β) (x : List α → β) (y : α) (ys : List α),   List.permutatio
nsAux2 t ts r (y…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `_private.Mathlib.Data.List.Permutation.0.List.permutationsAux2.match_1.e
q_1`：∀ {α : Type u_1} {β : Type u_2} (motive : List α × List β → Sort u_3) (us :
 List α) (zs : List β)   (h_1 : (us : List α) → (zs : List β) → m…
· 使用定理 `id.eq_1`：∀ {α : Sort u} (a : α), id a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A list is a permutation of the pair `[a, b]` if and only if it is equal to `[a, 
b]` or to
`[b, a]`.
-/
theorem perm_pair {a b : α} {l : List α} : l ~ [a, b] ↔ l = [a, b] ∨ l = [b, a] := by
  have : [a, b].permutations = [[a, b], [b, a]] := by cbv
  grind [=_ mem_permutations]

/-- The pair `[a, b]` is a permutation of a list if and only if that list is equal to `[a, b]` or
to `[b, a]`. -/
/-
**List.pair_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pair_perm {a b : α} {l : List α} : [a, b] ~ l ↔ l = [a, b] ∨ l = [b, a]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.perm_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ ↔ l₂.Perm 
l₁
· 使用定理 `List.perm_pair`：perm_pair {a b : α} {l : List α} : l ~ [a, b] ↔ l = [a, 
b] ∨ l = [b, a]

--- 原说明 ---
The pair `[a, b]` is a permutation of a list if and only if that list is equal t
o `[a, b]` or
to `[b, a]`.
-/
theorem pair_perm {a b : α} {l : List α} : [a, b] ~ l ↔ l = [a, b] ∨ l = [b, a] :=
  perm_comm.trans perm_pair
/-
**List.perm_permutations'Aux_comm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (a b : α) (l : List α),   (List.flatMap (List.permutation
s'Aux b) (List.permutations'Aux a l)).Perm     (List.flatMap (List.permutations'
Aux a) (List.permutations'Aux b l))
参数：a b : α；l : List α；List.flatMap (List.permutations'Aux b) (List.permutations'
Aux a l)；List.flatMap (List.permutations'Aux a) (List.permutations'Aux b l)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.Perm.swap'`：∀ {α : Type u_1} (x y : α) {l₁ l₂ : List α}, l₁.Perm l₂
 → (y :: x :: l₁).Perm (x :: y :: l₂)
· 使用定理 `List.flatMap_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α 
→ β) (g : β → List γ) (l : List α),   List.flatMap g (List.map f l) = List.flatM
ap (fu…
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.flatMap_append_perm`：flatMap_append_perm (l : List α) (f g : α -> L
ist β) : l.flatMap f ++ l.flatMap g ~ l.flatMap fun x => f x ++ g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_eq_flatMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α}, List.map f l = List.flatMap (fun x => [f x]) l
· 使用定理 `List.map_flatMap`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : β 
→ γ} {g : α → List β} {l : List α},   List.map f (List.flatMap g l) = List.flatM
ap (fu…
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `List.Perm.append_left`：∀ {α : Type u_1} {t₁ t₂ : List α} (l : List α), t
₁.Perm t₂ → (l ++ t₁).Perm (l ++ t₂)
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
-/
theorem perm_permutations'Aux_comm (a b : α) (l : List α) :
    (permutations'Aux a l).flatMap (permutations'Aux b) ~
      (permutations'Aux b l).flatMap (permutations'Aux a) := by
  induction l with
  | nil => exact Perm.swap [a, b] [b, a] []
  | cons c l ih => ?_
  simp only [permutations'Aux, flatMap_cons, map_cons, map_map, cons_append]
  apply Perm.swap'
  have :
    ∀ a b,
      (map (cons c) (permutations'Aux a l)).flatMap (permutations'Aux b) ~
        map (cons b ∘ cons c) (permutations'Aux a l) ++
          map (cons c) ((permutations'Aux a l).flatMap (permutations'Aux b)) := by
    intro a' b'
    simp only [flatMap_map, permutations'Aux]
    change (permutations'Aux _ l).flatMap (fun a => ([b' :: c :: a] ++
      map (cons c) (permutations'Aux _ a))) ~ _
    refine (flatMap_append_perm _ (fun x => [b' :: c :: x]) _).symm.trans ?_
    rw [← map_eq_flatMap, ← map_flatMap]
    exact Perm.refl _
  refine (((this _ _).append_left _).trans ?_).trans ((this _ _).append_left _).symm
  rw [← append_assoc, ← append_assoc]
  exact perm_append_comm.append (ih.map _)
/-
**List.Perm.permutations'** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {s t : List α}, s.Perm t → s.permutations'.Perm t.permuta
tions'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.permutations'`：permutations'Aux_eq_permutationsAux2 (t : α) (ts : L
ist α) : permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.Perm.flatMap_right`：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α
} (f : α → List β),   l₁.Perm l₂ → (List.flatMap f l₁).Perm (List.flatMap f l₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatMap_assoc`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : 
List α} {f : α → List β} {g : β → List γ},   List.flatMap g (List.flatMap f l) =
 List.fl…
· 使用定理 `List.Perm.flatMap_left`：∀ {α : Type u_1} {β : Type u_2} (l : List α) {f 
g : α → List β},   (∀ a ∈ l, (f a).Perm (g a)) → (List.flatMap f l).Perm (List.f
latMap g l)
· 使用定理 `List.perm_permutations'Aux_comm`：∀ {α : Type u_1} (a b : α) (l : List α)
,   (List.flatMap (List.permutations'Aux b) (List.permutations'Aux a l)).Perm   
  (List.flatMap (List…
-/
theorem Perm.permutations' {s t : List α} (p : s ~ t) : permutations' s ~ permutations' t := by
  induction p with
  | nil => simp
  | cons _ _ IH => exact IH.flatMap_right _
  | swap =>
    dsimp
    rw [flatMap_assoc, flatMap_assoc]
    apply Perm.flatMap_left
    intro l' _
    apply perm_permutations'Aux_comm
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂
/-
**List.permutations_perm_permutations'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutations_perm_permutations' (ts : List α) : ts.permutations ~ ts.permu
tations'
参数：ts : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.permutations'`：permutations'Aux_eq_permutationsAux2 (t : α) (ts : L
ist α) : permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux_nil`：permutationsAux_nil (is : List α) : permutatio
nsAux [] is = []
· 使用定理 `List.length_reverse`：∀ {α : Type u_1} {as : List α}, as.reverse.length =
 as.length
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
· 使用定理 `List.length_concat`：∀ {α : Type u} {as : List α} {a : α}, (as.concat a).
length = as.length + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.Perm.permutations'`：∀ {α : Type u_1} {s t : List α}, s.Perm t → s.p
ermutations'.Perm t.permutations'
· 使用定理 `List.reverse_perm`：∀ {α : Type u_1} (l : List α), l.reverse.Perm l
· 使用定理 `List.permutations_append`：permutations_append (is ts : List α) : permuta
tions (is ++ ts) = (permutations is).map (· ++ ts) ++ permutationsAux ts is.reve
rse
· 使用定理 `List.permutationsAux_cons`：permutationsAux_cons (t : α) (ts is : List α)
 : permutationsAux (t :: ts) is = foldr (fun y r => (permutationsAux2 t ts r y i
d).2) (permutat…
· 使用定理 `List.foldr_permutationsAux2`：foldr_permutationsAux2 (t : α) (ts : List α
) (r L : List (List α)) : foldr (fun y r => (permutationsAux2 t ts r y id).2) r 
L = (L.flatMap fu…
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.perm_append_comm`：∀ {α : Type u_1} {l₁ l₂ : List α}, (l₁ ++ l₂).Per
m (l₂ ++ l₁)
· 使用定理 `List.Perm.append`：∀ {α : Type u_1} {l₁ l₂ t₁ t₂ : List α}, l₁.Perm l₂ → 
t₁.Perm t₂ → (l₁ ++ t₁).Perm (l₂ ++ t₂)
· 使用定理 `List.Perm.flatMap_right`：∀ {α : Type u_1} {β : Type u_2} {l₁ l₂ : List α
} (f : α → List β),   l₁.Perm l₂ → (List.flatMap f l₁).Perm (List.flatMap f l₂)
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `List.map_eq_flatMap`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α}, List.map f l = List.flatMap (fun x => [f x]) l
· 使用定理 `List.singleton_append`：∀ {α : Type u_1} {x : α} {l : List α}, [x] ++ l =
 x :: l
· 使用定理 `List.permutations'.eq_2`：∀ {α : Type u_1} (a : α) (tail : List α),   (a 
:: tail).permutations' = List.flatMap (List.permutations'Aux a) tail.permutation
s'
· 使用定理 `List.flatMap_append_perm`：flatMap_append_perm (l : List α) (f g : α -> L
ist β) : l.flatMap f ++ l.flatMap g ~ l.flatMap fun x => f x ++ g x
· 使用定理 `List.Perm.of_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ = l₂ → l₁.Perm l₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.permutations'Aux_eq_permutationsAux2`：∀ {α : Type u_1} (t : α) (ts 
: List α), List.permutations'Aux t ts = (List.permutationsAux2 t [] [ts ++ [t]] 
ts id).2
（共 31 条，此处仅展示前 30 条）
-/
theorem permutations_perm_permutations' (ts : List α) : ts.permutations ~ ts.permutations' := by
  obtain ⟨n, h⟩ : ∃ n, length ts < n := ⟨_, Nat.lt_succ_self _⟩
  induction n generalizing ts with | zero => cases h | succ n IH => ?_
  refine List.reverseRecOn ts (fun _ => ?_) (fun ts t _ h => ?_) h; · simp [permutations]
  rw [← concat_eq_append, length_concat, Nat.succ_lt_succ_iff] at h
  have IH₂ := (IH ts.reverse (by rwa [length_reverse])).trans (reverse_perm _).permutations'
  simp only [permutations_append, foldr_permutationsAux2, permutationsAux_nil,
    permutationsAux_cons, append_nil]
  refine
    (perm_append_comm.trans ((IH₂.flatMap_right _).append ((IH _ h).map _))).trans
      (Perm.trans ?_ perm_append_comm.permutations')
  rw [map_eq_flatMap, singleton_append, permutations']
  refine (flatMap_append_perm _ _ _).trans ?_
  refine Perm.of_eq ?_
  congr
  funext _
  rw [permutations'Aux_eq_permutationsAux2, permutationsAux2_append]

@[simp]
/-
**List.mem_permutations'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_permutations' {s t : List α} : s in permutations' t ↔ s ~ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.permutations'`：permutations'Aux_eq_permutationsAux2 (t : α) (ts : L
ist α) : permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.permutations_perm_permutations'`：permutations_perm_permutations' (t
s : List α) : ts.permutations ~ ts.permutations'
· 使用定理 `List.mem_permutations`：mem_permutations {s t : List α} : s in permutatio
ns t ↔ s ~ t
-/
theorem mem_permutations' {s t : List α} : s ∈ permutations' t ↔ s ~ t :=
  (permutations_perm_permutations' _).symm.mem_iff.trans mem_permutations
/-
**List.Perm.permutations** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {s t : List α}, s.Perm t → s.permutations.Perm t.permutat
ions
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.permutations'`：permutations'Aux_eq_permutationsAux2 (t : α) (ts : L
ist α) : permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2
· 使用定理 `List.permutations_perm_permutations'`：permutations_perm_permutations' (t
s : List α) : ts.permutations ~ ts.permutations'
· 使用定理 `List.Perm.permutations'`：∀ {α : Type u_1} {s t : List α}, s.Perm t → s.p
ermutations'.Perm t.permutations'
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
-/
theorem Perm.permutations {s t : List α} (h : s ~ t) : permutations s ~ permutations t :=
  (permutations_perm_permutations' _).trans <|
    h.permutations'.trans (permutations_perm_permutations' _).symm

@[simp]
/-
**List.perm_permutations_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_permutations_iff {s t : List α} : permutations s ~ permutations t ↔ s
 ~ t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_permutations`：mem_permutations {s t : List α} : s in permutatio
ns t ↔ s ~ t
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `List.Perm.permutations`：∀ {α : Type u_1} {s t : List α}, s.Perm t → s.pe
rmutations.Perm t.permutations
-/
theorem perm_permutations_iff {s t : List α} : permutations s ~ permutations t ↔ s ~ t :=
  ⟨fun h => mem_permutations.1 <| h.mem_iff.1 <| mem_permutations.2 (Perm.refl _),
    Perm.permutations⟩

@[simp]
/-
**List.perm_permutations'_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {s t : List α}, s.permutations'.Perm t.permutations' ↔ s.
Perm t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.permutations'`：permutations'Aux_eq_permutationsAux2 (t : α) (ts : L
ist α) : permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_permutations'`：mem_permutations' {s t : List α} : s in permutat
ions' t ↔ s ~ t
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.refl`：∀ {α : Type u_1} (l : List α), l.Perm l
· 使用定理 `List.Perm.permutations'`：∀ {α : Type u_1} {s t : List α}, s.Perm t → s.p
ermutations'.Perm t.permutations'
-/
theorem perm_permutations'_iff {s t : List α} : permutations' s ~ permutations' t ↔ s ~ t :=
  ⟨fun h => mem_permutations'.1 <| h.mem_iff.1 <| mem_permutations'.2 (Perm.refl _),
    Perm.permutations'⟩
/-
**List.getElem_permutations'Aux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (s : List α) (x : α) (n : ℕ) (hn : n < (List.permutations
'Aux x s).length),   (List.permutations'Aux x s)[n] = s.insertIdx n x
参数：s : List α；x : α；n : ℕ；hn : n < (List.permutations'Aux x s).length；List.permu
tations'Aux x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
theorem getElem_permutations'Aux (s : List α) (x : α) (n : ℕ)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s)[n] = s.insertIdx n x := by
  induction s generalizing n with
  | nil =>
    simp only [permutations'Aux, length, Nat.zero_add, lt_one_iff] at hn
    simp [hn]
  | cons y s IH =>
    cases n
    · simp
    · simpa [get] using IH _ _
/-
**List.get_permutations'Aux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (s : List α) (x : α) (n : ℕ) (hn : n < (List.permutations
'Aux x s).length),   (List.permutations'Aux x s).get ⟨n, hn⟩ = s.insertIdx n x
参数：s : List α；x : α；n : ℕ；hn : n < (List.permutations'Aux x s).length；List.permu
tations'Aux x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_permutations'Aux`：∀ {α : Type u_1} (s : List α) (x : α) (n 
: ℕ) (hn : n < (List.permutations'Aux x s).length),   (List.permutations'Aux x s
)[n] = s.insertIdx …
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_permutations'Aux (s : List α) (x : α) (n : ℕ)
    (hn : n < length (permutations'Aux x s)) :
    (permutations'Aux x s).get ⟨n, hn⟩ = s.insertIdx n x := by
  simp [getElem_permutations'Aux]

-- Porting note: temporary theorem to solve diamond issue
/-
**List.DecEq_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem DecEq_eq [DecidableEq α] :
    List.instBEq = @instBEqOfDecidableEq (List α) instDecidableEqList :=
  congr_arg BEq.mk <| by
    funext l₁ l₂
    change (l₁ == l₂) = _
    rw [Bool.eq_iff_iff, @beq_iff_eq _ (_), decide_eq_true_iff]
/-
**List.count_permutations'Aux_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (l : List α) (x : α),   List.count
 (x :: l) (List.permutations'Aux x l) = (List.takeWhile (fun x_1 => decide (x = 
x_1)) l).length + 1
参数：l : List α；x : α；x :: l；List.permutations'Aux x l；List.takeWhile (fun x_1 => 
decide (x = x_1)) l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.countP_cons_of_pos`：∀ {α : Type u_1} {p : α → Bool} {a : α} {l : Li
st α}, p a = true → List.countP p (a :: l) = List.countP p l + 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `BEq.rfl`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a : α}, (a == a) =
 true
· 使用定理 `List.instReflBEq`：∀ {α : Type u} [inst : BEq α] [ReflBEq α], ReflBEq (Li
st α)
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `List.permutations'Aux.eq_2`：∀ {α : Type u_1} (t a : α) (tail : List α), 
  List.permutations'Aux t (a :: tail) = (t :: a :: tail) :: List.map (List.cons 
a) (List.permuta…
· 使用定理 `List.count_cons_self`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a :
 α} {l : List α}, List.count a (a :: l) = List.count a l + 1
· 使用定理 `List.instLawfulBEq`：∀ {α : Type u} [inst : BEq α] [LawfulBEq α], LawfulB
Eq (List α)
· 使用定理 `List.count_map_of_injective`：count_map_of_injective [BEq β] [LawfulBEq β
] (l : List α) (f : α -> β) (hf : Function.Injective f) (x : α) : count (f x) (m
ap f l) = count x…
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `List.takeWhile.eq_2`：∀ {α : Type u} (p : α → Bool) (a : α) (as : List α)
,   List.takeWhile p (a :: as) =     match p a with     | true => a :: List.take
While p a…
· 使用定理 `List.count_eq_zero_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBE
q α] {a : α} {l : List α}, a ∉ l → List.count a l = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
-/
theorem count_permutations'Aux_self [DecidableEq α] (l : List α) (x : α) :
    count (x :: l) (permutations'Aux x l) = length (takeWhile (x = ·) l) + 1 := by
  induction l generalizing x with
  | nil => simp [takeWhile, count]
  | cons y l IH =>
    rw [permutations'Aux, count_cons_self]
    by_cases hx : x = y
    · subst hx
      simpa [takeWhile, Nat.succ_inj, DecEq_eq] using IH _
    · rw [takeWhile]
      simp only [mem_map, cons.injEq, Ne.symm hx, false_and, and_false, exists_false,
        not_false_iff, count_eq_zero_of_not_mem, Nat.zero_add, hx, decide_false, length_nil]

@[simp]
/-
**List.length_permutations'Aux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (s : List α) (x : α), (List.permutations'Aux x s).length 
= s.length + 1
参数：s : List α；x : α；List.permutations'Aux x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
-/
theorem length_permutations'Aux (s : List α) (x : α) :
    length (permutations'Aux x s) = length s + 1 := by
  induction s with
  | nil => simp
  | cons y s IH => simpa using IH
/-
**List.injective_permutations'Aux** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (x : α), Function.Injective (List.permutations'Aux x)
参数：x : α；List.permutations'Aux x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.insertIdx_injective`：insertIdx_injective (n : Nat) (x : α) : Functi
on.Injective (fun l : List α => l.insertIdx n x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_permutations'Aux`：∀ {α : Type u_1} (s : List α) (x : α), (Li
st.permutations'Aux x s).length = s.length + 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.get_permutations'Aux`：∀ {α : Type u_1} (s : List α) (x : α) (n : ℕ)
 (hn : n < (List.permutations'Aux x s).length),   (List.permutations'Aux x s).ge
t ⟨n, hn⟩ = s.i…
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem injective_permutations'Aux (x : α) : Function.Injective (permutations'Aux x) := by
  intro s t h
  apply insertIdx_injective s.length x
  dsimp
  have hl : s.length = t.length := by simpa using congr_arg length h
  rw [← get_permutations'Aux s x s.length (by simp),
    ← get_permutations'Aux t x s.length (by simp [hl])]
  simp only [get_eq_getElem, h, hl]
/-
**List.nodup_permutations'Aux_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (s : List α), ∀ x ∉ s, (List.permutations'Aux x s).Nodup
参数：s : List α；List.permutations'Aux x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `List.nodup_map_iff`：nodup_map_iff {f : α -> β} {l : List α} (hf : Inject
ive f) : Nodup (map f l) ↔ Nodup l
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem nodup_permutations'Aux_of_notMem (s : List α) (x : α) (hx : x ∉ s) :
    Nodup (permutations'Aux x s) := by
  induction s with
  | nil => simp
  | cons y s IH =>
    simp only [not_or, mem_cons] at hx
    simp only [permutations'Aux, nodup_cons, mem_map, cons.injEq, exists_eq_right_right, not_and]
    refine ⟨fun _ => Ne.symm hx.left, ?_⟩
    rw [nodup_map_iff]
    · exact IH hx.right
    · simp
/-
**List.nodup_permutations'Aux_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {s : List α} {x : α}, (List.permutations'Aux x s).Nodup ↔
 x ∉ s
参数：List.permutations'Aux x s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ n, l.g
et n = a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.succ_ne_self`：∀ (n : ℕ), n.succ ≠ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_permutations'Aux`：∀ {α : Type u_1} (s : List α) (x : α), (Li
st.permutations'Aux x s).length = s.length + 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.mk.inj_iff`：∀ {n a b : ℕ} {ha : a < n} {hb : b < n}, ⟨a, ha⟩ = ⟨b, h
b⟩ ↔ a = b
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
· 使用定理 `List.get_permutations'Aux`：∀ {α : Type u_1} (s : List α) (x : α) (n : ℕ)
 (hn : n < (List.permutations'Aux x s).length),   (List.permutations'Aux x s).ge
t ⟨n, hn⟩ = s.i…
· 使用定理 `List.length_insertIdx_of_le_length`：∀ {α : Type u} {i : ℕ} {as : List α}
, i ≤ as.length → ∀ (a : α), (as.insertIdx i a).length = as.length + 1
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m
· 使用定理 `List.ext_get`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁.length = l₂.length
 →     (∀ (n : ℕ) (h₁ : n < l₁.length) (h₂ : n < l₂.length), l₁.get ⟨n, h₁⟩ = l₂
.g…
· 使用定理 `List.nodup_permutations'Aux_of_notMem`：∀ {α : Type u_1} (s : List α), ∀ 
x ∉ s, (List.permutations'Aux x s).Nodup
-/
theorem nodup_permutations'Aux_iff {s : List α} {x : α} : Nodup (permutations'Aux x s) ↔ x ∉ s := by
  refine ⟨fun h H ↦ ?_, nodup_permutations'Aux_of_notMem _ _⟩
  obtain ⟨⟨k, hk⟩, hk'⟩ := get_of_mem H
  rw [nodup_iff_injective_get] at h
  apply k.succ_ne_self.symm
  have kl : k < (permutations'Aux x s).length := by simpa [Nat.lt_succ_iff] using hk.le
  have k1l : k + 1 < (permutations'Aux x s).length := by simpa using hk
  rw [← @Fin.mk.inj_iff _ _ _ kl k1l]; apply h
  rw [get_permutations'Aux, get_permutations'Aux]
  have hl : length (s.insertIdx k x) = length (s.insertIdx (k + 1) x) := by
    rw [length_insertIdx_of_le_length hk.le, length_insertIdx_of_le_length (Nat.succ_le_of_lt hk)]
  exact ext_get hl fun n hn hn' => by grind
/-
**List.nodup_permutations** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_permutations (s : List α) (hs : Nodup s) : Nodup s.permutations
参数：s : List α；hs : Nodup s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.permutations'`：permutations'Aux_eq_permutationsAux2 (t : α) (ts : L
ist α) : permutations'Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.permutations_perm_permutations'`：permutations_perm_permutations' (t
s : List α) : ts.permutations ~ ts.permutations'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `List.permutations'.eq_2`：∀ {α : Type u_1} (a : α) (tail : List α),   (a 
:: tail).permutations' = List.flatMap (List.permutations'Aux a) tail.permutation
s'
· 使用定理 `List.nodup_flatMap`：nodup_flatMap {l₁ : List α} {f : α -> List β} : Nodu
p (l₁.flatMap f) ↔ (forall x in l₁, Nodup (f x)) ∧ Pairwise (Disjoint on f) l₁
· 使用定理 `List.nodup_permutations'Aux_iff`：∀ {α : Type u_1} {s : List α} {x : α}, 
(List.permutations'Aux x s).Nodup ↔ x ∉ s
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.mem_permutations'`：mem_permutations' {s t : List α} : s in permutat
ions' t ↔ s ~ t
· 使用定理 `List.Nodup.pairwise_of_forall_ne`：∀ {α : Type u} {l : List α} {r : α → α
 → Prop}, l.Nodup → (∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) → List.Pairwise r l
· 使用定理 `Function.onFun.eq_1`：∀ {α : Sort u₁} {β : Sort u₂} {φ : Sort u₃} (f : β 
→ β → φ) (g : α → β) (x y : α),   Function.onFun f g x y = f (g x) (g y)
· 使用定理 `List.disjoint_iff_ne`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Disjoint l₂ 
↔ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b
· 使用定理 `List.get_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ n, l.g
et n = a
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.length_insertIdx_of_le_length`：∀ {α : Type u} {i : ℕ} {as : List α}
, i ≤ as.length → ∀ (a : α), (as.insertIdx i a).length = as.length + 1
· 使用定理 `List.length_permutations'Aux`：∀ {α : Type u_1} (s : List α) (x : α), (Li
st.permutations'Aux x s).length = s.length + 1
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.get_permutations'Aux`：∀ {α : Type u_1} (s : List α) (x : α) (n : ℕ)
 (hn : n < (List.permutations'Aux x s).length),   (List.permutations'Aux x s).ge
t ⟨n, hn⟩ = s.i…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.getElem_insertIdx_self`：∀ {α : Type u} {l : List α} {x : α} {i : ℕ}
 (hi : i < (l.insertIdx i x).length), (l.insertIdx i x)[i] = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
（共 34 条，此处仅展示前 30 条）
-/
theorem nodup_permutations (s : List α) (hs : Nodup s) : Nodup s.permutations := by
  rw [(permutations_perm_permutations' s).nodup_iff]
  induction hs with
  | nil => simp
  | @cons x l h h' IH =>
    rw [permutations']
    rw [nodup_flatMap]
    constructor
    · intro ys hy
      rw [mem_permutations'] at hy
      rw [nodup_permutations'Aux_iff, hy.mem_iff]
      exact fun H => h x H rfl
    · refine IH.pairwise_of_forall_ne fun as ha bs hb H => ?_
      rw [Function.onFun, disjoint_iff_ne]
      rintro a ha' b hb' rfl
      obtain ⟨⟨n, hn⟩, hn'⟩ := get_of_mem ha'
      obtain ⟨⟨m, hm⟩, hm'⟩ := get_of_mem hb'
      rw [mem_permutations'] at ha hb
      have hl : as.length = bs.length := (ha.trans hb.symm).length_eq
      simp only [Nat.lt_succ_iff, length_permutations'Aux] at hn hm
      rw [get_permutations'Aux] at hn' hm'
      have hx : (as.insertIdx n x)[m]'(by
          rwa [length_insertIdx_of_le_length hn, Nat.lt_succ_iff, hl]) = x := by
        simp [hn', ← hm']
      have hx' : (bs.insertIdx m x)[n]'(by
          rwa [length_insertIdx_of_le_length hm, Nat.lt_succ_iff, ← hl]) = x := by
        simp [hm', ← hn']
      rcases lt_trichotomy n m with (ht | ht | ht)
      · suffices x ∈ bs by exact h x (hb.subset this) rfl
        rw [← hx', getElem_insertIdx_of_lt ht]
        exact getElem_mem _
      · simp only [ht] at hm' hn'
        rw [← hm'] at hn'
        exact H (insertIdx_injective _ _ hn')
      · suffices x ∈ as by exact h x (ha.subset this) rfl
        rw [← hx, getElem_insertIdx_of_lt ht]
        exact getElem_mem _
/-
**List.permutations_take_two** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：permutations_take_two (x y : α) (s : List α) : (x :: y :: s).permutations.
take 2 = [x :: y :: s, y :: x :: s]
参数：x y : α；s : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.permutationsAux_cons`：permutationsAux_cons (t : α) (ts is : List α)
 : permutationsAux (t :: ts) is = foldr (fun y r => (permutationsAux2 t ts r y i
d).2) (permutat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.permutationsAux_nil`：permutationsAux_nil (is : List α) : permutatio
nsAux [] is = []
· 使用定理 `List.permutationsAux2_snd_cons`：permutationsAux2_snd_cons (t : α) (ts : 
List α) (r : List β) (y : α) (ys : List α) (f : List α -> β) : (permutationsAux2
 t ts r (y :: ys) f)…
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma permutations_take_two (x y : α) (s : List α) :
    (x :: y :: s).permutations.take 2 = [x :: y :: s, y :: x :: s] := by
  induction s <;> simp [permutations]

@[simp]
/-
**List.nodup_permutations_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_permutations_iff {s : List α} : Nodup s.permutations ↔ Nodup s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.exists_duplicate_iff_not_nodup`：exists_duplicate_iff_not_nodup : (e
xists x : α, x in+ l) ↔ ¬Nodup l
· 使用定理 `List.Sublist.exists_perm_append`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.S
ublist l₂ → ∃ l, l₂.Perm (l₁ ++ l)
· 使用定理 `List.duplicate_iff_sublist`：duplicate_iff_sublist : x in+ l ↔ [x, x] <+ 
l
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.Perm.permutations`：∀ {α : Type u_1} {s t : List α}, s.Perm t → s.pe
rmutations.Perm t.permutations
· 使用引理 `List.permutations_take_two`：permutations_take_two (x y : α) (s : List α)
 : (x :: y :: s).permutations.take 2 = [x :: y :: s, y :: x :: s]
· 使用定理 `List.take_sublist`：∀ {α : Type u_1} (i : ℕ) (l : List α), (List.take i l
).Sublist l
· 使用定理 `List.nodup_permutations`：nodup_permutations (s : List α) (hs : Nodup s) 
: Nodup s.permutations
-/
theorem nodup_permutations_iff {s : List α} : Nodup s.permutations ↔ Nodup s := by
  refine ⟨?_, nodup_permutations s⟩
  contrapose
  rw [← exists_duplicate_iff_not_nodup]
  intro ⟨x, hs⟩
  rw [duplicate_iff_sublist] at hs
  obtain ⟨l, ht⟩ := List.Sublist.exists_perm_append hs
  rw [List.Perm.nodup_iff (List.Perm.permutations ht), ← exists_duplicate_iff_not_nodup]
  use x :: x :: l
  rw [List.duplicate_iff_sublist, ← permutations_take_two]
  exact take_sublist 2 _

-- TODO: `count s s.permutations = (zipWith count s s.tails).prod`

end List

