/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Rudy Peterson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# Bind operation for multisets

This file defines a few basic operations on `Multiset`, notably the monadic bind.

## Main declarations

* `Multiset.join`: The join, aka union or sum, of multisets.
* `Multiset.bind`: The bind of a multiset-indexed family of multisets.
* `Multiset.product`: Cartesian product of two multisets.
* `Multiset.sigma`: Disjoint sum of multisets in a sigma type.
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

universe v

variable {α : Type*} {β : Type v} {γ δ : Type*}

namespace Multiset

/-! ### Join -/

/-- `join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.
  For example, `join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2}`. -/
/-
**Multiset.join** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：join : Multiset (Multiset α) -> Multiset α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`join S`, where `S` is a multiset of multisets, is the lift of the list join
  operation, that is, the union of all the sets.
  For example, `join {{1, 2}, {1, 2}, {0, 1}} = {0, 1, 1, 1, 2, 2}`.
-/
def join : Multiset (Multiset α) → Multiset α :=
  sum
/-
**Multiset.coe_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (L : List (List α)), (↑(List.map Multiset.ofList L)).join
 = ↑L.flatten
参数：L : List (List α)；↑(List.map Multiset.ofList L)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_join : ∀ L : List (List α), join (L.map ((↑) : List α → Multiset α) :
    Multiset (Multiset α)) = L.flatten
  | [] => rfl
  | l :: L => by
      exact congr_arg (fun s : Multiset α => ↑l + s) (coe_join L)

@[simp]
/-
**Multiset.join_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：join_zero : @join α 0 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem join_zero : @join α 0 = 0 :=
  rfl

@[simp]
/-
**Multiset.join_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：join_cons (s S) : @join α (s ::ₘ S) = s + join S
参数：s S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
-/
theorem join_cons (s S) : @join α (s ::ₘ S) = s + join S :=
  sum_cons _ _

@[simp]
/-
**Multiset.join_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：join_add (S T) : @join α (S + T) = join S + join T
参数：S T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sum_add`：∀ {M : Type u_5} [inst : AddCommMonoid M] (s t : Multi
set M), (s + t).sum = s.sum + t.sum
-/
theorem join_add (S T) : @join α (S + T) = join S + join T :=
  sum_add _ _

@[simp]
/-
**Multiset.singleton_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：singleton_join (a) : join ({a} : Multiset (Multiset α)) = a
参数：a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
-/
theorem singleton_join (a) : join ({a} : Multiset (Multiset α)) = a :=
  sum_singleton _

@[simp]
/-
**Multiset.mem_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_join {a S} : a in @join α S ↔ exists s in S, a in s
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
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Multiset.join_cons`：join_cons (s S) : @join α (s ::ₘ S) = s + join S
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mem_join {a S} : a ∈ @join α S ↔ ∃ s ∈ S, a ∈ s :=
  Multiset.induction_on S (by simp) <| by
    simp +contextual [or_and_right, exists_or]

@[simp]
/-
**Multiset.card_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_join (S) : card (@join α S) = sum (map card S)
参数：S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.join_cons`：join_cons (s S) : @join α (s ::ₘ S) = s + join S
· 使用定理 `Multiset.card_add`：card_add (s t : Multiset α) : card (s + t) = card s +
 card t
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem card_join (S) : card (@join α S) = sum (map card S) :=
  Multiset.induction_on S (by simp) (by simp)

@[simp]
/-
**Multiset.map_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_join (f : α -> β) (S : Multiset (Multiset α)) : map f (join S) = join 
(map (map f) S)
参数：f : α -> β；S : Multiset (Multiset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.join_cons`：join_cons (s S) : @join α (s ::ₘ S) = s + join S
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem map_join (f : α → β) (S : Multiset (Multiset α)) :
    map f (join S) = join (map (map f) S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

@[to_additive (attr := simp)]
/-
**Multiset.prod_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_join [CommMonoid α] {S : Multiset (Multiset α)} : prod (join S) = pro
d (map prod S)
参数：Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.join_cons`：join_cons (s S) : @join α (s ::ₘ S) = s + join S
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
-/
theorem prod_join [CommMonoid α] {S : Multiset (Multiset α)} :
    prod (join S) = prod (map prod S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]
/-
**Multiset.rel_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_join {r : α -> β -> Prop} {s t} (h : Rel (Rel r) s t) : Rel r s.join t
.join
参数：h : Rel (Rel r) s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.join_cons`：join_cons (s S) : @join α (s ::ₘ S) = s + join S
· 使用定理 `Multiset.Rel.add`：∀ {α : Type u_1} {β : Type v} {r : α → β → Prop} {s : 
Multiset α} {t : Multiset β} {u : Multiset α} {v : Multiset β},   Multiset.Rel r
 s t →…
-/
theorem rel_join {r : α → β → Prop} {s t} (h : Rel (Rel r) s t) : Rel r s.join t.join := by
  induction h with
  | zero => simp
  | cons hab hst ih => simpa using hab.add ih
/-
**Multiset.filter_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_join (S : Multiset (Multiset α)) (p : α -> Prop) [DecidablePred p] 
: filter p (join S) = join (map (filter p) S)
参数：S : Multiset (Multiset α)；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p
_1 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Multis
et α),       s =…
· 使用定理 `Multiset.join_cons`：join_cons (s S) : @join α (s ::ₘ S) = s + join S
· 使用定理 `Multiset.filter_add`：filter_add (s t : Multiset α) : filter p (s + t) = 
filter p s + filter p t
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem filter_join (S : Multiset (Multiset α)) (p : α → Prop) [DecidablePred p] :
    filter p (join S) = join (map (filter p) S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]
/-
**Multiset.filterMap_join** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_join (S : Multiset (Multiset α)) (f : α -> Option β) : filterMap
 f (join S) = join (map (filterMap f) S)
参数：S : Multiset (Multiset α)；f : α -> Option β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.join_cons`：join_cons (s S) : @join α (s ::ₘ S) = s + join S
· 使用定理 `Multiset.filterMap_add`：filterMap_add (f : α -> Option β) (s t : Multise
t α) : filterMap f (s + t) = filterMap f s + filterMap f t
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem filterMap_join (S : Multiset (Multiset α)) (f : α → Option β) :
    filterMap f (join S) = join (map (filterMap f) S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

/-! ### Bind -/


section Bind

variable (a : α) (s t : Multiset α) (f g : α → Multiset β)

/-- `s.bind f` is the monad bind operation, defined as `(s.map f).join`. It is the union of `f a` as
`a` ranges over `s`. -/
/-
**Multiset.bind** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：bind (s : Multiset α) (f : α -> Multiset β) : Multiset β
参数：s : Multiset α；f : α -> Multiset β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`s.bind f` is the monad bind operation, defined as `(s.map f).join`. It is the u
nion of `f a` as
`a` ranges over `s`.
-/
def bind (s : Multiset α) (f : α → Multiset β) : Multiset β :=
  (s.map f).join

@[simp]
/-
**Multiset.coe_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_bind (l : List α) (f : α -> List β) : (@bind α β l fun a => f a) = l.f
latMap f
参数：l : List α；f : α -> List β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatMap.eq_1`：∀ {α : Type u} {β : Type v} (b : α → List β) (as : Li
st α), List.flatMap b as = (List.map b as).flatten
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_join`：∀ {α : Type u_1} (L : List (List α)), (↑(List.map Mul
tiset.ofList L)).join = ↑L.flatten
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
-/
theorem coe_bind (l : List α) (f : α → List β) : (@bind α β l fun a => f a) = l.flatMap f := by
  rw [List.flatMap, ← coe_join, List.map_map]
  rfl

@[simp]
/-
**Multiset.zero_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_bind : bind 0 f = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_bind : bind 0 f = 0 :=
  rfl

@[simp]
/-
**Multiset.cons_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.join_cons`：join_cons (s S) : @join α (s ::ₘ S) = s + join S
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_bind : (a ::ₘ s).bind f = f a + s.bind f := by simp [bind]

@[simp]
/-
**Multiset.singleton_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：singleton_bind : bind {a} f = f a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.singleton_join`：singleton_join (a) : join ({a} : Multiset (Mult
iset α)) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_bind : bind {a} f = f a := by simp [bind]

@[simp]
/-
**Multiset.add_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：add_bind : (s + t).bind f = s.bind f + t.bind f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.join_add`：join_add (S T) : @join α (S + T) = join S + join T
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_bind : (s + t).bind f = s.bind f + t.bind f := by simp [bind]

@[simp]
/-
**Multiset.bind_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_zero : s.bind (fun _ => 0 : α -> Multiset β) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_zero : s.bind (fun _ => 0 : α → Multiset β) = 0 := by simp [bind, join, nsmul_zero]

@[simp]
/-
**Multiset.bind_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_add : (s.bind fun a => f a + g a) = s.bind f + s.bind g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sum_map_add`：∀ {ι : Type u_2} {M : Type u_5} [inst : AddCommMon
oid M] {m : Multiset ι} {f g : ι → M},   (Multiset.map (fun i => f i + g i) m).s
um = (Mult…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_add : (s.bind fun a => f a + g a) = s.bind f + s.bind g := by simp [bind, join]

@[simp]
/-
**Multiset.bind_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_cons (f : α -> β) (g : α -> Multiset β) : (s.bind fun a => f a ::ₘ g 
a) = map f s + s.bind g
参数：f : α -> β；g : α -> Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `Multiset.cons_add`：cons_add (a : α) (s t : Multiset α) : a ::ₘ s + t = a
 ::ₘ (s + t)
· 使用定理 `Multiset.add_cons`：add_cons (a : α) (s t : Multiset α) : s + a ::ₘ t = a
 ::ₘ (s + t)
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_cons (f : α → β) (g : α → Multiset β) :
    (s.bind fun a => f a ::ₘ g a) = map f s + s.bind g :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [add_comm, add_left_comm, add_assoc])

@[simp]
/-
**Multiset.bind_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_singleton (f : α -> β) : (s.bind fun x => ({f x} : Multiset β)) = map
 f s
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_bind`：zero_bind : bind 0 f = 0
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_singleton (f : α → β) : (s.bind fun x => ({f x} : Multiset β)) = map f s :=
  Multiset.induction_on s (by rw [zero_bind, map_zero]) (by simp [singleton_add])

@[simp]
/-
**Multiset.mem_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_bind {b s} {f : α -> Multiset β} : b in bind s f ↔ exists a in s, b in
 f a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_bind {b s} {f : α → Multiset β} : b ∈ bind s f ↔ ∃ a ∈ s, b ∈ f a := by
  simp [bind]

@[simp]
/-
**Multiset.card_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_bind : card (s.bind f) = (s.map (card ∘ f)).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_join`：card_join (S) : card (@join α S) = sum (map card S)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_bind : card (s.bind f) = (s.map (card ∘ f)).sum := by simp [bind]

@[congr]
/-
**Multiset.bind_congr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_congr {f g : α -> Multiset β} {m : Multiset α} : (forall a in m, f a 
= g a) -> bind m f = bind m g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_congr {f g : α → Multiset β} {m : Multiset α} :
    (∀ a ∈ m, f a = g a) → bind m f = bind m g := by simp +contextual [bind]
/-
**Multiset.bind_hcongr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_hcongr {β' : Type v} {m : Multiset α} {f : α -> Multiset β} {f' : α -
> Multiset β'} (h : β = β') (hf : forall a in m, f a ≍ f' a) : bind m f ≍ bind m
 f'
参数：h : β = β'；hf : forall a in m, f a ≍ f' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem bind_hcongr {β' : Type v} {m : Multiset α} {f : α → Multiset β} {f' : α → Multiset β'}
    (h : β = β') (hf : ∀ a ∈ m, f a ≍ f' a) : bind m f ≍ bind m f' := by
  subst h
  simp only [heq_eq_eq] at hf
  simp [bind_congr hf]
/-
**Multiset.map_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_bind (m : Multiset α) (n : α -> Multiset β) (f : β -> γ) : map f (bind
 m n) = bind m fun a => map f (n a)
参数：m : Multiset α；n : α -> Multiset β；f : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_join`：map_join (f : α -> β) (S : Multiset (Multiset α)) : m
ap f (join S) = join (map (map f) S)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_bind (m : Multiset α) (n : α → Multiset β) (f : β → γ) :
    map f (bind m n) = bind m fun a => map f (n a) := by simp [bind]
/-
**Multiset.bind_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_map (m : Multiset α) (n : β -> Multiset γ) (f : α -> β) : bind (map f
 m) n = bind m fun a => n (f a)
参数：m : Multiset α；n : β -> Multiset γ；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_map (m : Multiset α) (n : β → Multiset γ) (f : α → β) :
    bind (map f m) n = bind m fun a => n (f a) :=
  Multiset.induction_on m (by simp) (by simp +contextual)
/-
**Multiset.bind_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_assoc {s : Multiset α} {f : α -> Multiset β} {g : β -> Multiset γ} : 
(s.bind f).bind g = s.bind fun a => (f a).bind g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `Multiset.add_bind`：add_bind : (s + t).bind f = s.bind f + t.bind f
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_assoc {s : Multiset α} {f : α → Multiset β} {g : β → Multiset γ} :
    (s.bind f).bind g = s.bind fun a => (f a).bind g :=
  Multiset.induction_on s (by simp) (by simp +contextual)
/-
**Multiset.bind_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_bind (m : Multiset α) (n : Multiset β) {f : α -> β -> Multiset γ} : (
(bind m) fun a => (bind n) fun b => f a b) = (bind n) fun b => (bind m) fun a =>
 f a b
参数：m : Multiset α；n : Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.bind_zero`：bind_zero : s.bind (fun _ => 0 : α -> Multiset β) = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Multiset.bind_add`：bind_add : (s.bind fun a => f a + g a) = s.bind f + s
.bind g
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_bind (m : Multiset α) (n : Multiset β) {f : α → β → Multiset γ} :
    ((bind m) fun a => (bind n) fun b => f a b) = (bind n) fun b => (bind m) fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp +contextual)
/-
**Multiset.bind_map_comm** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_map_comm (m : Multiset α) (n : Multiset β) {f : α -> β -> γ} : ((bind
 m) fun a => n.map fun b => f a b) = (bind n) fun b => m.map fun a => f a b
参数：m : Multiset α；n : Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.bind_zero`：bind_zero : s.bind (fun _ => 0 : α -> Multiset β) = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.bind_cons`：bind_cons (f : α -> β) (g : α -> Multiset β) : (s.bi
nd fun a => f a ::ₘ g a) = map f s + s.bind g
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem bind_map_comm (m : Multiset α) (n : Multiset β) {f : α → β → γ} :
    ((bind m) fun a => n.map fun b => f a b) = (bind n) fun b => m.map fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp +contextual)
/-
**Multiset.filter_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_eq_bind (m : Multiset α) (p : α -> Prop) [DecidablePred p] : filter
 p m = bind m (fun a => if p a then {a} else 0)
参数：m : Multiset α；p : α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_cons`：filter_cons {a : α} (s : Multiset α) : filter p (a
 ::ₘ s) = (if p a then {a} else 0) + filter p s
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
-/
theorem filter_eq_bind (m : Multiset α) (p : α → Prop) [DecidablePred p] :
    filter p m = bind m (fun a => if p a then {a} else 0) := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filter_cons, ih]
/-
**Multiset.bind_filter** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_filter (m : Multiset α) (p : α -> Prop) (f : α -> Multiset β) [Decida
blePred p] : bind (filter p m) f = bind m (fun a => if p a then f a else 0)
参数：m : Multiset α；p : α -> Prop；f : α -> Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.filter_eq_bind`：filter_eq_bind (m : Multiset α) (p : α -> Prop)
 [DecidablePred p] : filter p m = bind m (fun a => if p a then {a} else 0)
· 使用定理 `Multiset.bind_assoc`：bind_assoc {s : Multiset α} {f : α -> Multiset β} {
g : β -> Multiset γ} : (s.bind f).bind g = s.bind fun a => (f a).bind g
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.singleton_bind`：singleton_bind : bind {a} f = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem bind_filter (m : Multiset α) (p : α → Prop) (f : α → Multiset β) [DecidablePred p] :
    bind (filter p m) f = bind m (fun a => if p a then f a else 0) := by
  simp only [filter_eq_bind, bind_assoc]
  apply Multiset.bind_congr; intro a ham
  split_ifs <;> simp
/-
**Multiset.filter_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filter_bind (m : Multiset α) (f : α -> Multiset β) (p : β -> Prop) [Decida
blePred p] : filter p (bind m f) = bind m (fun a => filter p (f a))
参数：m : Multiset α；f : α -> Multiset β；p : β -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filter_join`：filter_join (S : Multiset (Multiset α)) (p : α -> 
Prop) [DecidablePred p] : filter p (join S) = join (map (filter p) S)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filter_bind (m : Multiset α) (f : α → Multiset β) (p : β → Prop) [DecidablePred p] :
    filter p (bind m f) = bind m (fun a => filter p (f a)) := by
  simp [bind, filter_join]
/-
**Multiset.filterMap_eq_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_eq_bind (m : Multiset α) (f : α -> Option β) : filterMap f m = b
ind m (fun a => ((f a).map singleton).getD 0)
参数：m : Multiset α；f : α -> Option β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filterMap_cons`：filterMap_cons (f : α -> Option β) (a : α) (s :
 Multiset α) : filterMap f (a ::ₘ s) = ((f a).map singleton).getD 0 + filterMap 
f s
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
-/
theorem filterMap_eq_bind (m : Multiset α) (f : α → Option β) :
    filterMap f m = bind m (fun a => ((f a).map singleton).getD 0) := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filterMap_cons, ih]
/-
**Multiset.bind_filterMap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_filterMap (m : Multiset α) (f : α -> Option β) (g : β -> Multiset γ) 
: bind (filterMap f m) g = bind m (fun a => ((f a).map g).getD 0)
参数：m : Multiset α；f : α -> Option β；g : β -> Multiset γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.filterMap_eq_bind`：filterMap_eq_bind (m : Multiset α) (f : α ->
 Option β) : filterMap f m = bind m (fun a => ((f a).map singleton).getD 0)
· 使用定理 `Multiset.bind_assoc`：bind_assoc {s : Multiset α} {f : α -> Multiset β} {
g : β -> Multiset γ} : (s.bind f).bind g = s.bind fun a => (f a).bind g
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.singleton_bind`：singleton_bind : bind {a} f = f a
-/
theorem bind_filterMap (m : Multiset α) (f : α → Option β) (g : β → Multiset γ) :
    bind (filterMap f m) g = bind m (fun a => ((f a).map g).getD 0) := by
  simp only [filterMap_eq_bind, Multiset.bind_assoc]
  apply Multiset.bind_congr; intro a ham
  cases f a with
  | none => simp
  | some b => simp
/-
**Multiset.filterMap_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：filterMap_bind (m : Multiset α) (f : α -> Multiset β) (g : β -> Option γ) 
: filterMap g (bind m f) = bind m (fun a => filterMap g (f a))
参数：m : Multiset α；f : α -> Multiset β；g : β -> Option γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.filterMap_join`：filterMap_join (S : Multiset (Multiset α)) (f :
 α -> Option β) : filterMap f (join S) = join (map (filterMap f) S)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem filterMap_bind (m : Multiset α) (f : α → Multiset β) (g : β → Option γ) :
    filterMap g (bind m f) = bind m (fun a => filterMap g (f a)) := by
  simp [bind, filterMap_join]

@[to_additive (attr := simp)]
/-
**Multiset.prod_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：prod_bind [CommMonoid β] (s : Multiset α) (t : α -> Multiset β) : (s.bind 
t).prod = (s.map fun a => (t a).prod).prod
参数：s : Multiset α；t : α -> Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_join`：prod_join [CommMonoid α] {S : Multiset (Multiset α)}
 : prod (join S) = prod (map prod S)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_bind [CommMonoid β] (s : Multiset α) (t : α → Multiset β) :
    (s.bind t).prod = (s.map fun a => (t a).prod).prod := by simp [bind]

open scoped Relator in
/-
**Multiset.rel_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_bind {r : α -> β -> Prop} {p : γ -> δ -> Prop} {s t} {f : α -> Multise
t γ} {g : β -> Multiset δ} (h : (r ⇒ Rel p) f g) (hst : Rel r s t) : Rel p (s.bi
nd f) (t.bind g)
参数：h : (r ⇒ Rel p) f g；hst : Rel r s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.rel_join`：rel_join {r : α -> β -> Prop} {s t} (h : Rel (Rel r) 
s t) : Rel r s.join t.join
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.rel_map`：rel_map {s : Multiset α} {t : Multiset β} {f : α -> γ}
 {g : β -> δ} : Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t
· 使用定理 `Multiset.Rel.mono`：∀ {α : Type u_1} {β : Type v} {r p : α → β → Prop} {s
 : Multiset α} {t : Multiset β},   Multiset.Rel r s t → (∀ a ∈ s, ∀ b ∈ t, r a b
 → p a …
-/
theorem rel_bind {r : α → β → Prop} {p : γ → δ → Prop} {s t} {f : α → Multiset γ}
    {g : β → Multiset δ} (h : (r ⇒ Rel p) f g) (hst : Rel r s t) :
    Rel p (s.bind f) (t.bind g) := by
  apply rel_join
  rw [rel_map]
  exact hst.mono fun a _ b _ hr => h hr
/-
**Multiset.count_sum** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_sum [DecidableEq α] {m : Multiset β} {f : β -> Multiset α} {a : α} :
 count a (map f m).sum = sum (m.map fun b => count a <| f b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem count_sum [DecidableEq α] {m : Multiset β} {f : β → Multiset α} {a : α} :
    count a (map f m).sum = sum (m.map fun b => count a <| f b) :=
  Multiset.induction_on m (by simp) (by simp)
/-
**Multiset.count_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：count_bind [DecidableEq α] {m : Multiset β} {f : β -> Multiset α} {a : α} 
: count a (bind m f) = sum (m.map fun b => count a <| f b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.count_sum`：count_sum [DecidableEq α] {m : Multiset β} {f : β ->
 Multiset α} {a : α} : count a (map f m).sum = sum (m.map fun b => count a <| f 
b)
-/
theorem count_bind [DecidableEq α] {m : Multiset β} {f : β → Multiset α} {a : α} :
    count a (bind m f) = sum (m.map fun b => count a <| f b) :=
  count_sum
/-
**Multiset.le_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_bind {α β : Type*} {f : α -> Multiset β} (S : Multiset α) {x : α} (hx :
 x in S) : f x <= S.bind f
参数：S : Multiset α；hx : x in S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `Multiset.mem_map_of_mem`：mem_map_of_mem (f : α -> β) {a : α} {s : Multis
et α} (h : a in s) : f a in map f s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_bind`：count_bind [DecidableEq α] {m : Multiset β} {f : β 
-> Multiset α} {a : α} : count a (bind m f) = sum (m.map fun b => count a <| f b
)
· 使用定理 `Multiset.sum_cons`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M) (s 
: Multiset M), (a ::ₘ s).sum = a + s.sum
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem le_bind {α β : Type*} {f : α → Multiset β} (S : Multiset α) {x : α} (hx : x ∈ S) :
    f x ≤ S.bind f := by
  classical
  refine le_iff_count.2 fun a ↦ ?_
  obtain ⟨m', hm'⟩ := exists_cons_of_mem <| mem_map_of_mem (fun b ↦ count a (f b)) hx
  rw [count_bind, hm', sum_cons]
  exact Nat.le_add_right _ _

@[simp]
/-
**Multiset.attach_bind_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：attach_bind_coe (s : Multiset α) (f : α -> Multiset β) : (s.attach.bind fu
n i => f i) = s.bind f
参数：s : Multiset α；f : α -> Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.attach_map_val'`：attach_map_val' (s : Multiset α) (f : α -> β) 
: (s.attach.map fun i => f i.val) = s.map f
-/
theorem attach_bind_coe (s : Multiset α) (f : α → Multiset β) :
    (s.attach.bind fun i => f i) = s.bind f :=
  congr_arg join <| attach_map_val' _ _

variable {f s t}

open scoped Function in -- required for scoped `on` notation
/-
**Multiset.nodup_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {f : α → Multiset β},   (s.
bind f).Nodup ↔ (∀ a ∈ s, (f a).Nodup) ∧ Multiset.Pairwise (Function.onFun Disjo
int f) s
参数：s.bind f；∀ a ∈ s, (f a).Nodup；Function.onFun Disjoint f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.Disjoint.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Disjoint l₂ → 
l₂.Disjoint l₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_bind`：coe_bind (l : List α) (f : α -> List β) : (@bind α β 
l fun a => f a) = l.flatMap f
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
@[simp] lemma nodup_bind :
    Nodup (bind s f) ↔ (∀ a ∈ s, Nodup (f a)) ∧ s.Pairwise (Disjoint on f) := by
  have : ∀ a, ∃ l : List β, f a = l := fun a => Quot.induction_on (f a) fun l => ⟨l, rfl⟩
  choose f' h' using this
  have : f = fun a ↦ ofList (f' a) := funext h'
  have _ : Std.Symm fun a b : List β ↦ List.Disjoint a b := { symm a b h := h.symm }
  exact Quot.induction_on s <| by
    unfold Function.onFun
    simp [this, List.nodup_flatMap, pairwise_coe_iff_pairwise]

@[simp]
/-
**Multiset.dedup_bind_dedup** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：dedup_bind_dedup [DecidableEq α] [DecidableEq β] (s : Multiset α) (f : α -
> Multiset β) : (s.dedup.bind f).dedup = (s.bind f).dedup
参数：s : Multiset α；f : α -> Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_dedup`：count_dedup (m : Multiset α) (a : α) : m.dedup.cou
nt a = if a in m then 1 else 0
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma dedup_bind_dedup [DecidableEq α] [DecidableEq β] (s : Multiset α) (f : α → Multiset β) :
    (s.dedup.bind f).dedup = (s.bind f).dedup := by
  ext x
  -- Porting note: was `simp_rw [count_dedup, mem_bind, mem_dedup]`
  simp_rw [count_dedup]
  congr 1
  simp

variable (op : α → α → α) [hc : Std.Commutative op] [ha : Std.Associative op]
/-
**Multiset.fold_bind** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fold_bind {ι : Type*} (s : Multiset ι) (t : ι -> Multiset α) (b : ι -> α) 
(b₀ : α) : (s.bind t).fold op ((s.map b).fold op b₀) = (s.map fun i => (t i).fol
d op (b i)).fold op b₀
参数：s : Multiset ι；t : ι -> Multiset α；b : ι -> α；b₀ : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.zero_bind`：zero_bind : bind 0 f = 0
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
· 使用定理 `Multiset.fold_zero`：fold_zero (b : α) : (0 : Multiset α).fold op b = b
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.fold_cons_left`：fold_cons_left : forall (b a : α) (s : Multiset
 α), (a ::ₘ s).fold op b = a * s.fold op b
· 使用定理 `Multiset.fold_add`：fold_add (b₁ b₂ : α) (s₁ s₂ : Multiset α) : (s₁ + s₂)
.fold op (b₁ * b₂) = s₁.fold op b₁ * s₂.fold op b₂
-/
theorem fold_bind {ι : Type*} (s : Multiset ι) (t : ι → Multiset α) (b : ι → α) (b₀ : α) :
    (s.bind t).fold op ((s.map b).fold op b₀) =
    (s.map fun i => (t i).fold op (b i)).fold op b₀ := by
  induction s using Multiset.induction_on with
  | empty => rw [zero_bind, map_zero, map_zero, fold_zero]
  | cons a ha ih => rw [cons_bind, map_cons, map_cons, fold_cons_left, fold_cons_left, fold_add, ih]

end Bind

/-! ### Product of two multisets -/


section Product

variable (a : α) (b : β) (s : Multiset α) (t : Multiset β)

/-- The multiplicity of `(a, b)` in `s ×ˢ t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`. -/
/-
**Multiset.product** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：product (s : Multiset α) (t : Multiset β) : Multiset (α × β)
参数：s : Multiset α；t : Multiset β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The multiplicity of `(a, b)` in `s ×ˢ t` is
  the product of the multiplicity of `a` in `s` and `b` in `t`.
-/
def product (s : Multiset α) (t : Multiset β) : Multiset (α × β) :=
  s.bind fun a => t.map <| Prod.mk a
/-
**Multiset.instSProd** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instSProd : SProd (Multiset α) (Multiset β) (Multiset (α × β)) where sprod
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSProd : SProd (Multiset α) (Multiset β) (Multiset (α × β)) where
  sprod := Multiset.product

@[simp]
/-
**Multiset.coe_product** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_product (l₁ : List α) (l₂ : List β) : (l₁ : Multiset α) ×ˢ (l₂ : Multi
set β) = (l₁ ×ˢ l₂)
参数：l₁ : List α；l₂ : List β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.product.eq_1`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (t
 : Multiset β),   s.product t = s.bind fun a => Multiset.map (Prod.mk a) t
· 使用定理 `List.product.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l₁ : List α) (l₂ : L
ist β),   l₁.product l₂ = List.flatMap (fun a => List.map (Prod.mk a) l₂) l₁
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_bind`：coe_bind (l : List α) (f : α -> List β) : (@bind α β 
l fun a => f a) = l.flatMap f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_product (l₁ : List α) (l₂ : List β) :
    (l₁ : Multiset α) ×ˢ (l₂ : Multiset β) = (l₁ ×ˢ l₂) := by
  dsimp only [SProd.sprod]
  rw [product, List.product, ← coe_bind]
  simp

@[simp]
/-
**Multiset.zero_product** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_product : (0 : Multiset α) ×ˢ t = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_product : (0 : Multiset α) ×ˢ t = 0 :=
  rfl

@[simp]
/-
**Multiset.cons_product** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t + s ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t + s ×ˢ t := by simp [SProd.sprod, product]

@[simp]
/-
**Multiset.product_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：product_zero : s ×ˢ (0 : Multiset β) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.bind_zero`：bind_zero : s.bind (fun _ => 0 : α -> Multiset β) = 
0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem product_zero : s ×ˢ (0 : Multiset β) = 0 := by simp [SProd.sprod, product]

@[simp]
/-
**Multiset.product_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：product_cons : s ×ˢ (b ::ₘ t) = (s.map fun a => (a, b)) + s ×ˢ t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.bind_congr`：bind_congr {f g : α -> Multiset β} {m : Multiset α}
 : (forall a in m, f a = g a) -> bind m f = bind m g
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.bind_cons`：bind_cons (f : α -> β) (g : α -> Multiset β) : (s.bi
nd fun a => f a ::ₘ g a) = map f s + s.bind g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem product_cons : s ×ˢ (b ::ₘ t) = (s.map fun a => (a, b)) + s ×ˢ t := by
  simp [SProd.sprod, product]

@[simp]
/-
**Multiset.product_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：product_singleton : ({a} : Multiset α) ×ˢ ({b} : Multiset β) = {(a, b)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.bind_singleton`：bind_singleton (f : α -> β) : (s.bind fun x => 
({f x} : Multiset β)) = map f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem product_singleton : ({a} : Multiset α) ×ˢ ({b} : Multiset β) = {(a, b)} := by
  simp only [SProd.sprod, product, bind_singleton, map_singleton]

@[simp]
/-
**Multiset.add_product** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：add_product (s t : Multiset α) (u : Multiset β) : (s + t) ×ˢ u = s ×ˢ u + 
t ×ˢ u
参数：s t : Multiset α；u : Multiset β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_bind`：add_bind : (s + t).bind f = s.bind f + t.bind f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_product (s t : Multiset α) (u : Multiset β) : (s + t) ×ˢ u = s ×ˢ u + t ×ˢ u := by
  simp [SProd.sprod, product]

@[simp]
/-
**Multiset.product_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：product_add (s : Multiset α) : forall t u : Multiset β, s ×ˢ (t + u) = s ×
ˢ t + s ×ˢ u
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.cons_product`：cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t
 + s ×ˢ t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem product_add (s : Multiset α) : ∀ t u : Multiset β, s ×ˢ (t + u) = s ×ˢ t + s ×ˢ u :=
  Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_product, IH]
    simp [add_left_comm, add_assoc]

@[simp]
/-
**Multiset.card_product** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_product : card (s ×ˢ t) = card s * card t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_bind`：card_bind : card (s.bind f) = (s.map (card ∘ f)).sum
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_product : card (s ×ˢ t) = card s * card t := by simp [SProd.sprod, product]

variable {s t}
/-
**Multiset.mem_product** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {t : Multiset β} {p : α × β
}, p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_product : ∀ {p : α × β}, p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t
  | (a, b) => by simp [SProd.sprod, product, and_left_comm]
/-
**Multiset.Nodup.product** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {t : Multiset β}, s.Nodup →
 t.Nodup → (s ×ˢ t).Nodup
参数：s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.coe_product`：coe_product (l₁ : List α) (l₂ : List β) : (l₁ : Mu
ltiset α) ×ˢ (l₂ : Multiset β) = (l₁ ×ˢ l₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `List.Nodup.product`：∀ {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List
 β}, l₁.Nodup → l₂.Nodup → (l₁ ×ˢ l₂).Nodup
-/
protected theorem Nodup.product : Nodup s → Nodup t → Nodup (s ×ˢ t) :=
  Quotient.inductionOn₂ s t fun l₁ l₂ d₁ d₂ => by simp [List.Nodup.product d₁ d₂]

set_option backward.isDefEq.respectTransparency false in
/-
**Multiset.map_swap_product** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (t : Multiset β), Multiset.
map Prod.swap (s ×ˢ t) = t ×ˢ s
参数：s : Multiset α；t : Multiset β；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.product_zero`：product_zero : s ×ˢ (0 : Multiset β) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.cons_product`：cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t
 + s ×ˢ t
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.product_cons`：product_cons : s ×ˢ (b ::ₘ t) = (s.map fun a => (
a, b)) + s ×ˢ t
-/
@[simp] lemma map_swap_product (s : Multiset α) (t : Multiset β) :
    (s ×ˢ t).map Prod.swap = t ×ˢ s := by
  induction s using Multiset.induction <;> simp_all
/-
**Multiset.prod_map_product_eq_prod_prod** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：prod_map_product_eq_prod_prod {M : Type*} [CommMonoid M] (s : Multiset α) 
(t : Multiset β) (f : α × β -> M) : ((s ×ˢ t).map f).prod = (s.map fun i => (t.m
ap fun j => f (i, j)).prod).prod
参数：s : Multiset α；t : Multiset β；f : α × β -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.cons_product`：cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t
 + s ×ˢ t
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.prod_add`：prod_add (s t : Multiset M) : prod (s + t) = prod s *
 prod t
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
-/
lemma prod_map_product_eq_prod_prod {M : Type*} [CommMonoid M]
    (s : Multiset α) (t : Multiset β) (f : α × β → M) :
    ((s ×ˢ t).map f).prod = (s.map fun i ↦ (t.map fun j ↦ f (i, j)).prod).prod := by
  induction s using Multiset.induction <;> simp_all

end Product

/-! ### Disjoint sum of multisets -/


section Sigma

variable {σ : α → Type*} (a : α) (s : Multiset α) (t : ∀ a, Multiset (σ a))

/-- `Multiset.sigma s t` is the dependent version of `Multiset.product`. It is the sum of
  `(a, b)` as `a` ranges over `s` and `b` ranges over `t a`. -/
/-
**Multiset.sigma** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：{α : Type u_1} → {σ : α → Type u_4} → Multiset α → ((a : α) → Multiset (σ 
a)) → Multiset ((a : α) × σ a)
参数：(a : α) → Multiset (σ a)；(a : α) × σ a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Multiset.sigma s t` is the dependent version of `Multiset.product`. It is the s
um of
  `(a, b)` as `a` ranges over `s` and `b` ranges over `t a`.
-/
protected def sigma (s : Multiset α) (t : ∀ a, Multiset (σ a)) : Multiset (Σ a, σ a) :=
  s.bind fun a => (t a).map <| Sigma.mk a

@[simp]
/-
**Multiset.coe_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_sigma (l₁ : List α) (l₂ : forall a, List (σ a)) : (@Multiset.sigma α σ
 l₁ fun a => l₂ a) = l₁.sigma l₂
参数：l₁ : List α；l₂ : forall a, List (σ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.sigma.eq_1`：∀ {α : Type u_1} {σ : α → Type u_4} (s : Multiset α
) (t : (a : α) → Multiset (σ a)),   s.sigma t = s.bind fun a => Multiset.map (Si
gma.mk a)…
· 使用定理 `List.sigma.eq_1`：∀ {α : Type u_1} {σ : α → Type u_2} (l₁ : List α) (l₂ :
 (a : α) → List (σ a)),   l₁.sigma l₂ = List.flatMap (fun a => List.map (Sigma.m
k a) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_bind`：coe_bind (l : List α) (f : α -> List β) : (@bind α β 
l fun a => f a) = l.flatMap f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_sigma (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (@Multiset.sigma α σ l₁ fun a => l₂ a) = l₁.sigma l₂ := by
  rw [Multiset.sigma, List.sigma, ← coe_bind]
  simp

@[simp]
/-
**Multiset.zero_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_sigma : @Multiset.sigma α σ 0 t = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_sigma : @Multiset.sigma α σ 0 t = 0 :=
  rfl

@[simp]
/-
**Multiset.cons_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：cons_sigma : (a ::ₘ s).sigma t = (t a).map (Sigma.mk a) + s.sigma t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.cons_bind`：cons_bind : (a ::ₘ s).bind f = f a + s.bind f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_sigma : (a ::ₘ s).sigma t = (t a).map (Sigma.mk a) + s.sigma t := by
  simp [Multiset.sigma]

@[simp]
/-
**Multiset.sigma_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sigma_singleton (b : α -> β) : (({a} : Multiset α).sigma fun a => ({b a} :
 Multiset β)) = {⟨a, b a⟩}
参数：b : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sigma_singleton (b : α → β) :
    (({a} : Multiset α).sigma fun a => ({b a} : Multiset β)) = {⟨a, b a⟩} :=
  rfl

@[simp]
/-
**Multiset.add_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：add_sigma (s t : Multiset α) (u : forall a, Multiset (σ a)) : (s + t).sigm
a u = s.sigma u + t.sigma u
参数：s t : Multiset α；u : forall a, Multiset (σ a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.add_bind`：add_bind : (s + t).bind f = s.bind f + t.bind f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_sigma (s t : Multiset α) (u : ∀ a, Multiset (σ a)) :
    (s + t).sigma u = s.sigma u + t.sigma u := by simp [Multiset.sigma]

@[simp]
/-
**Multiset.sigma_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：sigma_add : forall t u : forall a, Multiset (σ a), (s.sigma fun a => t a +
 u a) = s.sigma t + s.sigma u
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.cons_sigma`：cons_sigma : (a ::ₘ s).sigma t = (t a).map (Sigma.m
k a) + s.sigma t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sigma_add :
    ∀ t u : ∀ a, Multiset (σ a), (s.sigma fun a => t a + u a) = s.sigma t + s.sigma u :=
  Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_sigma, IH]
    simp [add_comm, add_left_comm, add_assoc]

@[simp]
/-
**Multiset.card_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_sigma : card (s.sigma t) = sum (map (fun a => card (t a)) s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_bind`：card_bind : card (s.bind f) = (s.map (card ∘ f)).sum
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem card_sigma : card (s.sigma t) = sum (map (fun a => card (t a)) s) := by
  simp [Multiset.sigma, (· ∘ ·)]

variable {s t}
/-
**Multiset.mem_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {σ : α → Type u_4} {s : Multiset α} {t : (a : α) → Multis
et (σ a)} {p : (a : α) × σ a},   p ∈ s.sigma t ↔ p.fst ∈ s ∧ p.snd ∈ t p.fst
参数：a : α；σ a；a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_sigma : ∀ {p : Σ a, σ a}, p ∈ @Multiset.sigma α σ s t ↔ p.1 ∈ s ∧ p.2 ∈ t p.1
  | ⟨a, b⟩ => by simp [Multiset.sigma, and_left_comm]
/-
**Multiset.Nodup.sigma** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {s : Multiset α} {σ : α → Type u_5} {t : (a : α) → Multis
et (σ a)},   s.Nodup → (∀ (a : α), (t a).Nodup) → (s.sigma t).Nodup
参数：a : α；σ a；∀ (a : α), (t a).Nodup；s.sigma t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.coe_sigma`：coe_sigma (l₁ : List α) (l₂ : forall a, List (σ a)) 
: (@Multiset.sigma α σ l₁ fun a => l₂ a) = l₁.sigma l₂
· 使用定理 `List.Nodup.sigma`：∀ {α : Type u} {l₁ : List α} {σ : α → Type u_1} {l₂ : 
(a : α) → List (σ a)},   l₁.Nodup → (∀ (a : α), (l₂ a).Nodup) → (l₁.sigma l₂).No
dup
· 使用定理 `Quotient.exists_rep`：∀ {α : Sort u} {s : Setoid α} (q : Quotient s), ∃ a
, ⟦a⟧ = q
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
protected theorem Nodup.sigma {σ : α → Type*} {t : ∀ a, Multiset (σ a)} :
    Nodup s → (∀ a, Nodup (t a)) → Nodup (s.sigma t) :=
  Quot.induction_on s fun l₁ => by
    choose f hf using fun a => Quotient.exists_rep (t a)
    simpa [← funext hf] using List.Nodup.sigma

end Sigma

end Multiset

