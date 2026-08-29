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

/--
Definition of `join` / `join` 的定义

English:
definition join
  signature: : Multiset (Multiset α) -> Multiset α
  body: sum

中文:
定义 join
  签名: : Multiset (Multiset α) -> Multiset α
  定义体: sum
-/
def join : Multiset (Multiset α) -> Multiset α :=
  sum

/--
theorem `coe_join` / 定理 `coe_join`

English:
theorem coe_join
  statement: forall L : List (List α), join (L.map ((↑) : List α -> Multiset α) :

中文:
定理 coe_join
  结论: 对任意 L : 列表 (列表 α), join (L.map ((↑) : 列表 α -> Multiset α) :
-/
theorem coe_join : forall L : List (List α), join (L.map ((↑) : List α -> Multiset α) :
    Multiset (Multiset α)) = L.flatten
  | [] => rfl
  | l :: L => by
      exact congr_arg (fun s : Multiset α => ↑l + s) (coe_join L)

@[simp]
/--
theorem `join_zero` / 定理 `join_zero`

English:
theorem join_zero
  statement: @join α 0 = 0
  proof: rfl

@[simp]

中文:
定理 join_zero
  结论: @join α 0 = 0
  证明: rfl

@[simp]
-/
theorem join_zero : @join α 0 = 0 :=
  rfl

@[simp]
/--
theorem `join_cons` / 定理 `join_cons`

English:
theorem join_cons
  given: (s S)
  statement: @join α (s ::ₘ S) = s + join S
  proof: sum_cons _ _

@[simp]

中文:
定理 join_cons
  条件: (s S)
  结论: @join α (s ::ₘ S) = s + join S
  证明: sum_cons _ _

@[simp]

Depends on / 依赖: sum_cons
-/
theorem join_cons (s S) : @join α (s ::ₘ S) = s + join S :=
  sum_cons _ _

@[simp]
/--
theorem `join_add` / 定理 `join_add`

English:
theorem join_add
  given: (S T)
  statement: @join α (S + T) = join S + join T
  proof: sum_add _ _

@[simp]

中文:
定理 join_add
  条件: (S T)
  结论: @join α (S + T) = join S + join T
  证明: sum_add _ _

@[simp]

Depends on / 依赖: sum_add
-/
theorem join_add (S T) : @join α (S + T) = join S + join T :=
  sum_add _ _

@[simp]
/--
theorem `singleton_join` / 定理 `singleton_join`

English:
theorem singleton_join
  given: (a)
  statement: join ({a} : Multiset (Multiset α)) = a
  proof: sum_singleton _

@[simp]

中文:
定理 singleton_join
  条件: (a)
  结论: join ({a} : Multiset (Multiset α)) = a
  证明: sum_singleton _

@[simp]

Depends on / 依赖: sum_singleton
-/
theorem singleton_join (a) : join ({a} : Multiset (Multiset α)) = a :=
  sum_singleton _

@[simp]
/--
theorem `mem_join` / 定理 `mem_join`

English:
theorem mem_join
  given: {a S}
  statement: a in @join α S ↔ exists s in S, a in s
  proof: Multiset.induction_on S (by simp) by
    simp +contextual [or_and_right, exists_or]

@[simp]

中文:
定理 mem_join
  条件: {a S}
  结论: a in @join α S ↔ 存在 s in S, a in s
  证明: Multiset.induction_on S (by simp) by
    simp +contextual [or_and_right, exists_or]

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, exists_or, induction_on, or_and_right
-/
theorem mem_join {a S} : a in @join α S ↔ exists s in S, a in s :=
Multiset.induction_on S (by simp) by
    simp +contextual [or_and_right, exists_or]

@[simp]
/--
theorem `card_join` / 定理 `card_join`

English:
theorem card_join
  given: (S)
  statement: card (@join α S) = sum (map card S)
  proof: Multiset.induction_on S (by simp) (by simp)

@[simp]

中文:
定理 card_join
  条件: (S)
  结论: card (@join α S) = 求和 (map card S)
  证明: Multiset.induction_on S (by simp) (by simp)

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem card_join (S) : card (@join α S) = sum (map card S) :=
  Multiset.induction_on S (by simp) (by simp)

@[simp]
/--
theorem `map_join` / 定理 `map_join`

English:
theorem map_join
  given: (f : α -> β) (S : Multiset (Multiset α))
  proof: by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

@[to_additive (attr := simp)]

中文:
定理 map_join
  条件: (f : α -> β) (S : Multiset (Multiset α))
  证明: by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

@[to_additive (attr := simp)]

Depends on / 依赖: Multiset, Multiset.induction
-/
theorem map_join (f : α -> β) (S : Multiset (Multiset α)) :
    map f (join S) = join (map (map f) S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

@[to_additive (attr := simp)]
/--
theorem `prod_join` / 定理 `prod_join`

English:
theorem prod_join
  given: [CommMonoid α] {S : Multiset (Multiset α)}
  proof: by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

中文:
定理 prod_join
  条件: [交换幺半群 α] {S : Multiset (Multiset α)}
  证明: by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

Depends on / 依赖: Multiset, Multiset.induction
-/
theorem prod_join [CommMonoid α] {S : Multiset (Multiset α)} :
    prod (join S) = prod (map prod S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

/--
theorem `rel_join` / 定理 `rel_join`

English:
theorem rel_join
  given: {r : α -> β -> Prop} {s t} (h : Rel (Rel r) s t)
  statement: Rel r s.join t.join
  proof: by
  induction h with
  | zero => simp
  | cons hab hst ih => simpa using hab.add ih

中文:
定理 rel_join
  条件: {r : α -> β -> 命题} {s t} (h : 关系 (关系 r) s t)
  结论: 关系 r s.join t.join
  证明: by
  induction h with
  | zero => simp
  | cons hab hst ih => simpa using hab.add ih

Depends on / 依赖: hab.add
-/
theorem rel_join {r : α -> β -> Prop} {s t} (h : Rel (Rel r) s t) : Rel r s.join t.join := by
  induction h with
  | zero => simp
  | cons hab hst ih => simpa using hab.add ih

/--
theorem `filter_join` / 定理 `filter_join`

English:
theorem filter_join
  given: (S : Multiset (Multiset α)) (p : α -> Prop) [DecidablePred p]
  proof: by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

中文:
定理 filter_join
  条件: (S : Multiset (Multiset α)) (p : α -> 命题) [DecidablePred p]
  证明: by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

Depends on / 依赖: Multiset, Multiset.induction
-/
theorem filter_join (S : Multiset (Multiset α)) (p : α -> Prop) [DecidablePred p] :
    filter p (join S) = join (map (filter p) S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

/--
theorem `filterMap_join` / 定理 `filterMap_join`

English:
theorem filterMap_join
  given: (S : Multiset (Multiset α)) (f : α -> Option β)
  proof: by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

中文:
定理 filterMap_join
  条件: (S : Multiset (Multiset α)) (f : α -> 选项类型 β)
  证明: by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

Depends on / 依赖: Multiset, Multiset.induction
-/
theorem filterMap_join (S : Multiset (Multiset α)) (f : α -> Option β) :
    filterMap f (join S) = join (map (filterMap f) S) := by
  induction S using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

/-! ### Bind -/


section Bind

variable (a : α) (s t : Multiset α) (f g : α -> Multiset β)

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (s : Multiset α) (f : α -> Multiset β)
  body: (s.map f).join

@[simp]

中文:
定义 bind
  签名: (s : Multiset α) (f : α -> Multiset β)
  定义体: (s.map f).join

@[simp]

Depends on / 依赖: s.map
-/
def bind (s : Multiset α) (f : α -> Multiset β) : Multiset β :=
  (s.map f).join

@[simp]
/--
theorem `coe_bind` / 定理 `coe_bind`

English:
theorem coe_bind
  given: (l : List α) (f : α -> List β)
  statement: (@bind α β l fun a => f a) = l.flatMap f
  proof: by
  rw [List.flatMap]; rw [← coe_join]; rw [List.map_map]
  rfl

@[simp]

中文:
定理 coe_bind
  条件: (l : 列表 α) (f : α -> 列表 β)
  结论: (@bind α β l fun a => f a) = l.flatMap f
  证明: by
  rw [List.flatMap]; rw [← coe_join]; rw [List.map_map]
  rfl

@[simp]

Depends on / 依赖: List.flatMap, List.map_map, coe_join, flatMap, map_map
-/
theorem coe_bind (l : List α) (f : α -> List β) : (@bind α β l fun a => f a) = l.flatMap f := by
  rw [List.flatMap]; rw [← coe_join]; rw [List.map_map]
  rfl

@[simp]
/--
theorem `zero_bind` / 定理 `zero_bind`

English:
theorem zero_bind
  statement: bind 0 f = 0
  proof: rfl

@[simp]

中文:
定理 zero_bind
  结论: bind 0 f = 0
  证明: rfl

@[simp]
-/
theorem zero_bind : bind 0 f = 0 :=
  rfl

@[simp]
/--
theorem `cons_bind` / 定理 `cons_bind`

English:
theorem cons_bind
  statement: (a ::ₘ s).bind f = f a + s.bind f
  proof: by simp [bind]

@[simp]

中文:
定理 cons_bind
  结论: (a ::ₘ s).bind f = f a + s.bind f
  证明: by simp [bind]

@[simp]
-/
theorem cons_bind : (a ::ₘ s).bind f = f a + s.bind f := by simp [bind]

@[simp]
/--
theorem `singleton_bind` / 定理 `singleton_bind`

English:
theorem singleton_bind
  statement: bind {a} f = f a
  proof: by simp [bind]

@[simp]

中文:
定理 singleton_bind
  结论: bind {a} f = f a
  证明: by simp [bind]

@[simp]
-/
theorem singleton_bind : bind {a} f = f a := by simp [bind]

@[simp]
/--
theorem `add_bind` / 定理 `add_bind`

English:
theorem add_bind
  statement: (s + t).bind f = s.bind f + t.bind f
  proof: by simp [bind]

@[simp]

中文:
定理 add_bind
  结论: (s + t).bind f = s.bind f + t.bind f
  证明: by simp [bind]

@[simp]
-/
theorem add_bind : (s + t).bind f = s.bind f + t.bind f := by simp [bind]

@[simp]
/--
theorem `bind_zero` / 定理 `bind_zero`

English:
theorem bind_zero
  statement: s.bind (fun _ => 0 : α -> Multiset β) = 0
  proof: by simp [bind, join, nsmul_zero]

@[simp]

中文:
定理 bind_zero
  结论: s.bind (fun _ => 0 : α -> Multiset β) = 0
  证明: by simp [bind, join, nsmul_zero]

@[simp]

Depends on / 依赖: nsmul_zero
-/
theorem bind_zero : s.bind (fun _ => 0 : α -> Multiset β) = 0 := by simp [bind, join, nsmul_zero]

@[simp]
/--
theorem `bind_add` / 定理 `bind_add`

English:
theorem bind_add
  statement: (s.bind fun a => f a + g a) = s.bind f + s.bind g
  proof: by simp [bind, join]

@[simp]

中文:
定理 bind_add
  结论: (s.bind fun a => f a + g a) = s.bind f + s.bind g
  证明: by simp [bind, join]

@[simp]
-/
theorem bind_add : (s.bind fun a => f a + g a) = s.bind f + s.bind g := by simp [bind, join]

@[simp]
/--
theorem `bind_cons` / 定理 `bind_cons`

English:
theorem bind_cons
  given: (f : α -> β) (g : α -> Multiset β)
  proof: Multiset.induction_on s (by simp)
    (by simp +contextual [add_comm, add_left_comm, add_assoc])

@[simp]

中文:
定理 bind_cons
  条件: (f : α -> β) (g : α -> Multiset β)
  证明: Multiset.induction_on s (by simp)
    (by simp +contextual [add_comm, add_left_comm, add_assoc])

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, add_assoc, add_comm, add_left_comm, contextual, induction_on
-/
theorem bind_cons (f : α -> β) (g : α -> Multiset β) :
    (s.bind fun a => f a ::ₘ g a) = map f s + s.bind g :=
  Multiset.induction_on s (by simp)
    (by simp +contextual [add_comm, add_left_comm, add_assoc])

@[simp]
/--
theorem `bind_singleton` / 定理 `bind_singleton`

English:
theorem bind_singleton
  given: (f : α -> β)
  statement: (s.bind fun x => ({f x} : Multiset β)) = map f s
  proof: Multiset.induction_on s (by rw [zero_bind, map_zero]) (by simp [singleton_add])

@[simp]

中文:
定理 bind_singleton
  条件: (f : α -> β)
  结论: (s.bind fun x => ({f x} : Multiset β)) = map f s
  证明: Multiset.induction_on s (by rw [zero_bind, map_zero]) (by simp [singleton_add])

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on, map_zero, singleton_add, zero_bind
-/
theorem bind_singleton (f : α -> β) : (s.bind fun x => ({f x} : Multiset β)) = map f s :=
  Multiset.induction_on s (by rw [zero_bind, map_zero]) (by simp [singleton_add])

@[simp]
/--
theorem `mem_bind` / 定理 `mem_bind`

English:
theorem mem_bind
  given: {b s} {f : α -> Multiset β}
  statement: b in bind s f ↔ exists a in s, b in f a
  proof: by
  simp [bind]

@[simp]

中文:
定理 mem_bind
  条件: {b s} {f : α -> Multiset β}
  结论: b in bind s f ↔ 存在 a in s, b in f a
  证明: by
  simp [bind]

@[simp]
-/
theorem mem_bind {b s} {f : α -> Multiset β} : b in bind s f ↔ exists a in s, b in f a := by
  simp [bind]

@[simp]
/--
theorem `card_bind` / 定理 `card_bind`

English:
theorem card_bind
  statement: card (s.bind f) = (s.map (card ∘ f)).sum
  proof: by simp [bind]

@[congr]

中文:
定理 card_bind
  结论: card (s.bind f) = (s.map (card ∘ f)).求和
  证明: by simp [bind]

@[congr]
-/
theorem card_bind : card (s.bind f) = (s.map (card ∘ f)).sum := by simp [bind]

@[congr]
/--
theorem `bind_congr` / 定理 `bind_congr`

English:
theorem bind_congr
  given: {f g : α -> Multiset β} {m : Multiset α}
  proof: by simp +contextual [bind]

中文:
定理 bind_congr
  条件: {f g : α -> Multiset β} {m : Multiset α}
  证明: by simp +contextual [bind]

Depends on / 依赖: contextual
-/
theorem bind_congr {f g : α -> Multiset β} {m : Multiset α} :
    (forall a in m, f a = g a) -> bind m f = bind m g := by simp +contextual [bind]

/--
theorem `bind_hcongr` / 定理 `bind_hcongr`

English:
theorem bind_hcongr
  statement: {β' : Type v} {m : Multiset α} {f : α -> Multiset β} {f' : α -> Multiset β'}
  proof: by
  subst h
  simp only [heq_eq_eq] at hf
  simp [bind_congr hf]

中文:
定理 bind_hcongr
  结论: {β' : 类型v} {m : Multiset α} {f : α -> Multiset β} {f' : α -> Multiset β'}
  证明: by
  subst h
  simp only [heq_eq_eq] at hf
  simp [bind_congr hf]

Depends on / 依赖: bind_congr, heq_eq_eq
-/
theorem bind_hcongr {β' : Type v} {m : Multiset α} {f : α -> Multiset β} {f' : α -> Multiset β'}
    (h : β = β') (hf : forall a in m, f a ≍ f' a) : bind m f ≍ bind m f' := by
  subst h
  simp only [heq_eq_eq] at hf
  simp [bind_congr hf]

/--
theorem `map_bind` / 定理 `map_bind`

English:
theorem map_bind
  given: (m : Multiset α) (n : α -> Multiset β) (f : β -> γ)
  proof: by simp [bind]

中文:
定理 map_bind
  条件: (m : Multiset α) (n : α -> Multiset β) (f : β -> γ)
  证明: by simp [bind]
-/
theorem map_bind (m : Multiset α) (n : α -> Multiset β) (f : β -> γ) :
    map f (bind m n) = bind m fun a => map f (n a) := by simp [bind]

/--
theorem `bind_map` / 定理 `bind_map`

English:
theorem bind_map
  given: (m : Multiset α) (n : β -> Multiset γ) (f : α -> β)
  proof: Multiset.induction_on m (by simp) (by simp +contextual)

中文:
定理 bind_map
  条件: (m : Multiset α) (n : β -> Multiset γ) (f : α -> β)
  证明: Multiset.induction_on m (by simp) (by simp +contextual)

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, induction_on
-/
theorem bind_map (m : Multiset α) (n : β -> Multiset γ) (f : α -> β) :
    bind (map f m) n = bind m fun a => n (f a) :=
  Multiset.induction_on m (by simp) (by simp +contextual)

/--
theorem `bind_assoc` / 定理 `bind_assoc`

English:
theorem bind_assoc
  given: {s : Multiset α} {f : α -> Multiset β} {g : β -> Multiset γ}
  proof: Multiset.induction_on s (by simp) (by simp +contextual)

中文:
定理 bind_assoc
  条件: {s : Multiset α} {f : α -> Multiset β} {g : β -> Multiset γ}
  证明: Multiset.induction_on s (by simp) (by simp +contextual)

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, induction_on
-/
theorem bind_assoc {s : Multiset α} {f : α -> Multiset β} {g : β -> Multiset γ} :
    (s.bind f).bind g = s.bind fun a => (f a).bind g :=
  Multiset.induction_on s (by simp) (by simp +contextual)

/--
theorem `bind_bind` / 定理 `bind_bind`

English:
theorem bind_bind
  given: (m : Multiset α) (n : Multiset β) {f : α -> β -> Multiset γ}
  proof: Multiset.induction_on m (by simp) (by simp +contextual)

中文:
定理 bind_bind
  条件: (m : Multiset α) (n : Multiset β) {f : α -> β -> Multiset γ}
  证明: Multiset.induction_on m (by simp) (by simp +contextual)

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, induction_on
-/
theorem bind_bind (m : Multiset α) (n : Multiset β) {f : α -> β -> Multiset γ} :
    ((bind m) fun a => (bind n) fun b => f a b) = (bind n) fun b => (bind m) fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp +contextual)

/--
theorem `bind_map_comm` / 定理 `bind_map_comm`

English:
theorem bind_map_comm
  given: (m : Multiset α) (n : Multiset β) {f : α -> β -> γ}
  proof: Multiset.induction_on m (by simp) (by simp +contextual)

中文:
定理 bind_map_comm
  条件: (m : Multiset α) (n : Multiset β) {f : α -> β -> γ}
  证明: Multiset.induction_on m (by simp) (by simp +contextual)

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, induction_on
-/
theorem bind_map_comm (m : Multiset α) (n : Multiset β) {f : α -> β -> γ} :
    ((bind m) fun a => n.map fun b => f a b) = (bind n) fun b => m.map fun a => f a b :=
  Multiset.induction_on m (by simp) (by simp +contextual)

/--
theorem `filter_eq_bind` / 定理 `filter_eq_bind`

English:
theorem filter_eq_bind
  given: (m : Multiset α) (p : α -> Prop) [DecidablePred p]
  proof: by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filter_cons, ih]

中文:
定理 filter_eq_bind
  条件: (m : Multiset α) (p : α -> 命题) [DecidablePred p]
  证明: by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filter_cons, ih]

Depends on / 依赖: Multiset, Multiset.induction, filter_cons
-/
theorem filter_eq_bind (m : Multiset α) (p : α -> Prop) [DecidablePred p] :
    filter p m = bind m (fun a => if p a then {a} else 0) := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filter_cons, ih]

/--
theorem `bind_filter` / 定理 `bind_filter`

English:
theorem bind_filter
  given: (m : Multiset α) (p : α -> Prop) (f : α -> Multiset β) [DecidablePred p]
  proof: by
  simp only [filter_eq_bind, bind_assoc]
  apply Multiset.bind_congr; intro a ham
  split_ifs <;> simp

中文:
定理 bind_filter
  条件: (m : Multiset α) (p : α -> 命题) (f : α -> Multiset β) [DecidablePred p]
  证明: by
  simp only [filter_eq_bind, bind_assoc]
  apply Multiset.bind_congr; intro a ham
  split_ifs <;> simp

Depends on / 依赖: Multiset, Multiset.bind_congr, bind_assoc, bind_congr, filter_eq_bind, split_ifs
-/
theorem bind_filter (m : Multiset α) (p : α -> Prop) (f : α -> Multiset β) [DecidablePred p] :
    bind (filter p m) f = bind m (fun a => if p a then f a else 0) := by
  simp only [filter_eq_bind, bind_assoc]
  apply Multiset.bind_congr; intro a ham
  split_ifs <;> simp

/--
theorem `filter_bind` / 定理 `filter_bind`

English:
theorem filter_bind
  given: (m : Multiset α) (f : α -> Multiset β) (p : β -> Prop) [DecidablePred p]
  proof: by
  simp [bind, filter_join]

中文:
定理 filter_bind
  条件: (m : Multiset α) (f : α -> Multiset β) (p : β -> 命题) [DecidablePred p]
  证明: by
  simp [bind, filter_join]

Depends on / 依赖: filter_join
-/
theorem filter_bind (m : Multiset α) (f : α -> Multiset β) (p : β -> Prop) [DecidablePred p] :
    filter p (bind m f) = bind m (fun a => filter p (f a)) := by
  simp [bind, filter_join]

/--
theorem `filterMap_eq_bind` / 定理 `filterMap_eq_bind`

English:
theorem filterMap_eq_bind
  given: (m : Multiset α) (f : α -> Option β)
  proof: by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filterMap_cons, ih]

中文:
定理 filterMap_eq_bind
  条件: (m : Multiset α) (f : α -> 选项类型 β)
  证明: by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filterMap_cons, ih]

Depends on / 依赖: Multiset, Multiset.induction, filterMap_cons
-/
theorem filterMap_eq_bind (m : Multiset α) (f : α -> Option β) :
    filterMap f m = bind m (fun a => ((f a).map singleton).getD 0) := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [filterMap_cons, ih]

/--
theorem `bind_filterMap` / 定理 `bind_filterMap`

English:
theorem bind_filterMap
  given: (m : Multiset α) (f : α -> Option β) (g : β -> Multiset γ)
  proof: by
  simp only [filterMap_eq_bind, Multiset.bind_assoc]
  apply Multiset.bind_congr; intro a ham
  cases f a with
  | none => simp
  | some b => simp

中文:
定理 bind_filterMap
  条件: (m : Multiset α) (f : α -> 选项类型 β) (g : β -> Multiset γ)
  证明: by
  simp only [filterMap_eq_bind, Multiset.bind_assoc]
  apply Multiset.bind_congr; intro a ham
  cases f a with
  | none => simp
  | some b => simp

Depends on / 依赖: Multiset, Multiset.bind_assoc, Multiset.bind_congr, bind_assoc, bind_congr, filterMap_eq_bind
-/
theorem bind_filterMap (m : Multiset α) (f : α -> Option β) (g : β -> Multiset γ) :
    bind (filterMap f m) g = bind m (fun a => ((f a).map g).getD 0) := by
  simp only [filterMap_eq_bind, Multiset.bind_assoc]
  apply Multiset.bind_congr; intro a ham
  cases f a with
  | none => simp
  | some b => simp

/--
theorem `filterMap_bind` / 定理 `filterMap_bind`

English:
theorem filterMap_bind
  given: (m : Multiset α) (f : α -> Multiset β) (g : β -> Option γ)
  proof: by
  simp [bind, filterMap_join]

@[to_additive (attr := simp)]

中文:
定理 filterMap_bind
  条件: (m : Multiset α) (f : α -> Multiset β) (g : β -> 选项类型 γ)
  证明: by
  simp [bind, filterMap_join]

@[to_additive (attr := simp)]

Depends on / 依赖: filterMap_join
-/
theorem filterMap_bind (m : Multiset α) (f : α -> Multiset β) (g : β -> Option γ) :
    filterMap g (bind m f) = bind m (fun a => filterMap g (f a)) := by
  simp [bind, filterMap_join]

@[to_additive (attr := simp)]
/--
theorem `prod_bind` / 定理 `prod_bind`

English:
theorem prod_bind
  given: [CommMonoid β] (s : Multiset α) (t : α -> Multiset β)
  proof: by simp [bind]

中文:
定理 prod_bind
  条件: [交换幺半群 β] (s : Multiset α) (t : α -> Multiset β)
  证明: by simp [bind]
-/
theorem prod_bind [CommMonoid β] (s : Multiset α) (t : α -> Multiset β) :
    (s.bind t).prod = (s.map fun a => (t a).prod).prod := by simp [bind]

open scoped Relator in
/--
theorem `rel_bind` / 定理 `rel_bind`

English:
theorem rel_bind
  statement: {r : α -> β -> Prop} {p : γ -> δ -> Prop} {s t} {f : α -> Multiset γ}
  proof: by
  apply rel_join
  rw [rel_map]
  exact hst.mono fun a _ b _ hr => h hr

中文:
定理 rel_bind
  结论: {r : α -> β -> 命题} {p : γ -> δ -> 命题} {s t} {f : α -> Multiset γ}
  证明: by
  apply rel_join
  rw [rel_map]
  exact hst.mono fun a _ b _ hr => h hr

Depends on / 依赖: hst.mono, rel_join, rel_map
-/
theorem rel_bind {r : α -> β -> Prop} {p : γ -> δ -> Prop} {s t} {f : α -> Multiset γ}
    {g : β -> Multiset δ} (h : (r ⇒ Rel p) f g) (hst : Rel r s t) :
    Rel p (s.bind f) (t.bind g) := by
  apply rel_join
  rw [rel_map]
  exact hst.mono fun a _ b _ hr => h hr

/--
theorem `count_sum` / 定理 `count_sum`

English:
theorem count_sum
  given: [DecidableEq α] {m : Multiset β} {f : β -> Multiset α} {a : α}
  proof: Multiset.induction_on m (by simp) (by simp)

中文:
定理 count_sum
  条件: [DecidableEq α] {m : Multiset β} {f : β -> Multiset α} {a : α}
  证明: Multiset.induction_on m (by simp) (by simp)

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on
-/
theorem count_sum [DecidableEq α] {m : Multiset β} {f : β -> Multiset α} {a : α} :
    count a (map f m).sum = sum (m.map fun b => count a <| f b) :=
  Multiset.induction_on m (by simp) (by simp)

/--
theorem `count_bind` / 定理 `count_bind`

English:
theorem count_bind
  given: [DecidableEq α] {m : Multiset β} {f : β -> Multiset α} {a : α}
  proof: count_sum

中文:
定理 count_bind
  条件: [DecidableEq α] {m : Multiset β} {f : β -> Multiset α} {a : α}
  证明: count_sum

Depends on / 依赖: count_sum
-/
theorem count_bind [DecidableEq α] {m : Multiset β} {f : β -> Multiset α} {a : α} :
    count a (bind m f) = sum (m.map fun b => count a <| f b) :=
  count_sum

/--
theorem `le_bind` / 定理 `le_bind`

English:
theorem le_bind
  given: {α β : Type*} {f : α -> Multiset β} (S : Multiset α) {x : α} (hx : x in S)
  proof: by
  classical
  refine le_iff_count.2 fun a => ?_
obtain ⟨m', hm'⟩ := exists_cons_of_mem mem_map_of_mem (fun b => count a (f b)) hx
  rw [count_bind]; rw [hm']; rw [sum_cons]
  exact Nat.le_add_right _ _

@[simp]

中文:
定理 le_bind
  条件: {α β : 类型} {f : α -> Multiset β} (S : Multiset α) {x : α} (hx : x in S)
  证明: by
  classical
  refine le_iff_count.2 fun a => ?_
obtain ⟨m', hm'⟩ := exists_cons_of_mem mem_map_of_mem (fun b => count a (f b)) hx
  rw [count_bind]; rw [hm']; rw [sum_cons]
  exact Nat.le_add_right _ _

@[simp]

Depends on / 依赖: Nat.le_add_right, classical, count_bind, exists_cons_of_mem, le_add_right, le_iff_count, mem_map_of_mem, sum_cons
-/
theorem le_bind {α β : Type*} {f : α -> Multiset β} (S : Multiset α) {x : α} (hx : x in S) :
    f x <= S.bind f := by
  classical
  refine le_iff_count.2 fun a => ?_
obtain ⟨m', hm'⟩ := exists_cons_of_mem mem_map_of_mem (fun b => count a (f b)) hx
  rw [count_bind]; rw [hm']; rw [sum_cons]
  exact Nat.le_add_right _ _

@[simp]
/--
theorem `attach_bind_coe` / 定理 `attach_bind_coe`

English:
theorem attach_bind_coe
  given: (s : Multiset α) (f : α -> Multiset β)
  proof: congr_arg join attach_map_val' _ _

中文:
定理 attach_bind_coe
  条件: (s : Multiset α) (f : α -> Multiset β)
  证明: congr_arg join attach_map_val' _ _

Depends on / 依赖: attach_map_val, congr_arg
-/
theorem attach_bind_coe (s : Multiset α) (f : α -> Multiset β) :
    (s.attach.bind fun i => f i) = s.bind f :=
congr_arg join attach_map_val' _ _

variable {f s t}

open scoped Function in -- required for scoped `on` notation
/--
lemma `nodup_bind` / 引理 `nodup_bind`

English:
lemma nodup_bind
  proof: by
  have : forall a, exists l : List β, f a = l := fun a => Quot.induction_on (f a) fun l => ⟨l, rfl⟩
  choose f' h' using this
  have : f = fun a => ofList (f' a) := funext h'
  have _ : Std.Symm fun a b : List β => List.Disjoint a b := { symm a b h := h.symm }
exact Quot.induction_on s by
    unfold Function.onFun
    simp [this, List.nodup_flatMap, pairwise_coe_iff_pairwise]

@[simp]

中文:
引理 nodup_bind
  证明: by
  have : forall a, exists l : List β, f a = l := fun a => Quot.induction_on (f a) fun l => ⟨l, rfl⟩
  choose f' h' using this
  have : f = fun a => ofList (f' a) := funext h'
  have _ : Std.Symm fun a b : List β => List.Disjoint a b := { symm a b h := h.symm }
exact Quot.induction_on s by
    unfold Function.onFun
    simp [this, List.nodup_flatMap, pairwise_coe_iff_pairwise]

@[simp]
-/
@[simp] lemma nodup_bind :
    Nodup (bind s f) ↔ (forall a in s, Nodup (f a)) ∧ s.Pairwise (Disjoint on f) := by
  have : forall a, exists l : List β, f a = l := fun a => Quot.induction_on (f a) fun l => ⟨l, rfl⟩
  choose f' h' using this
  have : f = fun a => ofList (f' a) := funext h'
  have _ : Std.Symm fun a b : List β => List.Disjoint a b := { symm a b h := h.symm }
exact Quot.induction_on s by
    unfold Function.onFun
    simp [this, List.nodup_flatMap, pairwise_coe_iff_pairwise]

@[simp]
/--
lemma `dedup_bind_dedup` / 引理 `dedup_bind_dedup`

English:
lemma dedup_bind_dedup
  given: [DecidableEq α] [DecidableEq β] (s : Multiset α) (f : α -> Multiset β)
  proof: by
  ext x
  -- Porting note: was `simp_rw [count_dedup, mem_bind, mem_dedup]`
  simp_rw [count_dedup]
  congr 1
  simp

中文:
引理 dedup_bind_dedup
  条件: [DecidableEq α] [DecidableEq β] (s : Multiset α) (f : α -> Multiset β)
  证明: by
  ext x
  -- Porting note: was `simp_rw [count_dedup, mem_bind, mem_dedup]`
  simp_rw [count_dedup]
  congr 1
  simp
-/
lemma dedup_bind_dedup [DecidableEq α] [DecidableEq β] (s : Multiset α) (f : α -> Multiset β) :
    (s.dedup.bind f).dedup = (s.bind f).dedup := by
  ext x
  -- Porting note: was `simp_rw [count_dedup, mem_bind, mem_dedup]`
  simp_rw [count_dedup]
  congr 1
  simp

variable (op : α -> α -> α) [hc : Std.Commutative op] [ha : Std.Associative op]

/--
theorem `fold_bind` / 定理 `fold_bind`

English:
theorem fold_bind
  given: {ι : Type*} (s : Multiset ι) (t : ι -> Multiset α) (b : ι -> α) (b₀ : α)
  proof: by
  induction s using Multiset.induction_on with
  | empty => rw [zero_bind, map_zero, map_zero, fold_zero]
  | cons a ha ih => rw [cons_bind, map_cons, map_cons, fold_cons_left, fold_cons_left, fold_add, ih]

中文:
定理 fold_bind
  条件: {ι : 类型} (s : Multiset ι) (t : ι -> Multiset α) (b : ι -> α) (b₀ : α)
  证明: by
  induction s using Multiset.induction_on with
  | empty => rw [zero_bind, map_zero, map_zero, fold_zero]
  | cons a ha ih => rw [cons_bind, map_cons, map_cons, fold_cons_left, fold_cons_left, fold_add, ih]

Depends on / 依赖: Multiset, Multiset.induction_on, cons_bind, fold_add, fold_cons_left, fold_zero, induction_on, map_cons, map_zero, zero_bind
-/
theorem fold_bind {ι : Type*} (s : Multiset ι) (t : ι -> Multiset α) (b : ι -> α) (b₀ : α) :
    (s.bind t).fold op ((s.map b).fold op b₀) =
    (s.map fun i => (t i).fold op (b i)).fold op b₀ := by
  induction s using Multiset.induction_on with
  | empty => rw [zero_bind, map_zero, map_zero, fold_zero]
  | cons a ha ih => rw [cons_bind, map_cons, map_cons, fold_cons_left, fold_cons_left, fold_add, ih]

end Bind

/-! ### Product of two multisets -/


section Product

variable (a : α) (b : β) (s : Multiset α) (t : Multiset β)

/--
Definition of `product` / `product` 的定义

English:
definition product
  signature: (s : Multiset α) (t : Multiset β)
  body: s.bind fun a => t.map Prod.mk a

中文:
定义 product
  签名: (s : Multiset α) (t : Multiset β)
  定义体: s.bind fun a => t.map Prod.mk a

Depends on / 依赖: Prod.mk, s.bind, t.map
-/
def product (s : Multiset α) (t : Multiset β) : Multiset (α × β) :=
s.bind fun a => t.map Prod.mk a

/--
Instance `instSProd` / 实例 `instSProd`

English:
instance instSProd
  signature: : SProd (Multiset α) (Multiset β) (Multiset (α × β)) where
  body: Multiset.product

@[simp]

中文:
实例 instSProd
  签名: : SProd (Multiset α) (Multiset β) (Multiset (α × β)) where
  定义体: Multiset.product

@[simp]

Depends on / 依赖: Multiset, Multiset.product, product
-/
instance instSProd : SProd (Multiset α) (Multiset β) (Multiset (α × β)) where
  sprod := Multiset.product

@[simp]
/--
theorem `coe_product` / 定理 `coe_product`

English:
theorem coe_product
  given: (l₁ : List α) (l₂ : List β)
  proof: by
  dsimp only [SProd.sprod]
  rw [product]; rw [List.product]; rw [← coe_bind]
  simp

@[simp]

中文:
定理 coe_product
  条件: (l₁ : 列表 α) (l₂ : 列表 β)
  证明: by
  dsimp only [SProd.sprod]
  rw [product]; rw [List.product]; rw [← coe_bind]
  simp

@[simp]

Depends on / 依赖: List.product, SProd.sprod, coe_bind, product
-/
theorem coe_product (l₁ : List α) (l₂ : List β) :
    (l₁ : Multiset α) ×ˢ (l₂ : Multiset β) = (l₁ ×ˢ l₂) := by
  dsimp only [SProd.sprod]
  rw [product]; rw [List.product]; rw [← coe_bind]
  simp

@[simp]
/--
theorem `zero_product` / 定理 `zero_product`

English:
theorem zero_product
  statement: (0 : Multiset α) ×ˢ t = 0
  proof: rfl

@[simp]

中文:
定理 zero_product
  结论: (0 : Multiset α) ×ˢ t = 0
  证明: rfl

@[simp]
-/
theorem zero_product : (0 : Multiset α) ×ˢ t = 0 :=
  rfl

@[simp]
/--
theorem `cons_product` / 定理 `cons_product`

English:
theorem cons_product
  statement: (a ::ₘ s) ×ˢ t = map (Prod.mk a) t + s ×ˢ t
  proof: by simp [SProd.sprod, product]

@[simp]

中文:
定理 cons_product
  结论: (a ::ₘ s) ×ˢ t = map (积类型.mk a) t + s ×ˢ t
  证明: by simp [SProd.sprod, product]

@[simp]

Depends on / 依赖: SProd.sprod, product
-/
theorem cons_product : (a ::ₘ s) ×ˢ t = map (Prod.mk a) t + s ×ˢ t := by simp [SProd.sprod, product]

@[simp]
/--
theorem `product_zero` / 定理 `product_zero`

English:
theorem product_zero
  statement: s ×ˢ (0 : Multiset β) = 0
  proof: by simp [SProd.sprod, product]

@[simp]

中文:
定理 product_zero
  结论: s ×ˢ (0 : Multiset β) = 0
  证明: by simp [SProd.sprod, product]

@[simp]

Depends on / 依赖: SProd.sprod, product
-/
theorem product_zero : s ×ˢ (0 : Multiset β) = 0 := by simp [SProd.sprod, product]

@[simp]
/--
theorem `product_cons` / 定理 `product_cons`

English:
theorem product_cons
  statement: s ×ˢ (b ::ₘ t) = (s.map fun a => (a, b)) + s ×ˢ t
  proof: by
  simp [SProd.sprod, product]

@[simp]

中文:
定理 product_cons
  结论: s ×ˢ (b ::ₘ t) = (s.map fun a => (a, b)) + s ×ˢ t
  证明: by
  simp [SProd.sprod, product]

@[simp]

Depends on / 依赖: SProd.sprod, product
-/
theorem product_cons : s ×ˢ (b ::ₘ t) = (s.map fun a => (a, b)) + s ×ˢ t := by
  simp [SProd.sprod, product]

@[simp]
/--
theorem `product_singleton` / 定理 `product_singleton`

English:
theorem product_singleton
  statement: ({a} : Multiset α) ×ˢ ({b} : Multiset β) = {(a, b)}
  proof: by
  simp only [SProd.sprod, product, bind_singleton, map_singleton]

@[simp]

中文:
定理 product_singleton
  结论: ({a} : Multiset α) ×ˢ ({b} : Multiset β) = {(a, b)}
  证明: by
  simp only [SProd.sprod, product, bind_singleton, map_singleton]

@[simp]

Depends on / 依赖: SProd.sprod, bind_singleton, map_singleton, product
-/
theorem product_singleton : ({a} : Multiset α) ×ˢ ({b} : Multiset β) = {(a, b)} := by
  simp only [SProd.sprod, product, bind_singleton, map_singleton]

@[simp]
/--
theorem `add_product` / 定理 `add_product`

English:
theorem add_product
  given: (s t : Multiset α) (u : Multiset β)
  statement: (s + t) ×ˢ u = s ×ˢ u + t ×ˢ u
  proof: by
  simp [SProd.sprod, product]

@[simp]

中文:
定理 add_product
  条件: (s t : Multiset α) (u : Multiset β)
  结论: (s + t) ×ˢ u = s ×ˢ u + t ×ˢ u
  证明: by
  simp [SProd.sprod, product]

@[simp]

Depends on / 依赖: SProd.sprod, product
-/
theorem add_product (s t : Multiset α) (u : Multiset β) : (s + t) ×ˢ u = s ×ˢ u + t ×ˢ u := by
  simp [SProd.sprod, product]

@[simp]
/--
theorem `product_add` / 定理 `product_add`

English:
theorem product_add
  given: (s : Multiset α)
  statement: forall t u : Multiset β, s ×ˢ (t + u) = s ×ˢ t + s ×ˢ u
  proof: Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_product]; rw [IH]
    simp [add_left_comm, add_assoc]

@[simp]

中文:
定理 product_add
  条件: (s : Multiset α)
  结论: 对任意 t u : Multiset β, s ×ˢ (t + u) = s ×ˢ t + s ×ˢ u
  证明: Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_product]; rw [IH]
    simp [add_left_comm, add_assoc]

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, add_assoc, add_left_comm, cons_product, induction_on
-/
theorem product_add (s : Multiset α) : forall t u : Multiset β, s ×ˢ (t + u) = s ×ˢ t + s ×ˢ u :=
  Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_product]; rw [IH]
    simp [add_left_comm, add_assoc]

@[simp]
/--
theorem `card_product` / 定理 `card_product`

English:
theorem card_product
  statement: card (s ×ˢ t) = card s * card t
  proof: by simp [SProd.sprod, product]

中文:
定理 card_product
  结论: card (s ×ˢ t) = card s * card t
  证明: by simp [SProd.sprod, product]

Depends on / 依赖: SProd.sprod, product
-/
theorem card_product : card (s ×ˢ t) = card s * card t := by simp [SProd.sprod, product]

variable {s t}

/--
lemma `mem_product` / 引理 `mem_product`

English:
lemma mem_product
  statement: forall {p : α × β}, p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t

中文:
引理 mem_product
  结论: 对任意 {p : α × β}, p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
-/
@[simp] lemma mem_product : forall {p : α × β}, p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
  | (a, b) => by simp [SProd.sprod, product, and_left_comm]

/--
theorem `Nodup.product` / 定理 `Nodup.product`

English:
theorem Nodup.product
  statement: Nodup s -> Nodup t -> Nodup (s ×ˢ t)
  proof: Quotient.inductionOn₂ s t fun l₁ l₂ d₁ d₂ => by simp [List.Nodup.product d₁ d₂]

中文:
定理 Nodup.product
  结论: Nodup s -> Nodup t -> Nodup (s ×ˢ t)
  证明: Quotient.inductionOn₂ s t fun l₁ l₂ d₁ d₂ => by simp [List.Nodup.product d₁ d₂]
-/
protected theorem Nodup.product : Nodup s -> Nodup t -> Nodup (s ×ˢ t) :=
  Quotient.inductionOn₂ s t fun l₁ l₂ d₁ d₂ => by simp [List.Nodup.product d₁ d₂]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `map_swap_product` / 引理 `map_swap_product`

English:
lemma map_swap_product
  given: (s : Multiset α) (t : Multiset β)
  proof: by
  induction s using Multiset.induction <;> simp_all

中文:
引理 map_swap_product
  条件: (s : Multiset α) (t : Multiset β)
  证明: by
  induction s using Multiset.induction <;> simp_all
-/
@[simp] lemma map_swap_product (s : Multiset α) (t : Multiset β) :
    (s ×ˢ t).map Prod.swap = t ×ˢ s := by
  induction s using Multiset.induction <;> simp_all

/--
lemma `prod_map_product_eq_prod_prod` / 引理 `prod_map_product_eq_prod_prod`

English:
lemma prod_map_product_eq_prod_prod
  statement: {M : Type*} [CommMonoid M]
  proof: by
  induction s using Multiset.induction <;> simp_all

中文:
引理 prod_map_product_eq_prod_prod
  结论: {M : 类型} [交换幺半群 M]
  证明: by
  induction s using Multiset.induction <;> simp_all

Depends on / 依赖: List.decidablePerm, Multiset, Multiset.induction, decidablePerm
-/
lemma prod_map_product_eq_prod_prod {M : Type*} [CommMonoid M]
    (s : Multiset α) (t : Multiset β) (f : α × β -> M) :
    ((s ×ˢ t).map f).prod = (s.map fun i => (t.map fun j => f (i, j)).prod).prod := by
  induction s using Multiset.induction <;> simp_all

end Product

/-! ### Disjoint sum of multisets -/


section Sigma

variable {σ : α -> Type*} (a : α) (s : Multiset α) (t : forall a, Multiset (σ a))

/--
Definition of `sigma` / `sigma` 的定义

English:
definition sigma
  signature: (s : Multiset α) (t : forall a, Multiset (σ a))
  body: s.bind fun a => (t a).map Sigma.mk a

@[simp]

中文:
定义 sigma
  签名: (s : Multiset α) (t : 对任意 a, Multiset (σ a))
  定义体: s.bind fun a => (t a).map Sigma.mk a

@[simp]
-/
protected def sigma (s : Multiset α) (t : forall a, Multiset (σ a)) : Multiset (Σ a, σ a) :=
s.bind fun a => (t a).map Sigma.mk a

@[simp]
/--
theorem `coe_sigma` / 定理 `coe_sigma`

English:
theorem coe_sigma
  given: (l₁ : List α) (l₂ : forall a, List (σ a))
  proof: by
  rw [Multiset.sigma]; rw [List.sigma]; rw [← coe_bind]
  simp

@[simp]

中文:
定理 coe_sigma
  条件: (l₁ : 列表 α) (l₂ : 对任意 a, 列表 (σ a))
  证明: by
  rw [Multiset.sigma]; rw [List.sigma]; rw [← coe_bind]
  simp

@[simp]

Depends on / 依赖: List.sigma, Multiset, Multiset.sigma, coe_bind
-/
theorem coe_sigma (l₁ : List α) (l₂ : forall a, List (σ a)) :
    (@Multiset.sigma α σ l₁ fun a => l₂ a) = l₁.sigma l₂ := by
  rw [Multiset.sigma]; rw [List.sigma]; rw [← coe_bind]
  simp

@[simp]
/--
theorem `zero_sigma` / 定理 `zero_sigma`

English:
theorem zero_sigma
  statement: @Multiset.sigma α σ 0 t = 0
  proof: rfl

@[simp]

中文:
定理 zero_sigma
  结论: @Multiset.sigma α σ 0 t = 0
  证明: rfl

@[simp]
-/
theorem zero_sigma : @Multiset.sigma α σ 0 t = 0 :=
  rfl

@[simp]
/--
theorem `cons_sigma` / 定理 `cons_sigma`

English:
theorem cons_sigma
  statement: (a ::ₘ s).sigma t = (t a).map (Sigma.mk a) + s.sigma t
  proof: by
  simp [Multiset.sigma]

@[simp]

中文:
定理 cons_sigma
  结论: (a ::ₘ s).sigma t = (t a).map (依赖和类型.mk a) + s.sigma t
  证明: by
  simp [Multiset.sigma]

@[simp]

Depends on / 依赖: Multiset, Multiset.sigma
-/
theorem cons_sigma : (a ::ₘ s).sigma t = (t a).map (Sigma.mk a) + s.sigma t := by
  simp [Multiset.sigma]

@[simp]
/--
theorem `sigma_singleton` / 定理 `sigma_singleton`

English:
theorem sigma_singleton
  given: (b : α -> β)
  proof: rfl

@[simp]

中文:
定理 sigma_singleton
  条件: (b : α -> β)
  证明: rfl

@[simp]
-/
theorem sigma_singleton (b : α -> β) :
    (({a} : Multiset α).sigma fun a => ({b a} : Multiset β)) = {⟨a, b a⟩} :=
  rfl

@[simp]
/--
theorem `add_sigma` / 定理 `add_sigma`

English:
theorem add_sigma
  given: (s t : Multiset α) (u : forall a, Multiset (σ a))
  proof: by simp [Multiset.sigma]

@[simp]

中文:
定理 add_sigma
  条件: (s t : Multiset α) (u : 对任意 a, Multiset (σ a))
  证明: by simp [Multiset.sigma]

@[simp]

Depends on / 依赖: Multiset, Multiset.sigma
-/
theorem add_sigma (s t : Multiset α) (u : forall a, Multiset (σ a)) :
    (s + t).sigma u = s.sigma u + t.sigma u := by simp [Multiset.sigma]

@[simp]
/--
theorem `sigma_add` / 定理 `sigma_add`

English:
theorem sigma_add
  proof: Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_sigma]; rw [IH]
    simp [add_comm, add_left_comm, add_assoc]

@[simp]

中文:
定理 sigma_add
  证明: Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_sigma]; rw [IH]
    simp [add_comm, add_left_comm, add_assoc]

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, add_assoc, add_comm, add_left_comm, cons_sigma, induction_on
-/
theorem sigma_add :
    forall t u : forall a, Multiset (σ a), (s.sigma fun a => t a + u a) = s.sigma t + s.sigma u :=
  Multiset.induction_on s (fun _ _ => rfl) fun a s IH t u => by
    rw [cons_sigma]; rw [IH]
    simp [add_comm, add_left_comm, add_assoc]

@[simp]
/--
theorem `card_sigma` / 定理 `card_sigma`

English:
theorem card_sigma
  statement: card (s.sigma t) = sum (map (fun a => card (t a)) s)
  proof: by
  simp [Multiset.sigma, (· ∘ ·)]

中文:
定理 card_sigma
  结论: card (s.sigma t) = 求和 (map (fun a => card (t a)) s)
  证明: by
  simp [Multiset.sigma, (· ∘ ·)]

Depends on / 依赖: Multiset, Multiset.sigma
-/
theorem card_sigma : card (s.sigma t) = sum (map (fun a => card (t a)) s) := by
  simp [Multiset.sigma, (· ∘ ·)]

variable {s t}

/--
lemma `mem_sigma` / 引理 `mem_sigma`

English:
lemma mem_sigma
  statement: forall {p : Σ a, σ a}, p in @Multiset.sigma α σ s t ↔ p.1 in s ∧ p.2 in t p.1

中文:
引理 mem_sigma
  结论: 对任意 {p : Σ a, σ a}, p in @Multiset.sigma α σ s t ↔ p.1 in s ∧ p.2 in t p.1
-/
@[simp] lemma mem_sigma : forall {p : Σ a, σ a}, p in @Multiset.sigma α σ s t ↔ p.1 in s ∧ p.2 in t p.1
  | ⟨a, b⟩ => by simp [Multiset.sigma, and_left_comm]

/--
theorem `Nodup.sigma` / 定理 `Nodup.sigma`

English:
theorem Nodup.sigma
  given: {σ : α -> Type*} {t : forall a, Multiset (σ a)}
  proof: Quot.induction_on s fun l₁ => by
    choose f hf using fun a => Quotient.exists_rep (t a)
    simpa [← funext hf] using List.Nodup.sigma

中文:
定理 Nodup.sigma
  条件: {σ : α -> 类型} {t : 对任意 a, Multiset (σ a)}
  证明: Quot.induction_on s fun l₁ => by
    choose f hf using fun a => Quotient.exists_rep (t a)
    simpa [← funext hf] using List.Nodup.sigma
-/
protected theorem Nodup.sigma {σ : α -> Type*} {t : forall a, Multiset (σ a)} :
    Nodup s -> (forall a, Nodup (t a)) -> Nodup (s.sigma t) :=
  Quot.induction_on s fun l₁ => by
    choose f hf using fun a => Quotient.exists_rep (t a)
    simpa [← funext hf] using List.Nodup.sigma

end Sigma

end Multiset
