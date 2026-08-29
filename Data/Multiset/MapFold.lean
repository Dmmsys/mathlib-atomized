/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Multiset.Replicate
public import Mathlib.Data.Set.List

/-!
# Mapping and folding multisets

## Main definitions

* `Multiset.map`: `map f s` applies `f` to each element of `s`.
* `Multiset.foldl`: `foldl f b s` picks elements out of `s` and applies `f (f ... b x₁) x₂`.
* `Multiset.foldr`: `foldr f b s` picks elements out of `s` and applies `f x₁ (f ... x₂ b)`.

## TODO

Many lemmas about `Multiset.map` are proven in `Mathlib/Data/Multiset/Filter.lean`:
should we switch the import direction?

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.map` -/


/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (s : Multiset α)
  body: Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)

@[congr]

中文:
定义 map
  签名: (f : α -> β) (s : Multiset α)
  定义体: Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)

@[congr]

Depends on / 依赖: Multiset, Quot.liftOn, Quot.sound, l.map, liftOn, p.map
-/
def map (f : α -> β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)

@[congr]
/--
theorem `map_congr` / 定理 `map_congr`

English:
theorem map_congr
  given: {f g : α -> β} {s t : Multiset α}
  proof: by
  rintro rfl h
  induction s using Quot.inductionOn
  exact congr_arg _ (List.map_congr_left h)

中文:
定理 map_congr
  条件: {f g : α -> β} {s t : Multiset α}
  证明: by
  rintro rfl h
  induction s using Quot.inductionOn
  exact congr_arg _ (List.map_congr_left h)

Depends on / 依赖: List.map_congr_left, Quot.inductionOn, congr_arg, inductionOn, map_congr_left
-/
theorem map_congr {f g : α -> β} {s t : Multiset α} :
    s = t -> (forall x in t, f x = g x) -> map f s = map g t := by
  rintro rfl h
  induction s using Quot.inductionOn
  exact congr_arg _ (List.map_congr_left h)

/--
theorem `map_hcongr` / 定理 `map_hcongr`

English:
theorem map_hcongr
  statement: {β' : Type v} {m : Multiset α} {f : α -> β} {f' : α -> β'} (h : β = β')
  proof: by
  subst h; simp at hf
  simp [map_congr rfl hf]

中文:
定理 map_hcongr
  结论: {β' : 类型v} {m : Multiset α} {f : α -> β} {f' : α -> β'} (h : β = β')
  证明: by
  subst h; simp at hf
  simp [map_congr rfl hf]

Depends on / 依赖: map_congr
-/
theorem map_hcongr {β' : Type v} {m : Multiset α} {f : α -> β} {f' : α -> β'} (h : β = β')
    (hf : forall a in m, f a ≍ f' a) : map f m ≍ map f' m := by
  subst h; simp at hf
  simp [map_congr rfl hf]

/--
theorem `forall_mem_map_iff` / 定理 `forall_mem_map_iff`

English:
theorem forall_mem_map_iff
  given: {f : α -> β} {p : β -> Prop} {s : Multiset α}
  proof: Quotient.inductionOn' s fun _L => List.forall_mem_map

中文:
定理 对任意_mem_map_iff
  条件: {f : α -> β} {p : β -> 命题} {s : Multiset α}
  证明: Quotient.inductionOn' s fun _L => List.forall_mem_map

Depends on / 依赖: List.forall_mem_map, Quotient, Quotient.inductionOn, forall_mem_map, inductionOn
-/
theorem forall_mem_map_iff {f : α -> β} {p : β -> Prop} {s : Multiset α} :
    (forall y in s.map f, p y) ↔ forall x in s, p (f x) :=
  Quotient.inductionOn' s fun _L => List.forall_mem_map

/--
lemma `map_coe` / 引理 `map_coe`

English:
lemma map_coe
  given: (f : α -> β) (l : List α)
  statement: map f l = l.map f
  proof: rfl

@[simp]

中文:
引理 map_coe
  条件: (f : α -> β) (l : 列表 α)
  结论: map f l = l.map f
  证明: rfl

@[simp]
-/
@[simp, norm_cast] lemma map_coe (f : α -> β) (l : List α) : map f l = l.map f := rfl

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  given: (f : α -> β)
  statement: map f 0 = 0
  proof: rfl

@[simp]

中文:
定理 map_zero
  条件: (f : α -> β)
  结论: map f 0 = 0
  证明: rfl

@[simp]
-/
theorem map_zero (f : α -> β) : map f 0 = 0 :=
  rfl

@[simp]
/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  given: (f : α -> β) (a s)
  statement: map f (a ::ₘ s) = f a ::ₘ map f s
  proof: Quot.inductionOn s fun _l => rfl

中文:
定理 map_cons
  条件: (f : α -> β) (a s)
  结论: map f (a ::ₘ s) = f a ::ₘ map f s
  证明: Quot.inductionOn s fun _l => rfl

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s :=
  Quot.inductionOn s fun _l => rfl

/--
theorem `map_comp_cons` / 定理 `map_comp_cons`

English:
theorem map_comp_cons
  given: (f : α -> β) (t)
  statement: map f ∘ cons t = cons (f t) ∘ map f
  proof: by
  ext
  simp

@[simp]

中文:
定理 map_comp_cons
  条件: (f : α -> β) (t)
  结论: map f ∘ cons t = cons (f t) ∘ map f
  证明: by
  ext
  simp

@[simp]
-/
theorem map_comp_cons (f : α -> β) (t) : map f ∘ cons t = cons (f t) ∘ map f := by
  ext
  simp

@[simp]
/--
theorem `map_singleton` / 定理 `map_singleton`

English:
theorem map_singleton
  given: (f : α -> β) (a : α)
  statement: ({a} : Multiset α).map f = {f a}
  proof: rfl

@[simp]

中文:
定理 map_singleton
  条件: (f : α -> β) (a : α)
  结论: ({a} : Multiset α).map f = {f a}
  证明: rfl

@[simp]
-/
theorem map_singleton (f : α -> β) (a : α) : ({a} : Multiset α).map f = {f a} :=
  rfl

@[simp]
/--
theorem `map_replicate` / 定理 `map_replicate`

English:
theorem map_replicate
  given: (f : α -> β) (k : Nat) (a : α)
  statement: (replicate k a).map f = replicate k (f a)
  proof: by
  simp only [← coe_replicate, map_coe, List.map_replicate]

@[simp]

中文:
定理 map_replicate
  条件: (f : α -> β) (k : 自然数) (a : α)
  结论: (replicate k a).map f = replicate k (f a)
  证明: by
  simp only [← coe_replicate, map_coe, List.map_replicate]

@[simp]

Depends on / 依赖: List.map_replicate, coe_replicate, map_coe, map_replicate
-/
theorem map_replicate (f : α -> β) (k : Nat) (a : α) : (replicate k a).map f = replicate k (f a) := by
  simp only [← coe_replicate, map_coe, List.map_replicate]

@[simp]
/--
theorem `map_add` / 定理 `map_add`

English:
theorem map_add
  given: (f : α -> β) (s t)
  statement: map f (s + t) = map f s + map f t
  proof: Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ map_append

中文:
定理 map_add
  条件: (f : α -> β) (s t)
  结论: map f (s + t) = map f s + map f t
  证明: Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ map_append

Depends on / 依赖: Quotient, Quotient.inductionOn, congr_arg, map_append
-/
theorem map_add (f : α -> β) (s t) : map f (s + t) = map f s + map f t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ map_append

/--
Instance `canLift` / 实例 `canLift`

English:
instance canLift
  signature: (c) (p) [CanLift α β c p]
  body: by
    rintro ⟨l⟩ hl
    lift l to List β using hl
    exact ⟨l, map_coe _ _⟩

@[simp]

中文:
实例 canLift
  签名: (c) (p) [CanLift α β c p]
  定义体: by
    rintro ⟨l⟩ hl
    lift l to List β using hl
    exact ⟨l, map_coe _ _⟩

@[simp]

Depends on / 依赖: map_coe
-/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Multiset α) (Multiset β) (map c) fun s => forall x in s, p x where
  prf := by
    rintro ⟨l⟩ hl
    lift l to List β using hl
    exact ⟨l, map_coe _ _⟩

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : α -> β} {b : β} {s : Multiset α}
  statement: b in map f s ↔ exists a, a in s ∧ f a = b
  proof: Quot.inductionOn s fun _l => List.mem_map

@[simp]

中文:
定理 mem_map
  条件: {f : α -> β} {b : β} {s : Multiset α}
  结论: b in map f s ↔ 存在 a, a in s ∧ f a = b
  证明: Quot.inductionOn s fun _l => List.mem_map

@[simp]

Depends on / 依赖: List.mem_map, Quot.inductionOn, inductionOn, mem_map
-/
theorem mem_map {f : α -> β} {b : β} {s : Multiset α} : b in map f s ↔ exists a, a in s ∧ f a = b :=
  Quot.inductionOn s fun _l => List.mem_map

@[simp]
/--
theorem `card_map` / 定理 `card_map`

English:
theorem card_map
  given: (f : α -> β) (s)
  statement: card (map f s) = card s
  proof: Quot.inductionOn s fun _ => length_map _

@[simp]

中文:
定理 card_map
  条件: (f : α -> β) (s)
  结论: card (map f s) = card s
  证明: Quot.inductionOn s fun _ => length_map _

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn, length_map
-/
theorem card_map (f : α -> β) (s) : card (map f s) = card s :=
  Quot.inductionOn s fun _ => length_map _

@[simp]
/--
theorem `map_eq_zero` / 定理 `map_eq_zero`

English:
theorem map_eq_zero
  given: {s : Multiset α} {f : α -> β}
  statement: s.map f = 0 ↔ s = 0
  proof: by
  rw [← Multiset.card_eq_zero]; rw [Multiset.card_map]; rw [Multiset.card_eq_zero]

@[simp]

中文:
定理 map_eq_zero
  条件: {s : Multiset α} {f : α -> β}
  结论: s.map f = 0 ↔ s = 0
  证明: by
  rw [← Multiset.card_eq_zero]; rw [Multiset.card_map]; rw [Multiset.card_eq_zero]

@[simp]

Depends on / 依赖: Multiset, Multiset.card_eq_zero, Multiset.card_map, card_eq_zero, card_map
-/
theorem map_eq_zero {s : Multiset α} {f : α -> β} : s.map f = 0 ↔ s = 0 := by
  rw [← Multiset.card_eq_zero]; rw [Multiset.card_map]; rw [Multiset.card_eq_zero]

@[simp]
/--
theorem `zero_eq_map` / 定理 `zero_eq_map`

English:
theorem zero_eq_map
  given: {s : Multiset α} {f : α -> β}
  statement: 0 = s.map f ↔ s = 0
  proof: by
  rw [eq_comm]; rw [map_eq_zero]

中文:
定理 zero_eq_map
  条件: {s : Multiset α} {f : α -> β}
  结论: 0 = s.map f ↔ s = 0
  证明: by
  rw [eq_comm]; rw [map_eq_zero]

Depends on / 依赖: eq_comm, map_eq_zero
-/
theorem zero_eq_map {s : Multiset α} {f : α -> β} : 0 = s.map f ↔ s = 0 := by
  rw [eq_comm]; rw [map_eq_zero]

/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: (f : α -> β) {a : α} {s : Multiset α} (h : a in s)
  statement: f a in map f s
  proof: mem_map.2 ⟨_, h, rfl⟩

中文:
定理 mem_map_of_mem
  条件: (f : α -> β) {a : α} {s : Multiset α} (h : a in s)
  结论: f a in map f s
  证明: mem_map.2 ⟨_, h, rfl⟩

Depends on / 依赖: mem_map
-/
theorem mem_map_of_mem (f : α -> β) {a : α} {s : Multiset α} (h : a in s) : f a in map f s :=
  mem_map.2 ⟨_, h, rfl⟩

/--
theorem `map_eq_singleton` / 定理 `map_eq_singleton`

English:
theorem map_eq_singleton
  given: {f : α -> β} {s : Multiset α} {b : β}
  proof: by
  constructor
  · intro h
    obtain ⟨a, ha⟩ : exists a, s = {a} := by rw [← card_eq_one, ← card_map, h, card_singleton]
    refine ⟨a, ha, ?_⟩
    rw [← mem_singleton]; rw [← h]; rw [ha]; rw [map_singleton]; rw [mem_singleton]
  · rintro ⟨a, rfl, rfl⟩
    simp

中文:
定理 map_eq_singleton
  条件: {f : α -> β} {s : Multiset α} {b : β}
  证明: by
  constructor
  · intro h
    obtain ⟨a, ha⟩ : exists a, s = {a} := by rw [← card_eq_one, ← card_map, h, card_singleton]
    refine ⟨a, ha, ?_⟩
    rw [← mem_singleton]; rw [← h]; rw [ha]; rw [map_singleton]; rw [mem_singleton]
  · rintro ⟨a, rfl, rfl⟩
    simp

Depends on / 依赖: card_eq_one, card_map, card_singleton, map_singleton, mem_singleton
-/
theorem map_eq_singleton {f : α -> β} {s : Multiset α} {b : β} :
    map f s = {b} ↔ exists a : α, s = {a} ∧ f a = b := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ : exists a, s = {a} := by rw [← card_eq_one, ← card_map, h, card_singleton]
    refine ⟨a, ha, ?_⟩
    rw [← mem_singleton]; rw [← h]; rw [ha]; rw [map_singleton]; rw [mem_singleton]
  · rintro ⟨a, rfl, rfl⟩
    simp

/--
theorem `map_eq_cons` / 定理 `map_eq_cons`

English:
theorem map_eq_cons
  given: [DecidableEq α] (f : α -> β) (s : Multiset α) (t : Multiset β) (b : β)
  proof: by
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [← map_cons]; rw [Multiset.cons_erase ha]
  · intro h
    have : b in s.map f := by
      rw [h]
      exact mem_cons_self _ _
    obtain ⟨a, h1, rfl⟩ := mem_map.mp this
    obtain ⟨u, rfl⟩ := exists_cons_of_mem h1
    rw [map_cons]; rw [cons_inj_right] at h
    refine ⟨a, mem_cons_self _ _, rfl, ?_⟩
    rw [Multiset.erase_cons_head]; rw [h]

@[simp 1100]

中文:
定理 map_eq_cons
  条件: [DecidableEq α] (f : α -> β) (s : Multiset α) (t : Multiset β) (b : β)
  证明: by
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [← map_cons]; rw [Multiset.cons_erase ha]
  · intro h
    have : b in s.map f := by
      rw [h]
      exact mem_cons_self _ _
    obtain ⟨a, h1, rfl⟩ := mem_map.mp this
    obtain ⟨u, rfl⟩ := exists_cons_of_mem h1
    rw [map_cons]; rw [cons_inj_right] at h
    refine ⟨a, mem_cons_self _ _, rfl, ?_⟩
    rw [Multiset.erase_cons_head]; rw [h]

@[simp 1100]

Depends on / 依赖: Multiset, Multiset.cons_erase, Multiset.erase_cons_head, cons_erase, cons_inj_right, erase_cons_head, exists_cons_of_mem, map_cons, mem_cons_self, mem_map, mem_map.mp, s.map
-/
theorem map_eq_cons [DecidableEq α] (f : α -> β) (s : Multiset α) (t : Multiset β) (b : β) :
    (exists a in s, f a = b ∧ (s.erase a).map f = t) ↔ s.map f = b ::ₘ t := by
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [← map_cons]; rw [Multiset.cons_erase ha]
  · intro h
    have : b in s.map f := by
      rw [h]
      exact mem_cons_self _ _
    obtain ⟨a, h1, rfl⟩ := mem_map.mp this
    obtain ⟨u, rfl⟩ := exists_cons_of_mem h1
    rw [map_cons]; rw [cons_inj_right] at h
    refine ⟨a, mem_cons_self _ _, rfl, ?_⟩
    rw [Multiset.erase_cons_head]; rw [h]

@[simp 1100]
/--
theorem `mem_map_of_injective` / 定理 `mem_map_of_injective`

English:
theorem mem_map_of_injective
  given: {f : α -> β} (H : Function.Injective f) {a : α} {s : Multiset α}
  proof: Quot.inductionOn s fun _l => List.mem_map_of_injective H

@[simp]

中文:
定理 mem_map_of_injective
  条件: {f : α -> β} (H : 函数.单射 f) {a : α} {s : Multiset α}
  证明: Quot.inductionOn s fun _l => List.mem_map_of_injective H

@[simp]

Depends on / 依赖: List.mem_map_of_injective, Quot.inductionOn, inductionOn, mem_map_of_injective
-/
theorem mem_map_of_injective {f : α -> β} (H : Function.Injective f) {a : α} {s : Multiset α} :
    f a in map f s ↔ a in s :=
  Quot.inductionOn s fun _l => List.mem_map_of_injective H

@[simp]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β -> γ) (f : α -> β) (s : Multiset α)
  statement: map g (map f s) = map (g ∘ f) s
  proof: Quot.inductionOn s fun _l => congr_arg _ List.map_map

中文:
定理 map_map
  条件: (g : β -> γ) (f : α -> β) (s : Multiset α)
  结论: map g (map f s) = map (g ∘ f) s
  证明: Quot.inductionOn s fun _l => congr_arg _ List.map_map

Depends on / 依赖: List.map_map, Quot.inductionOn, congr_arg, inductionOn, map_map
-/
theorem map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : map g (map f s) = map (g ∘ f) s :=
  Quot.inductionOn s fun _l => congr_arg _ List.map_map

/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  given: (s : Multiset α)
  statement: map id s = s
  proof: Quot.inductionOn s fun _l => congr_arg _ List.map_id _

@[simp]

中文:
定理 map_id
  条件: (s : Multiset α)
  结论: map id s = s
  证明: Quot.inductionOn s fun _l => congr_arg _ List.map_id _

@[simp]

Depends on / 依赖: List.map_id, Quot.inductionOn, congr_arg, inductionOn, map_id
-/
theorem map_id (s : Multiset α) : map id s = s :=
Quot.inductionOn s fun _l => congr_arg _ List.map_id _

@[simp]
/--
theorem `map_id'` / 定理 `map_id'`

English:
theorem map_id'
  given: (s : Multiset α)
  statement: map (fun x => x) s = s
  proof: map_id s

中文:
定理 map_id'
  条件: (s : Multiset α)
  结论: map (fun x => x) s = s
  证明: map_id s

Depends on / 依赖: map_id
-/
theorem map_id' (s : Multiset α) : map (fun x => x) s = s :=
  map_id s

-- `simp`-normal form lemma is `map_const'`
/--
theorem `map_const` / 定理 `map_const`

English:
theorem map_const
  given: (s : Multiset α) (b : β)
  statement: map (const α b) s = replicate (card s) b
  proof: Quot.inductionOn s fun _ => congr_arg _ List.map_const'

中文:
定理 map_const
  条件: (s : Multiset α) (b : β)
  结论: map (const α b) s = replicate (card s) b
  证明: Quot.inductionOn s fun _ => congr_arg _ List.map_const'

Depends on / 依赖: List.map_const, Quot.inductionOn, congr_arg, inductionOn, map_const
-/
theorem map_const (s : Multiset α) (b : β) : map (const α b) s = replicate (card s) b :=
  Quot.inductionOn s fun _ => congr_arg _ List.map_const'

/--
theorem `map_const'` / 定理 `map_const'`

English:
theorem map_const'
  given: (s : Multiset α) (b : β)
  statement: map (fun _ => b) s = replicate (card s) b
  proof: map_const _ _

中文:
定理 map_const'
  条件: (s : Multiset α) (b : β)
  结论: map (fun _ => b) s = replicate (card s) b
  证明: map_const _ _
-/
@[simp] theorem map_const' (s : Multiset α) (b : β) : map (fun _ => b) s = replicate (card s) b :=
  map_const _ _

/--
theorem `eq_of_mem_map_const` / 定理 `eq_of_mem_map_const`

English:
theorem eq_of_mem_map_const
  given: {b₁ b₂ : β} {l : List α} (h : b₁ in map (Function.const α b₂) l)
  proof: eq_of_mem_replicate (n := card (l : Multiset α)) by rwa [map_const] at h

@[simp, gcongr]

中文:
定理 eq_of_mem_map_const
  条件: {b₁ b₂ : β} {l : 列表 α} (h : b₁ in map (函数.const α b₂) l)
  证明: eq_of_mem_replicate (n := card (l : Multiset α)) by rwa [map_const] at h

@[simp, gcongr]

Depends on / 依赖: Multiset, eq_of_mem_replicate, map_const
-/
theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ in map (Function.const α b₂) l) :
    b₁ = b₂ :=
eq_of_mem_replicate (n := card (l : Multiset α)) by rwa [map_const] at h

@[simp, gcongr]
/--
theorem `map_le_map` / 定理 `map_le_map`

English:
theorem map_le_map
  given: {f : α -> β} {s t : Multiset α} (h : s <= t)
  statement: map f s <= map f t
  proof: leInductionOn h fun h => (h.map f).subperm

@[simp, gcongr]

中文:
定理 map_le_map
  条件: {f : α -> β} {s t : Multiset α} (h : s <= t)
  结论: map f s <= map f t
  证明: leInductionOn h fun h => (h.map f).subperm

@[simp, gcongr]

Depends on / 依赖: h.map, leInductionOn, subperm
-/
theorem map_le_map {f : α -> β} {s t : Multiset α} (h : s <= t) : map f s <= map f t :=
  leInductionOn h fun h => (h.map f).subperm

@[simp, gcongr]
/--
theorem `map_lt_map` / 定理 `map_lt_map`

English:
theorem map_lt_map
  given: {f : α -> β} {s t : Multiset α} (h : s < t)
  statement: s.map f < t.map f
  proof: by
refine (map_le_map h.le).lt_of_not_ge fun H => h.ne eq_of_le_of_card_le h.le ?_
  rw [← s.card_map f]; rw [← t.card_map f]
  exact card_le_card H

@[gcongr]

中文:
定理 map_lt_map
  条件: {f : α -> β} {s t : Multiset α} (h : s < t)
  结论: s.map f < t.map f
  证明: by
refine (map_le_map h.le).lt_of_not_ge fun H => h.ne eq_of_le_of_card_le h.le ?_
  rw [← s.card_map f]; rw [← t.card_map f]
  exact card_le_card H

@[gcongr]

Depends on / 依赖: card_le_card, card_map, eq_of_le_of_card_le, h.le, h.ne, lt_of_not_ge, map_le_map, s.card_map, t.card_map
-/
theorem map_lt_map {f : α -> β} {s t : Multiset α} (h : s < t) : s.map f < t.map f := by
refine (map_le_map h.le).lt_of_not_ge fun H => h.ne eq_of_le_of_card_le h.le ?_
  rw [← s.card_map f]; rw [← t.card_map f]
  exact card_le_card H

@[gcongr]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: (f : α -> β)
  statement: Monotone (map f)
  proof: fun _ _ => map_le_map

@[gcongr]

中文:
定理 map_mono
  条件: (f : α -> β)
  结论: 递增 (map f)
  证明: fun _ _ => map_le_map

@[gcongr]

Depends on / 依赖: map_le_map
-/
theorem map_mono (f : α -> β) : Monotone (map f) := fun _ _ => map_le_map

@[gcongr]
/--
theorem `map_strictMono` / 定理 `map_strictMono`

English:
theorem map_strictMono
  given: (f : α -> β)
  statement: StrictMono (map f)
  proof: fun _ _ => map_lt_map

@[simp, gcongr]

中文:
定理 map_strictMono
  条件: (f : α -> β)
  结论: 严格递增 (map f)
  证明: fun _ _ => map_lt_map

@[simp, gcongr]

Depends on / 依赖: map_lt_map
-/
theorem map_strictMono (f : α -> β) : StrictMono (map f) := fun _ _ => map_lt_map

@[simp, gcongr]
/--
theorem `map_subset_map` / 定理 `map_subset_map`

English:
theorem map_subset_map
  given: {f : α -> β} {s t : Multiset α} (H : s subseteq t)
  statement: map f s subseteq map f t
  proof: fun _b m =>
  let ⟨a, h, e⟩ := mem_map.1 m
  mem_map.2 ⟨a, H h, e⟩

中文:
定理 map_subset_map
  条件: {f : α -> β} {s t : Multiset α} (H : s subseteq t)
  结论: map f s subseteq map f t
  证明: fun _b m =>
  let ⟨a, h, e⟩ := mem_map.1 m
  mem_map.2 ⟨a, H h, e⟩
-/
theorem map_subset_map {f : α -> β} {s t : Multiset α} (H : s subseteq t) : map f s subseteq map f t := fun _b m =>
  let ⟨a, h, e⟩ := mem_map.1 m
  mem_map.2 ⟨a, H h, e⟩

/--
theorem `map_erase` / 定理 `map_erase`

English:
theorem map_erase
  statement: [DecidableEq α] [DecidableEq β] (f : α -> β) (hf : Function.Injective f) (x : α)
  proof: by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  by_cases hxy : y = x
  · cases hxy
    simp
  · rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tail (hf.ne hxy), ih]

中文:
定理 map_erase
  结论: [DecidableEq α] [DecidableEq β] (f : α -> β) (hf : 函数.单射 f) (x : α)
  证明: by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  by_cases hxy : y = x
  · cases hxy
    simp
  · rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tail (hf.ne hxy), ih]

Depends on / 依赖: Multiset, Multiset.induction_on, erase_cons_tail, hf.ne, induction_on, map_cons, s.erase_cons_tail, s.map
-/
theorem map_erase [DecidableEq α] [DecidableEq β] (f : α -> β) (hf : Function.Injective f) (x : α)
    (s : Multiset α) : (s.erase x).map f = (s.map f).erase (f x) := by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  by_cases hxy : y = x
  · cases hxy
    simp
  · rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tail (hf.ne hxy), ih]

/--
theorem `map_erase_of_mem` / 定理 `map_erase_of_mem`

English:
theorem map_erase_of_mem
  statement: [DecidableEq α] [DecidableEq β] (f : α -> β)
  proof: by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  rcases eq_or_ne y x with rfl | hxy
  · simp
  replace h : x in s := by simpa [hxy.symm] using h
  rw [s.erase_cons_tail hxy]; rw [map_cons]; rw [map_cons]; rw [ih h]; rw [erase_cons_tail_of_mem (mem_map_of_mem f h)]

中文:
定理 map_erase_of_mem
  结论: [DecidableEq α] [DecidableEq β] (f : α -> β)
  证明: by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  rcases eq_or_ne y x with rfl | hxy
  · simp
  replace h : x in s := by simpa [hxy.symm] using h
  rw [s.erase_cons_tail hxy]; rw [map_cons]; rw [map_cons]; rw [ih h]; rw [erase_cons_tail_of_mem (mem_map_of_mem f h)]

Depends on / 依赖: Multiset, Multiset.induction_on, eq_or_ne, erase_cons_tail, erase_cons_tail_of_mem, hxy.symm, induction_on, map_cons, mem_map_of_mem, replace, s.erase_cons_tail
-/
theorem map_erase_of_mem [DecidableEq α] [DecidableEq β] (f : α -> β)
    (s : Multiset α) {x : α} (h : x in s) : (s.erase x).map f = (s.map f).erase (f x) := by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  rcases eq_or_ne y x with rfl | hxy
  · simp
  replace h : x in s := by simpa [hxy.symm] using h
  rw [s.erase_cons_tail hxy]; rw [map_cons]; rw [map_cons]; rw [ih h]; rw [erase_cons_tail_of_mem (mem_map_of_mem f h)]

/--
theorem `map_surjective_of_surjective` / 定理 `map_surjective_of_surjective`

English:
theorem map_surjective_of_surjective
  given: {f : α -> β} (hf : Function.Surjective f)
  proof: by
  intro s
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, map_zero _⟩
  | cons x s ih =>
    obtain ⟨y, rfl⟩ := hf x
    obtain ⟨t, rfl⟩ := ih
    exact ⟨y ::ₘ t, map_cons _ _ _⟩

中文:
定理 map_surjective_of_surjective
  条件: {f : α -> β} (hf : 函数.满射 f)
  证明: by
  intro s
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, map_zero _⟩
  | cons x s ih =>
    obtain ⟨y, rfl⟩ := hf x
    obtain ⟨t, rfl⟩ := ih
    exact ⟨y ::ₘ t, map_cons _ _ _⟩

Depends on / 依赖: Multiset, Multiset.induction_on, induction_on, map_cons, map_zero
-/
theorem map_surjective_of_surjective {f : α -> β} (hf : Function.Surjective f) :
    Function.Surjective (map f) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, map_zero _⟩
  | cons x s ih =>
    obtain ⟨y, rfl⟩ := hf x
    obtain ⟨t, rfl⟩ := ih
    exact ⟨y ::ₘ t, map_cons _ _ _⟩

/-! ### `Multiset.fold` -/


section foldl

/--
Definition of `foldl` / `foldl` 的定义

English:
definition foldl
  signature: (f : β -> α -> β) [RightCommutative f] (b : β) (s : Multiset α)
  body: Quot.liftOn s (fun l => List.foldl f b l) fun _l₁ _l₂ p => p.foldl_eq b

中文:
定义 foldl
  签名: (f : β -> α -> β) [右交换 f] (b : β) (s : Multiset α)
  定义体: Quot.liftOn s (fun l => List.foldl f b l) fun _l₁ _l₂ p => p.foldl_eq b

Depends on / 依赖: List.foldl, Quot.liftOn, foldl_eq, liftOn, p.foldl_eq
-/
def foldl (f : β -> α -> β) [RightCommutative f] (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => List.foldl f b l) fun _l₁ _l₂ p => p.foldl_eq b

variable (f : β -> α -> β) [RightCommutative f]

@[simp]
/--
theorem `foldl_zero` / 定理 `foldl_zero`

English:
theorem foldl_zero
  given: (b)
  statement: foldl f b 0 = b
  proof: rfl

@[simp]

中文:
定理 foldl_zero
  条件: (b)
  结论: foldl f b 0 = b
  证明: rfl

@[simp]
-/
theorem foldl_zero (b) : foldl f b 0 = b :=
  rfl

@[simp]
/--
theorem `foldl_cons` / 定理 `foldl_cons`

English:
theorem foldl_cons
  given: (b a s)
  statement: foldl f b (a ::ₘ s) = foldl f (f b a) s
  proof: Quot.inductionOn s fun _l => rfl

@[simp]

中文:
定理 foldl_cons
  条件: (b a s)
  结论: foldl f b (a ::ₘ s) = foldl f (f b a) s
  证明: Quot.inductionOn s fun _l => rfl

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem foldl_cons (b a s) : foldl f b (a ::ₘ s) = foldl f (f b a) s :=
  Quot.inductionOn s fun _l => rfl

@[simp]
/--
theorem `foldl_add` / 定理 `foldl_add`

English:
theorem foldl_add
  given: (b s t)
  statement: foldl f b (s + t) = foldl f (foldl f b s) t
  proof: Quotient.inductionOn₂ s t fun _ _ => foldl_append

中文:
定理 foldl_add
  条件: (b s t)
  结论: foldl f b (s + t) = foldl f (foldl f b s) t
  证明: Quotient.inductionOn₂ s t fun _ _ => foldl_append

Depends on / 依赖: Quotient, Quotient.inductionOn, foldl_append
-/
theorem foldl_add (b s t) : foldl f b (s + t) = foldl f (foldl f b s) t :=
  Quotient.inductionOn₂ s t fun _ _ => foldl_append

end foldl

section foldr

/--
Definition of `foldr` / `foldr` 的定义

English:
definition foldr
  signature: (f : α -> β -> β) [LeftCommutative f] (b : β) (s : Multiset α)
  body: Quot.liftOn s (fun l => List.foldr f b l) fun _l₁ _l₂ p => p.foldr_eq b

中文:
定义 foldr
  签名: (f : α -> β -> β) [左交换 f] (b : β) (s : Multiset α)
  定义体: Quot.liftOn s (fun l => List.foldr f b l) fun _l₁ _l₂ p => p.foldr_eq b

Depends on / 依赖: List.foldr, Quot.liftOn, foldr_eq, liftOn, p.foldr_eq
-/
def foldr (f : α -> β -> β) [LeftCommutative f] (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => List.foldr f b l) fun _l₁ _l₂ p => p.foldr_eq b

variable (f : α -> β -> β) [LeftCommutative f]

@[simp]
/--
theorem `foldr_zero` / 定理 `foldr_zero`

English:
theorem foldr_zero
  given: (b)
  statement: foldr f b 0 = b
  proof: rfl

@[simp]

中文:
定理 foldr_zero
  条件: (b)
  结论: foldr f b 0 = b
  证明: rfl

@[simp]
-/
theorem foldr_zero (b) : foldr f b 0 = b :=
  rfl

@[simp]
/--
theorem `foldr_cons` / 定理 `foldr_cons`

English:
theorem foldr_cons
  given: (b a s)
  statement: foldr f b (a ::ₘ s) = f a (foldr f b s)
  proof: Quot.inductionOn s fun _l => rfl

@[simp]

中文:
定理 foldr_cons
  条件: (b a s)
  结论: foldr f b (a ::ₘ s) = f a (foldr f b s)
  证明: Quot.inductionOn s fun _l => rfl

@[simp]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
theorem foldr_cons (b a s) : foldr f b (a ::ₘ s) = f a (foldr f b s) :=
  Quot.inductionOn s fun _l => rfl

@[simp]
/--
theorem `foldr_singleton` / 定理 `foldr_singleton`

English:
theorem foldr_singleton
  given: (b a)
  statement: foldr f b ({a} : Multiset α) = f a b
  proof: rfl

@[simp]

中文:
定理 foldr_singleton
  条件: (b a)
  结论: foldr f b ({a} : Multiset α) = f a b
  证明: rfl

@[simp]
-/
theorem foldr_singleton (b a) : foldr f b ({a} : Multiset α) = f a b :=
  rfl

@[simp]
/--
theorem `foldr_add` / 定理 `foldr_add`

English:
theorem foldr_add
  given: (b s t)
  statement: foldr f b (s + t) = foldr f (foldr f b t) s
  proof: Quotient.inductionOn₂ s t fun _ _ => foldr_append

中文:
定理 foldr_add
  条件: (b s t)
  结论: foldr f b (s + t) = foldr f (foldr f b t) s
  证明: Quotient.inductionOn₂ s t fun _ _ => foldr_append

Depends on / 依赖: Quotient, Quotient.inductionOn, foldr_append
-/
theorem foldr_add (b s t) : foldr f b (s + t) = foldr f (foldr f b t) s :=
  Quotient.inductionOn₂ s t fun _ _ => foldr_append

end foldr

@[simp]
/--
theorem `coe_foldr` / 定理 `coe_foldr`

English:
theorem coe_foldr
  given: (f : α -> β -> β) [LeftCommutative f] (b : β) (l : List α)
  proof: rfl

@[simp]

中文:
定理 coe_foldr
  条件: (f : α -> β -> β) [左交换 f] (b : β) (l : 列表 α)
  证明: rfl

@[simp]
-/
theorem coe_foldr (f : α -> β -> β) [LeftCommutative f] (b : β) (l : List α) :
    foldr f b l = l.foldr f b :=
  rfl

@[simp]
/--
theorem `coe_foldl` / 定理 `coe_foldl`

English:
theorem coe_foldl
  given: (f : β -> α -> β) [RightCommutative f] (b : β) (l : List α)
  proof: rfl

中文:
定理 coe_foldl
  条件: (f : β -> α -> β) [右交换 f] (b : β) (l : 列表 α)
  证明: rfl
-/
theorem coe_foldl (f : β -> α -> β) [RightCommutative f] (b : β) (l : List α) :
    foldl f b l = l.foldl f b :=
  rfl

/--
theorem `coe_foldr_swap` / 定理 `coe_foldr_swap`

English:
theorem coe_foldr_swap
  given: (f : α -> β -> β) [LeftCommutative f] (b : β) (l : List α)
  proof: (congr_arg (foldr f b) (coe_reverse l)).symm.trans foldr_reverse

中文:
定理 coe_foldr_swap
  条件: (f : α -> β -> β) [左交换 f] (b : β) (l : 列表 α)
  证明: (congr_arg (foldr f b) (coe_reverse l)).symm.trans foldr_reverse

Depends on / 依赖: coe_reverse, congr_arg, foldr_reverse, symm.trans
-/
theorem coe_foldr_swap (f : α -> β -> β) [LeftCommutative f] (b : β) (l : List α) :
    foldr f b l = l.foldl (fun x y => f y x) b :=
  (congr_arg (foldr f b) (coe_reverse l)).symm.trans foldr_reverse

/--
theorem `foldr_swap` / 定理 `foldr_swap`

English:
theorem foldr_swap
  given: (f : α -> β -> β) [LeftCommutative f] (b : β) (s : Multiset α)
  proof: Quot.inductionOn s fun _l => coe_foldr_swap _ _ _

中文:
定理 foldr_swap
  条件: (f : α -> β -> β) [左交换 f] (b : β) (s : Multiset α)
  证明: Quot.inductionOn s fun _l => coe_foldr_swap _ _ _

Depends on / 依赖: Quot.inductionOn, coe_foldr_swap, inductionOn
-/
theorem foldr_swap (f : α -> β -> β) [LeftCommutative f] (b : β) (s : Multiset α) :
    foldr f b s = foldl (fun x y => f y x) b s :=
  Quot.inductionOn s fun _l => coe_foldr_swap _ _ _

/--
theorem `foldl_swap` / 定理 `foldl_swap`

English:
theorem foldl_swap
  given: (f : β -> α -> β) [RightCommutative f] (b : β) (s : Multiset α)
  proof: (foldr_swap _ _ _).symm

中文:
定理 foldl_swap
  条件: (f : β -> α -> β) [右交换 f] (b : β) (s : Multiset α)
  证明: (foldr_swap _ _ _).symm

Depends on / 依赖: foldr_swap
-/
theorem foldl_swap (f : β -> α -> β) [RightCommutative f] (b : β) (s : Multiset α) :
    foldl f b s = foldr (fun x y => f y x) b s :=
  (foldr_swap _ _ _).symm

/--
theorem `foldr_induction'` / 定理 `foldr_induction'`

English:
theorem foldr_induction'
  statement: (f : α -> β -> β) [LeftCommutative f] (x : β) (q : α -> Prop)
  proof: by
  induction s using Multiset.induction with
  | empty => simpa
  | cons a s ihs =>
    simp only [forall_mem_cons, foldr_cons] at q_s ⊢
    exact hpqf _ _ q_s.1 (ihs q_s.2)

中文:
定理 foldr_induction'
  结论: (f : α -> β -> β) [左交换 f] (x : β) (q : α -> 命题)
  证明: by
  induction s using Multiset.induction with
  | empty => simpa
  | cons a s ihs =>
    simp only [forall_mem_cons, foldr_cons] at q_s ⊢
    exact hpqf _ _ q_s.1 (ihs q_s.2)

Depends on / 依赖: Multiset, Multiset.induction, foldr_cons, forall_mem_cons
-/
theorem foldr_induction' (f : α -> β -> β) [LeftCommutative f] (x : β) (q : α -> Prop)
    (p : β -> Prop) (s : Multiset α) (hpqf : forall a b, q a -> p b -> p (f a b)) (px : p x)
    (q_s : forall a in s, q a) : p (foldr f x s) := by
  induction s using Multiset.induction with
  | empty => simpa
  | cons a s ihs =>
    simp only [forall_mem_cons, foldr_cons] at q_s ⊢
    exact hpqf _ _ q_s.1 (ihs q_s.2)

/--
theorem `foldr_induction` / 定理 `foldr_induction`

English:
theorem foldr_induction
  statement: (f : α -> α -> α) [LeftCommutative f] (x : α) (p : α -> Prop)
  proof: foldr_induction' f x p p s p_f px p_s

中文:
定理 foldr_induction
  结论: (f : α -> α -> α) [左交换 f] (x : α) (p : α -> 命题)
  证明: foldr_induction' f x p p s p_f px p_s

Depends on / 依赖: foldr_induction
-/
theorem foldr_induction (f : α -> α -> α) [LeftCommutative f] (x : α) (p : α -> Prop)
    (s : Multiset α) (p_f : forall a b, p a -> p b -> p (f a b)) (px : p x) (p_s : forall a in s, p a) :
    p (foldr f x s) :=
  foldr_induction' f x p p s p_f px p_s

/--
theorem `foldl_induction'` / 定理 `foldl_induction'`

English:
theorem foldl_induction'
  statement: (f : β -> α -> β) [RightCommutative f] (x : β) (q : α -> Prop)
  proof: by
  rw [foldl_swap]
  exact foldr_induction' (fun x y => f y x) x q p s hpqf px q_s

中文:
定理 foldl_induction'
  结论: (f : β -> α -> β) [右交换 f] (x : β) (q : α -> 命题)
  证明: by
  rw [foldl_swap]
  exact foldr_induction' (fun x y => f y x) x q p s hpqf px q_s

Depends on / 依赖: foldl_swap, foldr_induction
-/
theorem foldl_induction' (f : β -> α -> β) [RightCommutative f] (x : β) (q : α -> Prop)
    (p : β -> Prop) (s : Multiset α) (hpqf : forall a b, q a -> p b -> p (f b a)) (px : p x)
    (q_s : forall a in s, q a) : p (foldl f x s) := by
  rw [foldl_swap]
  exact foldr_induction' (fun x y => f y x) x q p s hpqf px q_s

/--
theorem `foldl_induction` / 定理 `foldl_induction`

English:
theorem foldl_induction
  statement: (f : α -> α -> α) [RightCommutative f] (x : α) (p : α -> Prop)
  proof: foldl_induction' f x p p s p_f px p_s

中文:
定理 foldl_induction
  结论: (f : α -> α -> α) [右交换 f] (x : α) (p : α -> 命题)
  证明: foldl_induction' f x p p s p_f px p_s

Depends on / 依赖: foldl_induction
-/
theorem foldl_induction (f : α -> α -> α) [RightCommutative f] (x : α) (p : α -> Prop)
    (s : Multiset α) (p_f : forall a b, p a -> p b -> p (f b a)) (px : p x) (p_s : forall a in s, p a) :
    p (foldl f x s) :=
  foldl_induction' f x p p s p_f px p_s


/--
theorem `pmap_eq_map` / 定理 `pmap_eq_map`

English:
theorem pmap_eq_map
  given: (p : α -> Prop) (f : α -> β) (s : Multiset α)
  proof: Quot.inductionOn s fun _ H => congr_arg _ List.pmap_eq_map H

中文:
定理 pmap_eq_map
  条件: (p : α -> 命题) (f : α -> β) (s : Multiset α)
  证明: Quot.inductionOn s fun _ H => congr_arg _ List.pmap_eq_map H

Depends on / 依赖: List.pmap_eq_map, Quot.inductionOn, congr_arg, inductionOn, pmap_eq_map
-/
theorem pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Multiset α) :
    forall H, @pmap _ _ p (fun a _ => f a) s H = map f s :=
Quot.inductionOn s fun _ H => congr_arg _ List.pmap_eq_map H

/--
theorem `map_pmap` / 定理 `map_pmap`

English:
theorem map_pmap
  given: {p : α -> Prop} (g : β -> γ) (f : forall a, p a -> β) (s)
  proof: Quot.inductionOn s fun _ H => congr_arg _ List.map_pmap H

中文:
定理 map_pmap
  条件: {p : α -> 命题} (g : β -> γ) (f : 对任意 a, p a -> β) (s)
  证明: Quot.inductionOn s fun _ H => congr_arg _ List.map_pmap H

Depends on / 依赖: List.map_pmap, Quot.inductionOn, congr_arg, inductionOn, map_pmap
-/
theorem map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, p a -> β) (s) :
    forall H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H :=
Quot.inductionOn s fun _ H => congr_arg _ List.map_pmap H

/--
theorem `pmap_eq_map_attach` / 定理 `pmap_eq_map_attach`

English:
theorem pmap_eq_map_attach
  given: {p : α -> Prop} (f : forall a, p a -> β) (s)
  proof: Quot.inductionOn s fun _ H => congr_arg _ List.pmap_eq_map_attach H

@[simp]

中文:
定理 pmap_eq_map_attach
  条件: {p : α -> 命题} (f : 对任意 a, p a -> β) (s)
  证明: Quot.inductionOn s fun _ H => congr_arg _ List.pmap_eq_map_attach H

@[simp]

Depends on / 依赖: List.pmap_eq_map_attach, Quot.inductionOn, congr_arg, inductionOn, pmap_eq_map_attach
-/
theorem pmap_eq_map_attach {p : α -> Prop} (f : forall a, p a -> β) (s) :
    forall H, pmap f s H = s.attach.map fun x => f x.1 (H _ x.2) :=
Quot.inductionOn s fun _ H => congr_arg _ List.pmap_eq_map_attach H

@[simp]
/--
theorem `attach_map_val'` / 定理 `attach_map_val'`

English:
theorem attach_map_val'
  given: (s : Multiset α) (f : α -> β)
  statement: (s.attach.map fun i => f i.val) = s.map f
  proof: Quot.inductionOn s fun _ => congr_arg _ List.attach_map_val

@[simp]

中文:
定理 attach_map_val'
  条件: (s : Multiset α) (f : α -> β)
  结论: (s.attach.map fun i => f i.val) = s.map f
  证明: Quot.inductionOn s fun _ => congr_arg _ List.attach_map_val

@[simp]

Depends on / 依赖: List.attach_map_val, Quot.inductionOn, attach_map_val, congr_arg, inductionOn
-/
theorem attach_map_val' (s : Multiset α) (f : α -> β) : (s.attach.map fun i => f i.val) = s.map f :=
  Quot.inductionOn s fun _ => congr_arg _ List.attach_map_val

@[simp]
/--
theorem `attach_map_val` / 定理 `attach_map_val`

English:
theorem attach_map_val
  given: (s : Multiset α)
  statement: s.attach.map Subtype.val = s
  proof: (attach_map_val' _ _).trans s.map_id

中文:
定理 attach_map_val
  条件: (s : Multiset α)
  结论: s.attach.map 子类型.val = s
  证明: (attach_map_val' _ _).trans s.map_id

Depends on / 依赖: attach_map_val, map_id, s.map_id
-/
theorem attach_map_val (s : Multiset α) : s.attach.map Subtype.val = s :=
  (attach_map_val' _ _).trans s.map_id

set_option backward.isDefEq.respectTransparency false in
/--
theorem `attach_cons` / 定理 `attach_cons`

English:
theorem attach_cons
  given: (a : α) (m : Multiset α)
  proof: Quotient.inductionOn m fun l =>
congr_arg _
congr_arg (List.cons _) by
        rw [List.map_pmap]; exact List.pmap_congr_left _ fun _ _ _ _ => Subtype.ext rfl

中文:
定理 attach_cons
  条件: (a : α) (m : Multiset α)
  证明: Quotient.inductionOn m fun l =>
congr_arg _
congr_arg (List.cons _) by
        rw [List.map_pmap]; exact List.pmap_congr_left _ fun _ _ _ _ => Subtype.ext rfl

Depends on / 依赖: List.cons, List.map_pmap, List.pmap_congr_left, Quotient, Quotient.inductionOn, Subtype, Subtype.ext, congr_arg, inductionOn, map_pmap, pmap_congr_left
-/
theorem attach_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).attach =
      ⟨a, mem_cons_self a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p.2⟩ :=
  Quotient.inductionOn m fun l =>
congr_arg _
congr_arg (List.cons _) by
        rw [List.map_pmap]; exact List.pmap_congr_left _ fun _ _ _ _ => Subtype.ext rfl

section

variable [DecidableEq α] {s t u : Multiset α}

/--
lemma `erase_attach_map_val` / 引理 `erase_attach_map_val`

English:
lemma erase_attach_map_val
  given: (s : Multiset α) (x : {x // x in s})
  proof: by
  rw [Multiset.map_erase _ val_injective]; rw [attach_map_val]

中文:
引理 erase_attach_map_val
  条件: (s : Multiset α) (x : {x // x in s})
  证明: by
  rw [Multiset.map_erase _ val_injective]; rw [attach_map_val]

Depends on / 依赖: Multiset, Multiset.map_erase, attach_map_val, map_erase, val_injective
-/
lemma erase_attach_map_val (s : Multiset α) (x : {x // x in s}) :
    (s.attach.erase x).map (↑) = s.erase x := by
  rw [Multiset.map_erase _ val_injective]; rw [attach_map_val]

/--
lemma `erase_attach_map` / 引理 `erase_attach_map`

English:
lemma erase_attach_map
  given: (s : Multiset α) (f : α -> β) (x : {x // x in s})
  proof: by
  simp only [← Function.comp_apply (f := f)]
  rw [← map_map]; rw [erase_attach_map_val]

中文:
引理 erase_attach_map
  条件: (s : Multiset α) (f : α -> β) (x : {x // x in s})
  证明: by
  simp only [← Function.comp_apply (f := f)]
  rw [← map_map]; rw [erase_attach_map_val]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, erase_attach_map_val, map_map
-/
lemma erase_attach_map (s : Multiset α) (f : α -> β) (x : {x // x in s}) :
    (s.attach.erase x).map (fun j : {x // x in s} => f j) = (s.erase x).map f := by
  simp only [← Function.comp_apply (f := f)]
  rw [← map_map]; rw [erase_attach_map_val]

end

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/--
lemma `sub_eq_fold_erase` / 引理 `sub_eq_fold_erase`

English:
lemma sub_eq_fold_erase
  given: (s t : Multiset α)
  statement: s - t = foldl erase s t
  proof: Quotient.inductionOn₂ s t fun l₁ l₂ => by
    change ofList (l₁.diff l₂) = foldl erase l₁ l₂
    rw [diff_eq_foldl l₁ l₂]
    symm
    exact foldl_hom _ fun x y => rfl

中文:
引理 sub_eq_fold_erase
  条件: (s t : Multiset α)
  结论: s - t = foldl erase s t
  证明: Quotient.inductionOn₂ s t fun l₁ l₂ => by
    change ofList (l₁.diff l₂) = foldl erase l₁ l₂
    rw [diff_eq_foldl l₁ l₂]
    symm
    exact foldl_hom _ fun x y => rfl

Depends on / 依赖: Quotient, Quotient.inductionOn, diff_eq_foldl, foldl_hom, ofList
-/
lemma sub_eq_fold_erase (s t : Multiset α) : s - t = foldl erase s t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by
    change ofList (l₁.diff l₂) = foldl erase l₁ l₂
    rw [diff_eq_foldl l₁ l₂]
    symm
    exact foldl_hom _ fun x y => rfl

end sub

/-! ### Lift a relation to `Multiset`s -/


section Rel

variable {δ : Type*} {r : α -> β -> Prop} {p : γ -> δ -> Prop}

/--
theorem `rel_map_left` / 定理 `rel_map_left`

English:
theorem rel_map_left
  given: {s : Multiset γ} {f : γ -> α}
  proof: @(Multiset.induction_on s (by simp) (by simp +contextual [rel_cons_left]))

中文:
定理 rel_map_left
  条件: {s : Multiset γ} {f : γ -> α}
  证明: @(Multiset.induction_on s (by simp) (by simp +contextual [rel_cons_left]))

Depends on / 依赖: Multiset, Multiset.induction_on, contextual, induction_on, rel_cons_left
-/
theorem rel_map_left {s : Multiset γ} {f : γ -> α} :
    forall {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t :=
  @(Multiset.induction_on s (by simp) (by simp +contextual [rel_cons_left]))

/--
theorem `rel_map_right` / 定理 `rel_map_right`

English:
theorem rel_map_right
  given: {s : Multiset α} {t : Multiset γ} {f : γ -> β}
  proof: by
  rw [← rel_flip]; rw [rel_map_left]; rw [← rel_flip]; rfl

中文:
定理 rel_map_right
  条件: {s : Multiset α} {t : Multiset γ} {f : γ -> β}
  证明: by
  rw [← rel_flip]; rw [rel_map_left]; rw [← rel_flip]; rfl

Depends on / 依赖: rel_flip, rel_map_left
-/
theorem rel_map_right {s : Multiset α} {t : Multiset γ} {f : γ -> β} :
    Rel r s (t.map f) ↔ Rel (fun a b => r a (f b)) s t := by
  rw [← rel_flip]; rw [rel_map_left]; rw [← rel_flip]; rfl

/--
theorem `rel_map` / 定理 `rel_map`

English:
theorem rel_map
  given: {s : Multiset α} {t : Multiset β} {f : α -> γ} {g : β -> δ}
  proof: rel_map_left.trans rel_map_right

中文:
定理 rel_map
  条件: {s : Multiset α} {t : Multiset β} {f : α -> γ} {g : β -> δ}
  证明: rel_map_left.trans rel_map_right

Depends on / 依赖: rel_map_left, rel_map_left.trans, rel_map_right
-/
theorem rel_map {s : Multiset α} {t : Multiset β} {f : α -> γ} {g : β -> δ} :
    Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t :=
  rel_map_left.trans rel_map_right

end Rel

section Map

/--
theorem `map_eq_map` / 定理 `map_eq_map`

English:
theorem map_eq_map
  given: {f : α -> β} (hf : Function.Injective f) {s t : Multiset α}
  proof: by
  rw [← rel_eq]; rw [← rel_eq]; rw [rel_map]
  simp only [hf.eq_iff]

中文:
定理 map_eq_map
  条件: {f : α -> β} (hf : 函数.单射 f) {s t : Multiset α}
  证明: by
  rw [← rel_eq]; rw [← rel_eq]; rw [rel_map]
  simp only [hf.eq_iff]

Depends on / 依赖: eq_iff, hf.eq_iff, rel_eq, rel_map
-/
theorem map_eq_map {f : α -> β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f = t.map f ↔ s = t := by
  rw [← rel_eq]; rw [← rel_eq]; rw [rel_map]
  simp only [hf.eq_iff]

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: {f : α -> β} (hf : Function.Injective f)
  proof: fun _x _y => (map_eq_map hf).1

中文:
定理 map_injective
  条件: {f : α -> β} (hf : 函数.单射 f)
  证明: fun _x _y => (map_eq_map hf).1

Depends on / 依赖: map_eq_map
-/
theorem map_injective {f : α -> β} (hf : Function.Injective f) :
    Function.Injective (Multiset.map f) := fun _x _y => (map_eq_map hf).1

end Map

section Quot

/--
theorem `map_mk_eq_map_mk_of_rel` / 定理 `map_mk_eq_map_mk_of_rel`

English:
theorem map_mk_eq_map_mk_of_rel
  given: {r : α -> α -> Prop} {s t : Multiset α} (hst : s.Rel r t)
  proof: Rel.recOn hst rfl fun hab _hst ih => by simp [ih, Quot.sound hab]

中文:
定理 map_mk_eq_map_mk_of_rel
  条件: {r : α -> α -> 命题} {s t : Multiset α} (hst : s.关系 r t)
  证明: Rel.recOn hst rfl fun hab _hst ih => by simp [ih, Quot.sound hab]

Depends on / 依赖: Quot.sound, Rel.recOn, _hst
-/
theorem map_mk_eq_map_mk_of_rel {r : α -> α -> Prop} {s t : Multiset α} (hst : s.Rel r t) :
    s.map (Quot.mk r) = t.map (Quot.mk r) :=
  Rel.recOn hst rfl fun hab _hst ih => by simp [ih, Quot.sound hab]

/--
theorem `exists_multiset_eq_map_quot_mk` / 定理 `exists_multiset_eq_map_quot_mk`

English:
theorem exists_multiset_eq_map_quot_mk
  given: {r : α -> α -> Prop} (s : Multiset (Quot r))
  proof: Multiset.induction_on s ⟨0, rfl⟩ fun a _s ⟨t, ht⟩ =>
    Quot.inductionOn a fun a => ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩

中文:
定理 存在_multiset_eq_map_quot_mk
  条件: {r : α -> α -> 命题} (s : Multiset (商 r))
  证明: Multiset.induction_on s ⟨0, rfl⟩ fun a _s ⟨t, ht⟩ =>
    Quot.inductionOn a fun a => ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩

Depends on / 依赖: Multiset, Multiset.induction_on, Quot.inductionOn, ht.symm, inductionOn, induction_on, map_cons
-/
theorem exists_multiset_eq_map_quot_mk {r : α -> α -> Prop} (s : Multiset (Quot r)) :
    exists t : Multiset α, s = t.map (Quot.mk r) :=
  Multiset.induction_on s ⟨0, rfl⟩ fun a _s ⟨t, ht⟩ =>
    Quot.inductionOn a fun a => ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩

/--
theorem `induction_on_multiset_quot` / 定理 `induction_on_multiset_quot`

English:
theorem induction_on_multiset_quot
  statement: {r : α -> α -> Prop} {p : Multiset (Quot r) -> Prop}
  proof: match s, exists_multiset_eq_map_quot_mk s with
  | _, ⟨_t, rfl⟩ => fun h => h _

中文:
定理 induction_on_multiset_quot
  结论: {r : α -> α -> 命题} {p : Multiset (商 r) -> 命题}
  证明: match s, exists_multiset_eq_map_quot_mk s with
  | _, ⟨_t, rfl⟩ => fun h => h _

Depends on / 依赖: exists_multiset_eq_map_quot_mk
-/
theorem induction_on_multiset_quot {r : α -> α -> Prop} {p : Multiset (Quot r) -> Prop}
    (s : Multiset (Quot r)) : (forall s : Multiset α, p (s.map (Quot.mk r))) -> p s :=
  match s, exists_multiset_eq_map_quot_mk s with
  | _, ⟨_t, rfl⟩ => fun h => h _

end Quot

section Nodup

variable {s : Multiset α}

/--
theorem `Nodup.of_map` / 定理 `Nodup.of_map`

English:
theorem Nodup.of_map
  given: (f : α -> β)
  statement: Nodup (map f s) -> Nodup s
  proof: Quot.induction_on s fun _ => List.Nodup.of_map f

中文:
定理 Nodup.of_map
  条件: (f : α -> β)
  结论: Nodup (map f s) -> Nodup s
  证明: Quot.induction_on s fun _ => List.Nodup.of_map f
-/
theorem Nodup.of_map (f : α -> β) : Nodup (map f s) -> Nodup s :=
  Quot.induction_on s fun _ => List.Nodup.of_map f

/--
theorem `Nodup.map_on` / 定理 `Nodup.map_on`

English:
theorem Nodup.map_on
  given: {f : α -> β}
  proof: Quot.induction_on s fun _ => List.Nodup.map_on

中文:
定理 Nodup.map_on
  条件: {f : α -> β}
  证明: Quot.induction_on s fun _ => List.Nodup.map_on
-/
theorem Nodup.map_on {f : α -> β} :
    (forall x in s, forall y in s, f x = f y -> x = y) -> Nodup s -> Nodup (map f s) :=
  Quot.induction_on s fun _ => List.Nodup.map_on

/--
theorem `Nodup.map` / 定理 `Nodup.map`

English:
theorem Nodup.map
  given: {f : α -> β} {s : Multiset α} (hf : Injective f)
  statement: Nodup s -> Nodup (map f s)
  proof: Nodup.map_on fun _ _ _ _ h => hf h

中文:
定理 Nodup.map
  条件: {f : α -> β} {s : Multiset α} (hf : 单射 f)
  结论: Nodup s -> Nodup (map f s)
  证明: Nodup.map_on fun _ _ _ _ h => hf h

Depends on / 依赖: Nodup.map_on, map_on
-/
theorem Nodup.map {f : α -> β} {s : Multiset α} (hf : Injective f) : Nodup s -> Nodup (map f s) :=
  Nodup.map_on fun _ _ _ _ h => hf h

/--
theorem `nodup_map_iff_of_inj_on` / 定理 `nodup_map_iff_of_inj_on`

English:
theorem nodup_map_iff_of_inj_on
  given: {f : α -> β} (d : forall x in s, forall y in s, f x = f y -> x = y)
  proof: ⟨Nodup.of_map _, fun h => h.map_on d⟩

中文:
定理 nodup_map_iff_of_inj_on
  条件: {f : α -> β} (d : 对任意 x in s, 对任意 y in s, f x = f y -> x = y)
  证明: ⟨Nodup.of_map _, fun h => h.map_on d⟩

Depends on / 依赖: Nodup.of_map, h.map_on, map_on, of_map
-/
theorem nodup_map_iff_of_inj_on {f : α -> β} (d : forall x in s, forall y in s, f x = f y -> x = y) :
    Nodup (map f s) ↔ Nodup s :=
  ⟨Nodup.of_map _, fun h => h.map_on d⟩

/--
theorem `nodup_map_iff_of_injective` / 定理 `nodup_map_iff_of_injective`

English:
theorem nodup_map_iff_of_injective
  given: {f : α -> β} (d : Function.Injective f)
  proof: ⟨Nodup.of_map _, fun h => h.map d⟩

中文:
定理 nodup_map_iff_of_injective
  条件: {f : α -> β} (d : 函数.单射 f)
  证明: ⟨Nodup.of_map _, fun h => h.map d⟩

Depends on / 依赖: Nodup.of_map, h.map, of_map
-/
theorem nodup_map_iff_of_injective {f : α -> β} (d : Function.Injective f) :
    Nodup (map f s) ↔ Nodup s :=
  ⟨Nodup.of_map _, fun h => h.map d⟩

/--
theorem `inj_on_of_nodup_map` / 定理 `inj_on_of_nodup_map`

English:
theorem inj_on_of_nodup_map
  given: {f : α -> β} {s : Multiset α}
  proof: Quot.induction_on s fun _ => List.inj_on_of_nodup_map

中文:
定理 inj_on_of_nodup_map
  条件: {f : α -> β} {s : Multiset α}
  证明: Quot.induction_on s fun _ => List.inj_on_of_nodup_map

Depends on / 依赖: List.inj_on_of_nodup_map, Quot.induction_on, induction_on, inj_on_of_nodup_map
-/
theorem inj_on_of_nodup_map {f : α -> β} {s : Multiset α} :
    Nodup (map f s) -> forall x in s, forall y in s, f x = f y -> x = y :=
  Quot.induction_on s fun _ => List.inj_on_of_nodup_map

/--
theorem `nodup_map_iff_inj_on` / 定理 `nodup_map_iff_inj_on`

English:
theorem nodup_map_iff_inj_on
  given: {f : α -> β} {s : Multiset α} (d : Nodup s)
  proof: ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

中文:
定理 nodup_map_iff_inj_on
  条件: {f : α -> β} {s : Multiset α} (d : Nodup s)
  证明: ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

Depends on / 依赖: d.map_on, inj_on_of_nodup_map, map_on
-/
theorem nodup_map_iff_inj_on {f : α -> β} {s : Multiset α} (d : Nodup s) :
    Nodup (map f s) ↔ forall x in s, forall y in s, f x = f y -> x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩

/--
theorem `Nodup.pmap` / 定理 `Nodup.pmap`

English:
theorem Nodup.pmap
  statement: {p : α -> Prop} {f : forall a, p a -> β} {s : Multiset α} {H}
  proof: Quot.induction_on s (fun _ _ => List.Nodup.pmap hf) H

@[simp]

中文:
定理 Nodup.pmap
  结论: {p : α -> 命题} {f : 对任意 a, p a -> β} {s : Multiset α} {H}
  证明: Quot.induction_on s (fun _ _ => List.Nodup.pmap hf) H

@[simp]
-/
theorem Nodup.pmap {p : α -> Prop} {f : forall a, p a -> β} {s : Multiset α} {H}
    (hf : forall a ha b hb, f a ha = f b hb -> a = b) : Nodup s -> Nodup (pmap f s H) :=
  Quot.induction_on s (fun _ _ => List.Nodup.pmap hf) H

@[simp]
/--
theorem `nodup_attach` / 定理 `nodup_attach`

English:
theorem nodup_attach
  given: {s : Multiset α}
  statement: Nodup (attach s) ↔ Nodup s
  proof: Quot.induction_on s fun _ => List.nodup_attach

protected alias ⟨_, Nodup.attach⟩ := nodup_attach

中文:
定理 nodup_attach
  条件: {s : Multiset α}
  结论: Nodup (attach s) ↔ Nodup s
  证明: Quot.induction_on s fun _ => List.nodup_attach

protected alias ⟨_, Nodup.attach⟩ := nodup_attach

Depends on / 依赖: List.nodup_attach, Quot.induction_on, induction_on, nodup_attach
-/
theorem nodup_attach {s : Multiset α} : Nodup (attach s) ↔ Nodup s :=
  Quot.induction_on s fun _ => List.nodup_attach

protected alias ⟨_, Nodup.attach⟩ := nodup_attach

/--
theorem `map_eq_map_of_bij_of_nodup` / 定理 `map_eq_map_of_bij_of_nodup`

English:
theorem map_eq_map_of_bij_of_nodup
  statement: (f : α -> γ) (g : β -> γ) {s : Multiset α} {t : Multiset β}
  proof: by
  have : t = s.attach.map fun x => i x.1 x.2 := by
    rw [ht.ext]
    · aesop
· exact hs.attach.map fun x y hxy => Subtype.ext i_inj _ x.2 _ y.2 hxy
  calc
    s.map f = s.pmap (fun x _ => f x) fun _ => id := by rw [pmap_eq_map]
    _ = s.attach.map fun x => f x.1 := by rw [pmap_eq_map_attach]
    _ = t.map g := by rw [this, Multiset.map_map]; exact map_congr rfl fun x _ => h _ _

中文:
定理 map_eq_map_of_bij_of_nodup
  结论: (f : α -> γ) (g : β -> γ) {s : Multiset α} {t : Multiset β}
  证明: by
  have : t = s.attach.map fun x => i x.1 x.2 := by
    rw [ht.ext]
    · aesop
· exact hs.attach.map fun x y hxy => Subtype.ext i_inj _ x.2 _ y.2 hxy
  calc
    s.map f = s.pmap (fun x _ => f x) fun _ => id := by rw [pmap_eq_map]
    _ = s.attach.map fun x => f x.1 := by rw [pmap_eq_map_attach]
    _ = t.map g := by rw [this, Multiset.map_map]; exact map_congr rfl fun x _ => h _ _

Depends on / 依赖: Multiset, Multiset.map_map, Subtype, Subtype.ext, attach, hs.attach.map, ht.ext, i_inj, map_congr, map_map, pmap_eq_map, pmap_eq_map_attach, s.attach.map, s.map, s.pmap, t.map
-/
theorem map_eq_map_of_bij_of_nodup (f : α -> γ) (g : β -> γ) {s : Multiset α} {t : Multiset β}
    (hs : s.Nodup) (ht : t.Nodup) (i : forall a in s, β) (hi : forall a ha, i a ha in t)
    (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂)
    (i_surj : forall b in t, exists a ha, i a ha = b) (h : forall a ha, f a = g (i a ha)) : s.map f = t.map g := by
  have : t = s.attach.map fun x => i x.1 x.2 := by
    rw [ht.ext]
    · aesop
· exact hs.attach.map fun x y hxy => Subtype.ext i_inj _ x.2 _ y.2 hxy
  calc
    s.map f = s.pmap (fun x _ => f x) fun _ => id := by rw [pmap_eq_map]
    _ = s.attach.map fun x => f x.1 := by rw [pmap_eq_map_attach]
    _ = t.map g := by rw [this, Multiset.map_map]; exact map_congr rfl fun x _ => h _ _

end Nodup

end Multiset
