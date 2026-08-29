/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.Powerset

/-!
# The antidiagonal on a multiset.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/

@[expose] public section

assert_not_exists IsOrderedMonoid Ring

universe u

namespace Multiset

open List

variable {α β : Type*}

/--
Definition of `antidiagonal` / `antidiagonal` 的定义

English:
definition antidiagonal
  signature: (s : Multiset α)
  body: Quot.liftOn s (fun l => (revzip (powersetAux l) : Multiset (Multiset α × Multiset α)))
    fun _ _ h => Quot.sound (revzip_powersetAux_perm h)

中文:
定义 antidiagonal
  签名: (s : Multiset α)
  定义体: Quot.liftOn s (fun l => (revzip (powersetAux l) : Multiset (Multiset α × Multiset α)))
    fun _ _ h => Quot.sound (revzip_powersetAux_perm h)

Depends on / 依赖: Multiset, Quot.liftOn, Quot.sound, liftOn, powersetAux, revzip, revzip_powersetAux_perm
-/
def antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α) :=
  Quot.liftOn s (fun l => (revzip (powersetAux l) : Multiset (Multiset α × Multiset α)))
    fun _ _ h => Quot.sound (revzip_powersetAux_perm h)

/--
theorem `antidiagonal_coe` / 定理 `antidiagonal_coe`

English:
theorem antidiagonal_coe
  given: (l : List α)
  statement: @antidiagonal α l = revzip (powersetAux l)
  proof: rfl

@[simp]

中文:
定理 antidiagonal_coe
  条件: (l : 列表 α)
  结论: @antidiagonal α l = revzip (powersetAux l)
  证明: rfl

@[simp]
-/
theorem antidiagonal_coe (l : List α) : @antidiagonal α l = revzip (powersetAux l) :=
  rfl

@[simp]
/--
theorem `antidiagonal_coe'` / 定理 `antidiagonal_coe'`

English:
theorem antidiagonal_coe'
  given: (l : List α)
  statement: @antidiagonal α l = revzip (powersetAux' l)
  proof: Quot.sound revzip_powersetAux_perm_aux'

中文:
定理 antidiagonal_coe'
  条件: (l : 列表 α)
  结论: @antidiagonal α l = revzip (powersetAux' l)
  证明: Quot.sound revzip_powersetAux_perm_aux'

Depends on / 依赖: Quot.sound, revzip_powersetAux_perm_aux
-/
theorem antidiagonal_coe' (l : List α) : @antidiagonal α l = revzip (powersetAux' l) :=
  Quot.sound revzip_powersetAux_perm_aux'

/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp]
/--
theorem `mem_antidiagonal` / 定理 `mem_antidiagonal`

English:
theorem mem_antidiagonal
  given: {s : Multiset α} {x : Multiset α × Multiset α}
  proof: Quotient.inductionOn s fun l => by
    dsimp only [quot_mk_to_coe, antidiagonal_coe]
    refine ⟨fun h => revzip_powersetAux h, fun h => ?_⟩
    have _ := Classical.decEq α
    simp only [revzip_powersetAux_lemma l revzip_powersetAux, h.symm, mem_coe,
      List.mem_map, mem_powersetAux]
    obtain 

中文:
定理 mem_antidiagonal
  条件: {s : Multiset α} {x : Multiset α × Multiset α}
  证明: Quotient.inductionOn s fun l => by
    dsimp only [quot_mk_to_coe, antidiagonal_coe]
    refine ⟨fun h => revzip_powersetAux h, fun h => ?_⟩
    have _ := Classical.decEq α
    simp only [revzip_powersetAux_lemma l revzip_powersetAux, h.symm, mem_coe,
      List.mem_map, mem_powersetAux]
    obtain 

Depends on / 依赖: Classical, Classical.decEq, List.mem_map, Quotient, Quotient.inductionOn, add_tsub_cancel_left, antidiagonal_coe, h.symm, inductionOn, le_add_right, mem_coe, mem_map, mem_powersetAux, quot_mk_to_coe, revzip_powersetAux, revzip_powersetAux_lemma
-/
theorem mem_antidiagonal {s : Multiset α} {x : Multiset α × Multiset α} :
    x in antidiagonal s ↔ x.1 + x.2 = s :=
  Quotient.inductionOn s fun l => by
    dsimp only [quot_mk_to_coe, antidiagonal_coe]
    refine ⟨fun h => revzip_powersetAux h, fun h => ?_⟩
    have _ := Classical.decEq α
    simp only [revzip_powersetAux_lemma l revzip_powersetAux, h.symm, mem_coe,
      List.mem_map, mem_powersetAux]
    obtain ⟨x₁, x₂⟩ := x
    exact ⟨x₁, le_add_right _ _, by rw [add_tsub_cancel_left x₁ x₂]⟩

@[simp]
/--
theorem `antidiagonal_map_fst` / 定理 `antidiagonal_map_fst`

English:
theorem antidiagonal_map_fst
  given: (s : Multiset α)
  statement: (antidiagonal s).map Prod.fst = powerset s
  proof: Quotient.inductionOn s fun l => by simp [powersetAux']

@[simp]

中文:
定理 antidiagonal_map_fst
  条件: (s : Multiset α)
  结论: (antidiagonal s).map 积类型.fst = powerset s
  证明: Quotient.inductionOn s fun l => by simp [powersetAux']

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, powersetAux
-/
theorem antidiagonal_map_fst (s : Multiset α) : (antidiagonal s).map Prod.fst = powerset s :=
  Quotient.inductionOn s fun l => by simp [powersetAux']

@[simp]
/--
theorem `antidiagonal_map_snd` / 定理 `antidiagonal_map_snd`

English:
theorem antidiagonal_map_snd
  given: (s : Multiset α)
  statement: (antidiagonal s).map Prod.snd = powerset s
  proof: Quotient.inductionOn s fun l => by simp [powersetAux']

@[simp]

中文:
定理 antidiagonal_map_snd
  条件: (s : Multiset α)
  结论: (antidiagonal s).map 积类型.snd = powerset s
  证明: Quotient.inductionOn s fun l => by simp [powersetAux']

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, powersetAux
-/
theorem antidiagonal_map_snd (s : Multiset α) : (antidiagonal s).map Prod.snd = powerset s :=
  Quotient.inductionOn s fun l => by simp [powersetAux']

@[simp]
/--
theorem `antidiagonal_zero` / 定理 `antidiagonal_zero`

English:
theorem antidiagonal_zero
  statement: @antidiagonal α 0 = {(0, 0)}
  proof: rfl

@[simp]

中文:
定理 antidiagonal_zero
  结论: @antidiagonal α 0 = {(0, 0)}
  证明: rfl

@[simp]
-/
theorem antidiagonal_zero : @antidiagonal α 0 = {(0, 0)} :=
  rfl

@[simp]
/--
theorem `antidiagonal_cons` / 定理 `antidiagonal_cons`

English:
theorem antidiagonal_cons
  given: (a : α) (s)
  proof: Quotient.inductionOn s fun l => by
    simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powersetAux'_cons, cons_coe,
      map_coe, antidiagonal_coe', coe_add]
    rw [← zip_map]; rw [← zip_map]; rw [zip_append]; rw [(_ : _ ++ _ = _)] <;> simp

中文:
定理 antidiagonal_cons
  条件: (a : α) (s)
  证明: Quotient.inductionOn s fun l => by
    simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powersetAux'_cons, cons_coe,
      map_coe, antidiagonal_coe', coe_add]
    rw [← zip_map]; rw [← zip_map]; rw [zip_append]; rw [(_ : _ ++ _ = _)] <;> simp

Depends on / 依赖: Quotient, Quotient.inductionOn, _cons, antidiagonal_coe, coe_add, coe_eq_coe, cons_coe, inductionOn, map_coe, powersetAux, quot_mk_to_coe, reverse_append, revzip, zip_append, zip_map
-/
theorem antidiagonal_cons (a : α) (s) :
    antidiagonal (a ::ₘ s) =
      map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a) id) (antidiagonal s) :=
  Quotient.inductionOn s fun l => by
    simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powersetAux'_cons, cons_coe,
      map_coe, antidiagonal_coe', coe_add]
    rw [← zip_map]; rw [← zip_map]; rw [zip_append]; rw [(_ : _ ++ _ = _)] <;> simp

/--
theorem `antidiagonal_add` / 定理 `antidiagonal_add`

English:
theorem antidiagonal_add
  given: (s t : Multiset α)
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp_rw [cons_add, antidiagonal_cons, ih, add_bind, bind_map, map_bind, map_map]
    congr! <;> simp

@[simp]

中文:
定理 antidiagonal_add
  条件: (s t : Multiset α)
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp_rw [cons_add, antidiagonal_cons, ih, add_bind, bind_map, map_bind, map_map]
    congr! <;> simp

@[simp]

Depends on / 依赖: Multiset, Multiset.induction_on, add_bind, antidiagonal_cons, bind_map, cons_add, induction_on, map_bind, map_map, simp_rw
-/
theorem antidiagonal_add (s t : Multiset α) :
    (s + t).antidiagonal =
      s.antidiagonal.bind fun p => t.antidiagonal.map fun q => (p.1 + q.1, p.2 + q.2) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp_rw [cons_add, antidiagonal_cons, ih, add_bind, bind_map, map_bind, map_map]
    congr! <;> simp

@[simp]
/--
theorem `map_swap_antidiagonal` / 定理 `map_swap_antidiagonal`

English:
theorem map_swap_antidiagonal
  given: (s : Multiset α)
  proof: by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    simp only [antidiagonal_cons, map_add, map_map, ← Prod.map_comp_swap,
      ← Multiset.map_map _ Prod.swap, ih, add_comm]

中文:
定理 map_swap_antidiagonal
  条件: (s : Multiset α)
  证明: by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    simp only [antidiagonal_cons, map_add, map_map, ← Prod.map_comp_swap,
      ← Multiset.map_map _ Prod.swap, ih, add_comm]

Depends on / 依赖: Multiset, Multiset.induction_on, Multiset.map_map, Prod.map_comp_swap, Prod.swap, add_comm, antidiagonal_cons, induction_on, map_add, map_comp_swap, map_map
-/
theorem map_swap_antidiagonal (s : Multiset α) :
    s.antidiagonal.map Prod.swap = s.antidiagonal := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons a s ih =>
    simp only [antidiagonal_cons, map_add, map_map, ← Prod.map_comp_swap,
      ← Multiset.map_map _ Prod.swap, ih, add_comm]

/--
theorem `antidiagonal_eq_map_powerset` / 定理 `antidiagonal_eq_map_powerset`

English:
theorem antidiagonal_eq_map_powerset
  given: [DecidableEq α] (s : Multiset α)
  proof: by
  induction s using Multiset.induction_on with
  | empty => simp only [antidiagonal_zero, powerset_zero, Multiset.zero_sub, map_singleton]
  | cons a s hs =>
    simp_rw [antidiagonal_cons, powerset_cons, map_add, hs, map_map, Function.comp, Prod.map_apply,
      id, sub_cons, erase_cons_head]
  

中文:
定理 antidiagonal_eq_map_powerset
  条件: [DecidableEq α] (s : Multiset α)
  证明: by
  induction s using Multiset.induction_on with
  | empty => simp only [antidiagonal_zero, powerset_zero, Multiset.zero_sub, map_singleton]
  | cons a s hs =>
    simp_rw [antidiagonal_cons, powerset_cons, map_add, hs, map_map, Function.comp, Prod.map_apply,
      id, sub_cons, erase_cons_head]
  

Depends on / 依赖: Function, Function.comp, Multiset, Multiset.induction_on, Multiset.map_congr, Multiset.zero_sub, Prod.map_apply, add_comm, antidiagonal_cons, antidiagonal_zero, cons_sub_of_le, erase_cons_head, induction_on, map_add, map_apply, map_congr, map_map, map_singleton, mem_powerset, mem_powerset.mp
-/
theorem antidiagonal_eq_map_powerset [DecidableEq α] (s : Multiset α) :
    s.antidiagonal = s.powerset.map fun t => (s - t, t) := by
  induction s using Multiset.induction_on with
  | empty => simp only [antidiagonal_zero, powerset_zero, Multiset.zero_sub, map_singleton]
  | cons a s hs =>
    simp_rw [antidiagonal_cons, powerset_cons, map_add, hs, map_map, Function.comp, Prod.map_apply,
      id, sub_cons, erase_cons_head]
    rw [add_comm]
    congr 1
    refine Multiset.map_congr rfl fun x hx => ?_
    rw [cons_sub_of_le _ (mem_powerset.mp hx)]

@[simp]
/--
theorem `card_antidiagonal` / 定理 `card_antidiagonal`

English:
theorem card_antidiagonal
  given: (s : Multiset α)
  statement: card (antidiagonal s) = 2 ^ card s
  proof: by
  have := card_powerset s
  rwa [← antidiagonal_map_fst, card_map] at this

中文:
定理 card_antidiagonal
  条件: (s : Multiset α)
  结论: card (antidiagonal s) = 2 ^ card s
  证明: by
  have := card_powerset s
  rwa [← antidiagonal_map_fst, card_map] at this

Depends on / 依赖: antidiagonal_map_fst, card_map, card_powerset
-/
theorem card_antidiagonal (s : Multiset α) : card (antidiagonal s) = 2 ^ card s := by
  have := card_powerset s
  rwa [← antidiagonal_map_fst, card_map] at this

end Multiset
