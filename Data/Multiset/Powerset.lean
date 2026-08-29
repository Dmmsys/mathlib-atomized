/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Sublists
public import Mathlib.Data.List.Zip
public import Mathlib.Data.Multiset.Bind
public import Mathlib.Data.Multiset.Range

/-!
# The powerset of a multiset
-/

@[expose] public section

namespace Multiset

open List

variable {α : Type*}

/-! ### powerset -/

-- TODO: Write a more efficient version (this is slightly slower due to the `map (↑)`).
/--
Definition of `powersetAux` / `powersetAux` 的定义

English:
definition powersetAux
  signature: (l : List α)
  body: (sublists l).map (↑)

中文:
定义 powersetAux
  签名: (l : List α)
  定义体: (sublists l).map (↑)

Depends on / 依赖: sublists
-/
def powersetAux (l : List α) : List (Multiset α) :=
  (sublists l).map (↑)

/--
theorem `powersetAux_eq_map_coe` / 定理 `powersetAux_eq_map_coe`

English:
theorem powersetAux_eq_map_coe
  given: {l : List α}
  statement: powersetAux l = (sublists l).map (↑)
  proof: rfl

@[simp]

中文:
定理 powersetAux_eq_map_coe
  条件: {l : List α}
  结论: powersetAux l = (sublists l).map (↑)
  证明: rfl

@[simp]
-/
theorem powersetAux_eq_map_coe {l : List α} : powersetAux l = (sublists l).map (↑) :=
  rfl

@[simp]
/--
theorem `mem_powersetAux` / 定理 `mem_powersetAux`

English:
theorem mem_powersetAux
  given: {l : List α} {s}
  statement: s in powersetAux l ↔ s <= ↑l
  proof: Quotient.inductionOn s by simp [powersetAux_eq_map_coe, Subperm, and_comm]

中文:
定理 mem_powersetAux
  条件: {l : List α} {s}
  结论: s in powersetAux l ↔ s <= ↑l
  证明: Quotient.inductionOn s by simp [powersetAux_eq_map_coe, Subperm, and_comm]

Depends on / 依赖: Quotient, Quotient.inductionOn, Subperm, and_comm, inductionOn, powersetAux_eq_map_coe
-/
theorem mem_powersetAux {l : List α} {s} : s in powersetAux l ↔ s <= ↑l :=
Quotient.inductionOn s by simp [powersetAux_eq_map_coe, Subperm, and_comm]

/--
Definition of `powersetAux'` / `powersetAux'` 的定义

English:
definition powersetAux'
  signature: (l : List α)
  body: (sublists' l).map (↑)

中文:
定义 powersetAux'
  签名: (l : List α)
  定义体: (sublists' l).map (↑)

Depends on / 依赖: sublists
-/
def powersetAux' (l : List α) : List (Multiset α) :=
  (sublists' l).map (↑)

/--
theorem `powersetAux_perm_powersetAux'` / 定理 `powersetAux_perm_powersetAux'`

English:
theorem powersetAux_perm_powersetAux'
  given: {l : List α}
  statement: powersetAux l ~ powersetAux' l
  proof: by
  rw [powersetAux_eq_map_coe]; exact (sublists_perm_sublists' _).map _

@[simp]

中文:
定理 powersetAux_perm_powersetAux'
  条件: {l : List α}
  结论: powersetAux l ~ powersetAux' l
  证明: by
  rw [powersetAux_eq_map_coe]; exact (sublists_perm_sublists' _).map _

@[simp]

Depends on / 依赖: powersetAux_eq_map_coe, sublists_perm_sublists
-/
theorem powersetAux_perm_powersetAux' {l : List α} : powersetAux l ~ powersetAux' l := by
  rw [powersetAux_eq_map_coe]; exact (sublists_perm_sublists' _).map _

@[simp]
/--
theorem `powersetAux'_nil` / 定理 `powersetAux'_nil`

English:
theorem powersetAux'_nil
  statement: powersetAux' (@nil α) = [0]
  proof: rfl

@[simp]

中文:
定理 powersetAux'_nil
  结论: powersetAux' (@nil α) = [0]
  证明: rfl

@[simp]
-/
theorem powersetAux'_nil : powersetAux' (@nil α) = [0] :=
  rfl

@[simp]
/--
theorem `powersetAux'_cons` / 定理 `powersetAux'_cons`

English:
theorem powersetAux'_cons
  given: (a : α) (l : List α)
  proof: by
  simp [powersetAux']

中文:
定理 powersetAux'_cons
  条件: (a : α) (l : List α)
  证明: by
  simp [powersetAux']
-/
theorem powersetAux'_cons (a : α) (l : List α) :
    powersetAux' (a :: l) = powersetAux' l ++ List.map (cons a) (powersetAux' l) := by
  simp [powersetAux']

/--
theorem `powerset_aux'_perm` / 定理 `powerset_aux'_perm`

English:
theorem powerset_aux'_perm
  given: {l₁ l₂ : List α} (p : l₁ ~ l₂)
  statement: powersetAux' l₁ ~ powersetAux' l₂
  proof: by
  induction p with
  | nil => simp
  | cons _ _ IH =>
    simp only [powersetAux'_cons]
    exact IH.append (IH.map _)
  | swap a b =>
    simp only [powersetAux'_cons, map_append, List.map_map, append_assoc]
    apply Perm.append_left
    rw [← append_assoc]; rw [← append_assoc]; rw [(by funext 

中文:
定理 powerset_aux'_perm
  条件: {l₁ l₂ : List α} (p : l₁ ~ l₂)
  结论: powersetAux' l₁ ~ powersetAux' l₂
  证明: by
  induction p with
  | nil => simp
  | cons _ _ IH =>
    simp only [powersetAux'_cons]
    exact IH.append (IH.map _)
  | swap a b =>
    simp only [powersetAux'_cons, map_append, List.map_map, append_assoc]
    apply Perm.append_left
    rw [← append_assoc]; rw [← append_assoc]; rw [(by funext 

Depends on / 依赖: IH.append, IH.map, List.map_map, Perm.append_left, _cons, append, append_assoc, append_left, append_right, cons_swap, map_append, map_map, perm_append_comm, perm_append_comm.append_right, powersetAux
-/
theorem powerset_aux'_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux' l₁ ~ powersetAux' l₂ := by
  induction p with
  | nil => simp
  | cons _ _ IH =>
    simp only [powersetAux'_cons]
    exact IH.append (IH.map _)
  | swap a b =>
    simp only [powersetAux'_cons, map_append, List.map_map, append_assoc]
    apply Perm.append_left
    rw [← append_assoc]; rw [← append_assoc]; rw [(by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

/--
theorem `powersetAux_perm` / 定理 `powersetAux_perm`

English:
theorem powersetAux_perm
  given: {l₁ l₂ : List α} (p : l₁ ~ l₂)
  statement: powersetAux l₁ ~ powersetAux l₂
  proof: powersetAux_perm_powersetAux'.trans
    (powerset_aux'_perm p).trans powersetAux_perm_powersetAux'.symm

中文:
定理 powersetAux_perm
  条件: {l₁ l₂ : List α} (p : l₁ ~ l₂)
  结论: powersetAux l₁ ~ powersetAux l₂
  证明: powersetAux_perm_powersetAux'.trans
    (powerset_aux'_perm p).trans powersetAux_perm_powersetAux'.symm

Depends on / 依赖: _perm, powersetAux_perm_powersetAux, powerset_aux
-/
theorem powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) : powersetAux l₁ ~ powersetAux l₂ :=
powersetAux_perm_powersetAux'.trans
    (powerset_aux'_perm p).trans powersetAux_perm_powersetAux'.symm

/--
Definition of `powerset` / `powerset` 的定义

English:
definition powerset
  signature: (s : Multiset α)
  body: Quot.liftOn s
    (fun l => (powersetAux l : Multiset (Multiset α)))
    (fun _ _ h => Quot.sound (powersetAux_perm h))

中文:
定义 powerset
  签名: (s : Multiset α)
  定义体: Quot.liftOn s
    (fun l => (powersetAux l : Multiset (Multiset α)))
    (fun _ _ h => Quot.sound (powersetAux_perm h))

Depends on / 依赖: Multiset, Quot.liftOn, Quot.sound, liftOn, powersetAux, powersetAux_perm
-/
def powerset (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s
    (fun l => (powersetAux l : Multiset (Multiset α)))
    (fun _ _ h => Quot.sound (powersetAux_perm h))

/--
theorem `powerset_coe` / 定理 `powerset_coe`

English:
theorem powerset_coe
  given: (l : List α)
  statement: @powerset α l = ((sublists l).map (↑) : List (Multiset α))
  proof: congr_arg ((↑) : List (Multiset α) -> Multiset (Multiset α)) powersetAux_eq_map_coe

@[simp]

中文:
定理 powerset_coe
  条件: (l : List α)
  结论: @powerset α l = ((sublists l).map (↑) : List (Multiset α))
  证明: congr_arg ((↑) : List (Multiset α) -> Multiset (Multiset α)) powersetAux_eq_map_coe

@[simp]

Depends on / 依赖: Multiset, congr_arg, powersetAux_eq_map_coe
-/
theorem powerset_coe (l : List α) : @powerset α l = ((sublists l).map (↑) : List (Multiset α)) :=
  congr_arg ((↑) : List (Multiset α) -> Multiset (Multiset α)) powersetAux_eq_map_coe

@[simp]
/--
theorem `powerset_coe'` / 定理 `powerset_coe'`

English:
theorem powerset_coe'
  given: (l : List α)
  statement: @powerset α l = ((sublists' l).map (↑) : List (Multiset α))
  proof: Quot.sound powersetAux_perm_powersetAux'

@[simp]

中文:
定理 powerset_coe'
  条件: (l : List α)
  结论: @powerset α l = ((sublists' l).map (↑) : List (Multiset α))
  证明: Quot.sound powersetAux_perm_powersetAux'

@[simp]

Depends on / 依赖: Quot.sound, powersetAux_perm_powersetAux
-/
theorem powerset_coe' (l : List α) : @powerset α l = ((sublists' l).map (↑) : List (Multiset α)) :=
  Quot.sound powersetAux_perm_powersetAux'

@[simp]
/--
theorem `powerset_zero` / 定理 `powerset_zero`

English:
theorem powerset_zero
  statement: @powerset α 0 = {0}
  proof: rfl

@[simp]

中文:
定理 powerset_zero
  结论: @powerset α 0 = {0}
  证明: rfl

@[simp]
-/
theorem powerset_zero : @powerset α 0 = {0} :=
  rfl

@[simp]
/--
theorem `powerset_cons` / 定理 `powerset_cons`

English:
theorem powerset_cons
  given: (a : α) (s)
  statement: powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s)
  proof: Quotient.inductionOn s fun l => by simp [Function.comp_def]

@[simp]

中文:
定理 powerset_cons
  条件: (a : α) (s)
  结论: powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s)
  证明: Quotient.inductionOn s fun l => by simp [Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Quotient, Quotient.inductionOn, comp_def, inductionOn
-/
theorem powerset_cons (a : α) (s) : powerset (a ::ₘ s) = powerset s + map (cons a) (powerset s) :=
  Quotient.inductionOn s fun l => by simp [Function.comp_def]

@[simp]
/--
theorem `mem_powerset` / 定理 `mem_powerset`

English:
theorem mem_powerset
  given: {s t : Multiset α}
  statement: s in powerset t ↔ s <= t
  proof: Quotient.inductionOn₂ s t by simp [Subperm, and_comm]

中文:
定理 mem_powerset
  条件: {s t : Multiset α}
  结论: s in powerset t ↔ s <= t
  证明: Quotient.inductionOn₂ s t by simp [Subperm, and_comm]

Depends on / 依赖: Quotient, Quotient.inductionOn, Subperm, and_comm
-/
theorem mem_powerset {s t : Multiset α} : s in powerset t ↔ s <= t :=
Quotient.inductionOn₂ s t by simp [Subperm, and_comm]

/--
theorem `map_single_le_powerset` / 定理 `map_single_le_powerset`

English:
theorem map_single_le_powerset
  given: (s : Multiset α)
  statement: s.map singleton <= powerset s
  proof: Quotient.inductionOn s fun l => by
    simp only [powerset_coe, quot_mk_to_coe, coe_le, map_coe]
    change l.map (((↑) : List α -> Multiset α) ∘ pure) <+~ (sublists l).map (↑)
    rw [← List.map_map]
    exact ((map_pure_sublist_sublists _).map _).subperm

中文:
定理 map_single_le_powerset
  条件: (s : Multiset α)
  结论: s.map singleton <= powerset s
  证明: Quotient.inductionOn s fun l => by
    simp only [powerset_coe, quot_mk_to_coe, coe_le, map_coe]
    change l.map (((↑) : List α -> Multiset α) ∘ pure) <+~ (sublists l).map (↑)
    rw [← List.map_map]
    exact ((map_pure_sublist_sublists _).map _).subperm

Depends on / 依赖: List.map_map, Multiset, Quotient, Quotient.inductionOn, coe_le, inductionOn, l.map, map_coe, map_map, map_pure_sublist_sublists, powerset_coe, quot_mk_to_coe, sublists, subperm
-/
theorem map_single_le_powerset (s : Multiset α) : s.map singleton <= powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [powerset_coe, quot_mk_to_coe, coe_le, map_coe]
    change l.map (((↑) : List α -> Multiset α) ∘ pure) <+~ (sublists l).map (↑)
    rw [← List.map_map]
    exact ((map_pure_sublist_sublists _).map _).subperm

/--
theorem `zero_mem_powerset` / 定理 `zero_mem_powerset`

English:
theorem zero_mem_powerset
  given: (s : Multiset α)
  statement: 0 in s.powerset
  proof: Multiset.mem_powerset.mpr s.zero_le

中文:
定理 zero_mem_powerset
  条件: (s : Multiset α)
  结论: 0 in s.powerset
  证明: Multiset.mem_powerset.mpr s.zero_le

Depends on / 依赖: Multiset, Multiset.mem_powerset.mpr, mem_powerset, s.zero_le, zero_le
-/
theorem zero_mem_powerset (s : Multiset α) : 0 in s.powerset :=
  Multiset.mem_powerset.mpr s.zero_le

/--
theorem `self_mem_powerset` / 定理 `self_mem_powerset`

English:
theorem self_mem_powerset
  given: (s : Multiset α)
  statement: s in s.powerset
  proof: Multiset.mem_powerset.mpr le_rfl

@[simp]

中文:
定理 self_mem_powerset
  条件: (s : Multiset α)
  结论: s in s.powerset
  证明: Multiset.mem_powerset.mpr le_rfl

@[simp]

Depends on / 依赖: Multiset, Multiset.mem_powerset.mpr, le_rfl, mem_powerset
-/
theorem self_mem_powerset (s : Multiset α) : s in s.powerset :=
  Multiset.mem_powerset.mpr le_rfl

@[simp]
/--
theorem `card_powerset` / 定理 `card_powerset`

English:
theorem card_powerset
  given: (s : Multiset α)
  statement: card (powerset s) = 2 ^ card s
  proof: Quotient.inductionOn s by simp

@[simp]

中文:
定理 card_powerset
  条件: (s : Multiset α)
  结论: card (powerset s) = 2 ^ card s
  证明: Quotient.inductionOn s by simp

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem card_powerset (s : Multiset α) : card (powerset s) = 2 ^ card s :=
Quotient.inductionOn s by simp

@[simp]
/--
theorem `powerset_eq_singleton_zero_iff` / 定理 `powerset_eq_singleton_zero_iff`

English:
theorem powerset_eq_singleton_zero_iff
  given: (s : Multiset α)
  statement: powerset s = {0} ↔ s = 0 where
  proof: by
    intro rfl
    exact powerset_zero
  mp powerset := by
    simpa using congr(card $powerset)

中文:
定理 powerset_eq_singleton_zero_iff
  条件: (s : Multiset α)
  结论: powerset s = {0} ↔ s = 0 where
  证明: by
    intro rfl
    exact powerset_zero
  mp powerset := by
    simpa using congr(card $powerset)

Depends on / 依赖: powerset, powerset_zero
-/
theorem powerset_eq_singleton_zero_iff (s : Multiset α) : powerset s = {0} ↔ s = 0 where
  mpr := by
    intro rfl
    exact powerset_zero
  mp powerset := by
    simpa using congr(card $powerset)

/--
theorem `revzip_powersetAux` / 定理 `revzip_powersetAux`

English:
theorem revzip_powersetAux
  given: {l : List α} ⦃x⦄ (h : x in revzip (powersetAux l))
  statement: x.1 + x.2 = ↑l
  proof: by
  rw [revzip]; rw [powersetAux_eq_map_coe]; rw [← map_reverse]; rw [zip_map]; rw [← revzip]; rw [List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists _ _ _ h)

中文:
定理 revzip_powersetAux
  条件: {l : List α} ⦃x⦄ (h : x in revzip (powersetAux l))
  结论: x.1 + x.2 = ↑l
  证明: by
  rw [revzip]; rw [powersetAux_eq_map_coe]; rw [← map_reverse]; rw [zip_map]; rw [← revzip]; rw [List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists _ _ _ h)

Depends on / 依赖: List.mem_map, Prod.exists, Prod.map_apply, Quot.sound, map_apply, map_reverse, mem_map, powersetAux_eq_map_coe, revzip, revzip_sublists, zip_map
-/
theorem revzip_powersetAux {l : List α} ⦃x⦄ (h : x in revzip (powersetAux l)) : x.1 + x.2 = ↑l := by
  rw [revzip]; rw [powersetAux_eq_map_coe]; rw [← map_reverse]; rw [zip_map]; rw [← revzip]; rw [List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists _ _ _ h)

/--
theorem `revzip_powersetAux'` / 定理 `revzip_powersetAux'`

English:
theorem revzip_powersetAux'
  given: {l : List α} ⦃x⦄ (h : x in revzip (powersetAux' l))
  proof: by
  rw [revzip]; rw [powersetAux']; rw [← map_reverse]; rw [zip_map]; rw [← revzip]; rw [List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists' _ _ _ h)

中文:
定理 revzip_powersetAux'
  条件: {l : List α} ⦃x⦄ (h : x in revzip (powersetAux' l))
  证明: by
  rw [revzip]; rw [powersetAux']; rw [← map_reverse]; rw [zip_map]; rw [← revzip]; rw [List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists' _ _ _ h)

Depends on / 依赖: List.mem_map, Prod.exists, Prod.map_apply, Quot.sound, map_apply, map_reverse, mem_map, powersetAux, revzip, revzip_sublists, zip_map
-/
theorem revzip_powersetAux' {l : List α} ⦃x⦄ (h : x in revzip (powersetAux' l)) :
    x.1 + x.2 = ↑l := by
  rw [revzip]; rw [powersetAux']; rw [← map_reverse]; rw [zip_map]; rw [← revzip]; rw [List.mem_map] at h
  simp only [Prod.map_apply, Prod.exists] at h
  rcases h with ⟨l₁, l₂, h, rfl, rfl⟩
  exact Quot.sound (revzip_sublists' _ _ _ h)

/--
theorem `revzip_powersetAux_lemma` / 定理 `revzip_powersetAux_lemma`

English:
theorem revzip_powersetAux_lemma
  statement: {α : Type*} [DecidableEq α] (l : List α) {l' : List (Multiset α)}
  proof: by
  have :
    Forall₂ (fun (p : Multiset α × Multiset α) (s : Multiset α) => p = (s, ↑l - s)) (revzip l')
      ((revzip l').map Prod.fst) := by
    rw [forall₂_map_right_iff]; rw [forall₂_same]
    rintro ⟨s, t⟩ h
    dsimp
    rw [← H h]; rw [add_tsub_cancel_left]
  rw [← forall₂_eq_eq_eq]; rw [

中文:
定理 revzip_powersetAux_lemma
  结论: {α : 类型} [DecidableEq α] (l : List α) {l' : List (Multiset α)}
  证明: by
  have :
    Forall₂ (fun (p : Multiset α × Multiset α) (s : Multiset α) => p = (s, ↑l - s)) (revzip l')
      ((revzip l').map Prod.fst) := by
    rw [forall₂_map_right_iff]; rw [forall₂_same]
    rintro ⟨s, t⟩ h
    dsimp
    rw [← H h]; rw [add_tsub_cancel_left]
  rw [← forall₂_eq_eq_eq]; rw [

Depends on / 依赖: Multiset, Prod.fst, add_tsub_cancel_left, revzip
-/
theorem revzip_powersetAux_lemma {α : Type*} [DecidableEq α] (l : List α) {l' : List (Multiset α)}
    (H : forall ⦃x : _ × _⦄, x in revzip l' -> x.1 + x.2 = ↑l) :
    revzip l' = l'.map fun x => (x, (l : Multiset α) - x) := by
  have :
    Forall₂ (fun (p : Multiset α × Multiset α) (s : Multiset α) => p = (s, ↑l - s)) (revzip l')
      ((revzip l').map Prod.fst) := by
    rw [forall₂_map_right_iff]; rw [forall₂_same]
    rintro ⟨s, t⟩ h
    dsimp
    rw [← H h]; rw [add_tsub_cancel_left]
  rw [← forall₂_eq_eq_eq]; rw [forall₂_map_right_iff]
  simpa using this

/--
theorem `revzip_powersetAux_perm_aux'` / 定理 `revzip_powersetAux_perm_aux'`

English:
theorem revzip_powersetAux_perm_aux'
  given: {l : List α}
  proof: by
  have := Classical.decEq α
  rw [revzip_powersetAux_lemma l revzip_powersetAux]; rw [revzip_powersetAux_lemma l revzip_powersetAux']
  exact powersetAux_perm_powersetAux'.map _

中文:
定理 revzip_powersetAux_perm_aux'
  条件: {l : List α}
  证明: by
  have := Classical.decEq α
  rw [revzip_powersetAux_lemma l revzip_powersetAux]; rw [revzip_powersetAux_lemma l revzip_powersetAux']
  exact powersetAux_perm_powersetAux'.map _

Depends on / 依赖: Classical, Classical.decEq, powersetAux_perm_powersetAux, revzip_powersetAux, revzip_powersetAux_lemma
-/
theorem revzip_powersetAux_perm_aux' {l : List α} :
    revzip (powersetAux l) ~ revzip (powersetAux' l) := by
  have := Classical.decEq α
  rw [revzip_powersetAux_lemma l revzip_powersetAux]; rw [revzip_powersetAux_lemma l revzip_powersetAux']
  exact powersetAux_perm_powersetAux'.map _

/--
theorem `revzip_powersetAux_perm` / 定理 `revzip_powersetAux_perm`

English:
theorem revzip_powersetAux_perm
  given: {l₁ l₂ : List α} (p : l₁ ~ l₂)
  proof: by
  have := Classical.decEq α
  simp only [fun l : List α => revzip_powersetAux_lemma l revzip_powersetAux, coe_eq_coe.2 p]
  exact (powersetAux_perm p).map _

@[simp]

中文:
定理 revzip_powersetAux_perm
  条件: {l₁ l₂ : List α} (p : l₁ ~ l₂)
  证明: by
  have := Classical.decEq α
  simp only [fun l : List α => revzip_powersetAux_lemma l revzip_powersetAux, coe_eq_coe.2 p]
  exact (powersetAux_perm p).map _

@[simp]

Depends on / 依赖: Classical, Classical.decEq, coe_eq_coe, powersetAux_perm, revzip_powersetAux, revzip_powersetAux_lemma
-/
theorem revzip_powersetAux_perm {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    revzip (powersetAux l₁) ~ revzip (powersetAux l₂) := by
  have := Classical.decEq α
  simp only [fun l : List α => revzip_powersetAux_lemma l revzip_powersetAux, coe_eq_coe.2 p]
  exact (powersetAux_perm p).map _

@[simp]
/--
theorem `powerset_le_powerset_iff_le` / 定理 `powerset_le_powerset_iff_le`

English:
theorem powerset_le_powerset_iff_le
  given: {s t : Multiset α}
  proof: Multiset.mem_powerset.mp Multiset.mem_of_le powerset (self_mem_powerset s)
  mpr le :=
    leInductionOn le fun hsub => by
      rw [powerset_coe']; rw [powerset_coe']; rw [coe_le]
      apply Sublist.subperm
      apply Sublist.map
      exact Sublist.sublists' hsub

中文:
定理 powerset_le_powerset_iff_le
  条件: {s t : Multiset α}
  证明: Multiset.mem_powerset.mp Multiset.mem_of_le powerset (self_mem_powerset s)
  mpr le :=
    leInductionOn le fun hsub => by
      rw [powerset_coe']; rw [powerset_coe']; rw [coe_le]
      apply Sublist.subperm
      apply Sublist.map
      exact Sublist.sublists' hsub

Depends on / 依赖: Multiset, Multiset.mem_of_le, Multiset.mem_powerset.mp, mem_of_le, mem_powerset, powerset, self_mem_powerset
-/
theorem powerset_le_powerset_iff_le {s t : Multiset α} :
    s.powerset <= t.powerset ↔ s <= t where
mp powerset := Multiset.mem_powerset.mp Multiset.mem_of_le powerset (self_mem_powerset s)
  mpr le :=
    leInductionOn le fun hsub => by
      rw [powerset_coe']; rw [powerset_coe']; rw [coe_le]
      apply Sublist.subperm
      apply Sublist.map
      exact Sublist.sublists' hsub

/--
lemma `powerset_injective` / 引理 `powerset_injective`

English:
lemma powerset_injective
  statement: Function.Injective (@Multiset.powerset α)
  proof: by
  intro a₁ a₂ a
  exact le_antisymm
    (powerset_le_powerset_iff_le.mp (le_of_eq a))
    (powerset_le_powerset_iff_le.mp (le_of_eq a.symm))

中文:
引理 powerset_injective
  结论: Function.Injective (@Multiset.powerset α)
  证明: by
  intro a₁ a₂ a
  exact le_antisymm
    (powerset_le_powerset_iff_le.mp (le_of_eq a))
    (powerset_le_powerset_iff_le.mp (le_of_eq a.symm))

Depends on / 依赖: a.symm, le_antisymm, le_of_eq, powerset_le_powerset_iff_le, powerset_le_powerset_iff_le.mp
-/
lemma powerset_injective : Function.Injective (@Multiset.powerset α) := by
  intro a₁ a₂ a
  exact le_antisymm
    (powerset_le_powerset_iff_le.mp (le_of_eq a))
    (powerset_le_powerset_iff_le.mp (le_of_eq a.symm))

/--
lemma `powerset_strictMono` / 引理 `powerset_strictMono`

English:
lemma powerset_strictMono
  statement: StrictMono (@Multiset.powerset α)
  proof: strictMono_of_le_iff_le (fun _ _ => powerset_le_powerset_iff_le.symm)

中文:
引理 powerset_strictMono
  结论: StrictMono (@Multiset.powerset α)
  证明: strictMono_of_le_iff_le (fun _ _ => powerset_le_powerset_iff_le.symm)

Depends on / 依赖: powerset_le_powerset_iff_le, powerset_le_powerset_iff_le.symm, strictMono_of_le_iff_le
-/
lemma powerset_strictMono : StrictMono (@Multiset.powerset α) :=
  strictMono_of_le_iff_le (fun _ _ => powerset_le_powerset_iff_le.symm)

/--
lemma `powerset_mono` / 引理 `powerset_mono`

English:
lemma powerset_mono
  statement: Monotone (@Multiset.powerset α)
  proof: powerset_strictMono.monotone

中文:
引理 powerset_mono
  结论: Monotone (@Multiset.powerset α)
  证明: powerset_strictMono.monotone

Depends on / 依赖: monotone, powerset_strictMono, powerset_strictMono.monotone
-/
lemma powerset_mono : Monotone (@Multiset.powerset α) :=
  powerset_strictMono.monotone

/-! ### powersetCard -/


/--
Definition of `powersetCardAux` / `powersetCardAux` 的定义

English:
definition powersetCardAux
  signature: (n : Nat) (l : List α)
  body: sublistsLenAux n l (↑) []

中文:
定义 powersetCardAux
  签名: (n : 自然数) (l : List α)
  定义体: sublistsLenAux n l (↑) []

Depends on / 依赖: sublistsLenAux
-/
def powersetCardAux (n : Nat) (l : List α) : List (Multiset α) :=
  sublistsLenAux n l (↑) []

/--
theorem `powersetCardAux_eq_map_coe` / 定理 `powersetCardAux_eq_map_coe`

English:
theorem powersetCardAux_eq_map_coe
  given: {n} {l : List α}
  proof: by
  rw [powersetCardAux]; rw [sublistsLenAux_eq]; rw [append_nil]

@[simp]

中文:
定理 powersetCardAux_eq_map_coe
  条件: {n} {l : List α}
  证明: by
  rw [powersetCardAux]; rw [sublistsLenAux_eq]; rw [append_nil]

@[simp]

Depends on / 依赖: append_nil, powersetCardAux, sublistsLenAux_eq
-/
theorem powersetCardAux_eq_map_coe {n} {l : List α} :
    powersetCardAux n l = (sublistsLen n l).map (↑) := by
  rw [powersetCardAux]; rw [sublistsLenAux_eq]; rw [append_nil]

@[simp]
/--
theorem `mem_powersetCardAux` / 定理 `mem_powersetCardAux`

English:
theorem mem_powersetCardAux
  given: {n} {l : List α} {s}
  statement: s in powersetCardAux n l ↔ s <= ↑l ∧ card s = n
  proof: Quotient.inductionOn s by
    simp only [quot_mk_to_coe, powersetCardAux_eq_map_coe, List.mem_map, mem_sublistsLen,
      coe_eq_coe, coe_le, Subperm, coe_card]
    exact fun l₁ =>
      ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
       fun ⟨⟨l₂, p, s⟩, e⟩ => ⟨_, ⟨s, p.length_eq.

中文:
定理 mem_powersetCardAux
  条件: {n} {l : List α} {s}
  结论: s in powersetCardAux n l ↔ s <= ↑l ∧ card s = n
  证明: Quotient.inductionOn s by
    simp only [quot_mk_to_coe, powersetCardAux_eq_map_coe, List.mem_map, mem_sublistsLen,
      coe_eq_coe, coe_le, Subperm, coe_card]
    exact fun l₁ =>
      ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
       fun ⟨⟨l₂, p, s⟩, e⟩ => ⟨_, ⟨s, p.length_eq.

Depends on / 依赖: List.mem_map, Quotient, Quotient.inductionOn, Subperm, coe_card, coe_eq_coe, coe_le, inductionOn, length_eq, mem_map, mem_sublistsLen, p.length_eq.trans, p.symm.length_eq.trans, powersetCardAux_eq_map_coe, quot_mk_to_coe
-/
theorem mem_powersetCardAux {n} {l : List α} {s} : s in powersetCardAux n l ↔ s <= ↑l ∧ card s = n :=
Quotient.inductionOn s by
    simp only [quot_mk_to_coe, powersetCardAux_eq_map_coe, List.mem_map, mem_sublistsLen,
      coe_eq_coe, coe_le, Subperm, coe_card]
    exact fun l₁ =>
      ⟨fun ⟨l₂, ⟨s, e⟩, p⟩ => ⟨⟨_, p, s⟩, p.symm.length_eq.trans e⟩,
       fun ⟨⟨l₂, p, s⟩, e⟩ => ⟨_, ⟨s, p.length_eq.trans e⟩, p⟩⟩

@[simp]
/--
theorem `powersetCardAux_zero` / 定理 `powersetCardAux_zero`

English:
theorem powersetCardAux_zero
  given: (l : List α)
  statement: powersetCardAux 0 l = [0]
  proof: by
  simp [powersetCardAux_eq_map_coe]

@[simp]

中文:
定理 powersetCardAux_zero
  条件: (l : List α)
  结论: powersetCardAux 0 l = [0]
  证明: by
  simp [powersetCardAux_eq_map_coe]

@[simp]

Depends on / 依赖: powersetCardAux_eq_map_coe
-/
theorem powersetCardAux_zero (l : List α) : powersetCardAux 0 l = [0] := by
  simp [powersetCardAux_eq_map_coe]

@[simp]
/--
theorem `powersetCardAux_nil` / 定理 `powersetCardAux_nil`

English:
theorem powersetCardAux_nil
  given: (n : Nat)
  statement: powersetCardAux (n + 1) (@nil α) = []
  proof: rfl

@[simp]

中文:
定理 powersetCardAux_nil
  条件: (n : 自然数)
  结论: powersetCardAux (n + 1) (@nil α) = []
  证明: rfl

@[simp]
-/
theorem powersetCardAux_nil (n : Nat) : powersetCardAux (n + 1) (@nil α) = [] :=
  rfl

@[simp]
/--
theorem `powersetCardAux_cons` / 定理 `powersetCardAux_cons`

English:
theorem powersetCardAux_cons
  given: (n : Nat) (a : α) (l : List α)
  proof: by
  simp [powersetCardAux_eq_map_coe]

中文:
定理 powersetCardAux_cons
  条件: (n : 自然数) (a : α) (l : List α)
  证明: by
  simp [powersetCardAux_eq_map_coe]

Depends on / 依赖: powersetCardAux_eq_map_coe
-/
theorem powersetCardAux_cons (n : Nat) (a : α) (l : List α) :
    powersetCardAux (n + 1) (a :: l) =
      powersetCardAux (n + 1) l ++ List.map (cons a) (powersetCardAux n l) := by
  simp [powersetCardAux_eq_map_coe]

/--
theorem `powersetCardAux_perm` / 定理 `powersetCardAux_perm`

English:
theorem powersetCardAux_perm
  given: {n} {l₁ l₂ : List α} (p : l₁ ~ l₂)
  proof: by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction p with
  | nil => rfl
  | cons _ p IH =>
    simp only [powersetCardAux_cons]
    exact IH.append ((IHn p).map _)
  | swap a b =>
    simp only [powersetCardAux_cons, append_assoc]
    apply Perm.append_left
    c

中文:
定理 powersetCardAux_perm
  条件: {n} {l₁ l₂ : List α} (p : l₁ ~ l₂)
  证明: by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction p with
  | nil => rfl
  | cons _ p IH =>
    simp only [powersetCardAux_cons]
    exact IH.append ((IHn p).map _)
  | swap a b =>
    simp only [powersetCardAux_cons, append_assoc]
    apply Perm.append_left
    c

Depends on / 依赖: IH.append, List.map_map, Perm.append_left, Perm.swap, append, append_, append_assoc, append_left, cons_swap, generalizing, map_append, map_map, perm_append_comm, perm_append_comm.append_, powersetCardAux_cons
-/
theorem powersetCardAux_perm {n} {l₁ l₂ : List α} (p : l₁ ~ l₂) :
    powersetCardAux n l₁ ~ powersetCardAux n l₂ := by
  induction n generalizing l₁ l₂ with | zero => simp | succ n IHn => ?_
  induction p with
  | nil => rfl
  | cons _ p IH =>
    simp only [powersetCardAux_cons]
    exact IH.append ((IHn p).map _)
  | swap a b =>
    simp only [powersetCardAux_cons, append_assoc]
    apply Perm.append_left
    cases n
    · simp [Perm.swap]
    simp only [powersetCardAux_cons, map_append, List.map_map]
    rw [← append_assoc]; rw [← append_assoc]; rw [(by funext s; simp [cons_swap] : cons b ∘ cons a = cons a ∘ cons b)]
    exact perm_append_comm.append_right _
  | trans _ _ IH₁ IH₂ => exact IH₁.trans IH₂

/--
Definition of `powersetCard` / `powersetCard` 的定义

English:
definition powersetCard
  signature: (n : Nat) (s : Multiset α)
  body: Quot.liftOn s (fun l => (powersetCardAux n l : Multiset (Multiset α))) fun _ _ h =>
    Quot.sound (powersetCardAux_perm h)

中文:
定义 powersetCard
  签名: (n : 自然数) (s : Multiset α)
  定义体: Quot.liftOn s (fun l => (powersetCardAux n l : Multiset (Multiset α))) fun _ _ h =>
    Quot.sound (powersetCardAux_perm h)

Depends on / 依赖: Multiset, Quot.liftOn, Quot.sound, liftOn, powersetCardAux, powersetCardAux_perm
-/
def powersetCard (n : Nat) (s : Multiset α) : Multiset (Multiset α) :=
  Quot.liftOn s (fun l => (powersetCardAux n l : Multiset (Multiset α))) fun _ _ h =>
    Quot.sound (powersetCardAux_perm h)

/--
theorem `powersetCard_coe'` / 定理 `powersetCard_coe'`

English:
theorem powersetCard_coe'
  given: (n) (l : List α)
  statement: @powersetCard α n l = powersetCardAux n l
  proof: rfl

中文:
定理 powersetCard_coe'
  条件: (n) (l : List α)
  结论: @powersetCard α n l = powersetCardAux n l
  证明: rfl
-/
theorem powersetCard_coe' (n) (l : List α) : @powersetCard α n l = powersetCardAux n l :=
  rfl

/--
theorem `powersetCard_coe` / 定理 `powersetCard_coe`

English:
theorem powersetCard_coe
  given: (n) (l : List α)
  proof: congr_arg ((↑) : List (Multiset α) -> Multiset (Multiset α)) powersetCardAux_eq_map_coe

@[simp]

中文:
定理 powersetCard_coe
  条件: (n) (l : List α)
  证明: congr_arg ((↑) : List (Multiset α) -> Multiset (Multiset α)) powersetCardAux_eq_map_coe

@[simp]

Depends on / 依赖: Multiset, congr_arg, powersetCardAux_eq_map_coe
-/
theorem powersetCard_coe (n) (l : List α) :
    @powersetCard α n l = ((sublistsLen n l).map (↑) : List (Multiset α)) :=
  congr_arg ((↑) : List (Multiset α) -> Multiset (Multiset α)) powersetCardAux_eq_map_coe

@[simp]
/--
theorem `powersetCard_zero_left` / 定理 `powersetCard_zero_left`

English:
theorem powersetCard_zero_left
  given: (s : Multiset α)
  statement: powersetCard 0 s = {0}
  proof: Quotient.inductionOn s fun l => by simp [powersetCard_coe']

中文:
定理 powersetCard_zero_left
  条件: (s : Multiset α)
  结论: powersetCard 0 s = {0}
  证明: Quotient.inductionOn s fun l => by simp [powersetCard_coe']

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, powersetCard_coe
-/
theorem powersetCard_zero_left (s : Multiset α) : powersetCard 0 s = {0} :=
  Quotient.inductionOn s fun l => by simp [powersetCard_coe']

/--
theorem `powersetCard_zero_right` / 定理 `powersetCard_zero_right`

English:
theorem powersetCard_zero_right
  given: (n : Nat)
  statement: @powersetCard α (n + 1) 0 = 0
  proof: rfl

@[simp]

中文:
定理 powersetCard_zero_right
  条件: (n : 自然数)
  结论: @powersetCard α (n + 1) 0 = 0
  证明: rfl

@[simp]
-/
theorem powersetCard_zero_right (n : Nat) : @powersetCard α (n + 1) 0 = 0 :=
  rfl

@[simp]
/--
theorem `powersetCard_cons` / 定理 `powersetCard_cons`

English:
theorem powersetCard_cons
  given: (n : Nat) (a : α) (s)
  proof: Quotient.inductionOn s fun l => by simp [powersetCard_coe']

中文:
定理 powersetCard_cons
  条件: (n : 自然数) (a : α) (s)
  证明: Quotient.inductionOn s fun l => by simp [powersetCard_coe']

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, powersetCard_coe
-/
theorem powersetCard_cons (n : Nat) (a : α) (s) :
    powersetCard (n + 1) (a ::ₘ s) = powersetCard (n + 1) s + map (cons a) (powersetCard n s) :=
  Quotient.inductionOn s fun l => by simp [powersetCard_coe']

/--
theorem `powersetCard_one` / 定理 `powersetCard_one`

English:
theorem powersetCard_one
  given: (s : Multiset α)
  statement: powersetCard 1 s = s.map singleton
  proof: Quotient.inductionOn s fun l => by
    simp [powersetCard_coe, sublistsLen_one, map_reverse, Function.comp_def]

@[simp]

中文:
定理 powersetCard_one
  条件: (s : Multiset α)
  结论: powersetCard 1 s = s.map singleton
  证明: Quotient.inductionOn s fun l => by
    simp [powersetCard_coe, sublistsLen_one, map_reverse, Function.comp_def]

@[simp]

Depends on / 依赖: Function, Function.comp_def, Quotient, Quotient.inductionOn, comp_def, inductionOn, map_reverse, powersetCard_coe, sublistsLen_one
-/
theorem powersetCard_one (s : Multiset α) : powersetCard 1 s = s.map singleton :=
  Quotient.inductionOn s fun l => by
    simp [powersetCard_coe, sublistsLen_one, map_reverse, Function.comp_def]

@[simp]
/--
theorem `mem_powersetCard` / 定理 `mem_powersetCard`

English:
theorem mem_powersetCard
  given: {n : Nat} {s t : Multiset α}
  statement: s in powersetCard n t ↔ s <= t ∧ card s = n
  proof: Quotient.inductionOn t fun l => by simp [powersetCard_coe']

@[simp]

中文:
定理 mem_powersetCard
  条件: {n : 自然数} {s t : Multiset α}
  结论: s in powersetCard n t ↔ s <= t ∧ card s = n
  证明: Quotient.inductionOn t fun l => by simp [powersetCard_coe']

@[simp]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, powersetCard_coe
-/
theorem mem_powersetCard {n : Nat} {s t : Multiset α} : s in powersetCard n t ↔ s <= t ∧ card s = n :=
  Quotient.inductionOn t fun l => by simp [powersetCard_coe']

@[simp]
/--
theorem `card_powersetCard` / 定理 `card_powersetCard`

English:
theorem card_powersetCard
  given: (n : Nat) (s : Multiset α)
  proof: Quotient.inductionOn s by simp [powersetCard_coe]

中文:
定理 card_powersetCard
  条件: (n : 自然数) (s : Multiset α)
  证明: Quotient.inductionOn s by simp [powersetCard_coe]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, powersetCard_coe
-/
theorem card_powersetCard (n : Nat) (s : Multiset α) :
    card (powersetCard n s) = Nat.choose (card s) n :=
Quotient.inductionOn s by simp [powersetCard_coe]

/--
theorem `powersetCard_le_powerset` / 定理 `powersetCard_le_powerset`

English:
theorem powersetCard_le_powerset
  given: (n : Nat) (s : Multiset α)
  statement: powersetCard n s <= powerset s
  proof: Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, powersetCard_coe, powerset_coe', coe_le]
    exact ((sublistsLen_sublist_sublists' _ _).map _).subperm

中文:
定理 powersetCard_le_powerset
  条件: (n : 自然数) (s : Multiset α)
  结论: powersetCard n s <= powerset s
  证明: Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, powersetCard_coe, powerset_coe', coe_le]
    exact ((sublistsLen_sublist_sublists' _ _).map _).subperm

Depends on / 依赖: Quotient, Quotient.inductionOn, coe_le, congr_arg, dropn_add, inductionOn, powersetCard_coe, powerset_coe, quot_mk_to_coe, sublistsLen_sublist_sublists, subperm
-/
theorem powersetCard_le_powerset (n : Nat) (s : Multiset α) : powersetCard n s <= powerset s :=
  Quotient.inductionOn s fun l => by
    simp only [quot_mk_to_coe, powersetCard_coe, powerset_coe', coe_le]
    exact ((sublistsLen_sublist_sublists' _ _).map _).subperm

/--
theorem `powersetCard_mono` / 定理 `powersetCard_mono`

English:
theorem powersetCard_mono
  given: (n : Nat) {s t : Multiset α} (h : s <= t)
  proof: leInductionOn h fun {l₁ l₂} h => by
    simp only [powersetCard_coe, coe_le]
    exact ((sublistsLen_sublist_of_sublist _ h).map _).subperm

@[simp]

中文:
定理 powersetCard_mono
  条件: (n : 自然数) {s t : Multiset α} (h : s <= t)
  证明: leInductionOn h fun {l₁ l₂} h => by
    simp only [powersetCard_coe, coe_le]
    exact ((sublistsLen_sublist_of_sublist _ h).map _).subperm

@[simp]

Depends on / 依赖: coe_le, congr_arg, dropn_tail, leInductionOn, powersetCard_coe, sublistsLen_sublist_of_sublist, subperm
-/
theorem powersetCard_mono (n : Nat) {s t : Multiset α} (h : s <= t) :
    powersetCard n s <= powersetCard n t :=
  leInductionOn h fun {l₁ l₂} h => by
    simp only [powersetCard_coe, coe_le]
    exact ((sublistsLen_sublist_of_sublist _ h).map _).subperm

@[simp]
/--
theorem `powersetCard_eq_empty` / 定理 `powersetCard_eq_empty`

English:
theorem powersetCard_eq_empty
  given: {α : Type*} (n : Nat) {s : Multiset α} (h : card s < n)
  proof: card_eq_zero.mp (Nat.choose_eq_zero_of_lt h ▸ card_powersetCard _ _)

中文:
定理 powersetCard_eq_empty
  条件: {α : 类型} (n : 自然数) {s : Multiset α} (h : card s < n)
  证明: card_eq_zero.mp (Nat.choose_eq_zero_of_lt h ▸ card_powersetCard _ _)

Depends on / 依赖: Nat.choose_eq_zero_of_lt, card_eq_zero, card_eq_zero.mp, card_powersetCard, choose_eq_zero_of_lt
-/
theorem powersetCard_eq_empty {α : Type*} (n : Nat) {s : Multiset α} (h : card s < n) :
    powersetCard n s = 0 :=
  card_eq_zero.mp (Nat.choose_eq_zero_of_lt h ▸ card_powersetCard _ _)

/--
theorem `powersetCard_card_add` / 定理 `powersetCard_card_add`

English:
theorem powersetCard_card_add
  given: (s : Multiset α) {i : Nat} (hi : 0 < i)
  proof: by
  simp [hi]

@[simp]

中文:
定理 powersetCard_card_add
  条件: (s : Multiset α) {i : 自然数} (hi : 0 < i)
  证明: by
  simp [hi]

@[simp]
-/
theorem powersetCard_card_add (s : Multiset α) {i : Nat} (hi : 0 < i) :
    s.powersetCard (card s + i) = 0 := by
  simp [hi]

@[simp]
/--
theorem `powersetCard_self` / 定理 `powersetCard_self`

English:
theorem powersetCard_self
  given: (s : Multiset α)
  statement: powersetCard s.card s = {s}
  proof: by
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

中文:
定理 powersetCard_self
  条件: (s : Multiset α)
  结论: powersetCard s.card s = {s}
  证明: by
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

Depends on / 依赖: Multiset, Multiset.induction
-/
theorem powersetCard_self (s : Multiset α) : powersetCard s.card s = {s} := by
  induction s using Multiset.induction with
  | empty => simp
  | cons _ _ ih => simp [ih]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `powersetCard_map` / 定理 `powersetCard_map`

English:
theorem powersetCard_map
  given: {β : Type*} (f : α -> β) (n : Nat) (s : Multiset α)
  proof: by
  induction s using Multiset.induction generalizing n with
  | empty => cases n <;> simp [powersetCard_zero_left]
  | cons t s ih => cases n <;> simp [ih]

中文:
定理 powersetCard_map
  条件: {β : 类型} (f : α -> β) (n : 自然数) (s : Multiset α)
  证明: by
  induction s using Multiset.induction generalizing n with
  | empty => cases n <;> simp [powersetCard_zero_left]
  | cons t s ih => cases n <;> simp [ih]

Depends on / 依赖: Multiset, Multiset.induction, generalizing, powersetCard_zero_left
-/
theorem powersetCard_map {β : Type*} (f : α -> β) (n : Nat) (s : Multiset α) :
    powersetCard n (s.map f) = (powersetCard n s).map (map f) := by
  induction s using Multiset.induction generalizing n with
  | empty => cases n <;> simp [powersetCard_zero_left]
  | cons t s ih => cases n <;> simp [ih]

/--
theorem `pairwise_disjoint_powersetCard` / 定理 `pairwise_disjoint_powersetCard`

English:
theorem pairwise_disjoint_powersetCard
  given: (s : Multiset α)
  proof: fun _ _ h => disjoint_left.mpr fun hi hj =>
    h ((Multiset.mem_powersetCard.mp hi).2.symm.trans (Multiset.mem_powersetCard.mp hj).2)

中文:
定理 pairwise_disjoint_powersetCard
  条件: (s : Multiset α)
  证明: fun _ _ h => disjoint_left.mpr fun hi hj =>
    h ((Multiset.mem_powersetCard.mp hi).2.symm.trans (Multiset.mem_powersetCard.mp hj).2)

Depends on / 依赖: Multiset, Multiset.mem_powersetCard.mp, disjoint_left, disjoint_left.mpr, mem_powersetCard, symm.trans
-/
theorem pairwise_disjoint_powersetCard (s : Multiset α) :
    _root_.Pairwise fun i j => Disjoint (s.powersetCard i) (s.powersetCard j) :=
  fun _ _ h => disjoint_left.mpr fun hi hj =>
    h ((Multiset.mem_powersetCard.mp hi).2.symm.trans (Multiset.mem_powersetCard.mp hj).2)

/--
theorem `bind_powerset_len` / 定理 `bind_powerset_len`

English:
theorem bind_powerset_len
  given: {α : Type*} (S : Multiset α)
  proof: by
  induction S using Quotient.inductionOn
  simp_rw [quot_mk_to_coe, powerset_coe', powersetCard_coe, ← coe_range, coe_bind,
    ← List.map_flatMap, coe_card]
  exact coe_eq_coe.mpr ((List.range_bind_sublistsLen_perm _).map _)

@[simp]

中文:
定理 bind_powerset_len
  条件: {α : 类型} (S : Multiset α)
  证明: by
  induction S using Quotient.inductionOn
  simp_rw [quot_mk_to_coe, powerset_coe', powersetCard_coe, ← coe_range, coe_bind,
    ← List.map_flatMap, coe_card]
  exact coe_eq_coe.mpr ((List.range_bind_sublistsLen_perm _).map _)

@[simp]

Depends on / 依赖: List.map_flatMap, List.range_bind_sublistsLen_perm, Quotient, Quotient.inductionOn, coe_bind, coe_card, coe_eq_coe, coe_eq_coe.mpr, coe_range, inductionOn, map_flatMap, powersetCard_coe, powerset_coe, quot_mk_to_coe, range_bind_sublistsLen_perm, simp_rw
-/
theorem bind_powerset_len {α : Type*} (S : Multiset α) :
    (bind (Multiset.range (card S + 1)) fun k => S.powersetCard k) = S.powerset := by
  induction S using Quotient.inductionOn
  simp_rw [quot_mk_to_coe, powerset_coe', powersetCard_coe, ← coe_range, coe_bind,
    ← List.map_flatMap, coe_card]
  exact coe_eq_coe.mpr ((List.range_bind_sublistsLen_perm _).map _)

@[simp]
/--
theorem `nodup_powerset` / 定理 `nodup_powerset`

English:
theorem nodup_powerset
  given: {s : Multiset α}
  statement: Nodup (powerset s) ↔ Nodup s
  proof: ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    Quotient.inductionOn s fun l h => by
      simp only [quot_mk_to_coe, powerset_coe', coe_nodup]
      refine (nodup_sublists'.2 h).map_on ?_
      exact fun x sx y sy e =>
        (h.perm_iff_eq_of_sublist (mem_sublists'.1 sx) (mem_s

中文:
定理 nodup_powerset
  条件: {s : Multiset α}
  结论: Nodup (powerset s) ↔ Nodup s
  证明: ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    Quotient.inductionOn s fun l h => by
      simp only [quot_mk_to_coe, powerset_coe', coe_nodup]
      refine (nodup_sublists'.2 h).map_on ?_
      exact fun x sx y sy e =>
        (h.perm_iff_eq_of_sublist (mem_sublists'.1 sx) (mem_s

Depends on / 依赖: Quotient, Quotient.exact, Quotient.inductionOn, coe_nodup, h.perm_iff_eq_of_sublist, inductionOn, map_on, map_single_le_powerset, mem_sublists, nodup_of_le, nodup_sublists, of_map, perm_iff_eq_of_sublist, powerset_coe, quot_mk_to_coe
-/
theorem nodup_powerset {s : Multiset α} : Nodup (powerset s) ↔ Nodup s :=
  ⟨fun h => (nodup_of_le (map_single_le_powerset _) h).of_map _,
    Quotient.inductionOn s fun l h => by
      simp only [quot_mk_to_coe, powerset_coe', coe_nodup]
      refine (nodup_sublists'.2 h).map_on ?_
      exact fun x sx y sy e =>
        (h.perm_iff_eq_of_sublist (mem_sublists'.1 sx) (mem_sublists'.1 sy)).1 (Quotient.exact e)⟩

alias ⟨Nodup.ofPowerset, Nodup.powerset⟩ := nodup_powerset

/--
theorem `Nodup.powersetCard` / 定理 `Nodup.powersetCard`

English:
theorem Nodup.powersetCard
  given: {n : Nat} {s : Multiset α} (h : Nodup s)
  proof: nodup_of_le (powersetCard_le_powerset _ _) (nodup_powerset.2 h)

中文:
定理 Nodup.powersetCard
  条件: {n : 自然数} {s : Multiset α} (h : Nodup s)
  证明: nodup_of_le (powersetCard_le_powerset _ _) (nodup_powerset.2 h)
-/
protected theorem Nodup.powersetCard {n : Nat} {s : Multiset α} (h : Nodup s) :
    Nodup (powersetCard n s) :=
  nodup_of_le (powersetCard_le_powerset _ _) (nodup_powerset.2 h)

end Multiset
