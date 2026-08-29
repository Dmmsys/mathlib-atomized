/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Simon Hudon
-/
module

public import Batteries.Tactic.Alias
public import Batteries.Data.List.Basic
public import Mathlib.Init

/-!
# The Following Are Equivalent

This file allows to state that all propositions in a list are equivalent. It is used by
`Mathlib/Tactic/Tfae.lean`.
`TFAE l` means `∀ x ∈ l, ∀ y ∈ l, x ↔ y`. This is equivalent to `Pairwise (↔) l`.
-/

@[expose] public section


namespace List

/--
Definition of `TFAE` / `TFAE` 的定义

English:
definition TFAE
  signature: (l : List Prop)
  body: forall x in l, forall y in l, x ↔ y

中文:
定义 TFAE
  签名: (l : List 命题)
  定义体: forall x in l, forall y in l, x ↔ y
-/
def TFAE (l : List Prop) : Prop :=
  forall x in l, forall y in l, x ↔ y

/--
theorem `tfae_nil` / 定理 `tfae_nil`

English:
theorem tfae_nil
  statement: TFAE []
  proof: forall_mem_nil _

@[simp]

中文:
定理 tfae_nil
  结论: TFAE []
  证明: forall_mem_nil _

@[simp]

Depends on / 依赖: forall_mem_nil
-/
theorem tfae_nil : TFAE [] :=
  forall_mem_nil _

@[simp]
/--
theorem `tfae_singleton` / 定理 `tfae_singleton`

English:
theorem tfae_singleton
  given: (p)
  statement: TFAE [p]
  proof: by simp [TFAE, -eq_iff_iff]

中文:
定理 tfae_singleton
  条件: (p)
  结论: TFAE [p]
  证明: by simp [TFAE, -eq_iff_iff]

Depends on / 依赖: eq_iff_iff
-/
theorem tfae_singleton (p) : TFAE [p] := by simp [TFAE, -eq_iff_iff]

/--
theorem `tfae_cons_of_mem` / 定理 `tfae_cons_of_mem`

English:
theorem tfae_cons_of_mem
  given: {a b} {l : List Prop} (h : b in l)
  statement: TFAE (a :: l) ↔ (a ↔ b) ∧ TFAE l
  proof: ⟨fun H => ⟨H a (by simp) b (Mem.tail a h),
    fun _ hp _ hq => H _ (Mem.tail a hp) _ (Mem.tail a hq)⟩,
      by
        rintro ⟨ab, H⟩ p (_ | ⟨_, hp⟩) q (_ | ⟨_, hq⟩)
        · rfl
        · exact ab.trans (H _ h _ hq)
        · exact (ab.trans (H _ h _ hp)).symm
        · exact H _ hp _ hq⟩

中文:
定理 tfae_cons_of_mem
  条件: {a b} {l : List 命题} (h : b in l)
  结论: TFAE (a :: l) ↔ (a ↔ b) ∧ TFAE l
  证明: ⟨fun H => ⟨H a (by simp) b (Mem.tail a h),
    fun _ hp _ hq => H _ (Mem.tail a hp) _ (Mem.tail a hq)⟩,
      by
        rintro ⟨ab, H⟩ p (_ | ⟨_, hp⟩) q (_ | ⟨_, hq⟩)
        · rfl
        · exact ab.trans (H _ h _ hq)
        · exact (ab.trans (H _ h _ hp)).symm
        · exact H _ hp _ hq⟩

Depends on / 依赖: Mem.tail, ab.trans
-/
theorem tfae_cons_of_mem {a b} {l : List Prop} (h : b in l) : TFAE (a :: l) ↔ (a ↔ b) ∧ TFAE l :=
  ⟨fun H => ⟨H a (by simp) b (Mem.tail a h),
    fun _ hp _ hq => H _ (Mem.tail a hp) _ (Mem.tail a hq)⟩,
      by
        rintro ⟨ab, H⟩ p (_ | ⟨_, hp⟩) q (_ | ⟨_, hq⟩)
        · rfl
        · exact ab.trans (H _ h _ hq)
        · exact (ab.trans (H _ h _ hp)).symm
        · exact H _ hp _ hq⟩

/--
theorem `tfae_cons_cons` / 定理 `tfae_cons_cons`

English:
theorem tfae_cons_cons
  given: {a b} {l : List Prop}
  statement: TFAE (a :: b :: l) ↔ (a ↔ b) ∧ TFAE (b :: l)
  proof: tfae_cons_of_mem (Mem.head _)

@[simp]

中文:
定理 tfae_cons_cons
  条件: {a b} {l : List 命题}
  结论: TFAE (a :: b :: l) ↔ (a ↔ b) ∧ TFAE (b :: l)
  证明: tfae_cons_of_mem (Mem.head _)

@[simp]

Depends on / 依赖: Mem.head, tfae_cons_of_mem
-/
theorem tfae_cons_cons {a b} {l : List Prop} : TFAE (a :: b :: l) ↔ (a ↔ b) ∧ TFAE (b :: l) :=
  tfae_cons_of_mem (Mem.head _)

@[simp]
/--
theorem `tfae_cons_self` / 定理 `tfae_cons_self`

English:
theorem tfae_cons_self
  given: {a} {l : List Prop}
  statement: TFAE (a :: a :: l) ↔ TFAE (a :: l)
  proof: by
  simp [tfae_cons_cons]

中文:
定理 tfae_cons_self
  条件: {a} {l : List 命题}
  结论: TFAE (a :: a :: l) ↔ TFAE (a :: l)
  证明: by
  simp [tfae_cons_cons]

Depends on / 依赖: tfae_cons_cons
-/
theorem tfae_cons_self {a} {l : List Prop} : TFAE (a :: a :: l) ↔ TFAE (a :: l) := by
  simp [tfae_cons_cons]

/--
theorem `tfae_of_forall` / 定理 `tfae_of_forall`

English:
theorem tfae_of_forall
  given: (b : Prop) (l : List Prop) (h : forall a in l, a ↔ b)
  statement: TFAE l
  proof: fun _a₁ h₁ _a₂ h₂ => (h _ h₁).trans (h _ h₂).symm

中文:
定理 tfae_of_forall
  条件: (b : 命题) (l : List 命题) (h : 对任意 a in l, a ↔ b)
  结论: TFAE l
  证明: fun _a₁ h₁ _a₂ h₂ => (h _ h₁).trans (h _ h₂).symm
-/
theorem tfae_of_forall (b : Prop) (l : List Prop) (h : forall a in l, a ↔ b) : TFAE l :=
  fun _a₁ h₁ _a₂ h₂ => (h _ h₁).trans (h _ h₂).symm

/--
theorem `tfae_of_cycle` / 定理 `tfae_of_cycle`

English:
theorem tfae_of_cycle
  statement: {a b} {l : List Prop} (h_chain : List.IsChain (· -> ·) (a :: b :: l))
  proof: by
  induction l generalizing a b with
  | nil => simp_all [tfae_cons_cons, iff_def]
  | cons c l IH =>
    simp only [tfae_cons_cons, getLastD_cons, isChain_cons_cons] at *
    rcases h_chain with ⟨ab, ⟨bc, ch⟩⟩
    have := IH ⟨bc, ch⟩ (ab ∘ h_last)
    exact ⟨⟨ab, h_last ∘ (this.2 c (.head _) _ ge

中文:
定理 tfae_of_cycle
  结论: {a b} {l : List 命题} (h_chain : List.IsChain (· -> ·) (a :: b :: l))
  证明: by
  induction l generalizing a b with
  | nil => simp_all [tfae_cons_cons, iff_def]
  | cons c l IH =>
    simp only [tfae_cons_cons, getLastD_cons, isChain_cons_cons] at *
    rcases h_chain with ⟨ab, ⟨bc, ch⟩⟩
    have := IH ⟨bc, ch⟩ (ab ∘ h_last)
    exact ⟨⟨ab, h_last ∘ (this.2 c (.head _) _ ge

Depends on / 依赖: generalizing, getLastD_cons, getLastD_mem_cons, h_chain, h_last, iff_def, isChain_cons_cons, tfae_cons_cons
-/
theorem tfae_of_cycle {a b} {l : List Prop} (h_chain : List.IsChain (· -> ·) (a :: b :: l))
    (h_last : getLastD l b -> a) : TFAE (a :: b :: l) := by
  induction l generalizing a b with
  | nil => simp_all [tfae_cons_cons, iff_def]
  | cons c l IH =>
    simp only [tfae_cons_cons, getLastD_cons, isChain_cons_cons] at *
    rcases h_chain with ⟨ab, ⟨bc, ch⟩⟩
    have := IH ⟨bc, ch⟩ (ab ∘ h_last)
    exact ⟨⟨ab, h_last ∘ (this.2 c (.head _) _ getLastD_mem_cons).1 ∘ bc⟩, this⟩

/--
theorem `TFAE.out` / 定理 `TFAE.out`

English:
theorem TFAE.out
  statement: {l} (h : TFAE l) (n₁ n₂ : Nat) {a b}
  proof: h _ (List.mem_of_getElem? h₁) _ (List.mem_of_getElem? h₂)

中文:
定理 TFAE.out
  结论: {l} (h : TFAE l) (n₁ n₂ : 自然数) {a b}
  证明: h _ (List.mem_of_getElem? h₁) _ (List.mem_of_getElem? h₂)

Depends on / 依赖: List.mem_of_getElem, mem_of_getElem
-/
theorem TFAE.out {l} (h : TFAE l) (n₁ n₂ : Nat) {a b}
    (h₁ : l[n₁]? = some a := by rfl)
    (h₂ : l[n₂]? = some b := by rfl) :
    a ↔ b :=
  h _ (List.mem_of_getElem? h₁) _ (List.mem_of_getElem? h₂)

/--
theorem `forall_tfae` / 定理 `forall_tfae`

English:
theorem forall_tfae
  given: {α : Type*} (l : List (α -> Prop)) (H : forall a : α, (l.map (fun p => p a)).TFAE)
  proof: by
  simp only [TFAE, List.forall_mem_map]
  intro p₁ hp₁ p₂ hp₂
  exact forall_congr' fun a => H a (p₁ a) (mem_map_of_mem hp₁)
    (p₂ a) (mem_map_of_mem hp₂)

中文:
定理 forall_tfae
  条件: {α : 类型} (l : List (α -> 命题)) (H : 对任意 a : α, (l.map (fun p => p a)).TFAE)
  证明: by
  simp only [TFAE, List.forall_mem_map]
  intro p₁ hp₁ p₂ hp₂
  exact forall_congr' fun a => H a (p₁ a) (mem_map_of_mem hp₁)
    (p₂ a) (mem_map_of_mem hp₂)

Depends on / 依赖: List.forall_mem_map, forall_congr, forall_mem_map, mem_map_of_mem
-/
theorem forall_tfae {α : Type*} (l : List (α -> Prop)) (H : forall a : α, (l.map (fun p => p a)).TFAE) :
    (l.map (fun p => forall a, p a)).TFAE := by
  simp only [TFAE, List.forall_mem_map]
  intro p₁ hp₁ p₂ hp₂
  exact forall_congr' fun a => H a (p₁ a) (mem_map_of_mem hp₁)
    (p₂ a) (mem_map_of_mem hp₂)

/--
theorem `exists_tfae` / 定理 `exists_tfae`

English:
theorem exists_tfae
  given: {α : Type*} (l : List (α -> Prop)) (H : forall a : α, (l.map (fun p => p a)).TFAE)
  proof: by
  simp only [TFAE, List.forall_mem_map]
  intro p₁ hp₁ p₂ hp₂
  exact exists_congr fun a => H a (p₁ a) (mem_map_of_mem hp₁)
    (p₂ a) (mem_map_of_mem hp₂)

中文:
定理 exists_tfae
  条件: {α : 类型} (l : List (α -> 命题)) (H : 对任意 a : α, (l.map (fun p => p a)).TFAE)
  证明: by
  simp only [TFAE, List.forall_mem_map]
  intro p₁ hp₁ p₂ hp₂
  exact exists_congr fun a => H a (p₁ a) (mem_map_of_mem hp₁)
    (p₂ a) (mem_map_of_mem hp₂)

Depends on / 依赖: List.forall_mem_map, exists_congr, forall_mem_map, mem_map_of_mem
-/
theorem exists_tfae {α : Type*} (l : List (α -> Prop)) (H : forall a : α, (l.map (fun p => p a)).TFAE) :
    (l.map (fun p => exists a, p a)).TFAE := by
  simp only [TFAE, List.forall_mem_map]
  intro p₁ hp₁ p₂ hp₂
  exact exists_congr fun a => H a (p₁ a) (mem_map_of_mem hp₁)
    (p₂ a) (mem_map_of_mem hp₂)

/--
theorem `tfae_not_iff` / 定理 `tfae_not_iff`

English:
theorem tfae_not_iff
  given: {l : List Prop}
  statement: TFAE (l.map Not) ↔ TFAE l
  proof: by
  classical
  simp only [TFAE, mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Decidable.not_iff_not]

alias ⟨_, TFAE.not⟩ := tfae_not_iff

中文:
定理 tfae_not_iff
  条件: {l : List 命题}
  结论: TFAE (l.map Not) ↔ TFAE l
  证明: by
  classical
  simp only [TFAE, mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Decidable.not_iff_not]

alias ⟨_, TFAE.not⟩ := tfae_not_iff

Depends on / 依赖: Decidable, Decidable.not_iff_not, and_imp, classical, forall_exists_index, mem_map, not_iff_not
-/
theorem tfae_not_iff {l : List Prop} : TFAE (l.map Not) ↔ TFAE l := by
  classical
  simp only [TFAE, mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
    Decidable.not_iff_not]

alias ⟨_, TFAE.not⟩ := tfae_not_iff

end List
