/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# Monotone functions on bounded orders

-/

public section

assert_not_exists SemilatticeSup

open Function OrderDual

universe u v

variable {α : Type u} {β : Type v}

/-! ### Top, bottom element -/

section OrderTop

variable [PartialOrder α] [OrderTop α] [Preorder β] {f : α -> β} {a b : α}

/--
theorem `StrictMono.apply_eq_top_iff` / 定理 `StrictMono.apply_eq_top_iff`

English:
theorem StrictMono.apply_eq_top_iff
  given: (hf : StrictMono f)
  statement: f a = f ⊤ ↔ a = ⊤
  proof: ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne h, congr_arg _⟩

中文:
定理 严格递增.apply_eq_top_iff
  条件: (hf : 严格递增 f)
  结论: f a = f ⊤ ↔ a = ⊤
  证明: ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne h, congr_arg _⟩

Depends on / 依赖: congr_arg, not_lt_top_iff
-/
theorem StrictMono.apply_eq_top_iff (hf : StrictMono f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne h, congr_arg _⟩

/--
theorem `StrictAnti.apply_eq_top_iff` / 定理 `StrictAnti.apply_eq_top_iff`

English:
theorem StrictAnti.apply_eq_top_iff
  given: (hf : StrictAnti f)
  statement: f a = f ⊤ ↔ a = ⊤
  proof: ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne' h, congr_arg _⟩

中文:
定理 严格递减.apply_eq_top_iff
  条件: (hf : 严格递减 f)
  结论: f a = f ⊤ ↔ a = ⊤
  证明: ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne' h, congr_arg _⟩

Depends on / 依赖: congr_arg, not_lt_top_iff
-/
theorem StrictAnti.apply_eq_top_iff (hf : StrictAnti f) : f a = f ⊤ ↔ a = ⊤ :=
  ⟨fun h => not_lt_top_iff.1 fun ha => (hf ha).ne' h, congr_arg _⟩

end OrderTop

/--
theorem `StrictMono.maximal_preimage_top` / 定理 `StrictMono.maximal_preimage_top`

English:
theorem StrictMono.maximal_preimage_top
  statement: [LinearOrder α] [Preorder β] [OrderTop β] {f : α -> β}
  proof: H.maximal_of_maximal_image
    (fun p => by
      rw [h_top]
      exact le_top)
    x

中文:
定理 严格递增.maximal_preimage_top
  结论: [线性序 α] [预序 β] [有顶序 β] {f : α -> β}
  证明: H.maximal_of_maximal_image
    (fun p => by
      rw [h_top]
      exact le_top)
    x

Depends on / 依赖: H.maximal_of_maximal_image, h_top, le_top, maximal_of_maximal_image
-/
theorem StrictMono.maximal_preimage_top [LinearOrder α] [Preorder β] [OrderTop β] {f : α -> β}
    (H : StrictMono f) {a} (h_top : f a = ⊤) (x : α) : x <= a :=
  H.maximal_of_maximal_image
    (fun p => by
      rw [h_top]
      exact le_top)
    x

section OrderBot

variable [PartialOrder α] [OrderBot α] [Preorder β] {f : α -> β} {a b : α}

/--
theorem `StrictMono.apply_eq_bot_iff` / 定理 `StrictMono.apply_eq_bot_iff`

English:
theorem StrictMono.apply_eq_bot_iff
  given: (hf : StrictMono f)
  statement: f a = f ⊥ ↔ a = ⊥
  proof: hf.dual.apply_eq_top_iff

中文:
定理 严格递增.apply_eq_bot_iff
  条件: (hf : 严格递增 f)
  结论: f a = f ⊥ ↔ a = ⊥
  证明: hf.dual.apply_eq_top_iff

Depends on / 依赖: apply_eq_top_iff, hf.dual.apply_eq_top_iff
-/
theorem StrictMono.apply_eq_bot_iff (hf : StrictMono f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff

/--
theorem `StrictAnti.apply_eq_bot_iff` / 定理 `StrictAnti.apply_eq_bot_iff`

English:
theorem StrictAnti.apply_eq_bot_iff
  given: (hf : StrictAnti f)
  statement: f a = f ⊥ ↔ a = ⊥
  proof: hf.dual.apply_eq_top_iff

中文:
定理 严格递减.apply_eq_bot_iff
  条件: (hf : 严格递减 f)
  结论: f a = f ⊥ ↔ a = ⊥
  证明: hf.dual.apply_eq_top_iff

Depends on / 依赖: apply_eq_top_iff, hf.dual.apply_eq_top_iff
-/
theorem StrictAnti.apply_eq_bot_iff (hf : StrictAnti f) : f a = f ⊥ ↔ a = ⊥ :=
  hf.dual.apply_eq_top_iff

end OrderBot

/--
theorem `StrictMono.minimal_preimage_bot` / 定理 `StrictMono.minimal_preimage_bot`

English:
theorem StrictMono.minimal_preimage_bot
  statement: [LinearOrder α] [Preorder β] [OrderBot β] {f : α -> β}
  proof: H.minimal_of_minimal_image
    (fun p => by
      rw [h_bot]
      exact bot_le)
    x

中文:
定理 严格递增.minimal_preimage_bot
  结论: [线性序 α] [预序 β] [有底序 β] {f : α -> β}
  证明: H.minimal_of_minimal_image
    (fun p => by
      rw [h_bot]
      exact bot_le)
    x

Depends on / 依赖: H.minimal_of_minimal_image, bot_le, h_bot, minimal_of_minimal_image
-/
theorem StrictMono.minimal_preimage_bot [LinearOrder α] [Preorder β] [OrderBot β] {f : α -> β}
    (H : StrictMono f) {a} (h_bot : f a = ⊥) (x : α) : a <= x :=
  H.minimal_of_minimal_image
    (fun p => by
      rw [h_bot]
      exact bot_le)
    x

section Logic

/-!
#### In this section we prove some properties about monotone and antitone operations on `Prop`
-/


section Preorder

variable [Preorder α]

/--
theorem `monotone_and` / 定理 `monotone_and`

English:
theorem monotone_and
  given: {p q : α -> Prop} (m_p : Monotone p) (m_q : Monotone q)
  proof: fun _ _ h => And.imp (m_p h) (m_q h)

中文:
定理 monotone_and
  条件: {p q : α -> 命题} (m_p : 递增 p) (m_q : 递增 q)
  证明: fun _ _ h => And.imp (m_p h) (m_q h)

Depends on / 依赖: And.imp
-/
theorem monotone_and {p q : α -> Prop} (m_p : Monotone p) (m_q : Monotone q) :
    Monotone fun x => p x ∧ q x :=
  fun _ _ h => And.imp (m_p h) (m_q h)

-- Note: by finish [monotone] doesn't work
/--
theorem `monotone_or` / 定理 `monotone_or`

English:
theorem monotone_or
  given: {p q : α -> Prop} (m_p : Monotone p) (m_q : Monotone q)
  proof: fun _ _ h => Or.imp (m_p h) (m_q h)

中文:
定理 monotone_or
  条件: {p q : α -> 命题} (m_p : 递增 p) (m_q : 递增 q)
  证明: fun _ _ h => Or.imp (m_p h) (m_q h)

Depends on / 依赖: Or.imp
-/
theorem monotone_or {p q : α -> Prop} (m_p : Monotone p) (m_q : Monotone q) :
    Monotone fun x => p x ∨ q x :=
  fun _ _ h => Or.imp (m_p h) (m_q h)

/--
theorem `monotone_le` / 定理 `monotone_le`

English:
theorem monotone_le
  given: {x : α}
  statement: Monotone (x <= ·)
  proof: fun _ _ h' h => h.trans h'

中文:
定理 monotone_le
  条件: {x : α}
  结论: 递增 (x <= ·)
  证明: fun _ _ h' h => h.trans h'

Depends on / 依赖: h.trans
-/
theorem monotone_le {x : α} : Monotone (x <= ·) := fun _ _ h' h => h.trans h'

/--
theorem `monotone_lt` / 定理 `monotone_lt`

English:
theorem monotone_lt
  given: {x : α}
  statement: Monotone (x < ·)
  proof: fun _ _ h' h => h.trans_le h'

中文:
定理 monotone_lt
  条件: {x : α}
  结论: 递增 (x < ·)
  证明: fun _ _ h' h => h.trans_le h'

Depends on / 依赖: h.trans_le, trans_le
-/
theorem monotone_lt {x : α} : Monotone (x < ·) := fun _ _ h' h => h.trans_le h'

/--
theorem `antitone_le` / 定理 `antitone_le`

English:
theorem antitone_le
  given: {x : α}
  statement: Antitone (· <= x)
  proof: fun _ _ h' h => h'.trans h

中文:
定理 antitone_le
  条件: {x : α}
  结论: 递减 (· <= x)
  证明: fun _ _ h' h => h'.trans h
-/
theorem antitone_le {x : α} : Antitone (· <= x) := fun _ _ h' h => h'.trans h

/--
theorem `antitone_lt` / 定理 `antitone_lt`

English:
theorem antitone_lt
  given: {x : α}
  statement: Antitone (· < x)
  proof: fun _ _ h' h => h'.trans_lt h

中文:
定理 antitone_lt
  条件: {x : α}
  结论: 递减 (· < x)
  证明: fun _ _ h' h => h'.trans_lt h

Depends on / 依赖: trans_lt
-/
theorem antitone_lt {x : α} : Antitone (· < x) := fun _ _ h' h => h'.trans_lt h

/--
theorem `Monotone.forall` / 定理 `Monotone.forall`

English:
theorem Monotone.forall
  given: {P : β -> α -> Prop} (hP : forall x, Monotone (P x))
  proof: fun _ _ hy h x => hP x hy h x

中文:
定理 递增.对任意
  条件: {P : β -> α -> 命题} (hP : 对任意 x, 递增 (P x))
  证明: fun _ _ hy h x => hP x hy h x
-/
theorem Monotone.forall {P : β -> α -> Prop} (hP : forall x, Monotone (P x)) :
    Monotone fun y => forall x, P x y :=
fun _ _ hy h x => hP x hy h x

/--
theorem `Antitone.forall` / 定理 `Antitone.forall`

English:
theorem Antitone.forall
  given: {P : β -> α -> Prop} (hP : forall x, Antitone (P x))
  proof: fun _ _ hy h x => hP x hy (h x)

中文:
定理 递减.对任意
  条件: {P : β -> α -> 命题} (hP : 对任意 x, 递减 (P x))
  证明: fun _ _ hy h x => hP x hy (h x)
-/
theorem Antitone.forall {P : β -> α -> Prop} (hP : forall x, Antitone (P x)) :
    Antitone fun y => forall x, P x y :=
  fun _ _ hy h x => hP x hy (h x)

/--
theorem `Monotone.ball` / 定理 `Monotone.ball`

English:
theorem Monotone.ball
  given: {P : β -> α -> Prop} {s : Set β} (hP : forall x in s, Monotone (P x))
  proof: fun _ _ hy h x hx => hP x hx hy (h x hx)

中文:
定理 递增.ball
  条件: {P : β -> α -> 命题} {s : 集合 β} (hP : 对任意 x in s, 递增 (P x))
  证明: fun _ _ hy h x hx => hP x hx hy (h x hx)
-/
theorem Monotone.ball {P : β -> α -> Prop} {s : Set β} (hP : forall x in s, Monotone (P x)) :
    Monotone fun y => forall x in s, P x y := fun _ _ hy h x hx => hP x hx hy (h x hx)

/--
theorem `Antitone.ball` / 定理 `Antitone.ball`

English:
theorem Antitone.ball
  given: {P : β -> α -> Prop} {s : Set β} (hP : forall x in s, Antitone (P x))
  proof: fun _ _ hy h x hx => hP x hx hy (h x hx)

中文:
定理 递减.ball
  条件: {P : β -> α -> 命题} {s : 集合 β} (hP : 对任意 x in s, 递减 (P x))
  证明: fun _ _ hy h x hx => hP x hx hy (h x hx)
-/
theorem Antitone.ball {P : β -> α -> Prop} {s : Set β} (hP : forall x in s, Antitone (P x)) :
    Antitone fun y => forall x in s, P x y := fun _ _ hy h x hx => hP x hx hy (h x hx)

/--
theorem `Monotone.exists` / 定理 `Monotone.exists`

English:
theorem Monotone.exists
  given: {P : β -> α -> Prop} (hP : forall x, Monotone (P x))
  proof: fun _ _ hy ⟨x, hx⟩ => ⟨x, hP x hy hx⟩

中文:
定理 递增.存在
  条件: {P : β -> α -> 命题} (hP : 对任意 x, 递增 (P x))
  证明: fun _ _ hy ⟨x, hx⟩ => ⟨x, hP x hy hx⟩
-/
theorem Monotone.exists {P : β -> α -> Prop} (hP : forall x, Monotone (P x)) :
    Monotone fun y => exists x, P x y :=
  fun _ _ hy ⟨x, hx⟩ => ⟨x, hP x hy hx⟩

/--
theorem `Antitone.exists` / 定理 `Antitone.exists`

English:
theorem Antitone.exists
  given: {P : β -> α -> Prop} (hP : forall x, Antitone (P x))
  proof: fun _ _ hy ⟨x, hx⟩ => ⟨x, hP x hy hx⟩

中文:
定理 递减.存在
  条件: {P : β -> α -> 命题} (hP : 对任意 x, 递减 (P x))
  证明: fun _ _ hy ⟨x, hx⟩ => ⟨x, hP x hy hx⟩
-/
theorem Antitone.exists {P : β -> α -> Prop} (hP : forall x, Antitone (P x)) :
    Antitone fun y => exists x, P x y :=
  fun _ _ hy ⟨x, hx⟩ => ⟨x, hP x hy hx⟩

/--
theorem `forall_ge_iff` / 定理 `forall_ge_iff`

English:
theorem forall_ge_iff
  given: {P : α -> Prop} {x₀ : α} (hP : Monotone P)
  proof: ⟨fun H => H x₀ le_rfl, fun H _ hx => hP hx H⟩

中文:
定理 对任意_ge_iff
  条件: {P : α -> 命题} {x₀ : α} (hP : 递增 P)
  证明: ⟨fun H => H x₀ le_rfl, fun H _ hx => hP hx H⟩

Depends on / 依赖: le_rfl
-/
theorem forall_ge_iff {P : α -> Prop} {x₀ : α} (hP : Monotone P) :
    (forall x >= x₀, P x) ↔ P x₀ :=
  ⟨fun H => H x₀ le_rfl, fun H _ hx => hP hx H⟩

/--
theorem `forall_le_iff` / 定理 `forall_le_iff`

English:
theorem forall_le_iff
  given: {P : α -> Prop} {x₀ : α} (hP : Antitone P)
  proof: ⟨fun H => H x₀ le_rfl, fun H _ hx => hP hx H⟩

中文:
定理 对任意_le_iff
  条件: {P : α -> 命题} {x₀ : α} (hP : 递减 P)
  证明: ⟨fun H => H x₀ le_rfl, fun H _ hx => hP hx H⟩

Depends on / 依赖: le_rfl
-/
theorem forall_le_iff {P : α -> Prop} {x₀ : α} (hP : Antitone P) :
    (forall x <= x₀, P x) ↔ P x₀ :=
  ⟨fun H => H x₀ le_rfl, fun H _ hx => hP hx H⟩

end Preorder

end Logic
