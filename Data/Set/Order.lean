/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
module

public import Mathlib.Data.Set.Basic

/-!
# Order structures and monotonicity lemmas for `Set`
-/

public section

open Function

universe u v

namespace Set

variable {α : Type u} {β : Type v} {a b : α} {s s₁ s₂ t t₁ t₂ u : Set α}

section Preorder

variable [Preorder α] [Preorder β] {f : α -> β}

/--
theorem `monotoneOn_iff_monotone` / 定理 `monotoneOn_iff_monotone`

English:
theorem monotoneOn_iff_monotone
  statement: MonotoneOn f s ↔
  proof: by
  simp [Monotone, MonotoneOn]

中文:
定理 monotoneOn_iff_monotone
  结论: MonotoneOn f s ↔
  证明: by
  simp [Monotone, MonotoneOn]

Depends on / 依赖: Monotone, MonotoneOn
-/
theorem monotoneOn_iff_monotone : MonotoneOn f s ↔
    Monotone fun a : s => f a := by
  simp [Monotone, MonotoneOn]

/--
theorem `antitoneOn_iff_antitone` / 定理 `antitoneOn_iff_antitone`

English:
theorem antitoneOn_iff_antitone
  statement: AntitoneOn f s ↔
  proof: by
  simp [Antitone, AntitoneOn]

中文:
定理 antitoneOn_iff_antitone
  结论: AntitoneOn f s ↔
  证明: by
  simp [Antitone, AntitoneOn]

Depends on / 依赖: Antitone, AntitoneOn
-/
theorem antitoneOn_iff_antitone : AntitoneOn f s ↔
    Antitone fun a : s => f a := by
  simp [Antitone, AntitoneOn]

/--
theorem `strictMonoOn_iff_strictMono` / 定理 `strictMonoOn_iff_strictMono`

English:
theorem strictMonoOn_iff_strictMono
  statement: StrictMonoOn f s ↔
  proof: by
  simp [StrictMono, StrictMonoOn]

中文:
定理 strictMonoOn_iff_strictMono
  结论: StrictMonoOn f s ↔
  证明: by
  simp [StrictMono, StrictMonoOn]

Depends on / 依赖: StrictMono, StrictMonoOn
-/
theorem strictMonoOn_iff_strictMono : StrictMonoOn f s ↔
    StrictMono fun a : s => f a := by
  simp [StrictMono, StrictMonoOn]

/--
theorem `strictAntiOn_iff_strictAnti` / 定理 `strictAntiOn_iff_strictAnti`

English:
theorem strictAntiOn_iff_strictAnti
  statement: StrictAntiOn f s ↔
  proof: by
  simp [StrictAnti, StrictAntiOn]

中文:
定理 strictAntiOn_iff_strictAnti
  结论: StrictAntiOn f s ↔
  证明: by
  simp [StrictAnti, StrictAntiOn]

Depends on / 依赖: StrictAnti, StrictAntiOn
-/
theorem strictAntiOn_iff_strictAnti : StrictAntiOn f s ↔
    StrictAnti fun a : s => f a := by
  simp [StrictAnti, StrictAntiOn]

end Preorder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : α -> β}

/--
theorem `not_monotoneOn_not_antitoneOn_iff_exists_le_le` / 定理 `not_monotoneOn_not_antitoneOn_iff_exists_le_le`

English:
theorem not_monotoneOn_not_antitoneOn_iff_exists_le_le
  proof: by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_le_le, @and_left_comm (_ in s)]

中文:
定理 not_monotoneOn_not_antitoneOn_iff_exists_le_le
  证明: by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_le_le, @and_left_comm (_ in s)]

Depends on / 依赖: and_assoc, and_left_comm, antitoneOn_iff_antitone, exists_and_left, f.base, monotoneOn_iff_monotone, not_monotone_not_antitone_iff_exists_le_le
-/
theorem not_monotoneOn_not_antitoneOn_iff_exists_le_le :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      existsᵉ (a in s) (b in s) (c in s), a <= b ∧ b <= c ∧
        (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_le_le, @and_left_comm (_ in s)]

/--
theorem `not_monotoneOn_not_antitoneOn_iff_exists_lt_lt` / 定理 `not_monotoneOn_not_antitoneOn_iff_exists_lt_lt`

English:
theorem not_monotoneOn_not_antitoneOn_iff_exists_lt_lt
  proof: by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_lt_lt, @and_left_comm (_ in s)]

中文:
定理 not_monotoneOn_not_antitoneOn_iff_exists_lt_lt
  证明: by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_lt_lt, @and_left_comm (_ in s)]

Depends on / 依赖: and_assoc, and_left_comm, antitoneOn_iff_antitone, exists_and_left, monotoneOn_iff_monotone, not_monotone_not_antitone_iff_exists_lt_lt
-/
theorem not_monotoneOn_not_antitoneOn_iff_exists_lt_lt :
    ¬MonotoneOn f s ∧ ¬AntitoneOn f s ↔
      existsᵉ (a in s) (b in s) (c in s), a < b ∧ b < c ∧
        (f a < f b ∧ f c < f b ∨ f b < f a ∧ f b < f c) := by
  simp [monotoneOn_iff_monotone, antitoneOn_iff_antitone, and_assoc, exists_and_left,
    not_monotone_not_antitone_iff_exists_lt_lt, @and_left_comm (_ in s)]

end LinearOrder

end Set

/-! ### Monotone lemmas for sets -/

section Monotone
variable {α β : Type*}

/--
theorem `Monotone.inter` / 定理 `Monotone.inter`

English:
theorem Monotone.inter
  given: [Preorder β] {f g : β -> Set α} (hf : Monotone f) (hg : Monotone g)
  proof: hf.inf hg

中文:
定理 Monotone.inter
  条件: [Preorder β] {f g : β -> Set α} (hf : Monotone f) (hg : Monotone g)
  证明: hf.inf hg

Depends on / 依赖: hf.inf
-/
theorem Monotone.inter [Preorder β] {f g : β -> Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x inter g x :=
  hf.inf hg

/--
theorem `MonotoneOn.inter` / 定理 `MonotoneOn.inter`

English:
theorem MonotoneOn.inter
  statement: [Preorder β] {f g : β -> Set α} {s : Set β} (hf : MonotoneOn f s)
  proof: hf.inf hg

中文:
定理 MonotoneOn.inter
  结论: [Preorder β] {f g : β -> Set α} {s : Set β} (hf : MonotoneOn f s)
  证明: hf.inf hg

Depends on / 依赖: hf.inf
-/
theorem MonotoneOn.inter [Preorder β] {f g : β -> Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x inter g x) s :=
  hf.inf hg

/--
theorem `Antitone.inter` / 定理 `Antitone.inter`

English:
theorem Antitone.inter
  given: [Preorder β] {f g : β -> Set α} (hf : Antitone f) (hg : Antitone g)
  proof: hf.inf hg

中文:
定理 Antitone.inter
  条件: [Preorder β] {f g : β -> Set α} (hf : Antitone f) (hg : Antitone g)
  证明: hf.inf hg

Depends on / 依赖: hf.inf
-/
theorem Antitone.inter [Preorder β] {f g : β -> Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x inter g x :=
  hf.inf hg

/--
theorem `AntitoneOn.inter` / 定理 `AntitoneOn.inter`

English:
theorem AntitoneOn.inter
  statement: [Preorder β] {f g : β -> Set α} {s : Set β} (hf : AntitoneOn f s)
  proof: hf.inf hg

中文:
定理 AntitoneOn.inter
  结论: [Preorder β] {f g : β -> Set α} {s : Set β} (hf : AntitoneOn f s)
  证明: hf.inf hg

Depends on / 依赖: hf.inf
-/
theorem AntitoneOn.inter [Preorder β] {f g : β -> Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x inter g x) s :=
  hf.inf hg

/--
theorem `Monotone.union` / 定理 `Monotone.union`

English:
theorem Monotone.union
  given: [Preorder β] {f g : β -> Set α} (hf : Monotone f) (hg : Monotone g)
  proof: hf.sup hg

中文:
定理 Monotone.union
  条件: [Preorder β] {f g : β -> Set α} (hf : Monotone f) (hg : Monotone g)
  证明: hf.sup hg

Depends on / 依赖: hf.sup
-/
theorem Monotone.union [Preorder β] {f g : β -> Set α} (hf : Monotone f) (hg : Monotone g) :
    Monotone fun x => f x union g x :=
  hf.sup hg

/--
theorem `MonotoneOn.union` / 定理 `MonotoneOn.union`

English:
theorem MonotoneOn.union
  statement: [Preorder β] {f g : β -> Set α} {s : Set β} (hf : MonotoneOn f s)
  proof: hf.sup hg

中文:
定理 MonotoneOn.union
  结论: [Preorder β] {f g : β -> Set α} {s : Set β} (hf : MonotoneOn f s)
  证明: hf.sup hg

Depends on / 依赖: hf.sup
-/
theorem MonotoneOn.union [Preorder β] {f g : β -> Set α} {s : Set β} (hf : MonotoneOn f s)
    (hg : MonotoneOn g s) : MonotoneOn (fun x => f x union g x) s :=
  hf.sup hg

/--
theorem `Antitone.union` / 定理 `Antitone.union`

English:
theorem Antitone.union
  given: [Preorder β] {f g : β -> Set α} (hf : Antitone f) (hg : Antitone g)
  proof: hf.sup hg

中文:
定理 Antitone.union
  条件: [Preorder β] {f g : β -> Set α} (hf : Antitone f) (hg : Antitone g)
  证明: hf.sup hg

Depends on / 依赖: hf.sup
-/
theorem Antitone.union [Preorder β] {f g : β -> Set α} (hf : Antitone f) (hg : Antitone g) :
    Antitone fun x => f x union g x :=
  hf.sup hg

/--
theorem `AntitoneOn.union` / 定理 `AntitoneOn.union`

English:
theorem AntitoneOn.union
  statement: [Preorder β] {f g : β -> Set α} {s : Set β} (hf : AntitoneOn f s)
  proof: hf.sup hg

中文:
定理 AntitoneOn.union
  结论: [Preorder β] {f g : β -> Set α} {s : Set β} (hf : AntitoneOn f s)
  证明: hf.sup hg

Depends on / 依赖: hf.sup
-/
theorem AntitoneOn.union [Preorder β] {f g : β -> Set α} {s : Set β} (hf : AntitoneOn f s)
    (hg : AntitoneOn g s) : AntitoneOn (fun x => f x union g x) s :=
  hf.sup hg

namespace Set

/--
theorem `monotone_ofPred` / 定理 `monotone_ofPred`

English:
theorem monotone_ofPred
  given: [Preorder α] {p : α -> β -> Prop} (hp : forall b, Monotone fun a => p a b)
  proof: fun _ _ h b => hp b h

@[deprecated (since := "2026-07-09")] alias monotone_setOf := monotone_ofPred

中文:
定理 monotone_ofPred
  条件: [Preorder α] {p : α -> β -> 命题} (hp : 对任意 b, Monotone fun a => p a b)
  证明: fun _ _ h b => hp b h

@[deprecated (since := "2026-07-09")] alias monotone_setOf := monotone_ofPred
-/
theorem monotone_ofPred [Preorder α] {p : α -> β -> Prop} (hp : forall b, Monotone fun a => p a b) :
    Monotone fun a => { b | p a b } := fun _ _ h b => hp b h

@[deprecated (since := "2026-07-09")] alias monotone_setOf := monotone_ofPred

/--
theorem `antitone_ofPred` / 定理 `antitone_ofPred`

English:
theorem antitone_ofPred
  given: [Preorder α] {p : α -> β -> Prop} (hp : forall b, Antitone fun a => p a b)
  proof: fun _ _ h b => hp b h

@[deprecated (since := "2026-07-09")] alias antitone_setOf := antitone_ofPred

中文:
定理 antitone_ofPred
  条件: [Preorder α] {p : α -> β -> 命题} (hp : 对任意 b, Antitone fun a => p a b)
  证明: fun _ _ h b => hp b h

@[deprecated (since := "2026-07-09")] alias antitone_setOf := antitone_ofPred
-/
theorem antitone_ofPred [Preorder α] {p : α -> β -> Prop} (hp : forall b, Antitone fun a => p a b) :
    Antitone fun a => { b | p a b } := fun _ _ h b => hp b h

@[deprecated (since := "2026-07-09")] alias antitone_setOf := antitone_ofPred

/--
theorem `antitone_bforall` / 定理 `antitone_bforall`

English:
theorem antitone_bforall
  given: {P : α -> Prop}
  statement: Antitone fun s : Set α => forall x in s, P x
  proof: fun _ _ hst h x hx => h x hst hx

中文:
定理 antitone_bforall
  条件: {P : α -> 命题}
  结论: Antitone fun s : Set α => 对任意 x in s, P x
  证明: fun _ _ hst h x hx => h x hst hx
-/
theorem antitone_bforall {P : α -> Prop} : Antitone fun s : Set α => forall x in s, P x :=
fun _ _ hst h x hx => h x hst hx

end Set

end Monotone
