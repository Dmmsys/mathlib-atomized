/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Chris Hughes, Mantas Bakšys
-/
module

public import Mathlib.Data.List.Basic
public import Mathlib.Order.BoundedOrder.Lattice
public import Mathlib.Data.List.Induction
public import Mathlib.Order.MinMax
public import Mathlib.Order.WithBot

/-!
# Minimum and maximum of lists

## Main definitions

The main definitions are `argmax`, `argmin`, `minimum` and `maximum` for lists.

`argmax f l` returns `some a`, where `a` of `l` that maximises `f a`. If there are `a b` such that
  `f a = f b`, it returns whichever of `a` or `b` comes first in the list.
  `argmax f [] = none`

`minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]`
-/

@[expose] public section

namespace List

variable {α β : Type*}

section ArgAux

variable (r : α -> α -> Prop) [DecidableRel r] {l : List α} {o : Option α} {a : α}

/--
Definition of `argAux` / `argAux` 的定义

English:
definition argAux
  signature: (a : Option α) (b : α)
  body: Option.casesOn a (some b) fun c => if r b c then some b else some c

@[simp]

中文:
定义 argAux
  签名: (a : 选项类型 α) (b : α)
  定义体: Option.casesOn a (some b) fun c => if r b c then some b else some c

@[simp]

Depends on / 依赖: Option.casesOn, casesOn
-/
def argAux (a : Option α) (b : α) : Option α :=
  Option.casesOn a (some b) fun c => if r b c then some b else some c

@[simp]
/--
theorem `foldl_argAux_eq_none` / 定理 `foldl_argAux_eq_none`

English:
theorem foldl_argAux_eq_none
  statement: l.foldl (argAux r) o = none ↔ l = [] ∧ o = none
  proof: List.reverseRecOn l (by simp) fun tl hd => by
    simp only [foldl_append, foldl_cons, argAux, foldl_nil, append_eq_nil_iff]
    cases foldl (argAux r) o tl
    · simp
    · simp only
      split_ifs <;> simp

中文:
定理 foldl_argAux_eq_none
  结论: l.foldl (argAux r) o = none ↔ l = [] ∧ o = none
  证明: List.reverseRecOn l (by simp) fun tl hd => by
    simp only [foldl_append, foldl_cons, argAux, foldl_nil, append_eq_nil_iff]
    cases foldl (argAux r) o tl
    · simp
    · simp only
      split_ifs <;> simp

Depends on / 依赖: List.reverseRecOn, append_eq_nil_iff, argAux, foldl_append, foldl_cons, foldl_nil, reverseRecOn, split_ifs
-/
theorem foldl_argAux_eq_none : l.foldl (argAux r) o = none ↔ l = [] ∧ o = none :=
  List.reverseRecOn l (by simp) fun tl hd => by
    simp only [foldl_append, foldl_cons, argAux, foldl_nil, append_eq_nil_iff]
    cases foldl (argAux r) o tl
    · simp
    · simp only
      split_ifs <;> simp

/--
theorem `foldl_argAux_mem` / 定理 `foldl_argAux_mem`

English:
theorem foldl_argAux_mem
  given: (l)
  statement: forall a m : α, m in foldl (argAux r) (some a) l -> m in a :: l
  proof: List.reverseRecOn l (by simp [eq_comm]) by
    intro _ _ _ _
    simp only [foldl_append, foldl_cons, foldl_nil, argAux]
    cases _ : foldl _ _ _ <;> grind

@[simp]

中文:
定理 foldl_argAux_mem
  条件: (l)
  结论: 对任意 a m : α, m in foldl (argAux r) (some a) l -> m in a :: l
  证明: List.reverseRecOn l (by simp [eq_comm]) by
    intro _ _ _ _
    simp only [foldl_append, foldl_cons, foldl_nil, argAux]
    cases _ : foldl _ _ _ <;> grind

@[simp]
-/
private theorem foldl_argAux_mem (l) : forall a m : α, m in foldl (argAux r) (some a) l -> m in a :: l :=
List.reverseRecOn l (by simp [eq_comm]) by
    intro _ _ _ _
    simp only [foldl_append, foldl_cons, foldl_nil, argAux]
    cases _ : foldl _ _ _ <;> grind

@[simp]
/--
theorem `argAux_self` / 定理 `argAux_self`

English:
theorem argAux_self
  given: (hr₀ : Std.Irrefl r) (a : α)
  statement: argAux r (some a) a = a
  proof: if_neg hr₀.irrefl _

中文:
定理 argAux_self
  条件: (hr₀ : Std.Irrefl r) (a : α)
  结论: argAux r (some a) a = a
  证明: if_neg hr₀.irrefl _

Depends on / 依赖: if_neg, irrefl
-/
theorem argAux_self (hr₀ : Std.Irrefl r) (a : α) : argAux r (some a) a = a :=
if_neg hr₀.irrefl _

/--
theorem `not_of_mem_foldl_argAux` / 定理 `not_of_mem_foldl_argAux`

English:
theorem not_of_mem_foldl_argAux
  given: (hr₀ : Std.Irrefl r) (hr₁ : IsTrans α r)
  proof: by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton tl a ih => ?_
  intro b m o hb ho
  rw [foldl_append]; rw [foldl_cons]; rw [foldl_nil]; rw [argAux] at ho
  rcases hf : foldl (argAux r) o tl with - | c
  · rw [hf] at ho
    rw [foldl_argAux_eq_none] at hf
    simp_a

中文:
定理 not_of_mem_foldl_argAux
  条件: (hr₀ : Std.Irrefl r) (hr₁ : 是Trans α r)
  证明: by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton tl a ih => ?_
  intro b m o hb ho
  rw [foldl_append]; rw [foldl_cons]; rw [foldl_nil]; rw [argAux] at ho
  rcases hf : foldl (argAux r) o tl with - | c
  · rw [hf] at ho
    rw [foldl_argAux_eq_none] at hf
    simp_a

Depends on / 依赖: List.reverseRecOn, Option.mem_def, append_singleton, argAux, foldl_append, foldl_argAux_eq_none, foldl_cons, foldl_nil, irrefl, mem_def, reverseRecOn, splitIndPred
-/
theorem not_of_mem_foldl_argAux (hr₀ : Std.Irrefl r) (hr₁ : IsTrans α r) :
    forall {a m : α} {o : Option α}, a in l -> m in foldl (argAux r) o l -> ¬r a m := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton tl a ih => ?_
  intro b m o hb ho
  rw [foldl_append]; rw [foldl_cons]; rw [foldl_nil]; rw [argAux] at ho
  rcases hf : foldl (argAux r) o tl with - | c
  · rw [hf] at ho
    rw [foldl_argAux_eq_none] at hf
    simp_all [hf.1, hf.2, hr₀.irrefl _]
  rw [hf]; rw [Option.mem_def] at ho
  grind +splitIndPred

end ArgAux

section Preorder

variable [Preorder β] [DecidableLT β] {f : α -> β} {l : List α} {a m : α}

/-- `argmax f l` returns `some a`, where `f a` is maximal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f a < f b`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmax f [] = none`. -/
@[to_dual
/-- `argmin f l` returns `some a`, where `f a` is minimal among the elements of `l`, in the sense
that there is no `b ∈ l` with `f b < f a`. If `a`, `b` are such that `f a = f b`, it returns
whichever of `a` or `b` comes first in the list. `argmin f [] = none`. -/]
/--
Definition of `argmax` / `argmax` 的定义

English:
definition argmax
  signature: (f : α -> β) (l : List α)
  body: l.foldl (argAux fun b c => f c < f b) none

@[to_dual (attr := simp)]

中文:
定义 argmax
  签名: (f : α -> β) (l : 列表 α)
  定义体: l.foldl (argAux fun b c => f c < f b) none

@[to_dual (attr := simp)]

Depends on / 依赖: argAux, l.foldl
-/
def argmax (f : α -> β) (l : List α) : Option α :=
  l.foldl (argAux fun b c => f c < f b) none

@[to_dual (attr := simp)]
/--
theorem `argmax_nil` / 定理 `argmax_nil`

English:
theorem argmax_nil
  given: (f : α -> β)
  statement: argmax f [] = none
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 argmax_nil
  条件: (f : α -> β)
  结论: argmax f [] = none
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem argmax_nil (f : α -> β) : argmax f [] = none :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `argmax_singleton` / 定理 `argmax_singleton`

English:
theorem argmax_singleton
  given: {f : α -> β} {a : α}
  statement: argmax f [a] = a
  proof: rfl

@[to_dual]

中文:
定理 argmax_singleton
  条件: {f : α -> β} {a : α}
  结论: argmax f [a] = a
  证明: rfl

@[to_dual]
-/
theorem argmax_singleton {f : α -> β} {a : α} : argmax f [a] = a :=
  rfl

@[to_dual]
/--
theorem `not_lt_of_mem_argmax` / 定理 `not_lt_of_mem_argmax`

English:
theorem not_lt_of_mem_argmax
  statement: a in l -> m in argmax f l -> ¬f m < f a
  proof: not_of_mem_foldl_argAux _ ⟨fun x h => lt_irrefl (f x) h⟩
    ⟨fun _ _ z hxy hyz => lt_trans (a := f z) hyz hxy⟩

@[to_dual]

中文:
定理 not_lt_of_mem_argmax
  结论: a in l -> m in argmax f l -> ¬f m < f a
  证明: not_of_mem_foldl_argAux _ ⟨fun x h => lt_irrefl (f x) h⟩
    ⟨fun _ _ z hxy hyz => lt_trans (a := f z) hyz hxy⟩

@[to_dual]

Depends on / 依赖: lt_irrefl, lt_trans, not_of_mem_foldl_argAux
-/
theorem not_lt_of_mem_argmax : a in l -> m in argmax f l -> ¬f m < f a :=
  not_of_mem_foldl_argAux _ ⟨fun x h => lt_irrefl (f x) h⟩
    ⟨fun _ _ z hxy hyz => lt_trans (a := f z) hyz hxy⟩

@[to_dual]
/--
theorem `argmax_concat` / 定理 `argmax_concat`

English:
theorem argmax_concat
  given: (f : α -> β) (a : α) (l : List α)
  proof: by
  rw [argmax]; rw [argmax]; simp [argAux]

@[to_dual]

中文:
定理 argmax_concat
  条件: (f : α -> β) (a : α) (l : 列表 α)
  证明: by
  rw [argmax]; rw [argmax]; simp [argAux]

@[to_dual]

Depends on / 依赖: argAux, argmax
-/
theorem argmax_concat (f : α -> β) (a : α) (l : List α) :
    argmax f (l ++ [a]) =
      Option.casesOn (argmax f l) (some a) fun c => if f c < f a then some a else some c := by
  rw [argmax]; rw [argmax]; simp [argAux]

@[to_dual]
/--
theorem `argmax_mem` / 定理 `argmax_mem`

English:
theorem argmax_mem
  statement: forall {l : List α} {m : α}, m in argmax f l -> m in l

中文:
定理 argmax_mem
  结论: 对任意 {l : 列表 α} {m : α}, m in argmax f l -> m in l
-/
theorem argmax_mem : forall {l : List α} {m : α}, m in argmax f l -> m in l
  | [], m => by simp
  | hd :: tl, m => by simpa [argmax, argAux] using foldl_argAux_mem _ tl hd m

@[to_dual (attr := simp)]
/--
theorem `argmax_eq_none` / 定理 `argmax_eq_none`

English:
theorem argmax_eq_none
  statement: l.argmax f = none ↔ l = []
  proof: by simp [argmax]

中文:
定理 argmax_eq_none
  结论: l.argmax f = none ↔ l = []
  证明: by simp [argmax]

Depends on / 依赖: argmax
-/
theorem argmax_eq_none : l.argmax f = none ↔ l = [] := by simp [argmax]

end Preorder

section LinearOrder

variable [LinearOrder β] {f : α -> β} {l : List α} {a m : α}

@[to_dual]
/--
theorem `le_of_mem_argmax` / 定理 `le_of_mem_argmax`

English:
theorem le_of_mem_argmax
  statement: a in l -> m in argmax f l -> f a <= f m
  proof: fun ha hm =>
le_of_not_gt not_lt_of_mem_argmax ha hm

@[to_dual]

中文:
定理 le_of_mem_argmax
  结论: a in l -> m in argmax f l -> f a <= f m
  证明: fun ha hm =>
le_of_not_gt not_lt_of_mem_argmax ha hm

@[to_dual]
-/
theorem le_of_mem_argmax : a in l -> m in argmax f l -> f a <= f m := fun ha hm =>
le_of_not_gt not_lt_of_mem_argmax ha hm

@[to_dual]
/--
theorem `argmax_cons` / 定理 `argmax_cons`

English:
theorem argmax_cons
  given: (f : α -> β) (a : α) (l : List α)
  proof: List.reverseRecOn l rfl fun hd tl ih => by
    rw [← cons_append]; rw [argmax_concat]; rw [ih]; rw [argmax_concat]
    rcases h : argmax f hd with - | m
    · simp
    dsimp
    rw [← apply_ite]; rw [← apply_ite]
    grind -abstractProof -- Without `-abstractProof`, `to_dual` gives an error.

中文:
定理 argmax_cons
  条件: (f : α -> β) (a : α) (l : 列表 α)
  证明: List.reverseRecOn l rfl fun hd tl ih => by
    rw [← cons_append]; rw [argmax_concat]; rw [ih]; rw [argmax_concat]
    rcases h : argmax f hd with - | m
    · simp
    dsimp
    rw [← apply_ite]; rw [← apply_ite]
    grind -abstractProof -- Without `-abstractProof`, `to_dual` gives an error.

Depends on / 依赖: List.reverseRecOn, Without, abstractProof, apply_ite, argmax, argmax_concat, cons_append, reverseRecOn, to_dual
-/
theorem argmax_cons (f : α -> β) (a : α) (l : List α) :
    argmax f (a :: l) =
      Option.casesOn (argmax f l) (some a) fun c => if f a < f c then some c else some a :=
  List.reverseRecOn l rfl fun hd tl ih => by
    rw [← cons_append]; rw [argmax_concat]; rw [ih]; rw [argmax_concat]
    rcases h : argmax f hd with - | m
    · simp
    dsimp
    rw [← apply_ite]; rw [← apply_ite]
    grind -abstractProof -- Without `-abstractProof`, `to_dual` gives an error.

variable [DecidableEq α]

@[to_dual]
/--
theorem `index_of_argmax` / 定理 `index_of_argmax`

English:
theorem index_of_argmax
  proof: ha <;> split_ifs at hm <;> injection hm with hm <;> subst hm
    · cases not_le_of_gt ‹_› ‹_›
    · rw [if_pos rfl]
    · rw [if_neg, if_neg]
      · exact Nat.succ_le_succ (index_of_argmax h (by assumption) ham)
      · exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne
      · exact ne_of_apply_ne

中文:
定理 index_of_argmax
  证明: ha <;> split_ifs at hm <;> injection hm with hm <;> subst hm
    · cases not_le_of_gt ‹_› ‹_›
    · rw [if_pos rfl]
    · rw [if_neg, if_neg]
      · exact Nat.succ_le_succ (index_of_argmax h (by assumption) ham)
      · exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne
      · exact ne_of_apply_ne

Depends on / 依赖: injection, split_ifs
-/
theorem index_of_argmax :
    forall {l : List α} {m : α}, m in argmax f l -> forall {a}, a in l -> f m <= f a -> l.idxOf m <= l.idxOf a
  | [], m, _, _, _, _ => by simp
  | hd :: tl, m, hm, a, ha, ham => by
    simp only [idxOf_cons, argmax_cons, Option.mem_def] at hm ⊢
    cases h : argmax f tl
    · rw [h] at hm
      simp_all
    rw [h] at hm
    dsimp only at hm
    simp only [cond_eq_ite, beq_iff_eq]
    obtain ha | ha := ha <;> split_ifs at hm <;> injection hm with hm <;> subst hm
    · cases not_le_of_gt ‹_› ‹_›
    · rw [if_pos rfl]
    · rw [if_neg, if_neg]
      · exact Nat.succ_le_succ (index_of_argmax h (by assumption) ham)
      · exact ne_of_apply_ne f (lt_of_lt_of_le ‹_› ‹_›).ne
      · exact ne_of_apply_ne _ ‹f hd < f _›.ne
    · rw [if_pos rfl]
      exact Nat.zero_le _

@[to_dual]
/--
theorem `mem_argmax_iff` / 定理 `mem_argmax_iff`

English:
theorem mem_argmax_iff
  proof: ⟨fun hm => ⟨argmax_mem hm, fun _ ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩,
    by
      rintro ⟨hml, ham, hma⟩
      rcases harg : argmax f l with - | n
      · simp_all
      · have :=
          Nat.le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
            (ind

中文:
定理 mem_argmax_iff
  证明: ⟨fun hm => ⟨argmax_mem hm, fun _ ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩,
    by
      rintro ⟨hml, ham, hma⟩
      rcases harg : argmax f l with - | n
      · simp_all
      · have :=
          Nat.le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
            (ind

Depends on / 依赖: Nat.le_antisymm, Option.mem_def, argmax, argmax_mem, idxOf_inj, index_of_argmax, le_antisymm, le_of_mem_argmax, mem_def
-/
theorem mem_argmax_iff :
    m in argmax f l ↔
      m in l ∧ (forall a in l, f a <= f m) ∧ forall a in l, f m <= f a -> l.idxOf m <= l.idxOf a :=
  ⟨fun hm => ⟨argmax_mem hm, fun _ ha => le_of_mem_argmax ha hm, fun _ => index_of_argmax hm⟩,
    by
      rintro ⟨hml, ham, hma⟩
      rcases harg : argmax f l with - | n
      · simp_all
      · have :=
          Nat.le_antisymm (hma n (argmax_mem harg) (le_of_mem_argmax hml harg))
            (index_of_argmax harg hml (ham _ (argmax_mem harg)))
        rw [(idxOf_inj hml).1 this]; rw [Option.mem_def]⟩

@[to_dual]
/--
theorem `argmax_eq_some_iff` / 定理 `argmax_eq_some_iff`

English:
theorem argmax_eq_some_iff
  proof: mem_argmax_iff

中文:
定理 argmax_eq_some_iff
  证明: mem_argmax_iff

Depends on / 依赖: mem_argmax_iff
-/
theorem argmax_eq_some_iff :
    argmax f l = some m ↔
      m in l ∧ (forall a in l, f a <= f m) ∧ forall a in l, f m <= f a -> l.idxOf m <= l.idxOf a :=
  mem_argmax_iff

end LinearOrder

section MaximumMinimum

section Preorder

variable [Preorder α] [DecidableLT α] {l : List α} {a m : α}

/-- `maximum l` returns a `WithBot α`, the largest element of `l` for nonempty lists, and `⊥` for
`[]` -/
@[to_dual
/-- `minimum l` returns a `WithTop α`, the smallest element of `l` for nonempty lists, and `⊤` for
`[]` -/]
/--
Definition of `maximum` / `maximum` 的定义

English:
definition maximum
  signature: (l : List α)
  body: argmax id l

@[to_dual (attr := simp)]

中文:
定义 maximum
  签名: (l : 列表 α)
  定义体: argmax id l

@[to_dual (attr := simp)]

Depends on / 依赖: argmax
-/
def maximum (l : List α) : WithBot α :=
  argmax id l

@[to_dual (attr := simp)]
/--
theorem `maximum_nil` / 定理 `maximum_nil`

English:
theorem maximum_nil
  statement: maximum ([] : List α) = ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 maximum_nil
  结论: maximum ([] : 列表 α) = ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem maximum_nil : maximum ([] : List α) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `maximum_singleton` / 定理 `maximum_singleton`

English:
theorem maximum_singleton
  given: (a : α)
  statement: maximum [a] = a
  proof: rfl

@[to_dual]

中文:
定理 maximum_singleton
  条件: (a : α)
  结论: maximum [a] = a
  证明: rfl

@[to_dual]
-/
theorem maximum_singleton (a : α) : maximum [a] = a :=
  rfl

@[to_dual]
/--
theorem `maximum_mem` / 定理 `maximum_mem`

English:
theorem maximum_mem
  given: {l : List α} {m : α}
  statement: (maximum l : WithTop α) = m -> m in l
  proof: argmax_mem

@[to_dual (attr := simp)]

中文:
定理 maximum_mem
  条件: {l : 列表 α} {m : α}
  结论: (maximum l : WithTop α) = m -> m in l
  证明: argmax_mem

@[to_dual (attr := simp)]

Depends on / 依赖: argmax_mem
-/
theorem maximum_mem {l : List α} {m : α} : (maximum l : WithTop α) = m -> m in l :=
  argmax_mem

@[to_dual (attr := simp)]
/--
theorem `maximum_eq_bot` / 定理 `maximum_eq_bot`

English:
theorem maximum_eq_bot
  given: {l : List α}
  statement: l.maximum = ⊥ ↔ l = []
  proof: argmax_eq_none

@[to_dual not_lt_minimum_of_mem]

中文:
定理 maximum_eq_bot
  条件: {l : 列表 α}
  结论: l.maximum = ⊥ ↔ l = []
  证明: argmax_eq_none

@[to_dual not_lt_minimum_of_mem]

Depends on / 依赖: argmax_eq_none
-/
theorem maximum_eq_bot {l : List α} : l.maximum = ⊥ ↔ l = [] :=
  argmax_eq_none

@[to_dual not_lt_minimum_of_mem]
/--
theorem `not_maximum_lt_of_mem` / 定理 `not_maximum_lt_of_mem`

English:
theorem not_maximum_lt_of_mem
  statement: a in l -> (maximum l : WithBot α) = m -> ¬m < a
  proof: not_lt_of_mem_argmax

@[to_dual not_lt_minimum_of_mem']

中文:
定理 not_maximum_lt_of_mem
  结论: a in l -> (maximum l : WithBot α) = m -> ¬m < a
  证明: not_lt_of_mem_argmax

@[to_dual not_lt_minimum_of_mem']

Depends on / 依赖: not_lt_of_mem_argmax
-/
theorem not_maximum_lt_of_mem : a in l -> (maximum l : WithBot α) = m -> ¬m < a :=
  not_lt_of_mem_argmax

@[to_dual not_lt_minimum_of_mem']
/--
theorem `not_maximum_lt_of_mem'` / 定理 `not_maximum_lt_of_mem'`

English:
theorem not_maximum_lt_of_mem'
  given: (ha : a in l)
  statement: ¬maximum l < (a : WithBot α)
  proof: by
  cases h : l.maximum <;> simp_all [not_maximum_lt_of_mem ha]

中文:
定理 not_maximum_lt_of_mem'
  条件: (ha : a in l)
  结论: ¬maximum l < (a : WithBot α)
  证明: by
  cases h : l.maximum <;> simp_all [not_maximum_lt_of_mem ha]

Depends on / 依赖: l.maximum, maximum, not_maximum_lt_of_mem
-/
theorem not_maximum_lt_of_mem' (ha : a in l) : ¬maximum l < (a : WithBot α) := by
  cases h : l.maximum <;> simp_all [not_maximum_lt_of_mem ha]

end Preorder

section LinearOrder

variable [LinearOrder α] {l : List α} {a m : α}

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
/--
theorem `maximum_concat` / 定理 `maximum_concat`

English:
theorem maximum_concat
  given: (a : α) (l : List α)
  statement: maximum (l ++ [a]) = max (maximum l) a
  proof: by
  simp only [maximum, argmax_concat, id]
  cases argmax id l
  · exact (max_eq_right bot_le).symm
  · simp [WithBot.some_eq_coe, max_def_lt, WithBot.coe_lt_coe]

@[to_dual minimum_le_of_mem]

中文:
定理 maximum_concat
  条件: (a : α) (l : 列表 α)
  结论: maximum (l ++ [a]) = 最大值 (maximum l) a
  证明: by
  simp only [maximum, argmax_concat, id]
  cases argmax id l
  · exact (max_eq_right bot_le).symm
  · simp [WithBot.some_eq_coe, max_def_lt, WithBot.coe_lt_coe]

@[to_dual minimum_le_of_mem]

Depends on / 依赖: WithBot, WithBot.coe_lt_coe, WithBot.some_eq_coe, argmax, argmax_concat, bot_le, coe_lt_coe, max_def_lt, max_eq_right, maximum, some_eq_coe
-/
theorem maximum_concat (a : α) (l : List α) : maximum (l ++ [a]) = max (maximum l) a := by
  simp only [maximum, argmax_concat, id]
  cases argmax id l
  · exact (max_eq_right bot_le).symm
  · simp [WithBot.some_eq_coe, max_def_lt, WithBot.coe_lt_coe]

@[to_dual minimum_le_of_mem]
/--
theorem `le_maximum_of_mem` / 定理 `le_maximum_of_mem`

English:
theorem le_maximum_of_mem
  statement: a in l -> (maximum l : WithBot α) = m -> a <= m
  proof: le_of_mem_argmax

@[to_dual minimum_le_of_mem']

中文:
定理 le_maximum_of_mem
  结论: a in l -> (maximum l : WithBot α) = m -> a <= m
  证明: le_of_mem_argmax

@[to_dual minimum_le_of_mem']

Depends on / 依赖: le_of_mem_argmax
-/
theorem le_maximum_of_mem : a in l -> (maximum l : WithBot α) = m -> a <= m :=
  le_of_mem_argmax

@[to_dual minimum_le_of_mem']
/--
theorem `le_maximum_of_mem'` / 定理 `le_maximum_of_mem'`

English:
theorem le_maximum_of_mem'
  given: (ha : a in l)
  statement: (a : WithBot α) <= maximum l
  proof: le_of_not_gt not_maximum_lt_of_mem' ha

@[to_dual]

中文:
定理 le_maximum_of_mem'
  条件: (ha : a in l)
  结论: (a : WithBot α) <= maximum l
  证明: le_of_not_gt not_maximum_lt_of_mem' ha

@[to_dual]

Depends on / 依赖: le_of_not_gt, not_maximum_lt_of_mem
-/
theorem le_maximum_of_mem' (ha : a in l) : (a : WithBot α) <= maximum l :=
le_of_not_gt not_maximum_lt_of_mem' ha

@[to_dual]
/--
theorem `maximum_cons` / 定理 `maximum_cons`

English:
theorem maximum_cons
  given: (a : α) (l : List α)
  statement: maximum (a :: l) = max ↑a (maximum l)
  proof: List.reverseRecOn l (by simp) fun tl hd ih => by
    rw [← cons_append]; rw [maximum_concat]; rw [ih]; rw [maximum_concat]; rw [max_assoc]

@[to_dual]

中文:
定理 maximum_cons
  条件: (a : α) (l : 列表 α)
  结论: maximum (a :: l) = 最大值 ↑a (maximum l)
  证明: List.reverseRecOn l (by simp) fun tl hd ih => by
    rw [← cons_append]; rw [maximum_concat]; rw [ih]; rw [maximum_concat]; rw [max_assoc]

@[to_dual]

Depends on / 依赖: List.reverseRecOn, cons_append, max_assoc, maximum_concat, reverseRecOn
-/
theorem maximum_cons (a : α) (l : List α) : maximum (a :: l) = max ↑a (maximum l) :=
  List.reverseRecOn l (by simp) fun tl hd ih => by
    rw [← cons_append]; rw [maximum_concat]; rw [ih]; rw [maximum_concat]; rw [max_assoc]

@[to_dual]
/--
lemma `maximum_append` / 引理 `maximum_append`

English:
lemma maximum_append
  given: (l₁ l₂ : List α)
  statement: (l₁ ++ l₂).maximum = max l₁.maximum l₂.maximum
  proof: by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => rw [maximum_cons, cons_append, maximum_cons, ih, ← max_assoc]

@[to_dual le_minimum_of_forall_le]

中文:
引理 maximum_append
  条件: (l₁ l₂ : 列表 α)
  结论: (l₁ ++ l₂).maximum = 最大值 l₁.maximum l₂.maximum
  证明: by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => rw [maximum_cons, cons_append, maximum_cons, ih, ← max_assoc]

@[to_dual le_minimum_of_forall_le]

Depends on / 依赖: cons_append, max_assoc, maximum_cons
-/
lemma maximum_append (l₁ l₂ : List α) : (l₁ ++ l₂).maximum = max l₁.maximum l₂.maximum := by
  induction l₁ with
  | nil => simp
  | cons _ _ ih => rw [maximum_cons, cons_append, maximum_cons, ih, ← max_assoc]

@[to_dual le_minimum_of_forall_le]
/--
theorem `maximum_le_of_forall_le` / 定理 `maximum_le_of_forall_le`

English:
theorem maximum_le_of_forall_le
  given: {b : WithBot α} (h : forall a in l, a <= b)
  statement: l.maximum <= b
  proof: by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [maximum_cons, max_le_iff]
    exact ⟨h a (by simp), ih fun a w => h a (mem_cons.mpr (Or.inr w))⟩

@[to_dual minimum_anti]

中文:
定理 maximum_le_of_对任意_le
  条件: {b : WithBot α} (h : 对任意 a in l, a <= b)
  结论: l.maximum <= b
  证明: by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [maximum_cons, max_le_iff]
    exact ⟨h a (by simp), ih fun a w => h a (mem_cons.mpr (Or.inr w))⟩

@[to_dual minimum_anti]

Depends on / 依赖: Or.inr, max_le_iff, maximum_cons, mem_cons, mem_cons.mpr
-/
theorem maximum_le_of_forall_le {b : WithBot α} (h : forall a in l, a <= b) : l.maximum <= b := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [maximum_cons, max_le_iff]
    exact ⟨h a (by simp), ih fun a w => h a (mem_cons.mpr (Or.inr w))⟩

@[to_dual minimum_anti]
/--
theorem `maximum_mono` / 定理 `maximum_mono`

English:
theorem maximum_mono
  given: {l₁ l₂ : List α} (h : l₁ subseteq l₂)
  statement: l₁.maximum <= l₂.maximum
  proof: maximum_le_of_forall_le fun _ => (le_maximum_of_mem' <| h ·)

中文:
定理 maximum_mono
  条件: {l₁ l₂ : 列表 α} (h : l₁ subseteq l₂)
  结论: l₁.maximum <= l₂.maximum
  证明: maximum_le_of_forall_le fun _ => (le_maximum_of_mem' <| h ·)

Depends on / 依赖: le_maximum_of_mem, maximum_le_of_forall_le
-/
theorem maximum_mono {l₁ l₂ : List α} (h : l₁ subseteq l₂) : l₁.maximum <= l₂.maximum :=
  maximum_le_of_forall_le fun _ => (le_maximum_of_mem' <| h ·)

set_option backward.isDefEq.respectTransparency false in
@[to_dual]
/--
theorem `maximum_eq_coe_iff` / 定理 `maximum_eq_coe_iff`

English:
theorem maximum_eq_coe_iff
  statement: maximum l = m ↔ m in l ∧ forall a in l, a <= m
  proof: by
  rw [maximum]; rw [← WithBot.some_eq_coe]; rw [argmax_eq_some_iff]
  simp only [id_eq, and_congr_right_iff, and_iff_left_iff_imp]
  intro _ h a hal hma
  rw [_root_.le_antisymm hma (h a hal)]

@[to_dual minimum_le_coe_iff]

中文:
定理 maximum_eq_coe_iff
  结论: maximum l = m ↔ m in l ∧ 对任意 a in l, a <= m
  证明: by
  rw [maximum]; rw [← WithBot.some_eq_coe]; rw [argmax_eq_some_iff]
  simp only [id_eq, and_congr_right_iff, and_iff_left_iff_imp]
  intro _ h a hal hma
  rw [_root_.le_antisymm hma (h a hal)]

@[to_dual minimum_le_coe_iff]

Depends on / 依赖: WithBot, WithBot.some_eq_coe, _root_, _root_.le_antisymm, and_congr_right_iff, and_iff_left_iff_imp, argmax_eq_some_iff, id_eq, le_antisymm, maximum, some_eq_coe
-/
theorem maximum_eq_coe_iff : maximum l = m ↔ m in l ∧ forall a in l, a <= m := by
  rw [maximum]; rw [← WithBot.some_eq_coe]; rw [argmax_eq_some_iff]
  simp only [id_eq, and_congr_right_iff, and_iff_left_iff_imp]
  intro _ h a hal hma
  rw [_root_.le_antisymm hma (h a hal)]

@[to_dual minimum_le_coe_iff]
/--
theorem `coe_le_maximum_iff` / 定理 `coe_le_maximum_iff`

English:
theorem coe_le_maximum_iff
  statement: a <= l.maximum ↔ exists b, b in l ∧ a <= b
  proof: by
  induction l <;> simp [maximum_cons, *]

@[to_dual]

中文:
定理 coe_le_maximum_iff
  结论: a <= l.maximum ↔ 存在 b, b in l ∧ a <= b
  证明: by
  induction l <;> simp [maximum_cons, *]

@[to_dual]

Depends on / 依赖: maximum_cons
-/
theorem coe_le_maximum_iff : a <= l.maximum ↔ exists b, b in l ∧ a <= b := by
  induction l <;> simp [maximum_cons, *]

@[to_dual]
/--
theorem `maximum_ne_bot_of_ne_nil` / 定理 `maximum_ne_bot_of_ne_nil`

English:
theorem maximum_ne_bot_of_ne_nil
  given: (h : l != [])
  statement: l.maximum != ⊥
  proof: match l, h with | _ :: _, _ => by simp [maximum_cons]

@[to_dual]

中文:
定理 maximum_ne_bot_of_ne_nil
  条件: (h : l != [])
  结论: l.maximum != ⊥
  证明: match l, h with | _ :: _, _ => by simp [maximum_cons]

@[to_dual]

Depends on / 依赖: maximum_cons
-/
theorem maximum_ne_bot_of_ne_nil (h : l != []) : l.maximum != ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]

@[to_dual]
/--
theorem `maximum_ne_bot_of_length_pos` / 定理 `maximum_ne_bot_of_length_pos`

English:
theorem maximum_ne_bot_of_length_pos
  given: (h : 0 < l.length)
  statement: l.maximum != ⊥
  proof: match l, h with | _ :: _, _ => by simp [maximum_cons]

中文:
定理 maximum_ne_bot_of_length_pos
  条件: (h : 0 < l.length)
  结论: l.maximum != ⊥
  证明: match l, h with | _ :: _, _ => by simp [maximum_cons]

Depends on / 依赖: maximum_cons
-/
theorem maximum_ne_bot_of_length_pos (h : 0 < l.length) : l.maximum != ⊥ :=
  match l, h with | _ :: _, _ => by simp [maximum_cons]

/-- The maximum value in a non-empty `List`. -/
@[to_dual /-- The minimum value in a non-empty `List`. -/]
/--
Definition of `maximum_of_length_pos` / `maximum_of_length_pos` 的定义

English:
definition maximum_of_length_pos
  signature: (h : 0 < l.length)
  body: WithBot.unbot l.maximum (maximum_ne_bot_of_length_pos h)

@[to_dual (attr := simp)]

中文:
定义 maximum_of_length_pos
  签名: (h : 0 < l.length)
  定义体: WithBot.unbot l.maximum (maximum_ne_bot_of_length_pos h)

@[to_dual (attr := simp)]

Depends on / 依赖: WithBot, WithBot.unbot, l.maximum, maximum, maximum_ne_bot_of_length_pos
-/
def maximum_of_length_pos (h : 0 < l.length) : α :=
  WithBot.unbot l.maximum (maximum_ne_bot_of_length_pos h)

@[to_dual (attr := simp)]
/--
lemma `coe_maximum_of_length_pos` / 引理 `coe_maximum_of_length_pos`

English:
lemma coe_maximum_of_length_pos
  given: (h : 0 < l.length)
  proof: WithBot.coe_unbot _ _

@[to_dual (attr := simp) minimum_of_length_pos_le_iff]

中文:
引理 coe_maximum_of_length_pos
  条件: (h : 0 < l.length)
  证明: WithBot.coe_unbot _ _

@[to_dual (attr := simp) minimum_of_length_pos_le_iff]

Depends on / 依赖: WithBot, WithBot.coe_unbot, coe_unbot
-/
lemma coe_maximum_of_length_pos (h : 0 < l.length) :
    (l.maximum_of_length_pos h : α) = l.maximum :=
  WithBot.coe_unbot _ _

@[to_dual (attr := simp) minimum_of_length_pos_le_iff]
/--
theorem `le_maximum_of_length_pos_iff` / 定理 `le_maximum_of_length_pos_iff`

English:
theorem le_maximum_of_length_pos_iff
  given: {b : α} (h : 0 < l.length)
  proof: WithBot.le_unbot_iff _

@[to_dual]

中文:
定理 le_maximum_of_length_pos_iff
  条件: {b : α} (h : 0 < l.length)
  证明: WithBot.le_unbot_iff _

@[to_dual]

Depends on / 依赖: WithBot, WithBot.le_unbot_iff, le_unbot_iff
-/
theorem le_maximum_of_length_pos_iff {b : α} (h : 0 < l.length) :
    b <= maximum_of_length_pos h ↔ b <= l.maximum :=
  WithBot.le_unbot_iff _

@[to_dual]
/--
theorem `maximum_of_length_pos_mem` / 定理 `maximum_of_length_pos_mem`

English:
theorem maximum_of_length_pos_mem
  given: (h : 0 < l.length)
  proof: by
  apply maximum_mem
  simp only [coe_maximum_of_length_pos]

@[to_dual minimum_of_length_pos_le_of_mem]

中文:
定理 maximum_of_length_pos_mem
  条件: (h : 0 < l.length)
  证明: by
  apply maximum_mem
  simp only [coe_maximum_of_length_pos]

@[to_dual minimum_of_length_pos_le_of_mem]

Depends on / 依赖: coe_maximum_of_length_pos, maximum_mem
-/
theorem maximum_of_length_pos_mem (h : 0 < l.length) :
    maximum_of_length_pos h in l := by
  apply maximum_mem
  simp only [coe_maximum_of_length_pos]

@[to_dual minimum_of_length_pos_le_of_mem]
/--
theorem `le_maximum_of_length_pos_of_mem` / 定理 `le_maximum_of_length_pos_of_mem`

English:
theorem le_maximum_of_length_pos_of_mem
  given: (h : a in l) (w : 0 < l.length)
  proof: by
  simp only [le_maximum_of_length_pos_iff]
  exact le_maximum_of_mem' h

@[to_dual minimum_of_length_pos_le_getElem]

中文:
定理 le_maximum_of_length_pos_of_mem
  条件: (h : a in l) (w : 0 < l.length)
  证明: by
  simp only [le_maximum_of_length_pos_iff]
  exact le_maximum_of_mem' h

@[to_dual minimum_of_length_pos_le_getElem]

Depends on / 依赖: le_maximum_of_length_pos_iff, le_maximum_of_mem
-/
theorem le_maximum_of_length_pos_of_mem (h : a in l) (w : 0 < l.length) :
    a <= l.maximum_of_length_pos w := by
  simp only [le_maximum_of_length_pos_iff]
  exact le_maximum_of_mem' h

@[to_dual minimum_of_length_pos_le_getElem]
/--
theorem `getElem_le_maximum_of_length_pos` / 定理 `getElem_le_maximum_of_length_pos`

English:
theorem getElem_le_maximum_of_length_pos
  given: {i : Nat} (w : i < l.length) (h := (Nat.zero_lt_of_lt w))
  proof: by
  apply le_maximum_of_length_pos_of_mem
  exact getElem_mem _

@[to_dual]

中文:
定理 getElem_le_maximum_of_length_pos
  条件: {i : 自然数} (w : i < l.length) (h := (自然数.zero_lt_of_lt w))
  证明: by
  apply le_maximum_of_length_pos_of_mem
  exact getElem_mem _

@[to_dual]

Depends on / 依赖: Nat.zero_lt_of_lt, zero_lt_of_lt
-/
theorem getElem_le_maximum_of_length_pos {i : Nat} (w : i < l.length) (h := (Nat.zero_lt_of_lt w)) :
    l[i] <= l.maximum_of_length_pos h := by
  apply le_maximum_of_length_pos_of_mem
  exact getElem_mem _

@[to_dual]
/--
theorem `Perm.maximum_eq` / 定理 `Perm.maximum_eq`

English:
theorem Perm.maximum_eq
  given: {l l' : List α} (h : l ~ l')
  proof: by
  induction h with grind [maximum_cons]


@[to_dual]

中文:
定理 置换.maximum_eq
  条件: {l l' : 列表 α} (h : l ~ l')
  证明: by
  induction h with grind [maximum_cons]


@[to_dual]

Depends on / 依赖: maximum_cons
-/
theorem Perm.maximum_eq {l l' : List α} (h : l ~ l') :
    l.maximum = l'.maximum := by
  induction h with grind [maximum_cons]


@[to_dual]
/--
lemma `getD_max?_eq_unbotD_maximum` / 引理 `getD_max?_eq_unbotD_maximum`

English:
lemma getD_max?_eq_unbotD_maximum
  given: (l : List α) (d : α)
  statement: l.max?.getD d = l.maximum.unbotD d
  proof: by
  cases hy : l.maximum with
  | bot => simp [List.maximum_eq_bot.mp hy]
  | coe y =>
    rw [List.maximum_eq_coe_iff] at hy
    simp only [WithBot.unbotD_coe]
    cases hz : l.max? with
    | none => simp [List.max?_eq_none_iff.mp hz] at hy
    | some z =>
      have : Std.Antisymm (α := α) (· <=

中文:
引理 getD_max?_eq_unbotD_maximum
  条件: (l : 列表 α) (d : α)
  结论: l.最大值?.getD d = l.maximum.unbotD d
  证明: by
  cases hy : l.maximum with
  | bot => simp [List.maximum_eq_bot.mp hy]
  | coe y =>
    rw [List.maximum_eq_coe_iff] at hy
    simp only [WithBot.unbotD_coe]
    cases hz : l.max? with
    | none => simp [List.max?_eq_none_iff.mp hz] at hy
    | some z =>
      have : Std.Antisymm (α := α) (· <=

Depends on / 依赖: Antisymm, List.max, List.maximum_eq_bot.mp, List.maximum_eq_coe_iff, Option.getD_some, Std.Antisymm, WithBot, WithBot.unbotD_coe, _eq_none_iff, _eq_none_iff.mp, _eq_some_iff, _root_, _root_.le_antisymm, getD_some, hy.left, hy.right, hz.left, hz.right, l.max, l.maximum
-/
lemma getD_max?_eq_unbotD_maximum (l : List α) (d : α) : l.max?.getD d = l.maximum.unbotD d := by
  cases hy : l.maximum with
  | bot => simp [List.maximum_eq_bot.mp hy]
  | coe y =>
    rw [List.maximum_eq_coe_iff] at hy
    simp only [WithBot.unbotD_coe]
    cases hz : l.max? with
    | none => simp [List.max?_eq_none_iff.mp hz] at hy
    | some z =>
      have : Std.Antisymm (α := α) (· <= ·) := ⟨fun _ _ => _root_.le_antisymm⟩
      rw [List.max?_eq_some_iff] at hz
      · rw [Option.getD_some]
        exact _root_.le_antisymm (hy.right _ hz.left) (hz.right _ hy.left)

end LinearOrder

end MaximumMinimum

section Fold

variable [LinearOrder α]

section OrderBot

variable [OrderBot α] {l : List α}

@[to_dual (attr := simp)]
/--
theorem `foldr_max_of_ne_nil` / 定理 `foldr_max_of_ne_nil`

English:
theorem foldr_max_of_ne_nil
  given: (h : l != [])
  statement: ↑(l.foldr max ⊥) = l.maximum
  proof: by
  induction l with
  | nil => contradiction
  | cons hd tl IH =>
    rw [maximum_cons]; rw [foldr]; rw [WithBot.coe_max]
    by_cases h : tl = []
    · simp [h]
    · simp [IH h]

@[to_dual le_min_of_forall_le]

中文:
定理 foldr_max_of_ne_nil
  条件: (h : l != [])
  结论: ↑(l.foldr 最大值 ⊥) = l.maximum
  证明: by
  induction l with
  | nil => contradiction
  | cons hd tl IH =>
    rw [maximum_cons]; rw [foldr]; rw [WithBot.coe_max]
    by_cases h : tl = []
    · simp [h]
    · simp [IH h]

@[to_dual le_min_of_forall_le]

Depends on / 依赖: WithBot, WithBot.coe_max, coe_max, maximum_cons
-/
theorem foldr_max_of_ne_nil (h : l != []) : ↑(l.foldr max ⊥) = l.maximum := by
  induction l with
  | nil => contradiction
  | cons hd tl IH =>
    rw [maximum_cons]; rw [foldr]; rw [WithBot.coe_max]
    by_cases h : tl = []
    · simp [h]
    · simp [IH h]

@[to_dual le_min_of_forall_le]
/--
theorem `max_le_of_forall_le` / 定理 `max_le_of_forall_le`

English:
theorem max_le_of_forall_le
  given: (l : List α) (a : α) (h : forall x in l, x <= a)
  statement: l.foldr max ⊥ <= a
  proof: by
  induction l with
  | nil => simp
| cons y l IH => simpa [h y mem_cons_self] using IH fun x hx => h x mem_cons_of_mem _ hx

@[to_dual min_le_of_le]

中文:
定理 max_le_of_对任意_le
  条件: (l : 列表 α) (a : α) (h : 对任意 x in l, x <= a)
  结论: l.foldr 最大值 ⊥ <= a
  证明: by
  induction l with
  | nil => simp
| cons y l IH => simpa [h y mem_cons_self] using IH fun x hx => h x mem_cons_of_mem _ hx

@[to_dual min_le_of_le]

Depends on / 依赖: mem_cons_of_mem, mem_cons_self
-/
theorem max_le_of_forall_le (l : List α) (a : α) (h : forall x in l, x <= a) : l.foldr max ⊥ <= a := by
  induction l with
  | nil => simp
| cons y l IH => simpa [h y mem_cons_self] using IH fun x hx => h x mem_cons_of_mem _ hx

@[to_dual min_le_of_le]
/--
theorem `le_max_of_le` / 定理 `le_max_of_le`

English:
theorem le_max_of_le
  given: {l : List α} {a x : α} (hx : x in l) (h : a <= x)
  statement: a <= l.foldr max ⊥
  proof: by
  induction l with
  | nil => exact absurd hx not_mem_nil
  | cons y l IH =>
    obtain hl | hl := hx
    · simp only [foldr]
      exact le_max_of_le_left h
    · exact le_max_of_le_right (IH (by assumption))

中文:
定理 le_max_of_le
  条件: {l : 列表 α} {a x : α} (hx : x in l) (h : a <= x)
  结论: a <= l.foldr 最大值 ⊥
  证明: by
  induction l with
  | nil => exact absurd hx not_mem_nil
  | cons y l IH =>
    obtain hl | hl := hx
    · simp only [foldr]
      exact le_max_of_le_left h
    · exact le_max_of_le_right (IH (by assumption))

Depends on / 依赖: absurd, le_max_of_le_left, le_max_of_le_right, not_mem_nil
-/
theorem le_max_of_le {l : List α} {a x : α} (hx : x in l) (h : a <= x) : a <= l.foldr max ⊥ := by
  induction l with
  | nil => exact absurd hx not_mem_nil
  | cons y l IH =>
    obtain hl | hl := hx
    · simp only [foldr]
      exact le_max_of_le_left h
    · exact le_max_of_le_right (IH (by assumption))

end OrderBot

/-- If `a ≤ x` for some `x` in the list `l`, and `b : α`, then `a ≤ l.foldr max b`. -/
@[to_dual min_le_of_le']
/--
theorem `le_max_of_le'` / 定理 `le_max_of_le'`

English:
theorem le_max_of_le'
  given: {l : List α} {a x : α} (b : α) (hx : x in l) (h : a <= x)
  proof: by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l IH =>
    simp only [List.foldr]
    obtain rfl | hl := mem_cons.mp hx
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)

中文:
定理 le_max_of_le'
  条件: {l : 列表 α} {a x : α} (b : α) (hx : x in l) (h : a <= x)
  证明: by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l IH =>
    simp only [List.foldr]
    obtain rfl | hl := mem_cons.mp hx
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)

Depends on / 依赖: List.foldr, List.not_mem_nil, absurd, le_max_of_le_left, le_max_of_le_right, mem_cons, mem_cons.mp, not_mem_nil
-/
theorem le_max_of_le' {l : List α} {a x : α} (b : α) (hx : x in l) (h : a <= x) :
    a <= l.foldr max b := by
  induction l with
  | nil => exact absurd hx List.not_mem_nil
  | cons y l IH =>
    simp only [List.foldr]
    obtain rfl | hl := mem_cons.mp hx
    · exact le_max_of_le_left h
    · exact le_max_of_le_right (IH hl)

end Fold

end List
