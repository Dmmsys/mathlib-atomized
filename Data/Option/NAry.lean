/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Init

/-!
# Binary map of options

This file defines the binary map of `Option`. This is mostly useful to define pointwise operations
on intervals.

## Main declarations

* `Option.map₂`: Binary map of options.

## Notes

This file is very similar to the n-ary section of `Mathlib/Data/Set/Basic.lean`, to
`Mathlib/Data/Finset/NAry.lean` and to `Mathlib/Order/Filter/NAry.lean`. Please keep them in sync.

We do not define `Option.map₃` as its only purpose so far would be to prove properties of
`Option.map₂` and casing already fulfills this task.
-/

@[expose] public section

universe u

open Function

namespace Option

-- Allow `grind` to case split on `Option` in this file.
attribute [local grind cases] Option

variable {α β γ δ : Type*} {f : α -> β -> γ} {a : Option α} {b : Option β} {c : Option γ}

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : α -> β -> γ) (a : Option α) (b : Option β)
  body: a.bind fun a => b.map f a

中文:
定义 map₂
  签名: (f : α -> β -> γ) (a : 选项类型 α) (b : 选项类型 β)
  定义体: a.bind fun a => b.map f a

Depends on / 依赖: a.bind, b.map
-/
def map₂ (f : α -> β -> γ) (a : Option α) (b : Option β) : Option γ :=
a.bind fun a => b.map f a

/--
theorem `map₂_def` / 定理 `map₂_def`

English:
theorem map₂_def
  given: {α β γ : Type u} (f : α -> β -> γ) (a : Option α) (b : Option β)
  proof: by
  cases a <;> rfl

@[simp, grind =]

中文:
定理 map₂_def
  条件: {α β γ : 类型u} (f : α -> β -> γ) (a : 选项类型 α) (b : 选项类型 β)
  证明: by
  cases a <;> rfl

@[simp, grind =]
-/
theorem map₂_def {α β γ : Type u} (f : α -> β -> γ) (a : Option α) (b : Option β) :
map₂ f a b = f < > a <*> b := by
  cases a <;> rfl

@[simp, grind =]
/--
theorem `map₂_some_some` / 定理 `map₂_some_some`

English:
theorem map₂_some_some
  given: (f : α -> β -> γ) (a : α) (b : β)
  statement: map₂ f (some a) (some b) = f a b
  proof: rfl

中文:
定理 map₂_some_some
  条件: (f : α -> β -> γ) (a : α) (b : β)
  结论: map₂ f (some a) (some b) = f a b
  证明: rfl
-/
theorem map₂_some_some (f : α -> β -> γ) (a : α) (b : β) : map₂ f (some a) (some b) = f a b := rfl

/--
theorem `map₂_coe_coe` / 定理 `map₂_coe_coe`

English:
theorem map₂_coe_coe
  given: (f : α -> β -> γ) (a : α) (b : β)
  statement: map₂ f a b = f a b
  proof: rfl

@[simp, grind =]

中文:
定理 map₂_coe_coe
  条件: (f : α -> β -> γ) (a : α) (b : β)
  结论: map₂ f a b = f a b
  证明: rfl

@[simp, grind =]
-/
theorem map₂_coe_coe (f : α -> β -> γ) (a : α) (b : β) : map₂ f a b = f a b := rfl

@[simp, grind =]
/--
theorem `map₂_none_left` / 定理 `map₂_none_left`

English:
theorem map₂_none_left
  given: (f : α -> β -> γ) (b : Option β)
  statement: map₂ f none b = none
  proof: rfl

@[simp, grind =]

中文:
定理 map₂_none_left
  条件: (f : α -> β -> γ) (b : 选项类型 β)
  结论: map₂ f none b = none
  证明: rfl

@[simp, grind =]
-/
theorem map₂_none_left (f : α -> β -> γ) (b : Option β) : map₂ f none b = none := rfl

@[simp, grind =]
/--
theorem `map₂_none_right` / 定理 `map₂_none_right`

English:
theorem map₂_none_right
  given: (f : α -> β -> γ) (a : Option α)
  statement: map₂ f a none = none
  proof: by cases a <;> rfl

@[simp]

中文:
定理 map₂_none_right
  条件: (f : α -> β -> γ) (a : 选项类型 α)
  结论: map₂ f a none = none
  证明: by cases a <;> rfl

@[simp]
-/
theorem map₂_none_right (f : α -> β -> γ) (a : Option α) : map₂ f a none = none := by cases a <;> rfl

@[simp]
/--
theorem `map₂_coe_left` / 定理 `map₂_coe_left`

English:
theorem map₂_coe_left
  given: (f : α -> β -> γ) (a : α) (b : Option β)
  statement: map₂ f a b = b.map fun b => f a b
  proof: rfl

@[simp]

中文:
定理 map₂_coe_left
  条件: (f : α -> β -> γ) (a : α) (b : 选项类型 β)
  结论: map₂ f a b = b.map fun b => f a b
  证明: rfl

@[simp]
-/
theorem map₂_coe_left (f : α -> β -> γ) (a : α) (b : Option β) : map₂ f a b = b.map fun b => f a b :=
  rfl

@[simp]
/--
theorem `map₂_coe_right` / 定理 `map₂_coe_right`

English:
theorem map₂_coe_right
  given: (f : α -> β -> γ) (a : Option α) (b : β)
  proof: by grind

中文:
定理 map₂_coe_right
  条件: (f : α -> β -> γ) (a : 选项类型 α) (b : β)
  证明: by grind
-/
theorem map₂_coe_right (f : α -> β -> γ) (a : Option α) (b : β) :
    map₂ f a b = a.map fun a => f a b := by grind

/--
theorem `mem_map₂_iff` / 定理 `mem_map₂_iff`

English:
theorem mem_map₂_iff
  given: {c : γ}
  statement: c in map₂ f a b ↔ exists a' b', a' in a ∧ b' in b ∧ f a' b' = c
  proof: by
  grind

中文:
定理 mem_map₂_iff
  条件: {c : γ}
  结论: c in map₂ f a b ↔ 存在 a' b', a' in a ∧ b' in b ∧ f a' b' = c
  证明: by
  grind
-/
theorem mem_map₂_iff {c : γ} : c in map₂ f a b ↔ exists a' b', a' in a ∧ b' in b ∧ f a' b' = c := by
  grind

/-- `simp`-normal form of `mem_map₂_iff`. -/
@[simp]
/--
theorem `map₂_eq_some_iff` / 定理 `map₂_eq_some_iff`

English:
theorem map₂_eq_some_iff
  given: {c : γ}
  proof: by
  grind

@[simp]

中文:
定理 map₂_eq_some_iff
  条件: {c : γ}
  证明: by
  grind

@[simp]
-/
theorem map₂_eq_some_iff {c : γ} :
    map₂ f a b = some c ↔ exists a' b', a' in a ∧ b' in b ∧ f a' b' = c := by
  grind

@[simp]
/--
theorem `map₂_eq_none_iff` / 定理 `map₂_eq_none_iff`

English:
theorem map₂_eq_none_iff
  statement: map₂ f a b = none ↔ a = none ∨ b = none
  proof: by
  grind

中文:
定理 map₂_eq_none_iff
  结论: map₂ f a b = none ↔ a = none ∨ b = none
  证明: by
  grind
-/
theorem map₂_eq_none_iff : map₂ f a b = none ↔ a = none ∨ b = none := by
  grind

/--
theorem `map₂_swap` / 定理 `map₂_swap`

English:
theorem map₂_swap
  given: (f : α -> β -> γ) (a : Option α) (b : Option β)
  proof: by grind

中文:
定理 map₂_swap
  条件: (f : α -> β -> γ) (a : 选项类型 α) (b : 选项类型 β)
  证明: by grind
-/
theorem map₂_swap (f : α -> β -> γ) (a : Option α) (b : Option β) :
    map₂ f a b = map₂ (fun a b => f b a) b a := by grind

/--
theorem `map_map₂` / 定理 `map_map₂`

English:
theorem map_map₂
  given: (f : α -> β -> γ) (g : γ -> δ)
  proof: by grind

中文:
定理 map_map₂
  条件: (f : α -> β -> γ) (g : γ -> δ)
  证明: by grind
-/
theorem map_map₂ (f : α -> β -> γ) (g : γ -> δ) :
    (map₂ f a b).map g = map₂ (fun a b => g (f a b)) a b := by grind

/--
theorem `map₂_map_left` / 定理 `map₂_map_left`

English:
theorem map₂_map_left
  given: (f : γ -> β -> δ) (g : α -> γ)
  proof: by grind

中文:
定理 map₂_map_left
  条件: (f : γ -> β -> δ) (g : α -> γ)
  证明: by grind
-/
theorem map₂_map_left (f : γ -> β -> δ) (g : α -> γ) :
    map₂ f (a.map g) b = map₂ (fun a b => f (g a) b) a b := by grind

/--
theorem `map₂_map_right` / 定理 `map₂_map_right`

English:
theorem map₂_map_right
  given: (f : α -> γ -> δ) (g : β -> γ)
  proof: by grind

@[simp]

中文:
定理 map₂_map_right
  条件: (f : α -> γ -> δ) (g : β -> γ)
  证明: by grind

@[simp]
-/
theorem map₂_map_right (f : α -> γ -> δ) (g : β -> γ) :
    map₂ f a (b.map g) = map₂ (fun a b => f a (g b)) a b := by grind

@[simp]
/--
theorem `map₂_curry` / 定理 `map₂_curry`

English:
theorem map₂_curry
  given: (f : α × β -> γ) (a : Option α) (b : Option β)
  proof: by grind

@[simp]

中文:
定理 map₂_curry
  条件: (f : α × β -> γ) (a : 选项类型 α) (b : 选项类型 β)
  证明: by grind

@[simp]
-/
theorem map₂_curry (f : α × β -> γ) (a : Option α) (b : Option β) :
    map₂ (curry f) a b = Option.map f (map₂ Prod.mk a b) := by grind

@[simp]
/--
theorem `map_uncurry` / 定理 `map_uncurry`

English:
theorem map_uncurry
  given: (f : α -> β -> γ) (x : Option (α × β))
  proof: by grind

中文:
定理 map_uncurry
  条件: (f : α -> β -> γ) (x : 选项类型 (α × β))
  证明: by grind
-/
theorem map_uncurry (f : α -> β -> γ) (x : Option (α × β)) :
    x.map (uncurry f) = map₂ f (x.map Prod.fst) (x.map Prod.snd) := by grind

/-!
### Algebraic replacement rules

A collection of lemmas to transfer associativity, commutativity, distributivity, ... of operations
to the associativity, commutativity, distributivity, ... of `Option.map₂` of those operations.
The proof pattern is `map₂_lemma operation_lemma`. For example, `map₂_comm mul_comm` proves that
`map₂ (*) a b = map₂ (*) g f` in a `CommSemigroup`.
-/

variable {α' β' δ' ε ε' : Type*}

/--
theorem `map₂_assoc` / 定理 `map₂_assoc`

English:
theorem map₂_assoc
  statement: {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}
  proof: by grind

中文:
定理 map₂_assoc
  结论: {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}
  证明: by grind
-/
theorem map₂_assoc {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> ε' -> ε} {g' : β -> γ -> ε'}
    (h_assoc : forall a b c, f (g a b) c = f' a (g' b c)) :
    map₂ f (map₂ g a b) c = map₂ f' a (map₂ g' b c) := by grind

/--
theorem `map₂_comm` / 定理 `map₂_comm`

English:
theorem map₂_comm
  given: {g : β -> α -> γ} (h_comm : forall a b, f a b = g b a)
  statement: map₂ f a b = map₂ g b a
  proof: by
  grind

中文:
定理 map₂_comm
  条件: {g : β -> α -> γ} (h_comm : 对任意 a b, f a b = g b a)
  结论: map₂ f a b = map₂ g b a
  证明: by
  grind
-/
theorem map₂_comm {g : β -> α -> γ} (h_comm : forall a b, f a b = g b a) : map₂ f a b = map₂ g b a := by
  grind

/--
theorem `map₂_left_comm` / 定理 `map₂_left_comm`

English:
theorem map₂_left_comm
  statement: {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}
  proof: by grind

中文:
定理 map₂_left_comm
  结论: {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}
  证明: by grind
-/
theorem map₂_left_comm {f : α -> δ -> ε} {g : β -> γ -> δ} {f' : α -> γ -> δ'} {g' : β -> δ' -> ε}
    (h_left_comm : forall a b c, f a (g b c) = g' b (f' a c)) :
    map₂ f a (map₂ g b c) = map₂ g' b (map₂ f' a c) := by grind

/--
theorem `map₂_right_comm` / 定理 `map₂_right_comm`

English:
theorem map₂_right_comm
  statement: {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}
  proof: by grind

中文:
定理 map₂_right_comm
  结论: {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}
  证明: by grind
-/
theorem map₂_right_comm {f : δ -> γ -> ε} {g : α -> β -> δ} {f' : α -> γ -> δ'} {g' : δ' -> β -> ε}
    (h_right_comm : forall a b c, f (g a b) c = g' (f' a c) b) :
    map₂ f (map₂ g a b) c = map₂ g' (map₂ f' a c) b := by grind

/--
theorem `map_map₂_distrib` / 定理 `map_map₂_distrib`

English:
theorem map_map₂_distrib
  statement: {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
  proof: by grind

中文:
定理 map_map₂_distrib
  结论: {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
  证明: by grind
-/
theorem map_map₂_distrib {g : γ -> δ} {f' : α' -> β' -> δ} {g₁ : α -> α'} {g₂ : β -> β'}
    (h_distrib : forall a b, g (f a b) = f' (g₁ a) (g₂ b)) :
    (map₂ f a b).map g = map₂ f' (a.map g₁) (b.map g₂) := by grind

/-!
The following symmetric restatement are needed because unification has a hard time figuring all the
functions if you symmetrize on the spot. This is also how the other n-ary APIs do it.
-/

/--
theorem `map_map₂_distrib_left` / 定理 `map_map₂_distrib_left`

English:
theorem map_map₂_distrib_left
  statement: {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
  proof: by grind

中文:
定理 map_map₂_distrib_left
  结论: {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
  证明: by grind
-/
theorem map_map₂_distrib_left {g : γ -> δ} {f' : α' -> β -> δ} {g' : α -> α'}
    (h_distrib : forall a b, g (f a b) = f' (g' a) b) :
    (map₂ f a b).map g = map₂ f' (a.map g') b := by grind

/--
theorem `map_map₂_distrib_right` / 定理 `map_map₂_distrib_right`

English:
theorem map_map₂_distrib_right
  statement: {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
  proof: by
  grind

中文:
定理 map_map₂_distrib_right
  结论: {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
  证明: by
  grind
-/
theorem map_map₂_distrib_right {g : γ -> δ} {f' : α -> β' -> δ} {g' : β -> β'}
    (h_distrib : forall a b, g (f a b) = f' a (g' b)) : (map₂ f a b).map g = map₂ f' a (b.map g') := by
  grind

/--
theorem `map₂_map_left_comm` / 定理 `map₂_map_left_comm`

English:
theorem map₂_map_left_comm
  statement: {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
  proof: by
  grind

中文:
定理 map₂_map_left_comm
  结论: {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
  证明: by
  grind
-/
theorem map₂_map_left_comm {f : α' -> β -> γ} {g : α -> α'} {f' : α -> β -> δ} {g' : δ -> γ}
    (h_left_comm : forall a b, f (g a) b = g' (f' a b)) : map₂ f (a.map g) b = (map₂ f' a b).map g' := by
  grind

/--
theorem `map_map₂_right_comm` / 定理 `map_map₂_right_comm`

English:
theorem map_map₂_right_comm
  statement: {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
  proof: by grind

中文:
定理 map_map₂_right_comm
  结论: {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
  证明: by grind
-/
theorem map_map₂_right_comm {f : α -> β' -> γ} {g : β -> β'} {f' : α -> β -> δ} {g' : δ -> γ}
    (h_right_comm : forall a b, f a (g b) = g' (f' a b)) :
    map₂ f a (b.map g) = (map₂ f' a b).map g' := by grind

/--
theorem `map_map₂_antidistrib` / 定理 `map_map₂_antidistrib`

English:
theorem map_map₂_antidistrib
  statement: {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
  proof: by grind

中文:
定理 map_map₂_antidistrib
  结论: {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
  证明: by grind
-/
theorem map_map₂_antidistrib {g : γ -> δ} {f' : β' -> α' -> δ} {g₁ : β -> β'} {g₂ : α -> α'}
    (h_antidistrib : forall a b, g (f a b) = f' (g₁ b) (g₂ a)) :
    (map₂ f a b).map g = map₂ f' (b.map g₁) (a.map g₂) := by grind

/--
theorem `map_map₂_antidistrib_left` / 定理 `map_map₂_antidistrib_left`

English:
theorem map_map₂_antidistrib_left
  statement: {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
  proof: by grind

中文:
定理 map_map₂_antidistrib_left
  结论: {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
  证明: by grind
-/
theorem map_map₂_antidistrib_left {g : γ -> δ} {f' : β' -> α -> δ} {g' : β -> β'}
    (h_antidistrib : forall a b, g (f a b) = f' (g' b) a) :
    (map₂ f a b).map g = map₂ f' (b.map g') a := by grind

/--
theorem `map_map₂_antidistrib_right` / 定理 `map_map₂_antidistrib_right`

English:
theorem map_map₂_antidistrib_right
  statement: {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
  proof: by grind

中文:
定理 map_map₂_antidistrib_right
  结论: {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
  证明: by grind
-/
theorem map_map₂_antidistrib_right {g : γ -> δ} {f' : β -> α' -> δ} {g' : α -> α'}
    (h_antidistrib : forall a b, g (f a b) = f' b (g' a)) :
    (map₂ f a b).map g = map₂ f' b (a.map g') := by grind

/--
theorem `map₂_map_left_anticomm` / 定理 `map₂_map_left_anticomm`

English:
theorem map₂_map_left_anticomm
  statement: {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
  proof: by grind

中文:
定理 map₂_map_left_anticomm
  结论: {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
  证明: by grind
-/
theorem map₂_map_left_anticomm {f : α' -> β -> γ} {g : α -> α'} {f' : β -> α -> δ} {g' : δ -> γ}
    (h_left_anticomm : forall a b, f (g a) b = g' (f' b a)) :
    map₂ f (a.map g) b = (map₂ f' b a).map g' := by grind

/--
theorem `map_map₂_right_anticomm` / 定理 `map_map₂_right_anticomm`

English:
theorem map_map₂_right_anticomm
  statement: {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
  proof: by grind

中文:
定理 map_map₂_right_anticomm
  结论: {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
  证明: by grind
-/
theorem map_map₂_right_anticomm {f : α -> β' -> γ} {g : β -> β'} {f' : β -> α -> δ} {g' : δ -> γ}
    (h_right_anticomm : forall a b, f a (g b) = g' (f' b a)) :
    map₂ f a (b.map g) = (map₂ f' b a).map g' := by grind

/--
lemma `map₂_left_identity` / 引理 `map₂_left_identity`

English:
lemma map₂_left_identity
  given: {f : α -> β -> β} {a : α} (h : forall b, f a b = b) (o : Option β)
  proof: by grind

中文:
引理 map₂_left_identity
  条件: {f : α -> β -> β} {a : α} (h : 对任意 b, f a b = b) (o : 选项类型 β)
  证明: by grind
-/
lemma map₂_left_identity {f : α -> β -> β} {a : α} (h : forall b, f a b = b) (o : Option β) :
    map₂ f (some a) o = o := by grind

/--
lemma `map₂_right_identity` / 引理 `map₂_right_identity`

English:
lemma map₂_right_identity
  given: {f : α -> β -> α} {b : β} (h : forall a, f a b = a) (o : Option α)
  proof: by grind

中文:
引理 map₂_right_identity
  条件: {f : α -> β -> α} {b : β} (h : 对任意 a, f a b = a) (o : 选项类型 α)
  证明: by grind
-/
lemma map₂_right_identity {f : α -> β -> α} {b : β} (h : forall a, f a b = a) (o : Option α) :
    map₂ f o (some b) = o := by grind

end Option
