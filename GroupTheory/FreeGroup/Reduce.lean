/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Finset.Dedup
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.List.Sublists
public import Mathlib.GroupTheory.FreeGroup.Basic

/-!
# The maximal reduction of a word in a free group

## Main declarations

* `FreeGroup.reduce`: the maximal reduction of a word in a free group
* `FreeGroup.norm`: the length of the maximal reduction of a word in a free group

-/

@[expose] public section


namespace FreeGroup

variable {α : Type*}
variable {L L₁ L₂ L₃ L₄ : List (α × Bool)}

section Reduce

variable [DecidableEq α]

/-- The maximal reduction of a word. It is computable
iff `α` has decidable equality. -/
@[to_additive
/-- The maximal reduction of a word. It is computable iff `α` has decidable equality. -/]
/--
Definition of `reduce` / `reduce` 的定义

English:
definition reduce
  signature: : (L : List (α × Bool)) -> List (α × Bool)
  body: List.rec [] fun hd1 _tl1 ih =>
    List.casesOn ih [hd1] fun hd2 tl2 =>
      if hd1.1 = hd2.1 ∧ hd1.2 = not hd2.2 then tl2 else hd1 :: hd2 :: tl2

中文:
定义 reduce
  签名: : (L : 列表 (α × 布尔值)) -> 列表 (α × 布尔值)
  定义体: List.rec [] fun hd1 _tl1 ih =>
    List.casesOn ih [hd1] fun hd2 tl2 =>
      if hd1.1 = hd2.1 ∧ hd1.2 = not hd2.2 then tl2 else hd1 :: hd2 :: tl2

Depends on / 依赖: List.casesOn, List.rec, _tl1, casesOn
-/
def reduce : (L : List (α × Bool)) -> List (α × Bool) :=
  List.rec [] fun hd1 _tl1 ih =>
    List.casesOn ih [hd1] fun hd2 tl2 =>
      if hd1.1 = hd2.1 ∧ hd1.2 = not hd2.2 then tl2 else hd1 :: hd2 :: tl2

/--
lemma `reduce_nil` / 引理 `reduce_nil`

English:
lemma reduce_nil
  statement: reduce ([] : List (α × Bool)) = []
  proof: rfl

中文:
引理 reduce_nil
  结论: reduce ([] : 列表 (α × 布尔值)) = []
  证明: rfl
-/
@[to_additive (attr := simp)] lemma reduce_nil : reduce ([] : List (α × Bool)) = [] := rfl
/--
lemma `reduce_singleton` / 引理 `reduce_singleton`

English:
lemma reduce_singleton
  given: (s : α × Bool)
  statement: reduce [s] = [s]
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 reduce_singleton
  条件: (s : α × 布尔值)
  结论: reduce [s] = [s]
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive] lemma reduce_singleton (s : α × Bool) : reduce [s] = [s] := rfl

@[to_additive (attr := simp)]
/--
theorem `reduce.cons` / 定理 `reduce.cons`

English:
theorem reduce.cons
  given: (x)
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 reduce.cons
  条件: (x)
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem reduce.cons (x) :
    reduce (x :: L) =
      List.casesOn (reduce L) [x] fun hd tl =>
        if x.1 = hd.1 ∧ x.2 = not hd.2 then tl else x :: hd :: tl :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `reduce_replicate` / 定理 `reduce_replicate`

English:
theorem reduce_replicate
  given: (n : Nat) (x : α × Bool)
  proof: by
  induction n with
  | zero => simp [reduce]
  | succ n ih =>
    rw [List.replicate_succ]; rw [reduce.cons]; rw [ih]
    cases n with
    | zero => simp
    | succ n => simp [List.replicate_succ]

中文:
定理 reduce_replicate
  条件: (n : 自然数) (x : α × 布尔值)
  证明: by
  induction n with
  | zero => simp [reduce]
  | succ n ih =>
    rw [List.replicate_succ]; rw [reduce.cons]; rw [ih]
    cases n with
    | zero => simp
    | succ n => simp [List.replicate_succ]

Depends on / 依赖: List.replicate_succ, reduce.cons, replicate_succ
-/
theorem reduce_replicate (n : Nat) (x : α × Bool) :
    reduce (.replicate n x) = .replicate n x := by
  induction n with
  | zero => simp [reduce]
  | succ n ih =>
    rw [List.replicate_succ]; rw [reduce.cons]; rw [ih]
    cases n with
    | zero => simp
    | succ n => simp [List.replicate_succ]

/-- The first theorem that characterises the function `reduce`: a word reduces to its maximal
  reduction. -/
@[to_additive /-- The first theorem that characterises the function `reduce`: a word reduces to its
  maximal reduction. -/]
/--
theorem `reduce.red` / 定理 `reduce.red`

English:
theorem reduce.red
  statement: Red L (reduce L)
  proof: by
  induction L with
  | nil => constructor
  | cons hd1 tl1 ih =>
    dsimp
    revert ih
    generalize htl : reduce tl1 = TL
    intro ih
    cases TL with
    | nil => exact Red.cons_cons ih
    | cons hd2 tl2 =>
      dsimp only
      split_ifs with h
      · cases hd1
        cases hd2
      

中文:
定理 reduce.red
  结论: Red L (reduce L)
  证明: by
  induction L with
  | nil => constructor
  | cons hd1 tl1 ih =>
    dsimp
    revert ih
    generalize htl : reduce tl1 = TL
    intro ih
    cases TL with
    | nil => exact Red.cons_cons ih
    | cons hd2 tl2 =>
      dsimp only
      split_ifs with h
      · cases hd1
        cases hd2
      

Depends on / 依赖: Red.Step.cons_not_rev.to_red, Red.cons_cons, Red.trans, cons_cons, cons_not_rev, generalize, revert, split_ifs, to_red
-/
theorem reduce.red : Red L (reduce L) := by
  induction L with
  | nil => constructor
  | cons hd1 tl1 ih =>
    dsimp
    revert ih
    generalize htl : reduce tl1 = TL
    intro ih
    cases TL with
    | nil => exact Red.cons_cons ih
    | cons hd2 tl2 =>
      dsimp only
      split_ifs with h
      · cases hd1
        cases hd2
        cases h
        dsimp at *
        subst_vars
        apply Red.trans (Red.cons_cons ih)
        exact Red.Step.cons_not_rev.to_red
      · exact Red.cons_cons ih

@[to_additive]
/--
theorem `reduce.not` / 定理 `reduce.not`

English:
theorem reduce.not
  given: {p : Prop}
  proof: congr_arg List.length h
      grind
    | cons hd tail =>
      obtain ⟨y, c⟩ := hd
      dsimp only
      split_ifs with h <;> intro H
      · rw [H] at r
        exact @reduce.not _ L1 ((y, c) :: L2) L3 x' b' r
      rcases L2 with (_ | ⟨a, L2⟩)
      · injections; subst_vars
        simp at h
   

中文:
定理 reduce.not
  条件: {p : 命题}
  证明: congr_arg List.length h
      grind
    | cons hd tail =>
      obtain ⟨y, c⟩ := hd
      dsimp only
      split_ifs with h <;> intro H
      · rw [H] at r
        exact @reduce.not _ L1 ((y, c) :: L2) L3 x' b' r
      rcases L2 with (_ | ⟨a, L2⟩)
      · injections; subst_vars
        simp at h
   

Depends on / 依赖: List.length, congr_arg, length
-/
theorem reduce.not {p : Prop} :
    forall {L₁ L₂ L₃ : List (α × Bool)} {x b}, reduce L₁ = L₂ ++ (x, b) :: (x, !b) :: L₃ -> p
  | [], L2, L3, _, _ => fun h => by cases L2 <;> injections
  | (x, b) :: L1, L2, L3, x', b' => by
    dsimp
    cases r : reduce L1 with
    | nil =>
      dsimp; intro h
      exfalso
      have := congr_arg List.length h
      grind
    | cons hd tail =>
      obtain ⟨y, c⟩ := hd
      dsimp only
      split_ifs with h <;> intro H
      · rw [H] at r
        exact @reduce.not _ L1 ((y, c) :: L2) L3 x' b' r
      rcases L2 with (_ | ⟨a, L2⟩)
      · injections; subst_vars
        simp at h
      · refine @reduce.not _ L1 L2 L3 x' b' ?_
        rw [List.cons_append] at H
        injection H with _ H
        rw [r]; rw [H]

/-- The second theorem that characterises the function `reduce`: the maximal reduction of a word
only reduces to itself. -/
@[to_additive /-- The second theorem that characterises the function `reduce`: the maximal
  reduction of a word only reduces to itself. -/]
/--
theorem `reduce.min` / 定理 `reduce.min`

English:
theorem reduce.min
  given: (H : Red (reduce L₁) L₂)
  statement: reduce L₁ = L₂
  proof: by
  induction H with
  | refl => rfl
  | tail _ H1 H2 =>
    obtain ⟨L4, L5, x, b⟩ := H1
    exact reduce.not H2

中文:
定理 reduce.最小值
  条件: (H : Red (reduce L₁) L₂)
  结论: reduce L₁ = L₂
  证明: by
  induction H with
  | refl => rfl
  | tail _ H1 H2 =>
    obtain ⟨L4, L5, x, b⟩ := H1
    exact reduce.not H2

Depends on / 依赖: reduce.not
-/
theorem reduce.min (H : Red (reduce L₁) L₂) : reduce L₁ = L₂ := by
  induction H with
  | refl => rfl
  | tail _ H1 H2 =>
    obtain ⟨L4, L5, x, b⟩ := H1
    exact reduce.not H2

/-- `reduce` is idempotent, i.e. the maximal reduction of the maximal reduction of a word is the
  maximal reduction of the word. -/
@[to_additive (attr := simp) /-- `reduce` is idempotent, i.e. the maximal reduction of the maximal
  reduction of a word is the maximal reduction of the word. -/]
/--
theorem `reduce.idem` / 定理 `reduce.idem`

English:
theorem reduce.idem
  statement: reduce (reduce L) = reduce L
  proof: Eq.symm reduce.min reduce.red

@[to_additive]

中文:
定理 reduce.idem
  结论: reduce (reduce L) = reduce L
  证明: Eq.symm reduce.min reduce.red

@[to_additive]

Depends on / 依赖: Eq.symm, reduce.min, reduce.red
-/
theorem reduce.idem : reduce (reduce L) = reduce L :=
Eq.symm reduce.min reduce.red

@[to_additive]
/--
theorem `reduce.Step.eq` / 定理 `reduce.Step.eq`

English:
theorem reduce.Step.eq
  given: (H : Red.Step L₁ L₂)
  statement: reduce L₁ = reduce L₂
  proof: let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (reduce.red.head H)
  (reduce.min HR13).trans (reduce.min HR23).symm

中文:
定理 reduce.Step.eq
  条件: (H : Red.Step L₁ L₂)
  结论: reduce L₁ = reduce L₂
  证明: let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (reduce.red.head H)
  (reduce.min HR13).trans (reduce.min HR23).symm

Depends on / 依赖: Red.church_rosser, church_rosser, reduce.min, reduce.red, reduce.red.head
-/
theorem reduce.Step.eq (H : Red.Step L₁ L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (reduce.red.head H)
  (reduce.min HR13).trans (reduce.min HR23).symm

/-- If a word reduces to another word, then they have a common maximal reduction. -/
@[to_additive /-- If a word reduces to another word, then they have a common maximal reduction. -/]
/--
theorem `reduce.eq_of_red` / 定理 `reduce.eq_of_red`

English:
theorem reduce.eq_of_red
  given: (H : Red L₁ L₂)
  statement: reduce L₁ = reduce L₂
  proof: let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (Red.trans H reduce.red)
  (reduce.min HR13).trans (reduce.min HR23).symm

alias red.reduce_eq := reduce.eq_of_red

alias freeAddGroup.red.reduce_eq := FreeAddGroup.reduce.eq_of_red

@[to_additive]

中文:
定理 reduce.eq_of_red
  条件: (H : Red L₁ L₂)
  结论: reduce L₁ = reduce L₂
  证明: let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (Red.trans H reduce.red)
  (reduce.min HR13).trans (reduce.min HR23).symm

alias red.reduce_eq := reduce.eq_of_red

alias freeAddGroup.red.reduce_eq := FreeAddGroup.reduce.eq_of_red

@[to_additive]

Depends on / 依赖: Red.church_rosser, Red.trans, church_rosser, reduce.min, reduce.red
-/
theorem reduce.eq_of_red (H : Red L₁ L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, HR13, HR23⟩ := Red.church_rosser reduce.red (Red.trans H reduce.red)
  (reduce.min HR13).trans (reduce.min HR23).symm

alias red.reduce_eq := reduce.eq_of_red

alias freeAddGroup.red.reduce_eq := FreeAddGroup.reduce.eq_of_red

@[to_additive]
/--
theorem `Red.reduce_right` / 定理 `Red.reduce_right`

English:
theorem Red.reduce_right
  given: (h : Red L₁ L₂)
  statement: Red L₁ (reduce L₂)
  proof: reduce.eq_of_red h ▸ reduce.red

@[to_additive]

中文:
定理 Red.reduce_right
  条件: (h : Red L₁ L₂)
  结论: Red L₁ (reduce L₂)
  证明: reduce.eq_of_red h ▸ reduce.red

@[to_additive]

Depends on / 依赖: eq_of_red, reduce.eq_of_red, reduce.red
-/
theorem Red.reduce_right (h : Red L₁ L₂) : Red L₁ (reduce L₂) :=
  reduce.eq_of_red h ▸ reduce.red

@[to_additive]
/--
theorem `Red.reduce_left` / 定理 `Red.reduce_left`

English:
theorem Red.reduce_left
  given: (h : Red L₁ L₂)
  statement: Red L₂ (reduce L₁)
  proof: (reduce.eq_of_red h).symm ▸ reduce.red

中文:
定理 Red.reduce_left
  条件: (h : Red L₁ L₂)
  结论: Red L₂ (reduce L₁)
  证明: (reduce.eq_of_red h).symm ▸ reduce.red

Depends on / 依赖: eq_of_red, reduce.eq_of_red, reduce.red
-/
theorem Red.reduce_left (h : Red L₁ L₂) : Red L₂ (reduce L₁) :=
  (reduce.eq_of_red h).symm ▸ reduce.red

/-- If two words correspond to the same element in the free group, then they
have a common maximal reduction. This is the proof that the function that sends
an element of the free group to its maximal reduction is well-defined. -/
@[to_additive /-- If two words correspond to the same element in the additive free group, then they
  have a common maximal reduction. This is the proof that the function that sends an element of the
  free group to its maximal reduction is well-defined. -/]
/--
theorem `reduce.sound` / 定理 `reduce.sound`

English:
theorem reduce.sound
  given: (H : mk L₁ = mk L₂)
  statement: reduce L₁ = reduce L₂
  proof: let ⟨_L₃, H13, H23⟩ := Red.exact.1 H
  (reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

中文:
定理 reduce.sound
  条件: (H : mk L₁ = mk L₂)
  结论: reduce L₁ = reduce L₂
  证明: let ⟨_L₃, H13, H23⟩ := Red.exact.1 H
  (reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

Depends on / 依赖: Red.exact, eq_of_red, reduce.eq_of_red
-/
theorem reduce.sound (H : mk L₁ = mk L₂) : reduce L₁ = reduce L₂ :=
  let ⟨_L₃, H13, H23⟩ := Red.exact.1 H
  (reduce.eq_of_red H13).trans (reduce.eq_of_red H23).symm

/-- If two words have a common maximal reduction, then they correspond to the same element in the
  free group. -/
@[to_additive /-- If two words have a common maximal reduction, then they correspond to the same
  element in the additive free group. -/]
/--
theorem `reduce.exact` / 定理 `reduce.exact`

English:
theorem reduce.exact
  given: (H : reduce L₁ = reduce L₂)
  statement: mk L₁ = mk L₂
  proof: Red.exact.2 ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

中文:
定理 reduce.exact
  条件: (H : reduce L₁ = reduce L₂)
  结论: mk L₁ = mk L₂
  证明: Red.exact.2 ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

Depends on / 依赖: Red.exact, reduce.red
-/
theorem reduce.exact (H : reduce L₁ = reduce L₂) : mk L₁ = mk L₂ :=
  Red.exact.2 ⟨reduce L₂, H ▸ reduce.red, reduce.red⟩

/-- A word and its maximal reduction correspond to the same element of the free group. -/
@[to_additive /-- A word and its maximal reduction correspond to the same element of the additive
  free group. -/]
/--
theorem `reduce.self` / 定理 `reduce.self`

English:
theorem reduce.self
  statement: mk (reduce L) = mk L
  proof: reduce.exact reduce.idem

中文:
定理 reduce.self
  结论: mk (reduce L) = mk L
  证明: reduce.exact reduce.idem

Depends on / 依赖: reduce.exact, reduce.idem
-/
theorem reduce.self : mk (reduce L) = mk L :=
  reduce.exact reduce.idem

/-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`, then `w₂` reduces to the maximal reduction
  of `w₁`. -/
@[to_additive /-- If words `w₁ w₂` are such that `w₁` reduces to `w₂`, then `w₂` reduces to the
  maximal reduction of `w₁`. -/]
/--
theorem `reduce.rev` / 定理 `reduce.rev`

English:
theorem reduce.rev
  given: (H : Red L₁ L₂)
  statement: Red L₂ (reduce L₁)
  proof: (reduce.eq_of_red H).symm ▸ reduce.red

中文:
定理 reduce.rev
  条件: (H : Red L₁ L₂)
  结论: Red L₂ (reduce L₁)
  证明: (reduce.eq_of_red H).symm ▸ reduce.red

Depends on / 依赖: eq_of_red, reduce.eq_of_red, reduce.red
-/
theorem reduce.rev (H : Red L₁ L₂) : Red L₂ (reduce L₁) :=
  (reduce.eq_of_red H).symm ▸ reduce.red

/-- The function that sends an element of the free group to its maximal reduction. -/
@[to_additive /-- The function that sends an element of the additive free group to its maximal
  reduction. -/]
/--
Definition of `toWord` / `toWord` 的定义

English:
definition toWord
  signature: : FreeGroup α -> List (α × Bool)
  body: Quot.lift reduce fun _L₁ _L₂ H => reduce.Step.eq H

@[to_additive]

中文:
定义 toWord
  签名: : 自由群 α -> 列表 (α × 布尔值)
  定义体: Quot.lift reduce fun _L₁ _L₂ H => reduce.Step.eq H

@[to_additive]

Depends on / 依赖: Quot.lift, reduce.Step.eq
-/
def toWord : FreeGroup α -> List (α × Bool) :=
  Quot.lift reduce fun _L₁ _L₂ H => reduce.Step.eq H

@[to_additive]
/--
theorem `mk_toWord` / 定理 `mk_toWord`

English:
theorem mk_toWord
  statement: forall {x : FreeGroup α}, mk (toWord x) = x
  proof: by rintro ⟨L⟩; exact reduce.self

@[to_additive]

中文:
定理 mk_toWord
  结论: 对任意 {x : 自由群 α}, mk (toWord x) = x
  证明: by rintro ⟨L⟩; exact reduce.self

@[to_additive]

Depends on / 依赖: reduce.self
-/
theorem mk_toWord : forall {x : FreeGroup α}, mk (toWord x) = x := by rintro ⟨L⟩; exact reduce.self

@[to_additive]
/--
theorem `toWord_injective` / 定理 `toWord_injective`

English:
theorem toWord_injective
  statement: Function.Injective (toWord : FreeGroup α -> List (α × Bool))
  proof: by
  rintro ⟨L₁⟩ ⟨L₂⟩; exact reduce.exact

@[to_additive (attr := simp)]

中文:
定理 toWord_injective
  结论: 函数.单射 (toWord : 自由群 α -> 列表 (α × 布尔值))
  证明: by
  rintro ⟨L₁⟩ ⟨L₂⟩; exact reduce.exact

@[to_additive (attr := simp)]

Depends on / 依赖: reduce.exact
-/
theorem toWord_injective : Function.Injective (toWord : FreeGroup α -> List (α × Bool)) := by
  rintro ⟨L₁⟩ ⟨L₂⟩; exact reduce.exact

@[to_additive (attr := simp)]
/--
theorem `toWord_inj` / 定理 `toWord_inj`

English:
theorem toWord_inj
  given: {x y : FreeGroup α}
  statement: toWord x = toWord y ↔ x = y
  proof: toWord_injective.eq_iff

@[to_additive (attr := simp)]

中文:
定理 toWord_inj
  条件: {x y : 自由群 α}
  结论: toWord x = toWord y ↔ x = y
  证明: toWord_injective.eq_iff

@[to_additive (attr := simp)]

Depends on / 依赖: eq_iff, toWord_injective, toWord_injective.eq_iff
-/
theorem toWord_inj {x y : FreeGroup α} : toWord x = toWord y ↔ x = y :=
  toWord_injective.eq_iff

@[to_additive (attr := simp)]
/--
theorem `toWord_mk` / 定理 `toWord_mk`

English:
theorem toWord_mk
  statement: (mk L₁).toWord = reduce L₁
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toWord_mk
  结论: (mk L₁).toWord = reduce L₁
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toWord_mk : (mk L₁).toWord = reduce L₁ :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `toWord_of` / 定理 `toWord_of`

English:
theorem toWord_of
  given: (a : α)
  statement: (of a).toWord = [(a, true)]
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 toWord_of
  条件: (a : α)
  结论: (of a).toWord = [(a, true)]
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem toWord_of (a : α) : (of a).toWord = [(a, true)] :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `reduce_toWord` / 定理 `reduce_toWord`

English:
theorem reduce_toWord
  statement: forall x : FreeGroup α, reduce (toWord x) = toWord x
  proof: by
  rintro ⟨L⟩
  exact reduce.idem

@[to_additive (attr := simp)]

中文:
定理 reduce_toWord
  结论: 对任意 x : 自由群 α, reduce (toWord x) = toWord x
  证明: by
  rintro ⟨L⟩
  exact reduce.idem

@[to_additive (attr := simp)]

Depends on / 依赖: reduce.idem
-/
theorem reduce_toWord : forall x : FreeGroup α, reduce (toWord x) = toWord x := by
  rintro ⟨L⟩
  exact reduce.idem

@[to_additive (attr := simp)]
/--
theorem `toWord_one` / 定理 `toWord_one`

English:
theorem toWord_one
  statement: (1 : FreeGroup α).toWord = []
  proof: rfl

@[to_additive]

中文:
定理 toWord_one
  结论: (1 : 自由群 α).toWord = []
  证明: rfl

@[to_additive]
-/
theorem toWord_one : (1 : FreeGroup α).toWord = [] :=
  rfl

@[to_additive]
/--
theorem `toWord_mul` / 定理 `toWord_mul`

English:
theorem toWord_mul
  given: (x y : FreeGroup α)
  statement: toWord (x * y) = reduce (toWord x ++ toWord y)
  proof: by
  rw [← mk_toWord (x := x)]; rw [← mk_toWord (x := y)]
  simp

@[to_additive]

中文:
定理 toWord_mul
  条件: (x y : 自由群 α)
  结论: toWord (x * y) = reduce (toWord x ++ toWord y)
  证明: by
  rw [← mk_toWord (x := x)]; rw [← mk_toWord (x := y)]
  simp

@[to_additive]

Depends on / 依赖: mk_toWord
-/
theorem toWord_mul (x y : FreeGroup α) : toWord (x * y) = reduce (toWord x ++ toWord y) := by
  rw [← mk_toWord (x := x)]; rw [← mk_toWord (x := y)]
  simp

@[to_additive]
/--
theorem `toWord_pow` / 定理 `toWord_pow`

English:
theorem toWord_pow
  given: (x : FreeGroup α) (n : Nat)
  proof: by
  rw [← mk_toWord (x := x)]
  simp

@[to_additive (attr := simp)]

中文:
定理 toWord_pow
  条件: (x : 自由群 α) (n : 自然数)
  证明: by
  rw [← mk_toWord (x := x)]
  simp

@[to_additive (attr := simp)]

Depends on / 依赖: mk_toWord
-/
theorem toWord_pow (x : FreeGroup α) (n : Nat) :
    toWord (x ^ n) = reduce (List.replicate n x.toWord).flatten := by
  rw [← mk_toWord (x := x)]
  simp

@[to_additive (attr := simp)]
/--
theorem `toWord_of_pow` / 定理 `toWord_of_pow`

English:
theorem toWord_of_pow
  given: (a : α) (n : Nat)
  statement: (of a ^ n).toWord = List.replicate n (a, true)
  proof: by
  rw [of]; rw [pow_mk]; rw [List.flatten_replicate_singleton]; rw [toWord]
  exact reduce_replicate _ _

@[to_additive (attr := simp)]

中文:
定理 toWord_of_pow
  条件: (a : α) (n : 自然数)
  结论: (of a ^ n).toWord = 列表.replicate n (a, true)
  证明: by
  rw [of]; rw [pow_mk]; rw [List.flatten_replicate_singleton]; rw [toWord]
  exact reduce_replicate _ _

@[to_additive (attr := simp)]

Depends on / 依赖: List.flatten_replicate_singleton, flatten_replicate_singleton, pow_mk, reduce_replicate, toWord
-/
theorem toWord_of_pow (a : α) (n : Nat) : (of a ^ n).toWord = List.replicate n (a, true) := by
  rw [of]; rw [pow_mk]; rw [List.flatten_replicate_singleton]; rw [toWord]
  exact reduce_replicate _ _

@[to_additive (attr := simp)]
/--
theorem `toWord_eq_nil_iff` / 定理 `toWord_eq_nil_iff`

English:
theorem toWord_eq_nil_iff
  given: {x : FreeGroup α}
  statement: x.toWord = [] ↔ x = 1
  proof: toWord_injective.eq_iff' toWord_one

@[to_additive]

中文:
定理 toWord_eq_nil_iff
  条件: {x : 自由群 α}
  结论: x.toWord = [] ↔ x = 1
  证明: toWord_injective.eq_iff' toWord_one

@[to_additive]

Depends on / 依赖: eq_iff, toWord_injective, toWord_injective.eq_iff, toWord_one
-/
theorem toWord_eq_nil_iff {x : FreeGroup α} : x.toWord = [] ↔ x = 1 :=
  toWord_injective.eq_iff' toWord_one

@[to_additive]
/--
theorem `reduce_invRev` / 定理 `reduce_invRev`

English:
theorem reduce_invRev
  given: {w : List (α × Bool)}
  statement: reduce (invRev w) = invRev (reduce w)
  proof: by
  apply reduce.min
  rw [← red_invRev_iff]; rw [invRev_invRev]
  apply Red.reduce_left
  have : Red (invRev (invRev w)) (invRev (reduce (invRev w))) := reduce.red.invRev
  rwa [invRev_invRev] at this

@[to_additive (attr := simp)]

中文:
定理 reduce_invRev
  条件: {w : 列表 (α × 布尔值)}
  结论: reduce (invRev w) = invRev (reduce w)
  证明: by
  apply reduce.min
  rw [← red_invRev_iff]; rw [invRev_invRev]
  apply Red.reduce_left
  have : Red (invRev (invRev w)) (invRev (reduce (invRev w))) := reduce.red.invRev
  rwa [invRev_invRev] at this

@[to_additive (attr := simp)]

Depends on / 依赖: Red.reduce_left, invRev, invRev_invRev, red_invRev_iff, reduce.min, reduce.red.invRev, reduce_left
-/
theorem reduce_invRev {w : List (α × Bool)} : reduce (invRev w) = invRev (reduce w) := by
  apply reduce.min
  rw [← red_invRev_iff]; rw [invRev_invRev]
  apply Red.reduce_left
  have : Red (invRev (invRev w)) (invRev (reduce (invRev w))) := reduce.red.invRev
  rwa [invRev_invRev] at this

@[to_additive (attr := simp)]
/--
theorem `toWord_inv` / 定理 `toWord_inv`

English:
theorem toWord_inv
  given: (x : FreeGroup α)
  statement: x⁻¹.toWord = invRev x.toWord
  proof: by
  rcases x with ⟨L⟩
  rw [quot_mk_eq_mk]; rw [inv_mk]; rw [toWord_mk]; rw [toWord_mk]; rw [reduce_invRev]

@[to_additive]

中文:
定理 toWord_inv
  条件: (x : 自由群 α)
  结论: x⁻¹.toWord = invRev x.toWord
  证明: by
  rcases x with ⟨L⟩
  rw [quot_mk_eq_mk]; rw [inv_mk]; rw [toWord_mk]; rw [toWord_mk]; rw [reduce_invRev]

@[to_additive]

Depends on / 依赖: inv_mk, quot_mk_eq_mk, reduce_invRev, toWord_mk
-/
theorem toWord_inv (x : FreeGroup α) : x⁻¹.toWord = invRev x.toWord := by
  rcases x with ⟨L⟩
  rw [quot_mk_eq_mk]; rw [inv_mk]; rw [toWord_mk]; rw [toWord_mk]; rw [reduce_invRev]

@[to_additive]
/--
theorem `reduce_append_reduce_reduce` / 定理 `reduce_append_reduce_reduce`

English:
theorem reduce_append_reduce_reduce
  statement: reduce (reduce L₁ ++ reduce L₂) = reduce (L₁ ++ L₂)
  proof: by
  rw [← toWord_mk (L₁ := L₁ ++ L₂)]; rw [← mul_mk]; rw [toWord_mul]; rw [toWord_mk]; rw [toWord_mk]

@[to_additive]

中文:
定理 reduce_append_reduce_reduce
  结论: reduce (reduce L₁ ++ reduce L₂) = reduce (L₁ ++ L₂)
  证明: by
  rw [← toWord_mk (L₁ := L₁ ++ L₂)]; rw [← mul_mk]; rw [toWord_mul]; rw [toWord_mk]; rw [toWord_mk]

@[to_additive]

Depends on / 依赖: mul_mk, toWord_mk, toWord_mul
-/
theorem reduce_append_reduce_reduce : reduce (reduce L₁ ++ reduce L₂) = reduce (L₁ ++ L₂) := by
  rw [← toWord_mk (L₁ := L₁ ++ L₂)]; rw [← mul_mk]; rw [toWord_mul]; rw [toWord_mk]; rw [toWord_mk]

@[to_additive]
/--
theorem `reduce_cons_reduce` / 定理 `reduce_cons_reduce`

English:
theorem reduce_cons_reduce
  given: (a : α × Bool)
  statement: reduce (a :: reduce L) = reduce (a :: L)
  proof: by
  simp

@[to_additive]

中文:
定理 reduce_cons_reduce
  条件: (a : α × 布尔值)
  结论: reduce (a :: reduce L) = reduce (a :: L)
  证明: by
  simp

@[to_additive]
-/
theorem reduce_cons_reduce (a : α × Bool) : reduce (a :: reduce L) = reduce (a :: L) := by
  simp

@[to_additive]
/--
theorem `reduce_invRev_left_cancel` / 定理 `reduce_invRev_left_cancel`

English:
theorem reduce_invRev_left_cancel
  statement: reduce (invRev L ++ L) = []
  proof: by
  simp [← toWord_mk, ← mul_mk, ← inv_mk]

中文:
定理 reduce_invRev_left_cancel
  结论: reduce (invRev L ++ L) = []
  证明: by
  simp [← toWord_mk, ← mul_mk, ← inv_mk]

Depends on / 依赖: inv_mk, mul_mk, toWord_mk
-/
theorem reduce_invRev_left_cancel : reduce (invRev L ++ L) = [] := by
  simp [← toWord_mk, ← mul_mk, ← inv_mk]

open List -- for <+ notation

@[to_additive]
/--
lemma `toWord_mul_sublist` / 引理 `toWord_mul_sublist`

English:
lemma toWord_mul_sublist
  given: (x y : FreeGroup α)
  statement: (x * y).toWord <+ x.toWord ++ y.toWord
  proof: by
  refine Red.sublist ?_
  have : x * y = FreeGroup.mk (x.toWord ++ y.toWord) := by
    rw [← FreeGroup.mul_mk]; rw [FreeGroup.mk_toWord]; rw [FreeGroup.mk_toWord]
  rw [this]
  exact FreeGroup.reduce.red

中文:
引理 toWord_mul_sublist
  条件: (x y : 自由群 α)
  结论: (x * y).toWord <+ x.toWord ++ y.toWord
  证明: by
  refine Red.sublist ?_
  have : x * y = FreeGroup.mk (x.toWord ++ y.toWord) := by
    rw [← FreeGroup.mul_mk]; rw [FreeGroup.mk_toWord]; rw [FreeGroup.mk_toWord]
  rw [this]
  exact FreeGroup.reduce.red

Depends on / 依赖: FreeGroup, FreeGroup.mk, FreeGroup.mk_toWord, FreeGroup.mul_mk, FreeGroup.reduce.red, Red.sublist, mk_toWord, mul_mk, sublist, toWord, x.toWord, y.toWord
-/
lemma toWord_mul_sublist (x y : FreeGroup α) : (x * y).toWord <+ x.toWord ++ y.toWord := by
  refine Red.sublist ?_
  have : x * y = FreeGroup.mk (x.toWord ++ y.toWord) := by
    rw [← FreeGroup.mul_mk]; rw [FreeGroup.mk_toWord]; rw [FreeGroup.mk_toWord]
  rw [this]
  exact FreeGroup.reduce.red

/-- **Constructive Church-Rosser theorem** (compare `FreeGroup.Red.church_rosser`). -/
@[to_additive
/-- **Constructive Church-Rosser theorem** (compare `FreeAddGroup.Red.church_rosser`). -/]
/--
Definition of `reduce.churchRosser` / `reduce.churchRosser` 的定义

English:
definition reduce.churchRosser
  signature: (H12 : Red L₁ L₂) (H13 : Red L₁ L₃)
  body: ⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

@[to_additive]

中文:
定义 reduce.churchRosser
  签名: (H12 : Red L₁ L₂) (H13 : Red L₁ L₃)
  定义体: ⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

@[to_additive]

Depends on / 依赖: reduce.rev
-/
def reduce.churchRosser (H12 : Red L₁ L₂) (H13 : Red L₁ L₃) : { L₄ // Red L₂ L₄ ∧ Red L₃ L₄ } :=
  ⟨reduce L₁, reduce.rev H12, reduce.rev H13⟩

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (FreeGroup α)
  body: toWord_injective.decidableEq

中文:
实例 :
  签名: DecidableEq (自由群 α)
  定义体: toWord_injective.decidableEq

Depends on / 依赖: decidableEq, toWord_injective, toWord_injective.decidableEq
-/
instance : DecidableEq (FreeGroup α) :=
  toWord_injective.decidableEq

-- TODO @[to_additive] doesn't succeed, possibly due to a bug
-- FreeGroup.Red.decidableRel and FreeAddGroup.Red.decidableRel do not generate the same number
-- of equation lemmas.
/--
Instance `Red.decidableRel` / 实例 `Red.decidableRel`

English:
instance Red.decidableRel
  signature: : DecidableRel (@Red α)

中文:
实例 Red.decidableRel
  签名: : DecidableRel (@Red α)
-/
instance Red.decidableRel : DecidableRel (@Red α)
  | [], [] => isTrue Red.refl
  | [], _hd2 :: _tl2 => isFalse fun H => List.noConfusion rfl (heq_of_eq (Red.nil_iff.1 H))
  | (x, b) :: tl, [] =>
    match Red.decidableRel tl [(x, not b)] with
| isTrue H => isTrue Red.trans (Red.cons_cons H) (@Red.Step.not _ [] [] _ _).to_red
| isFalse H => isFalse fun H2 => H Red.cons_nil_iff_singleton.1 H2
  | (x1, b1) :: tl1, (x2, b2) :: tl2 =>
    if h : (x1, b1) = (x2, b2) then
      match Red.decidableRel tl1 tl2 with
| isTrue H => isTrue h ▸ Red.cons_cons H
| isFalse H => isFalse fun H2 => H (Red.cons_cons_iff _).1 h.symm ▸ H2
    else
      match Red.decidableRel tl1 ((x1, ! b1) :: (x2, b2) :: tl2) with
| isTrue H => isTrue (Red.cons_cons H).tail Red.Step.cons_not
| isFalse H => isFalse fun H2 => H Red.inv_of_red_of_ne h H2

/--
Definition of `Red.enum` / `Red.enum` 的定义

English:
definition Red.enum
  signature: (L₁ : List (α × Bool))
  body: List.filter (Red L₁) (List.sublists L₁)

中文:
定义 Red.enum
  签名: (L₁ : 列表 (α × 布尔值))
  定义体: List.filter (Red L₁) (List.sublists L₁)

Depends on / 依赖: List.filter, List.sublists, filter, sublists
-/
def Red.enum (L₁ : List (α × Bool)) : List (List (α × Bool)) :=
  List.filter (Red L₁) (List.sublists L₁)

/--
theorem `Red.enum.sound` / 定理 `Red.enum.sound`

English:
theorem Red.enum.sound
  given: (H : L₂ in List.filter (Red L₁) (List.sublists L₁))
  statement: Red L₁ L₂
  proof: of_decide_eq_true (@List.of_mem_filter _ _ L₂ _ H)

中文:
定理 Red.enum.sound
  条件: (H : L₂ in 列表.filter (Red L₁) (列表.sublists L₁))
  结论: Red L₁ L₂
  证明: of_decide_eq_true (@List.of_mem_filter _ _ L₂ _ H)

Depends on / 依赖: List.of_mem_filter, of_decide_eq_true, of_mem_filter
-/
theorem Red.enum.sound (H : L₂ in List.filter (Red L₁) (List.sublists L₁)) : Red L₁ L₂ :=
  of_decide_eq_true (@List.of_mem_filter _ _ L₂ _ H)

/--
theorem `Red.enum.complete` / 定理 `Red.enum.complete`

English:
theorem Red.enum.complete
  given: (H : Red L₁ L₂)
  statement: L₂ in Red.enum L₁
  proof: List.mem_filter_of_mem (List.mem_sublists.2 <| Red.sublist H) (decide_eq_true H)

中文:
定理 Red.enum.complete
  条件: (H : Red L₁ L₂)
  结论: L₂ in Red.enum L₁
  证明: List.mem_filter_of_mem (List.mem_sublists.2 <| Red.sublist H) (decide_eq_true H)

Depends on / 依赖: List.mem_filter_of_mem, List.mem_sublists, Red.sublist, decide_eq_true, mem_filter_of_mem, mem_sublists, sublist
-/
theorem Red.enum.complete (H : Red L₁ L₂) : L₂ in Red.enum L₁ :=
  List.mem_filter_of_mem (List.mem_sublists.2 <| Red.sublist H) (decide_eq_true H)

instance (L₁ : List (α × Bool)) : Fintype { L₂ // Red L₁ L₂ } :=
  Fintype.subtype (List.toFinset <| Red.enum L₁) fun _L₂ =>
⟨fun H => Red.enum.sound List.mem_toFinset.1 H, fun H =>
List.mem_toFinset.2 Red.enum.complete H⟩

@[to_additive]
/--
theorem `IsReduced.reduce_eq` / 定理 `IsReduced.reduce_eq`

English:
theorem IsReduced.reduce_eq
  given: (h : IsReduced L)
  statement: reduce L = L
  proof: by
  rw [← h.red_iff_eq]
  exact reduce.red

@[to_additive]

中文:
定理 是既约.reduce_eq
  条件: (h : 是既约 L)
  结论: reduce L = L
  证明: by
  rw [← h.red_iff_eq]
  exact reduce.red

@[to_additive]

Depends on / 依赖: h.red_iff_eq, red_iff_eq, reduce.red
-/
theorem IsReduced.reduce_eq (h : IsReduced L) : reduce L = L := by
  rw [← h.red_iff_eq]
  exact reduce.red

@[to_additive]
/--
theorem `IsReduced.of_reduce_eq` / 定理 `IsReduced.of_reduce_eq`

English:
theorem IsReduced.of_reduce_eq
  given: (h : reduce L = L)
  statement: IsReduced L
  proof: by
  rw [IsReduced]; rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl rfl
  rw [eq_comm]; rw [← Bool.ne_not]
  rintro rfl
  exact reduce.not (h.trans hl)

@[to_additive]

中文:
定理 是既约.of_reduce_eq
  条件: (h : reduce L = L)
  结论: 是既约 L
  证明: by
  rw [IsReduced]; rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl rfl
  rw [eq_comm]; rw [← Bool.ne_not]
  rintro rfl
  exact reduce.not (h.trans hl)

@[to_additive]

Depends on / 依赖: Bool.ne_not, IsReduced, List.isChain_iff_forall_rel_of_append_cons_cons, eq_comm, h.trans, isChain_iff_forall_rel_of_append_cons_cons, ne_not, reduce.not
-/
theorem IsReduced.of_reduce_eq (h : reduce L = L) : IsReduced L := by
  rw [IsReduced]; rw [List.isChain_iff_forall_rel_of_append_cons_cons]
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ l₁ l₂ hl rfl
  rw [eq_comm]; rw [← Bool.ne_not]
  rintro rfl
  exact reduce.not (h.trans hl)

@[to_additive]
/--
theorem `isReduced_iff_reduce_eq` / 定理 `isReduced_iff_reduce_eq`

English:
theorem isReduced_iff_reduce_eq
  statement: IsReduced L ↔ reduce L = L where
  proof: h.reduce_eq
  mpr := .of_reduce_eq

@[to_additive]

中文:
定理 isReduced_iff_reduce_eq
  结论: 是既约 L ↔ reduce L = L where
  证明: h.reduce_eq
  mpr := .of_reduce_eq

@[to_additive]

Depends on / 依赖: h.reduce_eq, reduce_eq
-/
theorem isReduced_iff_reduce_eq : IsReduced L ↔ reduce L = L where
  mp h := h.reduce_eq
  mpr := .of_reduce_eq

@[to_additive]
/--
theorem `isReduced_toWord` / 定理 `isReduced_toWord`

English:
theorem isReduced_toWord
  given: {x : FreeGroup α}
  statement: IsReduced x.toWord
  proof: by
  simp [isReduced_iff_reduce_eq]

中文:
定理 isReduced_toWord
  条件: {x : 自由群 α}
  结论: 是既约 x.toWord
  证明: by
  simp [isReduced_iff_reduce_eq]

Depends on / 依赖: isReduced_iff_reduce_eq
-/
theorem isReduced_toWord {x : FreeGroup α} : IsReduced x.toWord := by
  simp [isReduced_iff_reduce_eq]

end Reduce

@[to_additive (attr := simp)]
/--
theorem `one_ne_of` / 定理 `one_ne_of`

English:
theorem one_ne_of
  given: (a : α)
  statement: 1 != of a
  proof: letI := Classical.decEq α; ne_of_apply_ne toWord by simp

@[to_additive (attr := simp)]
.symm theorem of_ne_one (a : α) : of a != 1 := one_ne_of _

@[to_additive]

中文:
定理 one_ne_of
  条件: (a : α)
  结论: 1 != of a
  证明: letI := Classical.decEq α; ne_of_apply_ne toWord by simp

@[to_additive (attr := simp)]
.symm theorem of_ne_one (a : α) : of a != 1 := one_ne_of _

@[to_additive]

Depends on / 依赖: Classical, Classical.decEq, ne_of_apply_ne, toWord
-/
theorem one_ne_of (a : α) : 1 != of a :=
letI := Classical.decEq α; ne_of_apply_ne toWord by simp

@[to_additive (attr := simp)]
.symm theorem of_ne_one (a : α) : of a != 1 := one_ne_of _

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nontrivial (FreeGroup α) where
  body: let ⟨x⟩ := ‹Nonempty α›; ⟨1, of x, one_ne_of x⟩

中文:
实例 [非空
  签名: α] : 非平凡 (自由群 α) where
  定义体: let ⟨x⟩ := ‹Nonempty α›; ⟨1, of x, one_ne_of x⟩

Depends on / 依赖: Nonempty, one_ne_of
-/
instance [Nonempty α] : Nontrivial (FreeGroup α) where
  exists_pair_ne := let ⟨x⟩ := ‹Nonempty α›; ⟨1, of x, one_ne_of x⟩

section Metric

variable [DecidableEq α]

/-- The length of reduced words provides a norm on a free group. -/
@[to_additive /-- The length of reduced words provides a norm on an additive free group. -/]
/--
Definition of `norm` / `norm` 的定义

English:
definition norm
  signature: (x : FreeGroup α)
  body: x.toWord.length

@[to_additive (attr := simp)]

中文:
定义 norm
  签名: (x : 自由群 α)
  定义体: x.toWord.length

@[to_additive (attr := simp)]

Depends on / 依赖: length, toWord, x.toWord.length
-/
def norm (x : FreeGroup α) : Nat :=
  x.toWord.length

@[to_additive (attr := simp)]
/--
theorem `norm_inv_eq` / 定理 `norm_inv_eq`

English:
theorem norm_inv_eq
  given: {x : FreeGroup α}
  statement: norm x⁻¹ = norm x
  proof: by
  simp only [norm, toWord_inv, invRev_length]

@[to_additive (attr := simp)]

中文:
定理 norm_inv_eq
  条件: {x : 自由群 α}
  结论: norm x⁻¹ = norm x
  证明: by
  simp only [norm, toWord_inv, invRev_length]

@[to_additive (attr := simp)]

Depends on / 依赖: invRev_length, toWord_inv
-/
theorem norm_inv_eq {x : FreeGroup α} : norm x⁻¹ = norm x := by
  simp only [norm, toWord_inv, invRev_length]

@[to_additive (attr := simp)]
/--
theorem `norm_eq_zero` / 定理 `norm_eq_zero`

English:
theorem norm_eq_zero
  given: {x : FreeGroup α}
  statement: norm x = 0 ↔ x = 1
  proof: by
  simp only [norm, List.length_eq_zero_iff, toWord_eq_nil_iff]

@[to_additive (attr := simp)]

中文:
定理 norm_eq_zero
  条件: {x : 自由群 α}
  结论: norm x = 0 ↔ x = 1
  证明: by
  simp only [norm, List.length_eq_zero_iff, toWord_eq_nil_iff]

@[to_additive (attr := simp)]

Depends on / 依赖: List.length_eq_zero_iff, length_eq_zero_iff, toWord_eq_nil_iff
-/
theorem norm_eq_zero {x : FreeGroup α} : norm x = 0 ↔ x = 1 := by
  simp only [norm, List.length_eq_zero_iff, toWord_eq_nil_iff]

@[to_additive (attr := simp)]
/--
theorem `norm_one` / 定理 `norm_one`

English:
theorem norm_one
  statement: norm (1 : FreeGroup α) = 0
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 norm_one
  结论: norm (1 : 自由群 α) = 0
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem norm_one : norm (1 : FreeGroup α) = 0 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `norm_of` / 定理 `norm_of`

English:
theorem norm_of
  given: (a : α)
  statement: norm (of a) = 1
  proof: rfl

@[to_additive]

中文:
定理 norm_of
  条件: (a : α)
  结论: norm (of a) = 1
  证明: rfl

@[to_additive]
-/
theorem norm_of (a : α) : norm (of a) = 1 :=
  rfl

@[to_additive]
/--
theorem `norm_mk_le` / 定理 `norm_mk_le`

English:
theorem norm_mk_le
  statement: norm (mk L₁) <= L₁.length
  proof: reduce.red.length_le

@[to_additive]

中文:
定理 norm_mk_le
  结论: norm (mk L₁) <= L₁.length
  证明: reduce.red.length_le

@[to_additive]

Depends on / 依赖: length_le, reduce.red.length_le
-/
theorem norm_mk_le : norm (mk L₁) <= L₁.length :=
  reduce.red.length_le

@[to_additive]
/--
theorem `norm_mul_le` / 定理 `norm_mul_le`

English:
theorem norm_mul_le
  given: (x y : FreeGroup α)
  statement: norm (x * y) <= norm x + norm y
  proof: calc
    norm (x * y) = norm (mk (x.toWord ++ y.toWord)) := by rw [← mul_mk, mk_toWord, mk_toWord]
    _ <= (x.toWord ++ y.toWord).length := norm_mk_le
    _ = norm x + norm y := List.length_append

@[to_additive (attr := simp)]

中文:
定理 norm_mul_le
  条件: (x y : 自由群 α)
  结论: norm (x * y) <= norm x + norm y
  证明: calc
    norm (x * y) = norm (mk (x.toWord ++ y.toWord)) := by rw [← mul_mk, mk_toWord, mk_toWord]
    _ <= (x.toWord ++ y.toWord).length := norm_mk_le
    _ = norm x + norm y := List.length_append

@[to_additive (attr := simp)]

Depends on / 依赖: List.length_append, length, length_append, mk_toWord, mul_mk, norm_mk_le, toWord, x.toWord, y.toWord
-/
theorem norm_mul_le (x y : FreeGroup α) : norm (x * y) <= norm x + norm y :=
  calc
    norm (x * y) = norm (mk (x.toWord ++ y.toWord)) := by rw [← mul_mk, mk_toWord, mk_toWord]
    _ <= (x.toWord ++ y.toWord).length := norm_mk_le
    _ = norm x + norm y := List.length_append

@[to_additive (attr := simp)]
/--
theorem `norm_of_pow` / 定理 `norm_of_pow`

English:
theorem norm_of_pow
  given: (a : α) (n : Nat)
  statement: norm (of a ^ n) = n
  proof: by
  rw [norm]; rw [toWord_of_pow]; rw [List.length_replicate]

@[to_additive]

中文:
定理 norm_of_pow
  条件: (a : α) (n : 自然数)
  结论: norm (of a ^ n) = n
  证明: by
  rw [norm]; rw [toWord_of_pow]; rw [List.length_replicate]

@[to_additive]

Depends on / 依赖: List.length_replicate, length_replicate, toWord_of_pow
-/
theorem norm_of_pow (a : α) (n : Nat) : norm (of a ^ n) = n := by
  rw [norm]; rw [toWord_of_pow]; rw [List.length_replicate]

@[to_additive]
/--
theorem `norm_surjective` / 定理 `norm_surjective`

English:
theorem norm_surjective
  given: [Nonempty α]
  statement: Function.Surjective (norm (α := α))
  proof: by
  let ⟨a⟩ := ‹Nonempty α›
exact Function.RightInverse.surjective norm_of_pow a

中文:
定理 norm_surjective
  条件: [非空 α]
  结论: 函数.满射 (norm (α := α))
  证明: by
  let ⟨a⟩ := ‹Nonempty α›
exact Function.RightInverse.surjective norm_of_pow a

Depends on / 依赖: Function, Function.RightInverse.surjective, Nonempty, RightInverse, norm_of_pow, surjective
-/
theorem norm_surjective [Nonempty α] : Function.Surjective (norm (α := α)) := by
  let ⟨a⟩ := ‹Nonempty α›
exact Function.RightInverse.surjective norm_of_pow a

end Metric

end FreeGroup
