/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Logic.Relation
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.ToDual

/-!
# Shapes of homological complexes

We define a structure `ComplexShape ι` for describing the shapes of homological complexes
indexed by a type `ι`.
This is intended to capture chain complexes and cochain complexes, indexed by either `ℕ` or `ℤ`,
as well as more exotic examples.

Rather than insisting that the indexing type has a `succ` function
specifying where differentials should go,
inside `c : ComplexShape` we have `c.Rel : ι → ι → Prop`,
and when we define `HomologicalComplex`
we only allow nonzero differentials `d i j` from `i` to `j` if `c.Rel i j`.
Further, we require that `{ j // c.Rel i j }` and `{ i // c.Rel i j }` are subsingletons.
This means that the shape consists of some union of lines, rays, intervals, and circles.

Convenience functions `c.next` and `c.prev` provide these related elements
when they exist, and return their input otherwise.

This design aims to avoid certain problems arising from dependent type theory.
In particular we never have to ensure morphisms `d i : X i ⟶ X (succ i)` compose as
expected (which would often require rewriting by equations in the indexing type).
Instead such identities become separate proof obligations when verifying that a
complex we've constructed is of the desired shape.

If `α` is an `AddRightCancelSemigroup`, then we define `up α : ComplexShape α`,
the shape appropriate for cohomology, so `d : X i ⟶ X j` is nonzero only when `j = i + 1`,
as well as `down α : ComplexShape α`, appropriate for homology,
so `d : X i ⟶ X j` is nonzero only when `i = j + 1`.
(Later we'll introduce `CochainComplex` and `ChainComplex` as abbreviations for
`HomologicalComplex` with one of these shapes baked in.)
-/

@[expose] public section

noncomputable section

/-- A `c : ComplexShape ι` describes the shape of a chain complex,
with chain groups indexed by `ι`.
Typically `ι` will be `ℕ`, `ℤ`, or `Fin n`.

There is a relation `Rel : ι → ι → Prop`,
and we will only allow a non-zero differential from `i` to `j` when `Rel i j`.

There are axioms which imply `{ j // c.Rel i j }` and `{ i // c.Rel i j }` are subsingletons.
This means that the shape consists of some union of lines, rays, intervals, and circles.

Below we define `c.next` and `c.prev` which provide these related elements.
-/
@[ext]
/--
Definition of `ComplexShape` / `ComplexShape` 的定义

English:
structure ComplexShape
  parameters: (ι : Type*)
  axioms and operations (3):
    - Rel : ι -> ι -> Prop
    - next_eq : forall {i j j'}, Rel i j -> Rel i j' -> j = j'
    - prev_eq : forall {i i' j}, Rel i j -> Rel i' j -> i = i'

中文:
结构 余mplexShape
  参数: (ι : 类型)
  公理与运算 (3 个):
    - Rel : ι -> ι -> 命题
    - next_eq : 对任意 {i j j'}, 关系 i j -> 关系 i j' -> j = j'
    - prev_eq : 对任意 {i i' j}, 关系 i j -> 关系 i' j -> i = i'

Depends on / 依赖: ComplexShape, ComplexShape.Rel
-/
structure ComplexShape (ι : Type*) where
  /-- Nonzero differentials `X i ⟶ X j` shall be allowed
  on homological complexes when `Rel i j` holds. -/
  Rel : ι -> ι -> Prop
  /-- There is at most one nonzero differential from `X i`. -/
  next_eq : forall {i j j'}, Rel i j -> Rel i j' -> j = j'
  /-- There is at most one nonzero differential to `X j`. -/
  prev_eq : forall {i i' j}, Rel i j -> Rel i' j -> i = i'

attribute [to_dual self (reorder := 3 4)] ComplexShape.Rel
attribute [to_dual existing] ComplexShape.next_eq

namespace ComplexShape

variable {ι : Type*}

/-- The complex shape where only differentials from each `X.i` to itself are allowed.

This is mostly only useful so we can describe the relation of "related in `k` steps" below.
-/
@[simps]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (ι : Type*)
  body: i = j
  next_eq w w' := w.symm.trans w'
  prev_eq w w' := w.trans w'.symm

中文:
定义 refl
  签名: (ι : 类型)
  定义体: i = j
  next_eq w w' := w.symm.trans w'
  prev_eq w w' := w.trans w'.symm
-/
def refl (ι : Type*) : ComplexShape ι where
  Rel i j := i = j
  next_eq w w' := w.symm.trans w'
  prev_eq w w' := w.trans w'.symm

/-- The reverse of a `ComplexShape`.
-/
@[simps, implicit_reducible]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (c : ComplexShape ι)
  body: c.Rel j i
  next_eq w w' := c.prev_eq w w'
  prev_eq w w' := c.next_eq w w'

中文:
定义 symm
  签名: (c : 余mplexShape ι)
  定义体: c.Rel j i
  next_eq w w' := c.prev_eq w w'
  prev_eq w w' := c.next_eq w w'

Depends on / 依赖: c.Rel
-/
def symm (c : ComplexShape ι) : ComplexShape ι where
  Rel i j := c.Rel j i
  next_eq w w' := c.prev_eq w w'
  prev_eq w w' := c.next_eq w w'

/-- If `c : ComplexShape α` is such that `c.Rel` is decidable, it is also the
case of `c.symm.Rel`. -/
@[instance_reducible]
/--
Definition of `decidableRelSymm` / `decidableRelSymm` 的定义

English:
definition decidableRelSymm
  signature: {α : Type*} (c : ComplexShape α) [DecidableRel c.Rel]
  body: fun a b => decidable_of_iff (c.Rel b a) Iff.rfl

@[simp]

中文:
定义 decidableRelSymm
  签名: {α : 类型} (c : 余mplexShape α) [DecidableRel c.关系]
  定义体: fun a b => decidable_of_iff (c.Rel b a) Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, c.Rel, decidable_of_iff
-/
def decidableRelSymm {α : Type*} (c : ComplexShape α) [DecidableRel c.Rel] :
    DecidableRel c.symm.Rel :=
  fun a b => decidable_of_iff (c.Rel b a) Iff.rfl

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (c : ComplexShape ι)
  statement: c.symm.symm = c
  proof: rfl

中文:
定理 symm_symm
  条件: (c : 余mplexShape ι)
  结论: c.symm.symm = c
  证明: rfl
-/
theorem symm_symm (c : ComplexShape ι) : c.symm.symm = c := rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
定理 symm_bijective
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, infer_instance, symm_symm
-/
theorem symm_bijective :
    Function.Bijective (ComplexShape.symm : ComplexShape ι -> ComplexShape ι) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- The "composition" of two `ComplexShape`s.

We need this to define "related in k steps" later.
-/
@[simp]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (c₁ c₂ : ComplexShape ι)
  body: Relation.Comp c₁.Rel c₂.Rel
  next_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₁.next_eq w₁ w₁'] at w₂
    exact c₂.next_eq w₂ w₂'
  prev_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₂.prev_eq w₂ w₂'] at w₁
    exact c₁.pre

中文:
定义 trans
  签名: (c₁ c₂ : 余mplexShape ι)
  定义体: Relation.Comp c₁.Rel c₂.Rel
  next_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₁.next_eq w₁ w₁'] at w₂
    exact c₂.next_eq w₂ w₂'
  prev_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₂.prev_eq w₂ w₂'] at w₁
    exact c₁.pre

Depends on / 依赖: Relation, Relation.Comp, infer_instance
-/
def trans (c₁ c₂ : ComplexShape ι) : ComplexShape ι where
  Rel := Relation.Comp c₁.Rel c₂.Rel
  next_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₁.next_eq w₁ w₁'] at w₂
    exact c₂.next_eq w₂ w₂'
  prev_eq w w' := by
    obtain ⟨k, w₁, w₂⟩ := w
    obtain ⟨k', w₁', w₂'⟩ := w'
    rw [c₂.prev_eq w₂ w₂'] at w₁
    exact c₁.prev_eq w₁ w₁'

@[to_dual]
/--
Instance `subsingleton_next` / 实例 `subsingleton_next`

English:
instance subsingleton_next
  signature: (c : ComplexShape ι) (i : ι)
  body: by
  constructor
  rintro ⟨j, rij⟩ ⟨k, rik⟩
  congr
  exact c.next_eq rij rik

中文:
实例 subsingleton_next
  签名: (c : 余mplexShape ι) (i : ι)
  定义体: by
  constructor
  rintro ⟨j, rij⟩ ⟨k, rik⟩
  congr
  exact c.next_eq rij rik

Depends on / 依赖: c.next_eq, next_eq
-/
instance subsingleton_next (c : ComplexShape ι) (i : ι) : Subsingleton { j // c.Rel i j } := by
  constructor
  rintro ⟨j, rij⟩ ⟨k, rik⟩
  congr
  exact c.next_eq rij rik

open scoped Classical in
/-- An arbitrary choice of index `j` such that `Rel i j`, if such exists.
Returns `i` otherwise.
-/
@[to_dual
/-- An arbitrary choice of index `i` such that `Rel i j`, if such exists.
Returns `j` otherwise.
-/]
/--
Definition of `next` / `next` 的定义

English:
definition next
  signature: (c : ComplexShape ι) (i : ι)
  body: if h : exists j, c.Rel i j then h.choose else i

@[to_dual]

中文:
定义 next
  签名: (c : 余mplexShape ι) (i : ι)
  定义体: if h : exists j, c.Rel i j then h.choose else i

@[to_dual]

Depends on / 依赖: DerivedCategory, DerivedCategory.TStructure.t.IsGE, DerivedCategory.singleFunctor, TStructure, c.Rel, h.choose, infer_instance, singleFunctor
-/
def next (c : ComplexShape ι) (i : ι) : ι :=
  if h : exists j, c.Rel i j then h.choose else i

@[to_dual]
/--
theorem `next_eq'` / 定理 `next_eq'`

English:
theorem next_eq'
  given: (c : ComplexShape ι) {i j : ι} (h : c.Rel i j)
  statement: c.next i = j
  proof: by
  apply c.next_eq _ h
  rw [next]
  rw [dif_pos]
  exact Exists.choose_spec ⟨j, h⟩

@[to_dual]

中文:
定理 next_eq'
  条件: (c : 余mplexShape ι) {i j : ι} (h : c.关系 i j)
  结论: c.next i = j
  证明: by
  apply c.next_eq _ h
  rw [next]
  rw [dif_pos]
  exact Exists.choose_spec ⟨j, h⟩

@[to_dual]

Depends on / 依赖: DerivedCategory, DerivedCategory.TStructure.t.IsLE, DerivedCategory.singleFunctor, Exists, Exists.choose_spec, TStructure, c.next_eq, choose_spec, dif_pos, infer_instance, next_eq, singleFunctor
-/
theorem next_eq' (c : ComplexShape ι) {i j : ι} (h : c.Rel i j) : c.next i = j := by
  apply c.next_eq _ h
  rw [next]
  rw [dif_pos]
  exact Exists.choose_spec ⟨j, h⟩

@[to_dual]
/--
lemma `next_eq_self'` / 引理 `next_eq_self'`

English:
lemma next_eq_self'
  given: (c : ComplexShape ι) (j : ι) (hj : forall k, ¬c.Rel j k)
  proof: dif_neg (by simpa using hj)

@[to_dual]

中文:
引理 next_eq_self'
  条件: (c : 余mplexShape ι) (j : ι) (hj : 对任意 k, ¬c.关系 j k)
  证明: dif_neg (by simpa using hj)

@[to_dual]

Depends on / 依赖: dif_neg
-/
lemma next_eq_self' (c : ComplexShape ι) (j : ι) (hj : forall k, ¬c.Rel j k) :
    c.next j = j :=
  dif_neg (by simpa using hj)

@[to_dual]
/--
lemma `next_eq_self` / 引理 `next_eq_self`

English:
lemma next_eq_self
  given: (c : ComplexShape ι) (j : ι) (hj : ¬c.Rel j (c.next j))
  proof: c.next_eq_self' j (fun k hk' => hj (by simpa only [c.next_eq' hk'] using hk'))

中文:
引理 next_eq_self
  条件: (c : 余mplexShape ι) (j : ι) (hj : ¬c.关系 j (c.next j))
  证明: c.next_eq_self' j (fun k hk' => hj (by simpa only [c.next_eq' hk'] using hk'))

Depends on / 依赖: c.next_eq, c.next_eq_self, next_eq, next_eq_self
-/
lemma next_eq_self (c : ComplexShape ι) (j : ι) (hj : ¬c.Rel j (c.next j)) :
    c.next j = j :=
  c.next_eq_self' j (fun k hk' => hj (by simpa only [c.next_eq' hk'] using hk'))

/--
Definition of `up'` / `up'` 的定义

English:
definition up'
  signature: {α : Type*} [Add α] [IsRightCancelAdd α] (a : α)
  body: i + a = j
  next_eq hi hj := hi.symm.trans hj
  prev_eq hi hj := add_right_cancel (hi.trans hj.symm)

中文:
定义 up'
  签名: {α : 类型} [加法 α] [是右消去加法 α] (a : α)
  定义体: i + a = j
  next_eq hi hj := hi.symm.trans hj
  prev_eq hi hj := add_right_cancel (hi.trans hj.symm)
-/
def up' {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) : ComplexShape α where
  Rel i j := i + a = j
  next_eq hi hj := hi.symm.trans hj
  prev_eq hi hj := add_right_cancel (hi.trans hj.symm)

/-- The `ComplexShape` allowing differentials from `X (j+a)` to `X j`.
(For example when `a = 1`, a homology theory indexed by `ℕ` or `ℤ`)
-/
@[to_dual existing (attr := simps) up']
/--
Definition of `down'` / `down'` 的定义

English:
definition down'
  signature: {α : Type*} [Add α] [IsRightCancelAdd α] (a : α)
  body: j + a = i
  next_eq hi hj := add_right_cancel (hi.trans hj.symm)
  prev_eq hi hj := hi.symm.trans hj

@[to_dual (reorder := i j) down'_mk]

中文:
定义 down'
  签名: {α : 类型} [加法 α] [是右消去加法 α] (a : α)
  定义体: j + a = i
  next_eq hi hj := add_right_cancel (hi.trans hj.symm)
  prev_eq hi hj := hi.symm.trans hj

@[to_dual (reorder := i j) down'_mk]
-/
def down' {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) : ComplexShape α where
  Rel i j := j + a = i
  next_eq hi hj := add_right_cancel (hi.trans hj.symm)
  prev_eq hi hj := hi.symm.trans hj

@[to_dual (reorder := i j) down'_mk]
/--
theorem `up'_mk` / 定理 `up'_mk`

English:
theorem up'_mk
  given: {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) (i j : α) (h : i + a = j)
  proof: h

中文:
定理 up'_mk
  条件: {α : 类型} [加法 α] [是右消去加法 α] (a : α) (i j : α) (h : i + a = j)
  证明: h
-/
theorem up'_mk {α : Type*} [Add α] [IsRightCancelAdd α] (a : α) (i j : α) (h : i + a = j) :
    (up' a).Rel i j := h

/-- The `ComplexShape` appropriate for cohomology, so `d : X i ⟶ X j` only when `j = i + 1`.
-/
@[to_dual (attr := simps!) down
/-- The `ComplexShape` appropriate for homology, so `d : X i ⟶ X j` only when `i = j + 1`.
-/]
/--
Definition of `up` / `up` 的定义

English:
definition up
  signature: (α : Type*) [Add α] [IsRightCancelAdd α] [One α]
  body: up' 1

@[to_dual (reorder := i j) down_mk]

中文:
定义 up
  签名: (α : 类型) [加法 α] [是右消去加法 α] [幺 α]
  定义体: up' 1

@[to_dual (reorder := i j) down_mk]
-/
def up (α : Type*) [Add α] [IsRightCancelAdd α] [One α] : ComplexShape α :=
  up' 1

@[to_dual (reorder := i j) down_mk]
/--
theorem `up_mk` / 定理 `up_mk`

English:
theorem up_mk
  given: {α : Type*} [Add α] [IsRightCancelAdd α] [One α] (i j : α) (h : i + 1 = j)
  proof: up'_mk (1 : α) i j h

中文:
定理 up_mk
  条件: {α : 类型} [加法 α] [是右消去加法 α] [幺 α] (i j : α) (h : i + 1 = j)
  证明: up'_mk (1 : α) i j h
-/
theorem up_mk {α : Type*} [Add α] [IsRightCancelAdd α] [One α] (i j : α) (h : i + 1 = j) :
    (up α).Rel i j :=
  up'_mk (1 : α) i j h

end ComplexShape

end

namespace ComplexShape

variable (α : Type*) [AddRightCancelSemigroup α] [DecidableEq α]

set_option backward.defeqAttrib.useBackward true in
@[to_dual instDecidableRelRelDown']
/--
Instance `instDecidableRelRelUp'` / 实例 `instDecidableRelRelUp'`

English:
instance instDecidableRelRelUp'
  signature: (a : α)
  body: fun _ _ => by dsimp; infer_instance

@[to_dual instDecidableRelRelDown]

中文:
实例 instDecidableRelRelUp'
  签名: (a : α)
  定义体: fun _ _ => by dsimp; infer_instance

@[to_dual instDecidableRelRelDown]

Depends on / 依赖: infer_instance
-/
instance instDecidableRelRelUp' (a : α) : DecidableRel (ComplexShape.up' a).Rel :=
  fun _ _ => by dsimp; infer_instance

@[to_dual instDecidableRelRelDown]
/--
Instance `instDecidableRelRelUp` / 实例 `instDecidableRelRelUp`

English:
instance instDecidableRelRelUp
  signature: [One α]
  body: by
  dsimp [ComplexShape.up]; infer_instance

中文:
实例 instDecidableRelRelUp
  签名: [幺 α]
  定义体: by
  dsimp [ComplexShape.up]; infer_instance

Depends on / 依赖: ComplexShape, ComplexShape.up, infer_instance
-/
instance instDecidableRelRelUp [One α] : DecidableRel (ComplexShape.up α).Rel := by
  dsimp [ComplexShape.up]; infer_instance

end ComplexShape
