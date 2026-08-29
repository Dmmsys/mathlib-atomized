/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import Mathlib.Data.Fin.Fin2
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Common

/-!

# Tuples of types, and their categorical structure.

## Features

* `TypeVec n` - n-tuples of types
* `α ⟹ β` - n-tuples of maps
* `f ⊚ g` - composition

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β` - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α` - drops the last element of an (n+1)-tuple
* `last α` - returns the last element of an (n+1)-tuple
* `appendFun f g` - appends a function g to an n-tuple of functions
* `dropFun f` - drops the last function from an n+1-tuple
* `lastFun f` - returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/

@[expose] public section

universe u v w x

/-- n-tuples of types, as a category -/
@[pp_with_univ]
/--
Definition of `TypeVec` / `TypeVec` 的定义

English:
definition TypeVec
  signature: (n : Nat)
  body: Fin2 n -> Type*

中文:
定义 TypeVec
  签名: (n : 自然数)
  定义体: Fin2 n -> Type*
-/
def TypeVec (n : Nat) :=
  Fin2 n -> Type*

instance {n} : Inhabited (TypeVec.{u} n) :=
  ⟨fun _ => PUnit⟩

namespace TypeVec

variable {n : Nat}

/--
Definition of `Arrow` / `Arrow` 的定义

English:
definition Arrow
  signature: (α : TypeVec.{u} n) (β : TypeVec.{v} n)
  body: forall i : Fin2 n, α i -> β i

@[inherit_doc] scoped[MvFunctor] infixl:40 " ⟹ " => TypeVec.Arrow

中文:
定义 Arrow
  签名: (α : TypeVec.{u} n) (β : TypeVec.{v} n)
  定义体: forall i : Fin2 n, α i -> β i

@[inherit_doc] scoped[MvFunctor] infixl:40 " ⟹ " => TypeVec.Arrow
-/
def Arrow (α : TypeVec.{u} n) (β : TypeVec.{v} n) :=
  forall i : Fin2 n, α i -> β i

@[inherit_doc] scoped[MvFunctor] infixl:40 " ⟹ " => TypeVec.Arrow
open MvFunctor

variable {α : TypeVec.{u} n} {β : TypeVec.{v} n} {γ : TypeVec.{w} n} {δ : TypeVec.{x} n} in
section

/-- Extensionality for arrows -/
@[ext]
/--
theorem `Arrow.ext` / 定理 `Arrow.ext`

English:
theorem Arrow.ext
  given: (f g : α ⟹ β)
  proof: by
  intro h; funext i; apply h

中文:
定理 Arrow.ext
  条件: (f g : α ⟹ β)
  证明: by
  intro h; funext i; apply h
-/
theorem Arrow.ext (f g : α ⟹ β) :
    (forall i, f i = g i) -> f = g := by
  intro h; funext i; apply h

/--
Instance `Arrow.inhabited` / 实例 `Arrow.inhabited`

English:
instance Arrow.inhabited
  signature: (α β : TypeVec n) [forall i, Inhabited (β i)]
  body: ⟨fun _ _ => default⟩

中文:
实例 Arrow.inhabited
  签名: (α β : TypeVec n) [对任意 i, Inhabited (β i)]
  定义体: ⟨fun _ _ => default⟩
-/
instance Arrow.inhabited (α β : TypeVec n) [forall i, Inhabited (β i)] : Inhabited (α ⟹ β) :=
  ⟨fun _ _ => default⟩

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: {α : TypeVec n}
  body: fun _ x => x

中文:
定义 id
  签名: {α : TypeVec n}
  定义体: fun _ x => x
-/
def id {α : TypeVec n} : α ⟹ α := fun _ x => x


/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : β ⟹ γ) (f : α ⟹ β)
  body: fun i x => g i (f i x)

@[inherit_doc] scoped[MvFunctor] infixr:80 " ⊚ " => TypeVec.comp -- type as \oo

@[simp]

中文:
定义 comp
  签名: (g : β ⟹ γ) (f : α ⟹ β)
  定义体: fun i x => g i (f i x)

@[inherit_doc] scoped[MvFunctor] infixr:80 " ⊚ " => TypeVec.comp -- type as \oo

@[simp]
-/
def comp (g : β ⟹ γ) (f : α ⟹ β)
    : α ⟹ γ :=
  fun i x => g i (f i x)

@[inherit_doc] scoped[MvFunctor] infixr:80 " ⊚ " => TypeVec.comp -- type as \oo

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : α ⟹ β)
  statement: id ⊚ f = f
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: (f : α ⟹ β)
  结论: id ⊚ f = f
  证明: rfl

@[simp]
-/
theorem id_comp (f : α ⟹ β) : id ⊚ f = f :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : α ⟹ β)
  statement: f ⊚ id = f
  proof: rfl

中文:
定理 comp_id
  条件: (f : α ⟹ β)
  结论: f ⊚ id = f
  证明: rfl

Depends on / 依赖: Quotient, c.Quotient
-/
theorem comp_id (f : α ⟹ β) : f ⊚ id = f :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  proof: rfl

中文:
定理 comp_assoc
  证明: rfl

Depends on / 依赖: Decidable, DecidableEq, Quotient, c.Quotient
-/
theorem comp_assoc
    (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f :=
  rfl
end

/--
Definition of `append1` / `append1` 的定义

English:
definition append1
  signature: (α : TypeVec n) (β : Type*)

中文:
定义 append1
  签名: (α : TypeVec n) (β : 类型)
-/
def append1 (α : TypeVec n) (β : Type*) : TypeVec (n + 1)
  | Fin2.fs i => α i
  | Fin2.fz => β

@[inherit_doc] infixl:67 " ::: " => append1

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (α : TypeVec.{u} (n + 1))
  body: fun i => α i.fs

中文:
定义 drop
  签名: (α : TypeVec.{u} (n + 1))
  定义体: fun i => α i.fs

Depends on / 依赖: i.fs
-/
def drop (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.fs

/--
Definition of `last` / `last` 的定义

English:
definition last
  signature: (α : TypeVec.{u} (n + 1))
  body: α Fin2.fz

中文:
定义 last
  签名: (α : TypeVec.{u} (n + 1))
  定义体: α Fin2.fz

Depends on / 依赖: Fin2.fz
-/
def last (α : TypeVec.{u} (n + 1)) : Type _ :=
  α Fin2.fz

/--
Instance `last.inhabited` / 实例 `last.inhabited`

English:
instance last.inhabited
  signature: (α : TypeVec (n + 1)) [Inhabited (α Fin2.fz)]
  body: ⟨show α Fin2.fz from default⟩

中文:
实例 last.inhabited
  签名: (α : TypeVec (n + 1)) [Inhabited (α Fin2.fz)]
  定义体: ⟨show α Fin2.fz from default⟩

Depends on / 依赖: Fin2.fz
-/
instance last.inhabited (α : TypeVec (n + 1)) [Inhabited (α Fin2.fz)] : Inhabited (last α) :=
  ⟨show α Fin2.fz from default⟩

/--
theorem `drop_append1` / 定理 `drop_append1`

English:
theorem drop_append1
  given: {α : TypeVec n} {β : Type*} {i : Fin2 n}
  statement: drop (append1 α β) i = α i
  proof: rfl

中文:
定理 drop_append1
  条件: {α : TypeVec n} {β : 类型} {i : Fin2 n}
  结论: drop (append1 α β) i = α i
  证明: rfl
-/
theorem drop_append1 {α : TypeVec n} {β : Type*} {i : Fin2 n} : drop (append1 α β) i = α i :=
  rfl

/--
theorem `drop_append1'` / 定理 `drop_append1'`

English:
theorem drop_append1'
  given: {α : TypeVec n} {β : Type*}
  statement: drop (append1 α β) = α
  proof: funext fun _ => drop_append1

中文:
定理 drop_append1'
  条件: {α : TypeVec n} {β : 类型}
  结论: drop (append1 α β) = α
  证明: funext fun _ => drop_append1

Depends on / 依赖: drop_append1
-/
theorem drop_append1' {α : TypeVec n} {β : Type*} : drop (append1 α β) = α :=
  funext fun _ => drop_append1

/--
theorem `last_append1` / 定理 `last_append1`

English:
theorem last_append1
  given: {α : TypeVec n} {β : Type*}
  statement: last (append1 α β) = β
  proof: rfl

@[simp]

中文:
定理 last_append1
  条件: {α : TypeVec n} {β : 类型}
  结论: last (append1 α β) = β
  证明: rfl

@[simp]
-/
theorem last_append1 {α : TypeVec n} {β : Type*} : last (append1 α β) = β :=
  rfl

@[simp]
/--
theorem `append1_drop_last` / 定理 `append1_drop_last`

English:
theorem append1_drop_last
  given: (α : TypeVec (n + 1))
  statement: append1 (drop α) (last α) = α
  proof: funext fun i => by cases i <;> rfl

中文:
定理 append1_drop_last
  条件: (α : TypeVec (n + 1))
  结论: append1 (drop α) (last α) = α
  证明: funext fun i => by cases i <;> rfl
-/
theorem append1_drop_last (α : TypeVec (n + 1)) : append1 (drop α) (last α) = α :=
  funext fun i => by cases i <;> rfl

/-- cases on `(n+1)-length` vectors -/
@[elab_as_elim]
/--
Definition of `append1Cases` / `append1Cases` 的定义

English:
definition append1Cases
  signature: {C : TypeVec (n + 1) -> Sort u} (H : forall α β, C (append1 α β)) (γ)
  body: by
  rw [← @append1_drop_last _ γ]; apply H

@[simp]

中文:
定义 append1Cases
  签名: {C : TypeVec (n + 1) -> Sort u} (H : 对任意 α β, C (append1 α β)) (γ)
  定义体: by
  rw [← @append1_drop_last _ γ]; apply H

@[simp]

Depends on / 依赖: append1_drop_last
-/
def append1Cases {C : TypeVec (n + 1) -> Sort u} (H : forall α β, C (append1 α β)) (γ) : C γ := by
  rw [← @append1_drop_last _ γ]; apply H

@[simp]
/--
theorem `append1_cases_append1` / 定理 `append1_cases_append1`

English:
theorem append1_cases_append1
  given: {C : TypeVec (n + 1) -> Sort u} (H : forall α β, C (append1 α β)) (α β)
  proof: rfl

中文:
定理 append1_cases_append1
  条件: {C : TypeVec (n + 1) -> Sort u} (H : 对任意 α β, C (append1 α β)) (α β)
  证明: rfl
-/
theorem append1_cases_append1 {C : TypeVec (n + 1) -> Sort u} (H : forall α β, C (append1 α β)) (α β) :
    @append1Cases _ C H (append1 α β) = H α β :=
  rfl

/--
Definition of `splitFun` / `splitFun` 的定义

English:
definition splitFun
  signature: {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α')

中文:
定义 splitFun
  签名: {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α')
-/
def splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α') : α ⟹ α'
  | Fin2.fs i => f i
  | Fin2.fz => g

/--
Definition of `appendFun` / `appendFun` 的定义

English:
definition appendFun
  signature: {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β -> β')
  body: splitFun f g

@[inherit_doc] infixl:0 " ::: " => appendFun

中文:
定义 appendFun
  签名: {α α' : TypeVec n} {β β' : 类型} (f : α ⟹ α') (g : β -> β')
  定义体: splitFun f g

@[inherit_doc] infixl:0 " ::: " => appendFun

Depends on / 依赖: splitFun
-/
def appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β -> β') :
    append1 α β ⟹ append1 α' β' :=
  splitFun f g

@[inherit_doc] infixl:0 " ::: " => appendFun

/--
Definition of `dropFun` / `dropFun` 的定义

English:
definition dropFun
  signature: {α β : TypeVec (n + 1)} (f : α ⟹ β)
  body: fun i => f i.fs

中文:
定义 dropFun
  签名: {α β : TypeVec (n + 1)} (f : α ⟹ β)
  定义体: fun i => f i.fs

Depends on / 依赖: i.fs
-/
def dropFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : drop α ⟹ drop β := fun i => f i.fs

/--
Definition of `lastFun` / `lastFun` 的定义

English:
definition lastFun
  signature: {α β : TypeVec (n + 1)} (f : α ⟹ β)
  body: f Fin2.fz

中文:
定义 lastFun
  签名: {α β : TypeVec (n + 1)} (f : α ⟹ β)
  定义体: f Fin2.fz

Depends on / 依赖: Fin2.fz
-/
def lastFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : last α -> last β :=
  f Fin2.fz

/--
Definition of `nilFun` / `nilFun` 的定义

English:
definition nilFun
  signature: {α : TypeVec 0} {β : TypeVec 0}
  body: fun i => by apply Fin2.elim0 i

中文:
定义 nilFun
  签名: {α : TypeVec 0} {β : TypeVec 0}
  定义体: fun i => by apply Fin2.elim0 i

Depends on / 依赖: Fin2.elim0
-/
def nilFun {α : TypeVec 0} {β : TypeVec 0} : α ⟹ β := fun i => by apply Fin2.elim0 i

/--
theorem `eq_of_drop_last_eq` / 定理 `eq_of_drop_last_eq`

English:
theorem eq_of_drop_last_eq
  statement: {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
  proof: by
  refine funext (fun x => ?_)
  cases x
  · apply h₁
  · apply congr_fun h₀

@[simp]

中文:
定理 eq_of_drop_last_eq
  结论: {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
  证明: by
  refine funext (fun x => ?_)
  cases x
  · apply h₁
  · apply congr_fun h₀

@[simp]

Depends on / 依赖: congr_fun
-/
theorem eq_of_drop_last_eq {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
    (h₁ : lastFun f = lastFun g) : f = g := by
  refine funext (fun x => ?_)
  cases x
  · apply h₁
  · apply congr_fun h₀

@[simp]
/--
theorem `dropFun_splitFun` / 定理 `dropFun_splitFun`

English:
theorem dropFun_splitFun
  given: {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α')
  proof: rfl

中文:
定理 dropFun_splitFun
  条件: {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α')
  证明: rfl
-/
theorem dropFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α') :
    dropFun (splitFun f g) = f :=
  rfl

/--
Definition of `Arrow.mp` / `Arrow.mp` 的定义

English:
definition Arrow.mp
  signature: {α β : TypeVec n} (h : α = β)

中文:
定义 Arrow.mp
  签名: {α β : TypeVec n} (h : α = β)
-/
def Arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | _ => Eq.mp (congr_fun h _)

/--
Definition of `Arrow.mpr` / `Arrow.mpr` 的定义

English:
definition Arrow.mpr
  signature: {α β : TypeVec n} (h : α = β)

中文:
定义 Arrow.mpr
  签名: {α β : TypeVec n} (h : α = β)
-/
def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | _ => Eq.mpr (congr_fun h _)

/--
Definition of `toAppend1DropLast` / `toAppend1DropLast` 的定义

English:
definition toAppend1DropLast
  signature: {α : TypeVec (n + 1)}
  body: Arrow.mpr (append1_drop_last _)

中文:
定义 toAppend1DropLast
  签名: {α : TypeVec (n + 1)}
  定义体: Arrow.mpr (append1_drop_last _)

Depends on / 依赖: Arrow.mpr, append1_drop_last
-/
def toAppend1DropLast {α : TypeVec (n + 1)} : α ⟹ (drop α ::: last α) :=
  Arrow.mpr (append1_drop_last _)

/--
Definition of `fromAppend1DropLast` / `fromAppend1DropLast` 的定义

English:
definition fromAppend1DropLast
  signature: {α : TypeVec (n + 1)}
  body: Arrow.mp (append1_drop_last _)

@[simp]

中文:
定义 fromAppend1DropLast
  签名: {α : TypeVec (n + 1)}
  定义体: Arrow.mp (append1_drop_last _)

@[simp]

Depends on / 依赖: Arrow.mp, append1_drop_last
-/
def fromAppend1DropLast {α : TypeVec (n + 1)} : (drop α ::: last α) ⟹ α :=
  Arrow.mp (append1_drop_last _)

@[simp]
/--
theorem `lastFun_splitFun` / 定理 `lastFun_splitFun`

English:
theorem lastFun_splitFun
  given: {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α')
  proof: rfl

@[simp]

中文:
定理 lastFun_splitFun
  条件: {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α')
  证明: rfl

@[simp]
-/
theorem lastFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α -> last α') :
    lastFun (splitFun f g) = g :=
  rfl

@[simp]
/--
theorem `dropFun_appendFun` / 定理 `dropFun_appendFun`

English:
theorem dropFun_appendFun
  given: {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β -> β')
  proof: rfl

@[simp]

中文:
定理 dropFun_appendFun
  条件: {α α' : TypeVec n} {β β' : 类型} (f : α ⟹ α') (g : β -> β')
  证明: rfl

@[simp]
-/
theorem dropFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β -> β') :
    dropFun (f ::: g) = f :=
  rfl

@[simp]
/--
theorem `lastFun_appendFun` / 定理 `lastFun_appendFun`

English:
theorem lastFun_appendFun
  given: {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β -> β')
  proof: rfl

中文:
定理 lastFun_appendFun
  条件: {α α' : TypeVec n} {β β' : 类型} (f : α ⟹ α') (g : β -> β')
  证明: rfl
-/
theorem lastFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β -> β') :
    lastFun (f ::: g) = g :=
  rfl

/--
theorem `split_dropFun_lastFun` / 定理 `split_dropFun_lastFun`

English:
theorem split_dropFun_lastFun
  given: {α α' : TypeVec (n + 1)} (f : α ⟹ α')
  proof: eq_of_drop_last_eq rfl rfl

中文:
定理 split_dropFun_lastFun
  条件: {α α' : TypeVec (n + 1)} (f : α ⟹ α')
  证明: eq_of_drop_last_eq rfl rfl

Depends on / 依赖: eq_of_drop_last_eq
-/
theorem split_dropFun_lastFun {α α' : TypeVec (n + 1)} (f : α ⟹ α') :
    splitFun (dropFun f) (lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl

/--
theorem `splitFun_inj` / 定理 `splitFun_inj`

English:
theorem splitFun_inj
  statement: {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α -> last α'}
  proof: by
  rw [← dropFun_splitFun f g]; rw [H]; rw [← lastFun_splitFun f g]; rw [H]; simp

中文:
定理 splitFun_inj
  结论: {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α -> last α'}
  证明: by
  rw [← dropFun_splitFun f g]; rw [H]; rw [← lastFun_splitFun f g]; rw [H]; simp

Depends on / 依赖: dropFun_splitFun, lastFun_splitFun
-/
theorem splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α -> last α'}
    (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g' := by
  rw [← dropFun_splitFun f g]; rw [H]; rw [← lastFun_splitFun f g]; rw [H]; simp

/--
theorem `appendFun_inj` / 定理 `appendFun_inj`

English:
theorem appendFun_inj
  given: {α α' : TypeVec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β -> β'}
  proof: splitFun_inj

中文:
定理 appendFun_inj
  条件: {α α' : TypeVec n} {β β' : 类型} {f f' : α ⟹ α'} {g g' : β -> β'}
  证明: splitFun_inj

Depends on / 依赖: splitFun_inj
-/
theorem appendFun_inj {α α' : TypeVec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β -> β'} :
    (f ::: g : (α ::: β) ⟹ _) = (f' ::: g' : (α ::: β) ⟹ _)
    -> f = f' ∧ g = g' :=
  splitFun_inj

/--
theorem `splitFun_comp` / 定理 `splitFun_comp`

English:
theorem splitFun_comp
  statement: {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁)
  proof: eq_of_drop_last_eq rfl rfl

中文:
定理 splitFun_comp
  结论: {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁)
  证明: eq_of_drop_last_eq rfl rfl

Depends on / 依赖: eq_of_drop_last_eq
-/
theorem splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁)
    (f₁ : drop α₁ ⟹ drop α₂) (g₀ : last α₀ -> last α₁) (g₁ : last α₁ -> last α₂) :
    splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀ :=
  eq_of_drop_last_eq rfl rfl

/--
theorem `appendFun_comp_splitFun` / 定理 `appendFun_comp_splitFun`

English:
theorem appendFun_comp_splitFun
  statement: {α γ : TypeVec n} {β δ : Type*} {ε : TypeVec (n + 1)}
  proof: (splitFun_comp _ _ _ _).symm

中文:
定理 appendFun_comp_splitFun
  结论: {α γ : TypeVec n} {β δ : 类型} {ε : TypeVec (n + 1)}
  证明: (splitFun_comp _ _ _ _).symm

Depends on / 依赖: append1
-/
theorem appendFun_comp_splitFun {α γ : TypeVec n} {β δ : Type*} {ε : TypeVec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last ε -> β) (g₁ : β -> δ) :
    appendFun f₁ g₁ ⊚ splitFun f₀ g₀ = splitFun (α' := γ.append1 δ) (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (splitFun_comp _ _ _ _).symm

/--
theorem `appendFun_comp` / 定理 `appendFun_comp`

English:
theorem appendFun_comp
  statement: {α₀ α₁ α₂ : TypeVec n}
  proof: eq_of_drop_last_eq rfl rfl

中文:
定理 appendFun_comp
  结论: {α₀ α₁ α₂ : TypeVec n}
  证明: eq_of_drop_last_eq rfl rfl

Depends on / 依赖: eq_of_drop_last_eq
-/
theorem appendFun_comp {α₀ α₁ α₂ : TypeVec n}
    {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
    (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂) :
    (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

/--
theorem `appendFun_comp'` / 定理 `appendFun_comp'`

English:
theorem appendFun_comp'
  statement: {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type*}
  proof: eq_of_drop_last_eq rfl rfl

中文:
定理 appendFun_comp'
  结论: {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : 类型}
  证明: eq_of_drop_last_eq rfl rfl

Depends on / 依赖: eq_of_drop_last_eq
-/
theorem appendFun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂) :
    (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ ⊚ f₀ ::: g₁ ∘ g₀) :=
  eq_of_drop_last_eq rfl rfl

/--
theorem `nilFun_comp` / 定理 `nilFun_comp`

English:
theorem nilFun_comp
  given: {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0)
  statement: nilFun ⊚ f₀ = f₀
  proof: funext Fin2.elim0

中文:
定理 nilFun_comp
  条件: {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0)
  结论: nilFun ⊚ f₀ = f₀
  证明: funext Fin2.elim0

Depends on / 依赖: Fin2.elim0
-/
theorem nilFun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0) : nilFun ⊚ f₀ = f₀ :=
  funext Fin2.elim0

/--
theorem `appendFun_comp_id` / 定理 `appendFun_comp_id`

English:
theorem appendFun_comp_id
  given: {α : TypeVec n} {β₀ β₁ β₂ : Type u} (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂)
  proof: eq_of_drop_last_eq rfl rfl

@[simp]

中文:
定理 appendFun_comp_id
  条件: {α : TypeVec n} {β₀ β₁ β₂ : 类型u} (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂)
  证明: eq_of_drop_last_eq rfl rfl

@[simp]

Depends on / 依赖: eq_of_drop_last_eq
-/
theorem appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type u} (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂) :
    (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

@[simp]
/--
theorem `dropFun_comp` / 定理 `dropFun_comp`

English:
theorem dropFun_comp
  given: {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
  proof: rfl

@[simp]

中文:
定理 dropFun_comp
  条件: {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
  证明: rfl

@[simp]
-/
theorem dropFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀ :=
  rfl

@[simp]
/--
theorem `lastFun_comp` / 定理 `lastFun_comp`

English:
theorem lastFun_comp
  given: {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
  proof: rfl

中文:
定理 lastFun_comp
  条件: {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
  证明: rfl
-/
theorem lastFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀ :=
  rfl

/--
theorem `appendFun_aux` / 定理 `appendFun_aux`

English:
theorem appendFun_aux
  given: {α α' : TypeVec n} {β β' : Type*} (f : (α ::: β) ⟹ (α' ::: β'))
  proof: eq_of_drop_last_eq rfl rfl

中文:
定理 appendFun_aux
  条件: {α α' : TypeVec n} {β β' : 类型} (f : (α ::: β) ⟹ (α' ::: β'))
  证明: eq_of_drop_last_eq rfl rfl

Depends on / 依赖: eq_of_drop_last_eq
-/
theorem appendFun_aux {α α' : TypeVec n} {β β' : Type*} (f : (α ::: β) ⟹ (α' ::: β')) :
    (dropFun f ::: lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl

/--
theorem `appendFun_id_id` / 定理 `appendFun_id_id`

English:
theorem appendFun_id_id
  given: {α : TypeVec n} {β : Type*}
  proof: eq_of_drop_last_eq rfl rfl

中文:
定理 appendFun_id_id
  条件: {α : TypeVec n} {β : 类型}
  证明: eq_of_drop_last_eq rfl rfl

Depends on / 依赖: eq_of_drop_last_eq
-/
theorem appendFun_id_id {α : TypeVec n} {β : Type*} :
    (@TypeVec.id n α ::: @_root_.id β) = TypeVec.id :=
  eq_of_drop_last_eq rfl rfl

/--
Instance `subsingleton0` / 实例 `subsingleton0`

English:
instance subsingleton0
  signature: : Subsingleton (TypeVec 0)
  body: ⟨fun _ _ => funext Fin2.elim0⟩

中文:
实例 subsingleton0
  签名: : Subsingleton (TypeVec 0)
  定义体: ⟨fun _ _ => funext Fin2.elim0⟩

Depends on / 依赖: Fin2.elim0
-/
instance subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨fun _ _ => funext Fin2.elim0⟩

-- See `Mathlib/Tactic/Attr/Register.lean` for `register_simp_attr typevec`

/--
Definition of `casesNil` / `casesNil` 的定义

English:
definition casesNil
  signature: {β : TypeVec 0 -> Sort*} (f : β Fin2.elim0)
  body: fun v => cast (by congr; funext i; cases i) f

中文:
定义 casesNil
  签名: {β : TypeVec 0 -> Sort*} (f : β Fin2.elim0)
  定义体: fun v => cast (by congr; funext i; cases i) f
-/
protected def casesNil {β : TypeVec 0 -> Sort*} (f : β Fin2.elim0) : forall v, β v :=
  fun v => cast (by congr; funext i; cases i) f

/--
Definition of `casesCons` / `casesCons` 的定义

English:
definition casesCons
  signature: (n : Nat) {β : TypeVec (n + 1) -> Sort*}
  body: fun v : TypeVec (n + 1) => cast (by simp) (f v.last v.drop)

中文:
定义 casesCons
  签名: (n : 自然数) {β : TypeVec (n + 1) -> Sort*}
  定义体: fun v : TypeVec (n + 1) => cast (by simp) (f v.last v.drop)
-/
protected def casesCons (n : Nat) {β : TypeVec (n + 1) -> Sort*}
    (f : forall (t) (v : TypeVec n), β (v ::: t)) :
    forall v, β v :=
  fun v : TypeVec (n + 1) => cast (by simp) (f v.last v.drop)

/--
theorem `casesNil_append1` / 定理 `casesNil_append1`

English:
theorem casesNil_append1
  given: {β : TypeVec 0 -> Sort*} (f : β Fin2.elim0)
  proof: rfl

中文:
定理 casesNil_append1
  条件: {β : TypeVec 0 -> Sort*} (f : β Fin2.elim0)
  证明: rfl

Depends on / 依赖: Quotient, Quotient.map, c.pow
-/
protected theorem casesNil_append1 {β : TypeVec 0 -> Sort*} (f : β Fin2.elim0) :
    TypeVec.casesNil f Fin2.elim0 = f :=
  rfl

/--
theorem `casesCons_append1` / 定理 `casesCons_append1`

English:
theorem casesCons_append1
  statement: (n : Nat) {β : TypeVec (n + 1) -> Sort*}
  proof: rfl

中文:
定理 casesCons_append1
  结论: (n : 自然数) {β : TypeVec (n + 1) -> Sort*}
  证明: rfl
-/
protected theorem casesCons_append1 (n : Nat) {β : TypeVec (n + 1) -> Sort*}
    (f : forall (t) (v : TypeVec n), β (v ::: t)) (v : TypeVec n) (α) :
    TypeVec.casesCons n f (v ::: α) = f α v :=
  rfl

/--
Definition of `typevecCasesNil₃` / `typevecCasesNil₃` 的定义

English:
definition typevecCasesNil₃
  signature: {β : forall v v' : TypeVec 0, v ⟹ v' -> Sort*}
  body: fun v v' fs => by
  refine cast ?_ f
  have eq₁ : v = Fin2.elim0 := by funext i; contradiction
  have eq₂ : v' = Fin2.elim0 := by funext i; contradiction
  have eq₃ : fs = nilFun := by funext i; contradiction
  cases eq₁; cases eq₂; cases eq₃; rfl

中文:
定义 typevecCasesNil₃
  签名: {β : 对任意 v v' : TypeVec 0, v ⟹ v' -> Sort*}
  定义体: fun v v' fs => by
  refine cast ?_ f
  have eq₁ : v = Fin2.elim0 := by funext i; contradiction
  have eq₂ : v' = Fin2.elim0 := by funext i; contradiction
  have eq₃ : fs = nilFun := by funext i; contradiction
  cases eq₁; cases eq₂; cases eq₃; rfl

Depends on / 依赖: Fin2.elim0, nilFun
-/
def typevecCasesNil₃ {β : forall v v' : TypeVec 0, v ⟹ v' -> Sort*}
    (f : β Fin2.elim0 Fin2.elim0 nilFun) :
    forall v v' fs, β v v' fs := fun v v' fs => by
  refine cast ?_ f
  have eq₁ : v = Fin2.elim0 := by funext i; contradiction
  have eq₂ : v' = Fin2.elim0 := by funext i; contradiction
  have eq₃ : fs = nilFun := by funext i; contradiction
  cases eq₁; cases eq₂; cases eq₃; rfl

/--
Definition of `typevecCasesCons₃` / `typevecCasesCons₃` 的定义

English:
definition typevecCasesCons₃
  signature: (n : Nat) {β : forall v v' : TypeVec (n + 1), v ⟹ v' -> Sort*}
  body: by
  intro v v'
  rw [← append1_drop_last v]; rw [← append1_drop_last v']
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

中文:
定义 typevecCasesCons₃
  签名: (n : 自然数) {β : 对任意 v v' : TypeVec (n + 1), v ⟹ v' -> Sort*}
  定义体: by
  intro v v'
  rw [← append1_drop_last v]; rw [← append1_drop_last v']
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

Depends on / 依赖: append1_drop_last, split_dropFun_lastFun
-/
def typevecCasesCons₃ (n : Nat) {β : forall v v' : TypeVec (n + 1), v ⟹ v' -> Sort*}
    (F : forall (t t') (f : t -> t') (v v' : TypeVec n) (fs : v ⟹ v'),
    β (v ::: t) (v' ::: t') (fs ::: f)) :
    forall v v' fs, β v v' fs := by
  intro v v'
  rw [← append1_drop_last v]; rw [← append1_drop_last v']
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

/--
Definition of `typevecCasesNil₂` / `typevecCasesNil₂` 的定义

English:
definition typevecCasesNil₂
  signature: {β : Fin2.elim0 ⟹ Fin2.elim0 -> Sort*} (f : β nilFun)
  body: by
  intro g
  suffices g = nilFun by rwa [this]
  ext ⟨⟩

中文:
定义 typevecCasesNil₂
  签名: {β : Fin2.elim0 ⟹ Fin2.elim0 -> Sort*} (f : β nilFun)
  定义体: by
  intro g
  suffices g = nilFun by rwa [this]
  ext ⟨⟩

Depends on / 依赖: nilFun
-/
def typevecCasesNil₂ {β : Fin2.elim0 ⟹ Fin2.elim0 -> Sort*} (f : β nilFun) : forall f, β f := by
  intro g
  suffices g = nilFun by rwa [this]
  ext ⟨⟩

/--
Definition of `typevecCasesCons₂` / `typevecCasesCons₂` 的定义

English:
definition typevecCasesCons₂
  signature: (n : Nat) (t t' : Type*) (v v' : TypeVec n)
  body: by
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

中文:
定义 typevecCasesCons₂
  签名: (n : 自然数) (t t' : 类型) (v v' : TypeVec n)
  定义体: by
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

Depends on / 依赖: split_dropFun_lastFun
-/
def typevecCasesCons₂ (n : Nat) (t t' : Type*) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') -> Sort*}
    (F : forall (f : t -> t') (fs : v ⟹ v'), β (fs ::: f)) : forall fs, β fs := by
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F


/--
theorem `typevecCasesNil₂_appendFun` / 定理 `typevecCasesNil₂_appendFun`

English:
theorem typevecCasesNil₂_appendFun
  given: {β : Fin2.elim0 ⟹ Fin2.elim0 -> Sort*} (f : β nilFun)
  proof: rfl

中文:
定理 typevecCasesNil₂_appendFun
  条件: {β : Fin2.elim0 ⟹ Fin2.elim0 -> Sort*} (f : β nilFun)
  证明: rfl
-/
theorem typevecCasesNil₂_appendFun {β : Fin2.elim0 ⟹ Fin2.elim0 -> Sort*} (f : β nilFun) :
    typevecCasesNil₂ f nilFun = f :=
  rfl

/--
theorem `typevecCasesCons₂_appendFun` / 定理 `typevecCasesCons₂_appendFun`

English:
theorem typevecCasesCons₂_appendFun
  statement: (n : Nat) (t t' : Type*) (v v' : TypeVec n)
  proof: rfl

中文:
定理 typevecCasesCons₂_appendFun
  结论: (n : 自然数) (t t' : 类型) (v v' : TypeVec n)
  证明: rfl
-/
theorem typevecCasesCons₂_appendFun (n : Nat) (t t' : Type*) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') -> Sort*}
    (F : forall (f : t -> t') (fs : v ⟹ v'), β (fs ::: f))
    (f fs) :
    typevecCasesCons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl

-- for lifting predicates and relations
/--
Definition of `PredLast` / `PredLast` 的定义

English:
definition PredLast
  signature: (α : TypeVec n) {β : Type*} (p : β -> Prop)

中文:
定义 PredLast
  签名: (α : TypeVec n) {β : 类型} (p : β -> 命题)
-/
def PredLast (α : TypeVec n) {β : Type*} (p : β -> Prop) : forall ⦃i⦄, (α.append1 β) i -> Prop
  | Fin2.fs _ => fun _ => True
  | Fin2.fz => p

/--
Definition of `RelLast` / `RelLast` 的定义

English:
definition RelLast
  signature: (α : TypeVec n) {β γ : Type u} (r : β -> γ -> Prop)

中文:
定义 RelLast
  签名: (α : TypeVec n) {β γ : 类型u} (r : β -> γ -> 命题)
-/
def RelLast (α : TypeVec n) {β γ : Type u} (r : β -> γ -> Prop) :
    forall ⦃i⦄, (α.append1 β) i -> (α.append1 γ) i -> Prop
  | Fin2.fs _ => Eq
  | Fin2.fz => r

section Liftp'

open Nat

/--
Definition of `«repeat»` / `«repeat»` 的定义

English:
definition «repeat»
  signature: : forall (n : Nat), Type u -> TypeVec n

中文:
定义 «repeat»
  签名: : 对任意 (n : 自然数), 类型u -> TypeVec n
-/
def «repeat» : forall (n : Nat), Type u -> TypeVec n
  | 0, _ => Fin2.elim0
  | Nat.succ i, t => append1 («repeat» i t) t

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: : forall {n}, TypeVec.{u} n -> TypeVec.{u} n -> TypeVec n

中文:
定义 prod
  签名: : 对任意 {n}, TypeVec.{u} n -> TypeVec.{u} n -> TypeVec n
-/
def prod : forall {n}, TypeVec.{u} n -> TypeVec.{u} n -> TypeVec n
  | 0, _, _ => Fin2.elim0
  | n + 1, α, β => (@prod n (drop α) (drop β)) ::: (last α × last β)

@[inherit_doc] scoped[MvFunctor] infixl:45 " otimes " => TypeVec.prod

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: {β} (x : β)

中文:
定义 const
  签名: {β} (x : β)
-/
protected def const {β} (x : β) : forall {n} (α : TypeVec n), α ⟹ «repeat» _ β
  | succ _, α, Fin2.fs _ => TypeVec.const x (drop α) _
  | succ _, _, Fin2.fz => fun _ => x

open Function (uncurry)

/--
Definition of `repeatEq` / `repeatEq` 的定义

English:
definition repeatEq
  signature: : forall {n} (α : TypeVec n), (α otimes α) ⟹ «repeat» _ Prop

中文:
定义 repeatEq
  签名: : 对任意 {n} (α : TypeVec n), (α otimes α) ⟹ «repeat» _ 命题
-/
def repeatEq : forall {n} (α : TypeVec n), (α otimes α) ⟹ «repeat» _ Prop
  | 0, _ => nilFun
  | succ _, α => repeatEq (drop α) ::: uncurry Eq

/--
theorem `const_append1` / 定理 `const_append1`

English:
theorem const_append1
  given: {β γ} (x : γ) {n} (α : TypeVec n)
  proof: by
  ext i : 1; cases i <;> rfl

中文:
定理 const_append1
  条件: {β γ} (x : γ) {n} (α : TypeVec n)
  证明: by
  ext i : 1; cases i <;> rfl
-/
theorem const_append1 {β γ} (x : γ) {n} (α : TypeVec n) :
    TypeVec.const x (α ::: β) = appendFun (TypeVec.const x α) fun _ => x := by
  ext i : 1; cases i <;> rfl

/--
theorem `eq_nilFun` / 定理 `eq_nilFun`

English:
theorem eq_nilFun
  given: {α β : TypeVec 0} (f : α ⟹ β)
  statement: f = nilFun
  proof: by
  ext x; cases x

中文:
定理 eq_nilFun
  条件: {α β : TypeVec 0} (f : α ⟹ β)
  结论: f = nilFun
  证明: by
  ext x; cases x
-/
theorem eq_nilFun {α β : TypeVec 0} (f : α ⟹ β) : f = nilFun := by
  ext x; cases x

/--
theorem `id_eq_nilFun` / 定理 `id_eq_nilFun`

English:
theorem id_eq_nilFun
  given: {α : TypeVec 0}
  statement: @id _ α = nilFun
  proof: by
  ext x; cases x

中文:
定理 id_eq_nilFun
  条件: {α : TypeVec 0}
  结论: @id _ α = nilFun
  证明: by
  ext x; cases x
-/
theorem id_eq_nilFun {α : TypeVec 0} : @id _ α = nilFun := by
  ext x; cases x

/--
theorem `const_nil` / 定理 `const_nil`

English:
theorem const_nil
  given: {β} (x : β) (α : TypeVec 0)
  statement: TypeVec.const x α = nilFun
  proof: by
  ext i : 1; cases i

@[typevec]

中文:
定理 const_nil
  条件: {β} (x : β) (α : TypeVec 0)
  结论: TypeVec.const x α = nilFun
  证明: by
  ext i : 1; cases i

@[typevec]
-/
theorem const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nilFun := by
  ext i : 1; cases i

@[typevec]
/--
theorem `repeat_eq_append1` / 定理 `repeat_eq_append1`

English:
theorem repeat_eq_append1
  given: {β} {n} (α : TypeVec n)
  proof: by
  induction n <;> rfl

@[typevec]

中文:
定理 repeat_eq_append1
  条件: {β} {n} (α : TypeVec n)
  证明: by
  induction n <;> rfl

@[typevec]

Depends on / 依赖: otimes
-/
theorem repeat_eq_append1 {β} {n} (α : TypeVec n) :
    repeatEq (α ::: β) = splitFun (α := (α otimes α) ::: _)
    (α' := («repeat» n Prop) ::: _) (repeatEq α) (uncurry Eq) := by
  induction n <;> rfl

@[typevec]
/--
theorem `repeat_eq_nil` / 定理 `repeat_eq_nil`

English:
theorem repeat_eq_nil
  given: (α : TypeVec 0)
  statement: repeatEq α = nilFun
  proof: by ext i; cases i

中文:
定理 repeat_eq_nil
  条件: (α : TypeVec 0)
  结论: repeatEq α = nilFun
  证明: by ext i; cases i
-/
theorem repeat_eq_nil (α : TypeVec 0) : repeatEq α = nilFun := by ext i; cases i

/--
Definition of `PredLast'` / `PredLast'` 的定义

English:
definition PredLast'
  signature: (α : TypeVec n) {β : Type*} (p : β -> Prop)
  body: splitFun (TypeVec.const True α) p

中文:
定义 PredLast'
  签名: (α : TypeVec n) {β : 类型} (p : β -> 命题)
  定义体: splitFun (TypeVec.const True α) p

Depends on / 依赖: TypeVec, TypeVec.const, splitFun
-/
def PredLast' (α : TypeVec n) {β : Type*} (p : β -> Prop) :
    (α ::: β) ⟹ «repeat» (n + 1) Prop :=
  splitFun (TypeVec.const True α) p

/--
Definition of `RelLast'` / `RelLast'` 的定义

English:
definition RelLast'
  signature: (α : TypeVec n) {β : Type*} (p : β -> β -> Prop)
  body: splitFun (repeatEq α) (uncurry p)

中文:
定义 RelLast'
  签名: (α : TypeVec n) {β : 类型} (p : β -> β -> 命题)
  定义体: splitFun (repeatEq α) (uncurry p)

Depends on / 依赖: repeatEq, splitFun, uncurry
-/
def RelLast' (α : TypeVec n) {β : Type*} (p : β -> β -> Prop) :
    (α ::: β) otimes (α ::: β) ⟹ «repeat» (n + 1) Prop :=
  splitFun (repeatEq α) (uncurry p)

/--
Definition of `Curry` / `Curry` 的定义

English:
definition Curry
  signature: (F : TypeVec.{u} (n + 1) -> Type*) (α : Type u) (β : TypeVec.{u} n)
  body: F (β ::: α)

中文:
定义 Curry
  签名: (F : TypeVec.{u} (n + 1) -> 类型) (α : 类型u) (β : TypeVec.{u} n)
  定义体: F (β ::: α)
-/
def Curry (F : TypeVec.{u} (n + 1) -> Type*) (α : Type u) (β : TypeVec.{u} n) : Type _ :=
  F (β ::: α)

/--
Instance `Curry.inhabited` / 实例 `Curry.inhabited`

English:
instance Curry.inhabited
  signature: (F : TypeVec.{u} (n + 1) -> Type*) (α : Type u) (β : TypeVec.{u} n)
  body: I

中文:
实例 Curry.inhabited
  签名: (F : TypeVec.{u} (n + 1) -> 类型) (α : 类型u) (β : TypeVec.{u} n)
  定义体: I
-/
instance Curry.inhabited (F : TypeVec.{u} (n + 1) -> Type*) (α : Type u) (β : TypeVec.{u} n)
    [I : Inhabited (F <| (β ::: α))] : Inhabited (Curry F α β) :=
  I

/--
Definition of `dropRepeat` / `dropRepeat` 的定义

English:
definition dropRepeat
  signature: (α : Type*)

中文:
定义 dropRepeat
  签名: (α : 类型)
-/
def dropRepeat (α : Type*) : forall {n}, drop («repeat» (succ n) α) ⟹ «repeat» n α
  | succ _, Fin2.fs i => dropRepeat α i
  | succ _, Fin2.fz => fun (a : α) => a

/--
Definition of `ofRepeat` / `ofRepeat` 的定义

English:
definition ofRepeat
  signature: {α : Sort _}

中文:
定义 ofRepeat
  签名: {α : Sort _}

Depends on / 依赖: c.eq
-/
def ofRepeat {α : Sort _} : forall {n i}, «repeat» n α i -> α
  | _, Fin2.fz => fun (a : α) => a
  | _, Fin2.fs i => @ofRepeat _ _ i

/--
theorem `const_iff_true` / 定理 `const_iff_true`

English:
theorem const_iff_true
  given: {α : TypeVec n} {i x p}
  statement: ofRepeat (TypeVec.const p α i x) ↔ p
  proof: by
  induction i with
  | fz => rfl
  | fs _ ih =>
    rw [TypeVec.const]
    exact ih

中文:
定理 const_iff_true
  条件: {α : TypeVec n} {i x p}
  结论: ofRepeat (TypeVec.const p α i x) ↔ p
  证明: by
  induction i with
  | fz => rfl
  | fs _ ih =>
    rw [TypeVec.const]
    exact ih

Depends on / 依赖: Quotient, Quotient.mk, TypeVec, TypeVec.const, _surjective
-/
theorem const_iff_true {α : TypeVec n} {i x p} : ofRepeat (TypeVec.const p α i x) ↔ p := by
  induction i with
  | fz => rfl
  | fs _ ih =>
    rw [TypeVec.const]
    exact ih

section

/--
Definition of `prod.fst` / `prod.fst` 的定义

English:
definition prod.fst
  signature: : forall {n} {α β : TypeVec.{u} n}, α otimes β ⟹ α

中文:
定义 prod.fst
  签名: : 对任意 {n} {α β : TypeVec.{u} n}, α otimes β ⟹ α
-/
def prod.fst : forall {n} {α β : TypeVec.{u} n}, α otimes β ⟹ α
  | succ _, α, β, Fin2.fs i => @prod.fst _ (drop α) (drop β) i
  | succ _, _, _, Fin2.fz => Prod.fst

/--
Definition of `prod.snd` / `prod.snd` 的定义

English:
definition prod.snd
  signature: : forall {n} {α β : TypeVec.{u} n}, α otimes β ⟹ β

中文:
定义 prod.snd
  签名: : 对任意 {n} {α β : TypeVec.{u} n}, α otimes β ⟹ β
-/
def prod.snd : forall {n} {α β : TypeVec.{u} n}, α otimes β ⟹ β
  | succ _, α, β, Fin2.fs i => @prod.snd _ (drop α) (drop β) i
  | succ _, _, _, Fin2.fz => Prod.snd

/--
Definition of `prod.diag` / `prod.diag` 的定义

English:
definition prod.diag
  signature: : forall {n} {α : TypeVec.{u} n}, α ⟹ α otimes α

中文:
定义 prod.diag
  签名: : 对任意 {n} {α : TypeVec.{u} n}, α ⟹ α otimes α
-/
def prod.diag : forall {n} {α : TypeVec.{u} n}, α ⟹ α otimes α
  | succ _, α, Fin2.fs _, x => @prod.diag _ (drop α) _ x
  | succ _, _, Fin2.fz, x => (x, x)

/--
Definition of `prod.mk` / `prod.mk` 的定义

English:
definition prod.mk
  signature: : forall {n} {α β : TypeVec.{u} n} (i : Fin2 n), α i -> β i -> (α otimes β) i

中文:
定义 prod.mk
  签名: : 对任意 {n} {α β : TypeVec.{u} n} (i : Fin2 n), α i -> β i -> (α otimes β) i

Depends on / 依赖: i.fs
-/
def prod.mk : forall {n} {α β : TypeVec.{u} n} (i : Fin2 n), α i -> β i -> (α otimes β) i
  | succ _, α, β, Fin2.fs i => mk (α := fun i => α i.fs) (β := fun i => β i.fs) i
  | succ _, _, _, Fin2.fz => Prod.mk

end


set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `prod_fst_mk` / 定理 `prod_fst_mk`

English:
theorem prod_fst_mk
  given: {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i)
  proof: by
  induction i with
  | fz => simp_all only [prod.fst, prod.mk]
  | fs _ i_ih => apply i_ih

中文:
定理 prod_fst_mk
  条件: {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i)
  证明: by
  induction i with
  | fz => simp_all only [prod.fst, prod.mk]
  | fs _ i_ih => apply i_ih

Depends on / 依赖: i_ih, prod.fst, prod.mk
-/
theorem prod_fst_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.fst i (prod.mk i a b) = a := by
  induction i with
  | fz => simp_all only [prod.fst, prod.mk]
  | fs _ i_ih => apply i_ih

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `prod_snd_mk` / 定理 `prod_snd_mk`

English:
theorem prod_snd_mk
  given: {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i)
  proof: by
  induction i with
  | fz => simp_all [prod.snd, prod.mk]
  | fs _ i_ih => apply i_ih

中文:
定理 prod_snd_mk
  条件: {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i)
  证明: by
  induction i with
  | fz => simp_all [prod.snd, prod.mk]
  | fs _ i_ih => apply i_ih

Depends on / 依赖: i_ih, prod.mk, prod.snd
-/
theorem prod_snd_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.snd i (prod.mk i a b) = b := by
  induction i with
  | fz => simp_all [prod.snd, prod.mk]
  | fs _ i_ih => apply i_ih

/--
Definition of `prod.map` / `prod.map` 的定义

English:
definition prod.map
  signature: : forall {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β -> α' ⟹ β' -> α otimes α' ⟹ β otimes β'

中文:
定义 prod.map
  签名: : 对任意 {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β -> α' ⟹ β' -> α otimes α' ⟹ β otimes β'
-/
protected def prod.map : forall {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β -> α' ⟹ β' -> α otimes α' ⟹ β otimes β'
  | succ _, α, α', β, β', x, y, Fin2.fs _, a =>
    @prod.map _ (drop α) (drop α') (drop β) (drop β') (dropFun x) (dropFun y) _ a
  | succ _, _, _, _, _, x, y, Fin2.fz, a => (x _ a.1, y _ a.2)



@[inherit_doc] scoped[MvFunctor] infixl:45 " otimes' " => TypeVec.prod.map

/--
theorem `fst_prod_mk` / 定理 `fst_prod_mk`

English:
theorem fst_prod_mk
  given: {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β')
  proof: by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

中文:
定理 fst_prod_mk
  条件: {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β')
  证明: by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

Depends on / 依赖: i_ih
-/
theorem fst_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.fst ⊚ (f otimes' g) = f ⊚ TypeVec.prod.fst := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

/--
theorem `snd_prod_mk` / 定理 `snd_prod_mk`

English:
theorem snd_prod_mk
  given: {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β')
  proof: by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

中文:
定理 snd_prod_mk
  条件: {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β')
  证明: by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

Depends on / 依赖: i_ih
-/
theorem snd_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.snd ⊚ (f otimes' g) = g ⊚ TypeVec.prod.snd := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

/--
theorem `fst_diag` / 定理 `fst_diag`

English:
theorem fst_diag
  given: {α : TypeVec n}
  statement: TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id
  proof: by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

中文:
定理 fst_diag
  条件: {α : TypeVec n}
  结论: TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id
  证明: by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

Depends on / 依赖: i_ih
-/
theorem fst_diag {α : TypeVec n} : TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

/--
theorem `snd_diag` / 定理 `snd_diag`

English:
theorem snd_diag
  given: {α : TypeVec n}
  statement: TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id
  proof: by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

中文:
定理 snd_diag
  条件: {α : TypeVec n}
  结论: TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id
  证明: by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

Depends on / 依赖: i_ih
-/
theorem snd_diag {α : TypeVec n} : TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih

/--
theorem `repeatEq_iff_eq` / 定理 `repeatEq_iff_eq`

English:
theorem repeatEq_iff_eq
  given: {α : TypeVec n} {i x y}
  proof: by
  induction i with
  | fz => rfl
  | fs _ i_ih =>
    rw [repeatEq]
    exact i_ih

中文:
定理 repeatEq_iff_eq
  条件: {α : TypeVec n} {i x y}
  证明: by
  induction i with
  | fz => rfl
  | fs _ i_ih =>
    rw [repeatEq]
    exact i_ih

Depends on / 依赖: i_ih, repeatEq
-/
theorem repeatEq_iff_eq {α : TypeVec n} {i x y} :
    ofRepeat (repeatEq α i (prod.mk _ x y)) ↔ x = y := by
  induction i with
  | fz => rfl
  | fs _ i_ih =>
    rw [repeatEq]
    exact i_ih

/--
Definition of `Subtype_` / `Subtype_` 的定义

English:
definition Subtype_
  signature: : forall {n} {α : TypeVec.{u} n}, (α ⟹ «repeat» n Prop) -> TypeVec n

中文:
定义 Subtype_
  签名: : 对任意 {n} {α : TypeVec.{u} n}, (α ⟹ «repeat» n 命题) -> TypeVec n
-/
def Subtype_ : forall {n} {α : TypeVec.{u} n}, (α ⟹ «repeat» n Prop) -> TypeVec n
  | _, _, p, Fin2.fz => Subtype fun x => p Fin2.fz x
  | _, _, p, Fin2.fs i => Subtype_ (dropFun p) i

/--
Definition of `subtypeVal` / `subtypeVal` 的定义

English:
definition subtypeVal
  signature: : forall {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop), Subtype_ p ⟹ α

中文:
定义 subtypeVal
  签名: : 对任意 {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n 命题), Subtype_ p ⟹ α
-/
def subtypeVal : forall {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop), Subtype_ p ⟹ α
  | succ n, _, _, Fin2.fs i => @subtypeVal n _ _ i
  | succ _, _, _, Fin2.fz => Subtype.val

/--
Definition of `toSubtype` / `toSubtype` 的定义

English:
definition toSubtype
  signature: :

中文:
定义 toSubtype
  签名: :
-/
def toSubtype :
    forall {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop),
      (fun i : Fin2 n => { x // ofRepeat <| p i x }) ⟹ Subtype_ p
  | succ _, _, p, Fin2.fs i, x => toSubtype (dropFun p) i x
  | succ _, _, _, Fin2.fz, x => x

/--
Definition of `ofSubtype` / `ofSubtype` 的定义

English:
definition ofSubtype
  signature: {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop)

中文:
定义 ofSubtype
  签名: {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n 命题)
-/
def ofSubtype {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop) :
    Subtype_ p ⟹ fun i : Fin2 n => { x // ofRepeat <| p i x }
  | Fin2.fs i, x => ofSubtype _ i x
  | Fin2.fz, x => x

/--
Definition of `toSubtype'` / `toSubtype'` 的定义

English:
definition toSubtype'
  signature: {n} {α : TypeVec.{u} n} (p : α otimes α ⟹ «repeat» n Prop)

中文:
定义 toSubtype'
  签名: {n} {α : TypeVec.{u} n} (p : α otimes α ⟹ «repeat» n 命题)
-/
def toSubtype' {n} {α : TypeVec.{u} n} (p : α otimes α ⟹ «repeat» n Prop) :
    (fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (prod.mk _ x.1 x.2) }) ⟹ Subtype_ p
  | Fin2.fs i, x => toSubtype' (dropFun p) i x
  | Fin2.fz, x => ⟨x.val, cast (by congr) x.property⟩

/--
Definition of `ofSubtype'` / `ofSubtype'` 的定义

English:
definition ofSubtype'
  signature: {n} {α : TypeVec.{u} n} (p : α otimes α ⟹ «repeat» n Prop)

中文:
定义 ofSubtype'
  签名: {n} {α : TypeVec.{u} n} (p : α otimes α ⟹ «repeat» n 命题)
-/
def ofSubtype' {n} {α : TypeVec.{u} n} (p : α otimes α ⟹ «repeat» n Prop) :
    Subtype_ p ⟹ fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (prod.mk _ x.1 x.2) }
  | Fin2.fs i, x => ofSubtype' _ i x
  | Fin2.fz, x => ⟨x.val, cast (by congr) x.property⟩

/--
Definition of `diagSub` / `diagSub` 的定义

English:
definition diagSub
  signature: {n} {α : TypeVec.{u} n}

中文:
定义 diagSub
  签名: {n} {α : TypeVec.{u} n}
-/
def diagSub {n} {α : TypeVec.{u} n} : α ⟹ Subtype_ (repeatEq α)
  | Fin2.fs _, x => @diagSub _ (drop α) _ x
  | Fin2.fz, x => ⟨(x, x), rfl⟩

/--
theorem `subtypeVal_nil` / 定理 `subtypeVal_nil`

English:
theorem subtypeVal_nil
  given: {α : TypeVec.{u} 0} (ps : α ⟹ «repeat» 0 Prop)
  proof: funext by rintro ⟨⟩

中文:
定理 subtypeVal_nil
  条件: {α : TypeVec.{u} 0} (ps : α ⟹ «repeat» 0 命题)
  证明: funext by rintro ⟨⟩
-/
theorem subtypeVal_nil {α : TypeVec.{u} 0} (ps : α ⟹ «repeat» 0 Prop) :
    TypeVec.subtypeVal ps = nilFun :=
funext by rintro ⟨⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `diag_sub_val` / 定理 `diag_sub_val`

English:
theorem diag_sub_val
  given: {n} {α : TypeVec.{u} n}
  statement: subtypeVal (repeatEq α) ⊚ diagSub = prod.diag
  proof: by
  ext i x
  induction i with
  | fz => simp only [comp, subtypeVal, diagSub, prod.diag]
  | fs _ i_ih => apply @i_ih (drop α)

中文:
定理 diag_sub_val
  条件: {n} {α : TypeVec.{u} n}
  结论: subtypeVal (repeatEq α) ⊚ diagSub = prod.diag
  证明: by
  ext i x
  induction i with
  | fz => simp only [comp, subtypeVal, diagSub, prod.diag]
  | fs _ i_ih => apply @i_ih (drop α)

Depends on / 依赖: diagSub, i_ih, prod.diag, subtypeVal
-/
theorem diag_sub_val {n} {α : TypeVec.{u} n} : subtypeVal (repeatEq α) ⊚ diagSub = prod.diag := by
  ext i x
  induction i with
  | fz => simp only [comp, subtypeVal, diagSub, prod.diag]
  | fs _ i_ih => apply @i_ih (drop α)

/--
theorem `prod_id` / 定理 `prod_id`

English:
theorem prod_id
  statement: forall {n} {α β : TypeVec.{u} n}, (id otimes' id) = (id : α otimes β ⟹ _)
  proof: by
  intros
  ext i a
  induction i with
  | fz => cases a; rfl
  | fs _ i_ih => apply i_ih

中文:
定理 prod_id
  结论: 对任意 {n} {α β : TypeVec.{u} n}, (id otimes' id) = (id : α otimes β ⟹ _)
  证明: by
  intros
  ext i a
  induction i with
  | fz => cases a; rfl
  | fs _ i_ih => apply i_ih

Depends on / 依赖: i_ih, intros
-/
theorem prod_id : forall {n} {α β : TypeVec.{u} n}, (id otimes' id) = (id : α otimes β ⟹ _) := by
  intros
  ext i a
  induction i with
  | fz => cases a; rfl
  | fs _ i_ih => apply i_ih

/--
theorem `append_prod_appendFun` / 定理 `append_prod_appendFun`

English:
theorem append_prod_appendFun
  statement: {n} {α α' β β' : TypeVec.{u} n} {φ φ' ψ ψ' : Type u}
  proof: by
  ext i a
  cases i
  · cases a
    rfl
  · rfl

中文:
定理 append_prod_appendFun
  结论: {n} {α α' β β' : TypeVec.{u} n} {φ φ' ψ ψ' : 类型u}
  证明: by
  ext i a
  cases i
  · cases a
    rfl
  · rfl
-/
theorem append_prod_appendFun {n} {α α' β β' : TypeVec.{u} n} {φ φ' ψ ψ' : Type u}
    {f₀ : α ⟹ α'} {g₀ : β ⟹ β'} {f₁ : φ -> φ'} {g₁ : ψ -> ψ'} :
    ((f₀ otimes' g₀) ::: (_root_.Prod.map f₁ g₁)) = ((f₀ ::: f₁) otimes' (g₀ ::: g₁)) := by
  ext i a
  cases i
  · cases a
    rfl
  · rfl

end Liftp'

@[simp]
/--
theorem `dropFun_diag` / 定理 `dropFun_diag`

English:
theorem dropFun_diag
  given: {α}
  statement: dropFun (@prod.diag (n + 1) α) = prod.diag
  proof: rfl

@[simp]

中文:
定理 dropFun_diag
  条件: {α}
  结论: dropFun (@prod.diag (n + 1) α) = prod.diag
  证明: rfl

@[simp]

Depends on / 依赖: CoprodI, Monoid, Monoid.CoprodI
-/
theorem dropFun_diag {α} : dropFun (@prod.diag (n + 1) α) = prod.diag := rfl

@[simp]
/--
theorem `dropFun_subtypeVal` / 定理 `dropFun_subtypeVal`

English:
theorem dropFun_subtypeVal
  given: {α} (p : α ⟹ «repeat» (n + 1) Prop)
  proof: rfl

@[simp]

中文:
定理 dropFun_subtypeVal
  条件: {α} (p : α ⟹ «repeat» (n + 1) 命题)
  证明: rfl

@[simp]

Depends on / 依赖: CoprodI, Monoid, Monoid.CoprodI
-/
theorem dropFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (subtypeVal p) = subtypeVal _ :=
  rfl

@[simp]
/--
theorem `lastFun_subtypeVal` / 定理 `lastFun_subtypeVal`

English:
theorem lastFun_subtypeVal
  given: {α} (p : α ⟹ «repeat» (n + 1) Prop)
  proof: rfl

@[simp]

中文:
定理 lastFun_subtypeVal
  条件: {α} (p : α ⟹ «repeat» (n + 1) 命题)
  证明: rfl

@[simp]
-/
theorem lastFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (subtypeVal p) = Subtype.val :=
  rfl

@[simp]
/--
theorem `dropFun_toSubtype` / 定理 `dropFun_toSubtype`

English:
theorem dropFun_toSubtype
  given: {α} (p : α ⟹ «repeat» (n + 1) Prop)
  proof: rfl

@[simp]

中文:
定理 dropFun_toSubtype
  条件: {α} (p : α ⟹ «repeat» (n + 1) 命题)
  证明: rfl

@[simp]

Depends on / 依赖: Quotient, coprodCon
-/
theorem dropFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (toSubtype p) = toSubtype _ := rfl

@[simp]
/--
theorem `lastFun_toSubtype` / 定理 `lastFun_toSubtype`

English:
theorem lastFun_toSubtype
  given: {α} (p : α ⟹ «repeat» (n + 1) Prop)
  proof: rfl

@[simp]

中文:
定理 lastFun_toSubtype
  条件: {α} (p : α ⟹ «repeat» (n + 1) 命题)
  证明: rfl

@[simp]
-/
theorem lastFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (toSubtype p) = _root_.id := rfl

@[simp]
/--
theorem `dropFun_of_subtype` / 定理 `dropFun_of_subtype`

English:
theorem dropFun_of_subtype
  given: {α} (p : α ⟹ «repeat» (n + 1) Prop)
  proof: rfl

@[simp]

中文:
定理 dropFun_of_subtype
  条件: {α} (p : α ⟹ «repeat» (n + 1) 命题)
  证明: rfl

@[simp]
-/
theorem dropFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (ofSubtype p) = ofSubtype _ := rfl

@[simp]
/--
theorem `lastFun_of_subtype` / 定理 `lastFun_of_subtype`

English:
theorem lastFun_of_subtype
  given: {α} (p : α ⟹ «repeat» (n + 1) Prop)
  proof: rfl

@[simp]

中文:
定理 lastFun_of_subtype
  条件: {α} (p : α ⟹ «repeat» (n + 1) 命题)
  证明: rfl

@[simp]
-/
theorem lastFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (ofSubtype p) = _root_.id := rfl

@[simp]
/--
theorem `dropFun_RelLast'` / 定理 `dropFun_RelLast'`

English:
theorem dropFun_RelLast'
  given: {α : TypeVec n} {β} (R : β -> β -> Prop)
  proof: rfl

中文:
定理 dropFun_RelLast'
  条件: {α : TypeVec n} {β} (R : β -> β -> 命题)
  证明: rfl
-/
theorem dropFun_RelLast' {α : TypeVec n} {β} (R : β -> β -> Prop) :
    dropFun (RelLast' α R) = repeatEq α :=
  rfl

attribute [simp] drop_append1'

@[simp]
/--
theorem `dropFun_prod` / 定理 `dropFun_prod`

English:
theorem dropFun_prod
  given: {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β')
  proof: rfl

@[simp]

中文:
定理 dropFun_prod
  条件: {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β')
  证明: rfl

@[simp]
-/
theorem dropFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    dropFun (f otimes' f') = (dropFun f otimes' dropFun f') := rfl

@[simp]
/--
theorem `lastFun_prod` / 定理 `lastFun_prod`

English:
theorem lastFun_prod
  given: {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β')
  proof: rfl

@[simp]

中文:
定理 lastFun_prod
  条件: {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β')
  证明: rfl

@[simp]
-/
theorem lastFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    lastFun (f otimes' f') = Prod.map (lastFun f) (lastFun f') := rfl

@[simp]
/--
theorem `dropFun_from_append1_drop_last` / 定理 `dropFun_from_append1_drop_last`

English:
theorem dropFun_from_append1_drop_last
  given: {α : TypeVec (n + 1)}
  proof: rfl

@[simp]

中文:
定理 dropFun_from_append1_drop_last
  条件: {α : TypeVec (n + 1)}
  证明: rfl

@[simp]
-/
theorem dropFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    dropFun (@fromAppend1DropLast _ α) = id :=
  rfl

@[simp]
/--
theorem `lastFun_from_append1_drop_last` / 定理 `lastFun_from_append1_drop_last`

English:
theorem lastFun_from_append1_drop_last
  given: {α : TypeVec (n + 1)}
  proof: rfl

@[simp]

中文:
定理 lastFun_from_append1_drop_last
  条件: {α : TypeVec (n + 1)}
  证明: rfl

@[simp]
-/
theorem lastFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    lastFun (@fromAppend1DropLast _ α) = _root_.id :=
  rfl

@[simp]
/--
theorem `dropFun_id` / 定理 `dropFun_id`

English:
theorem dropFun_id
  given: {α : TypeVec (n + 1)}
  statement: dropFun (@TypeVec.id _ α) = id
  proof: rfl

@[simp]

中文:
定理 dropFun_id
  条件: {α : TypeVec (n + 1)}
  结论: dropFun (@TypeVec.id _ α) = id
  证明: rfl

@[simp]
-/
theorem dropFun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id :=
  rfl

@[simp]
/--
theorem `prod_map_id` / 定理 `prod_map_id`

English:
theorem prod_map_id
  given: {α β : TypeVec n}
  statement: (@TypeVec.id _ α otimes' @TypeVec.id _ β) = id
  proof: prod_id

中文:
定理 prod_map_id
  条件: {α β : TypeVec n}
  结论: (@TypeVec.id _ α otimes' @TypeVec.id _ β) = id
  证明: prod_id

Depends on / 依赖: prod_id
-/
theorem prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α otimes' @TypeVec.id _ β) = id := prod_id

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toSubtype_of_subtype` / 定理 `toSubtype_of_subtype`

English:
theorem toSubtype_of_subtype
  given: {α : TypeVec n} (p : α ⟹ «repeat» n Prop)
  proof: by
  ext i x
  induction i <;> simp only [id, toSubtype, comp, ofSubtype] at *
  simp [*]

中文:
定理 toSubtype_of_subtype
  条件: {α : TypeVec n} (p : α ⟹ «repeat» n 命题)
  证明: by
  ext i x
  induction i <;> simp only [id, toSubtype, comp, ofSubtype] at *
  simp [*]

Depends on / 依赖: ofSubtype, toSubtype
-/
theorem toSubtype_of_subtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) :
    toSubtype p ⊚ ofSubtype p = id := by
  ext i x
  induction i <;> simp only [id, toSubtype, comp, ofSubtype] at *
  simp [*]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `subtypeVal_toSubtype` / 定理 `subtypeVal_toSubtype`

English:
theorem subtypeVal_toSubtype
  given: {α : TypeVec n} (p : α ⟹ «repeat» n Prop)
  proof: by
  ext i x
  induction i <;> simp only [toSubtype, comp, subtypeVal] at *
  simp [*]

中文:
定理 subtypeVal_toSubtype
  条件: {α : TypeVec n} (p : α ⟹ «repeat» n 命题)
  证明: by
  ext i x
  induction i <;> simp only [toSubtype, comp, subtypeVal] at *
  simp [*]

Depends on / 依赖: subtypeVal, toSubtype
-/
theorem subtypeVal_toSubtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) :
    subtypeVal p ⊚ toSubtype p = fun _ => Subtype.val := by
  ext i x
  induction i <;> simp only [toSubtype, comp, subtypeVal] at *
  simp [*]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toSubtype_of_subtype_assoc` / 定理 `toSubtype_of_subtype_assoc`

English:
theorem toSubtype_of_subtype_assoc
  proof: by
  rw [← comp_assoc]; rw [toSubtype_of_subtype]; simp

中文:
定理 toSubtype_of_subtype_assoc
  证明: by
  rw [← comp_assoc]; rw [toSubtype_of_subtype]; simp

Depends on / 依赖: comp_assoc, toSubtype_of_subtype
-/
theorem toSubtype_of_subtype_assoc
    {α β : TypeVec n} (p : α ⟹ «repeat» n Prop) (f : β ⟹ Subtype_ p) :
    @toSubtype n _ p ⊚ ofSubtype _ ⊚ f = f := by
  rw [← comp_assoc]; rw [toSubtype_of_subtype]; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toSubtype'_of_subtype'` / 定理 `toSubtype'_of_subtype'`

English:
theorem toSubtype'_of_subtype'
  given: {α : TypeVec n} (r : α otimes α ⟹ «repeat» n Prop)
  proof: by
  ext i x
  induction i
  <;> dsimp only [id, toSubtype', comp, ofSubtype'] at *
  <;> simp [*]

中文:
定理 toSubtype'_of_subtype'
  条件: {α : TypeVec n} (r : α otimes α ⟹ «repeat» n 命题)
  证明: by
  ext i x
  induction i
  <;> dsimp only [id, toSubtype', comp, ofSubtype'] at *
  <;> simp [*]

Depends on / 依赖: ofSubtype, toSubtype
-/
theorem toSubtype'_of_subtype' {α : TypeVec n} (r : α otimes α ⟹ «repeat» n Prop) :
    toSubtype' r ⊚ ofSubtype' r = id := by
  ext i x
  induction i
  <;> dsimp only [id, toSubtype', comp, ofSubtype'] at *
  <;> simp [*]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `subtypeVal_toSubtype'` / 定理 `subtypeVal_toSubtype'`

English:
theorem subtypeVal_toSubtype'
  given: {α : TypeVec n} (r : α otimes α ⟹ «repeat» n Prop)
  proof: by
  ext i x
  induction i <;> simp only [toSubtype', comp, subtypeVal, prod.mk] at *
  simp [*]

中文:
定理 subtypeVal_toSubtype'
  条件: {α : TypeVec n} (r : α otimes α ⟹ «repeat» n 命题)
  证明: by
  ext i x
  induction i <;> simp only [toSubtype', comp, subtypeVal, prod.mk] at *
  simp [*]

Depends on / 依赖: prod.mk, subtypeVal, toSubtype
-/
theorem subtypeVal_toSubtype' {α : TypeVec n} (r : α otimes α ⟹ «repeat» n Prop) :
    subtypeVal r ⊚ toSubtype' r = fun i x => prod.mk i x.1.fst x.1.snd := by
  ext i x
  induction i <;> simp only [toSubtype', comp, subtypeVal, prod.mk] at *
  simp [*]

end TypeVec
