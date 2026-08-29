/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.Push

/-!
# `lrat_proof` command

Defines a macro for producing SAT proofs from CNF / LRAT files.
These files are commonly used in the SAT community for writing proofs.

Most SAT solvers support export to [DRAT](https://arxiv.org/abs/1610.06229) format,
but this format can be expensive to reconstruct because it requires recomputing all
unit propagation steps. The [LRAT](https://arxiv.org/abs/1612.02353) format solves this
issue by attaching a proof to the deduction of each new clause.
(The L in LRAT stands for Linear time verification.)
There are several verified checkers for the LRAT format, and the program implemented here
makes it possible to use the lean kernel as an LRAT checker as well and expose the results
as a standard propositional theorem.

The input to the `lrat_proof` command is the name of the theorem to define,
and the statement (written in CNF format) and the proof (in LRAT format).
For example:
```
lrat_proof foo
  "p cnf 2 4 1 2 0 -1 2 0 1 -2 0 -1 -2 0"
  "5 -2 0 4 3 0 5 d 3 4 0 6 1 0 5 1 0 6 d 1 0 7 0 5 2 6 0"
```
produces a theorem:
```
foo : ∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1
```

* You can see the theorem statement by hovering over the word `foo`.
* You can use the `example` keyword in place of `foo` to avoid generating a theorem.
* You can use the `include_str` macro in place of the two strings
  to load CNF / LRAT files from disk.
-/

@[expose] public meta section

open Lean hiding Literal
open Std (HashMap)

namespace Sat

/--
Inductive type `Literal` / 归纳类型 `Literal`

English:
inductive Literal
  constructors (2):
    - pos: Nat -> Literal
    - neg: Nat -> Literal

中文:
归纳类型 Literal
  构造子 (2 个):
    - pos: 自然数 -> Literal
    - neg: 自然数 -> Literal
-/
inductive Literal
  | pos : Nat -> Literal
  | neg : Nat -> Literal

/--
Definition of `Literal.ofInt` / `Literal.ofInt` 的定义

English:
definition Literal.ofInt
  signature: (i : Int)
  body: if i < 0 then Literal.neg (-i-1).toNat else Literal.pos (i-1).toNat

中文:
定义 Literal.ofInt
  签名: (i : 整数)
  定义体: if i < 0 then Literal.neg (-i-1).toNat else Literal.pos (i-1).toNat

Depends on / 依赖: Literal, Literal.neg, Literal.pos
-/
def Literal.ofInt (i : Int) : Literal :=
  if i < 0 then Literal.neg (-i-1).toNat else Literal.pos (i-1).toNat

/--
Definition of `Literal.negate` / `Literal.negate` 的定义

English:
definition Literal.negate
  signature: : Literal -> Literal

中文:
定义 Literal.negate
  签名: : Literal -> Literal
-/
def Literal.negate : Literal -> Literal
  | pos i => neg i
  | neg i => pos i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ToExpr Literal
  body: mkConst ``Literal
  toExpr
  | Literal.pos i => mkApp (mkConst ``Literal.pos) (mkRawNatLit i)
  | Literal.neg i => mkApp (mkConst ``Literal.neg) (mkRawNatLit i)

中文:
实例 :
  签名: ToExpr Literal
  定义体: mkConst ``Literal
  toExpr
  | Literal.pos i => mkApp (mkConst ``Literal.pos) (mkRawNatLit i)
  | Literal.neg i => mkApp (mkConst ``Literal.neg) (mkRawNatLit i)

Depends on / 依赖: Literal, mkConst
-/
instance : ToExpr Literal where
  toTypeExpr := mkConst ``Literal
  toExpr
  | Literal.pos i => mkApp (mkConst ``Literal.pos) (mkRawNatLit i)
  | Literal.neg i => mkApp (mkConst ``Literal.neg) (mkRawNatLit i)

/--
Definition of `Clause` / `Clause` 的定义

English:
definition Clause
  body: List Literal

中文:
定义 Clause
  定义体: List Literal

Depends on / 依赖: Literal
-/
def Clause := List Literal

/--
Definition of `Clause.nil` / `Clause.nil` 的定义

English:
definition Clause.nil
  signature: : Clause
  body: []

中文:
定义 Clause.nil
  签名: : Clause
  定义体: []
-/
def Clause.nil : Clause := []

/--
Definition of `Clause.cons` / `Clause.cons` 的定义

English:
definition Clause.cons
  signature: : Literal -> Clause -> Clause
  body: List.cons

中文:
定义 Clause.cons
  签名: : Literal -> Clause -> Clause
  定义体: List.cons

Depends on / 依赖: List.cons
-/
def Clause.cons : Literal -> Clause -> Clause := List.cons

/--
Definition of `Fmla` / `Fmla` 的定义

English:
abbreviation Fmla
  body: List Clause

中文:
缩写 Fmla
  定义体: List Clause

Depends on / 依赖: Clause
-/
abbrev Fmla := List Clause

/--
Definition of `Fmla.one` / `Fmla.one` 的定义

English:
definition Fmla.one
  signature: (c : Clause)
  body: [c]

中文:
定义 Fmla.one
  签名: (c : Clause)
  定义体: [c]
-/
def Fmla.one (c : Clause) : Fmla := [c]

/--
Definition of `Fmla.and` / `Fmla.and` 的定义

English:
definition Fmla.and
  signature: (a b : Fmla)
  body: a ++ b

中文:
定义 Fmla.and
  签名: (a b : Fmla)
  定义体: a ++ b
-/
def Fmla.and (a b : Fmla) : Fmla := a ++ b

/--
Definition of `Fmla.subsumes` / `Fmla.subsumes` 的定义

English:
structure Fmla.subsumes
  parameters: (f f' : Fmla)
  axioms and operations (1):
    - prop : forall x, x in f' -> x in f

中文:
结构 Fmla.subsumes
  参数: (f f' : Fmla)
  公理与运算 (1 个):
    - prop : 对任意 x, x in f' -> x in f
-/
structure Fmla.subsumes (f f' : Fmla) : Prop where
  prop : forall x, x in f' -> x in f

/--
theorem `Fmla.subsumes_self` / 定理 `Fmla.subsumes_self`

English:
theorem Fmla.subsumes_self
  given: (f : Fmla)
  statement: f.subsumes f
  proof: ⟨fun _ h => h⟩

中文:
定理 Fmla.subsumes_self
  条件: (f : Fmla)
  结论: f.subsumes f
  证明: ⟨fun _ h => h⟩
-/
theorem Fmla.subsumes_self (f : Fmla) : f.subsumes f := ⟨fun _ h => h⟩
/--
theorem `Fmla.subsumes_left` / 定理 `Fmla.subsumes_left`

English:
theorem Fmla.subsumes_left
  given: (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂))
  statement: f.subsumes f₁
  proof: ⟨fun _ h => H.1 _ List.mem_append.2 Or.inl h⟩

中文:
定理 Fmla.subsumes_left
  条件: (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂))
  结论: f.subsumes f₁
  证明: ⟨fun _ h => H.1 _ List.mem_append.2 Or.inl h⟩

Depends on / 依赖: List.mem_append, Or.inl, mem_append
-/
theorem Fmla.subsumes_left (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂)) : f.subsumes f₁ :=
⟨fun _ h => H.1 _ List.mem_append.2 Or.inl h⟩
/--
theorem `Fmla.subsumes_right` / 定理 `Fmla.subsumes_right`

English:
theorem Fmla.subsumes_right
  given: (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂))
  statement: f.subsumes f₂
  proof: ⟨fun _ h => H.1 _ List.mem_append.2 Or.inr h⟩

中文:
定理 Fmla.subsumes_right
  条件: (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂))
  结论: f.subsumes f₂
  证明: ⟨fun _ h => H.1 _ List.mem_append.2 Or.inr h⟩

Depends on / 依赖: List.mem_append, Or.inr, mem_append
-/
theorem Fmla.subsumes_right (f f₁ f₂ : Fmla) (H : f.subsumes (f₁.and f₂)) : f.subsumes f₂ :=
⟨fun _ h => H.1 _ List.mem_append.2 Or.inr h⟩

/--
Definition of `Valuation` / `Valuation` 的定义

English:
definition Valuation
  body: Nat -> Prop

中文:
定义 Valuation
  定义体: Nat -> Prop
-/
def Valuation := Nat -> Prop

/--
Definition of `Valuation.neg` / `Valuation.neg` 的定义

English:
definition Valuation.neg
  signature: (v : Valuation)

中文:
定义 Valuation.neg
  签名: (v : Valuation)
-/
def Valuation.neg (v : Valuation) : Literal -> Prop
  | Literal.pos i => ¬ v i
  | Literal.neg i => v i

/--
Definition of `Valuation.satisfies` / `Valuation.satisfies` 的定义

English:
definition Valuation.satisfies
  signature: (v : Valuation)

中文:
定义 Valuation.satisfies
  签名: (v : Valuation)
-/
def Valuation.satisfies (v : Valuation) : Clause -> Prop
  | [] => False
  | l::c => v.neg l -> v.satisfies c
termination_by structural ps => ps

/--
Definition of `Valuation.satisfies_fmla` / `Valuation.satisfies_fmla` 的定义

English:
structure Valuation.satisfies_fmla
  parameters: (v : Valuation) (f : Fmla)
  axioms and operations (1):
    - prop : forall c, c in f -> v.satisfies c

中文:
结构 Valuation.satisfies_fmla
  参数: (v : Valuation) (f : Fmla)
  公理与运算 (1 个):
    - prop : 对任意 c, c in f -> v.satisfies c
-/
structure Valuation.satisfies_fmla (v : Valuation) (f : Fmla) : Prop where
  prop : forall c, c in f -> v.satisfies c

/--
Definition of `Fmla.proof` / `Fmla.proof` 的定义

English:
definition Fmla.proof
  signature: (f : Fmla) (c : Clause)
  body: forall v : Valuation, v.satisfies_fmla f -> v.satisfies c

中文:
定义 Fmla.proof
  签名: (f : Fmla) (c : Clause)
  定义体: forall v : Valuation, v.satisfies_fmla f -> v.satisfies c

Depends on / 依赖: Valuation, satisfies, satisfies_fmla, v.satisfies, v.satisfies_fmla
-/
def Fmla.proof (f : Fmla) (c : Clause) : Prop :=
  forall v : Valuation, v.satisfies_fmla f -> v.satisfies c

/--
theorem `Fmla.proof_of_subsumes` / 定理 `Fmla.proof_of_subsumes`

English:
theorem Fmla.proof_of_subsumes
  statement: {f : Fmla} {c : Clause}
  proof: fun _ h => h.1 _ H.1 _ List.Mem.head ..

中文:
定理 Fmla.proof_of_subsumes
  结论: {f : Fmla} {c : Clause}
  证明: fun _ h => h.1 _ H.1 _ List.Mem.head ..

Depends on / 依赖: List.Mem.head
-/
theorem Fmla.proof_of_subsumes {f : Fmla} {c : Clause}
    (H : Fmla.subsumes f (Fmla.one c)) : f.proof c :=
fun _ h => h.1 _ H.1 _ List.Mem.head ..

/--
theorem `Valuation.by_cases` / 定理 `Valuation.by_cases`

English:
theorem Valuation.by_cases
  statement: {v : Valuation} {l}
  proof: match l with
| Literal.pos _ => h₂ h₁
| Literal.neg _ => h₁ h₂

中文:
定理 Valuation.by_cases
  结论: {v : Valuation} {l}
  证明: match l with
| Literal.pos _ => h₂ h₁
| Literal.neg _ => h₁ h₂

Depends on / 依赖: Literal, Literal.neg, Literal.pos
-/
theorem Valuation.by_cases {v : Valuation} {l}
    (h₁ : v.neg l.negate -> False) (h₂ : v.neg l -> False) : False :=
match l with
| Literal.pos _ => h₂ h₁
| Literal.neg _ => h₁ h₂

/--
Definition of `Valuation.implies` / `Valuation.implies` 的定义

English:
definition Valuation.implies
  signature: (v : Valuation) (p : Prop)

中文:
定义 Valuation.implies
  签名: (v : Valuation) (p : 命题)
-/
def Valuation.implies (v : Valuation) (p : Prop) : List Prop -> Nat -> Prop
  | [], _ => p
  | a::as, n => (v n ↔ a) -> v.implies p as (n + 1)
termination_by structural ps => ps

/--
Definition of `Valuation.mk` / `Valuation.mk` 的定义

English:
definition Valuation.mk
  signature: : List Prop -> Valuation

中文:
定义 Valuation.mk
  签名: : List 命题 -> Valuation
-/
def Valuation.mk : List Prop -> Valuation
  | [], _ => False
  | a::_, 0 => a
  | _::as, n + 1 => mk as n
termination_by structural ps => ps

/--
theorem `Valuation.mk_implies` / 定理 `Valuation.mk_implies`

English:
theorem Valuation.mk_implies
  given: {p} {as ps} (as₁)
  statement: as = List.reverseAux as₁ ps ->
  proof: by
  induction ps generalizing as₁ with
  | nil => exact fun _ => id
  | cons a as ih =>
    refine fun e H => @ih (a::as₁) e (H ?_)
    subst e; clear ih H
    suffices forall n n', n' = List.length as₁ + n ->
      forall bs, mk (as₁.reverseAux bs) n' ↔ mk bs n from this 0 _ rfl (a::as)
    induct

中文:
定理 Valuation.mk_implies
  条件: {p} {as ps} (as₁)
  结论: as = List.reverseAux as₁ ps ->
  证明: by
  induction ps generalizing as₁ with
  | nil => exact fun _ => id
  | cons a as ih =>
    refine fun e H => @ih (a::as₁) e (H ?_)
    subst e; clear ih H
    suffices forall n n', n' = List.length as₁ + n ->
      forall bs, mk (as₁.reverseAux bs) n' ↔ mk bs n from this 0 _ rfl (a::as)
    induct

Depends on / 依赖: List.length, Nat.succ_add, generalizing, length, reverseAux, succ_add
-/
theorem Valuation.mk_implies {p} {as ps} (as₁) : as = List.reverseAux as₁ ps ->
    (Valuation.mk as).implies p ps as₁.length -> p := by
  induction ps generalizing as₁ with
  | nil => exact fun _ => id
  | cons a as ih =>
    refine fun e H => @ih (a::as₁) e (H ?_)
    subst e; clear ih H
    suffices forall n n', n' = List.length as₁ + n ->
      forall bs, mk (as₁.reverseAux bs) n' ↔ mk bs n from this 0 _ rfl (a::as)
    induction as₁ with
    | nil => simp
    | cons b as₁ ih => simpa using! fun n bs => ih (n + 1) _ (Nat.succ_add ..) _

/--
Definition of `Fmla.reify` / `Fmla.reify` 的定义

English:
structure Fmla.reify
  parameters: (v : Valuation) (f : Fmla) (p : Prop)
  axioms and operations (1):
    - prop : ¬ v.satisfies_fmla f -> p

中文:
结构 Fmla.reify
  参数: (v : Valuation) (f : Fmla) (p : 命题)
  公理与运算 (1 个):
    - prop : ¬ v.satisfies_fmla f -> p
-/
structure Fmla.reify (v : Valuation) (f : Fmla) (p : Prop) : Prop where
  prop : ¬ v.satisfies_fmla f -> p

variable {v : Valuation}

/--
theorem `Fmla.refute` / 定理 `Fmla.refute`

English:
theorem Fmla.refute
  statement: {p : Prop} {ps} (f : Fmla) (hf : f.proof [])
  proof: (Valuation.mk_implies [] rfl (hv _)).1 (hf _)

中文:
定理 Fmla.refute
  结论: {p : 命题} {ps} (f : Fmla) (hf : f.proof [])
  证明: (Valuation.mk_implies [] rfl (hv _)).1 (hf _)

Depends on / 依赖: Valuation, Valuation.mk_implies, mk_implies
-/
theorem Fmla.refute {p : Prop} {ps} (f : Fmla) (hf : f.proof [])
    (hv : forall v, Valuation.implies v (Fmla.reify v f p) ps 0) : p :=
  (Valuation.mk_implies [] rfl (hv _)).1 (hf _)

/--
theorem `Fmla.reify_or` / 定理 `Fmla.reify_or`

English:
theorem Fmla.reify_or
  statement: {f₁ : Fmla} {a : Prop} {f₂ : Fmla} {b : Prop}
  proof: by
  refine ⟨fun H => by_contra fun hn => H ⟨fun c h => by_contra fun hn' => ?_⟩⟩
  rcases List.mem_append.1 h with h | h
· exact hn Or.inl h₁.1 fun Hc => hn' Hc.1 _ h
· exact hn Or.inr h₂.1 fun Hc => hn' Hc.1 _ h

中文:
定理 Fmla.reify_or
  结论: {f₁ : Fmla} {a : 命题} {f₂ : Fmla} {b : 命题}
  证明: by
  refine ⟨fun H => by_contra fun hn => H ⟨fun c h => by_contra fun hn' => ?_⟩⟩
  rcases List.mem_append.1 h with h | h
· exact hn Or.inl h₁.1 fun Hc => hn' Hc.1 _ h
· exact hn Or.inr h₂.1 fun Hc => hn' Hc.1 _ h

Depends on / 依赖: List.mem_append, Or.inl, Or.inr, mem_append
-/
theorem Fmla.reify_or {f₁ : Fmla} {a : Prop} {f₂ : Fmla} {b : Prop}
    (h₁ : Fmla.reify v f₁ a) (h₂ : Fmla.reify v f₂ b) : Fmla.reify v (f₁.and f₂) (a ∨ b) := by
  refine ⟨fun H => by_contra fun hn => H ⟨fun c h => by_contra fun hn' => ?_⟩⟩
  rcases List.mem_append.1 h with h | h
· exact hn Or.inl h₁.1 fun Hc => hn' Hc.1 _ h
· exact hn Or.inr h₂.1 fun Hc => hn' Hc.1 _ h

/--
Definition of `Clause.reify` / `Clause.reify` 的定义

English:
structure Clause.reify
  parameters: (v : Valuation) (c : Clause) (p : Prop)
  axioms and operations (1):
    - prop : ¬ v.satisfies c -> p

中文:
结构 Clause.reify
  参数: (v : Valuation) (c : Clause) (p : 命题)
  公理与运算 (1 个):
    - prop : ¬ v.satisfies c -> p
-/
structure Clause.reify (v : Valuation) (c : Clause) (p : Prop) : Prop where
  prop : ¬ v.satisfies c -> p

/--
theorem `Fmla.reify_one` / 定理 `Fmla.reify_one`

English:
theorem Fmla.reify_one
  given: {c : Clause} {a : Prop} (h : Clause.reify v c a)
  proof: ⟨fun H => h.1 fun h => H ⟨fun | _, List.Mem.head .. => h⟩⟩

中文:
定理 Fmla.reify_one
  条件: {c : Clause} {a : 命题} (h : Clause.reify v c a)
  证明: ⟨fun H => h.1 fun h => H ⟨fun | _, List.Mem.head .. => h⟩⟩

Depends on / 依赖: List.Mem.head
-/
theorem Fmla.reify_one {c : Clause} {a : Prop} (h : Clause.reify v c a) :
    Fmla.reify v (Fmla.one c) a :=
  ⟨fun H => h.1 fun h => H ⟨fun | _, List.Mem.head .. => h⟩⟩

/--
Definition of `Literal.reify` / `Literal.reify` 的定义

English:
structure Literal.reify
  parameters: (v : Valuation) (l : Literal) (p : Prop)
  axioms and operations (1):
    - prop : v.neg l -> p

中文:
结构 Literal.reify
  参数: (v : Valuation) (l : Literal) (p : 命题)
  公理与运算 (1 个):
    - prop : v.neg l -> p
-/
structure Literal.reify (v : Valuation) (l : Literal) (p : Prop) : Prop where
  prop : v.neg l -> p

/--
theorem `Clause.reify_and` / 定理 `Clause.reify_and`

English:
theorem Clause.reify_and
  statement: {l : Literal} {a : Prop} {c : Clause} {b : Prop}
  proof: ⟨fun H => ⟨h₁.1 (by_contra fun hn => H hn.elim), h₂.1 fun h => H fun _ => h⟩⟩

中文:
定理 Clause.reify_and
  结论: {l : Literal} {a : 命题} {c : Clause} {b : 命题}
  证明: ⟨fun H => ⟨h₁.1 (by_contra fun hn => H hn.elim), h₂.1 fun h => H fun _ => h⟩⟩

Depends on / 依赖: hn.elim
-/
theorem Clause.reify_and {l : Literal} {a : Prop} {c : Clause} {b : Prop}
    (h₁ : Literal.reify v l a) (h₂ : Clause.reify v c b) :
    Clause.reify v (Clause.cons l c) (a ∧ b) :=
  ⟨fun H => ⟨h₁.1 (by_contra fun hn => H hn.elim), h₂.1 fun h => H fun _ => h⟩⟩

/--
theorem `Clause.reify_zero` / 定理 `Clause.reify_zero`

English:
theorem Clause.reify_zero
  statement: Clause.reify v Clause.nil True
  proof: ⟨fun _ => trivial⟩

中文:
定理 Clause.reify_zero
  结论: Clause.reify v Clause.nil True
  证明: ⟨fun _ => trivial⟩
-/
theorem Clause.reify_zero : Clause.reify v Clause.nil True := ⟨fun _ => trivial⟩

/--
theorem `Clause.reify_one` / 定理 `Clause.reify_one`

English:
theorem Clause.reify_one
  statement: {l : Literal} {a : Prop}
  proof: ⟨fun H => ((Clause.reify_and h₁ Clause.reify_zero).1 H).1⟩

中文:
定理 Clause.reify_one
  结论: {l : Literal} {a : 命题}
  证明: ⟨fun H => ((Clause.reify_and h₁ Clause.reify_zero).1 H).1⟩

Depends on / 依赖: Clause, Clause.reify_and, Clause.reify_zero, reify_and, reify_zero
-/
theorem Clause.reify_one {l : Literal} {a : Prop}
    (h₁ : Literal.reify v l a) : Clause.reify v (Clause.nil.cons l) a :=
  ⟨fun H => ((Clause.reify_and h₁ Clause.reify_zero).1 H).1⟩

/--
theorem `Literal.reify_pos` / 定理 `Literal.reify_pos`

English:
theorem Literal.reify_pos
  given: {a : Prop} {n : Nat} (h : v n ↔ a)
  statement: (Literal.pos n).reify v ¬a
  proof: ⟨mt h.2⟩

中文:
定理 Literal.reify_pos
  条件: {a : 命题} {n : 自然数} (h : v n ↔ a)
  结论: (Literal.pos n).reify v ¬a
  证明: ⟨mt h.2⟩
-/
theorem Literal.reify_pos {a : Prop} {n : Nat} (h : v n ↔ a) : (Literal.pos n).reify v ¬a := ⟨mt h.2⟩

/--
theorem `Literal.reify_neg` / 定理 `Literal.reify_neg`

English:
theorem Literal.reify_neg
  given: {a : Prop} {n : Nat} (h : v n ↔ a)
  statement: (Literal.neg n).reify v a
  proof: ⟨h.1⟩

中文:
定理 Literal.reify_neg
  条件: {a : 命题} {n : 自然数} (h : v n ↔ a)
  结论: (Literal.neg n).reify v a
  证明: ⟨h.1⟩
-/
theorem Literal.reify_neg {a : Prop} {n : Nat} (h : v n ↔ a) : (Literal.neg n).reify v a := ⟨h.1⟩

end Sat

namespace Mathlib.Tactic.Sat

/--
Definition of `Clause` / `Clause` 的定义

English:
structure Clause
  parameters: where
  axioms and operations (3):
    - lits : Array Int
    - expr : Expr
    - proof : Expr

中文:
结构 Clause
  参数: where
  公理与运算 (3 个):
    - lits : Array 整数
    - expr : Expr
    - proof : Expr
-/
structure Clause where
  /-- The list of literals as read from the input file -/
  lits : Array Int
  /-- The clause expression of type `Clause` -/
  expr : Expr
  /-- A proof of `⊢ ctx.proof c`.
  Note that we do not use `have` statements to cache these proofs:
  this is literally the proof expression itself. As a result, the proof terms
  rely heavily on dag-like sharing of the expression, and printing these proof terms
  directly is likely to crash lean for larger examples. -/
  proof : Expr

/--
Definition of `buildClause` / `buildClause` 的定义

English:
definition buildClause
  signature: (arr : Array Int)
  body: let nil := mkConst ``Sat.Clause.nil
  let cons := mkConst ``Sat.Clause.cons
  arr.foldr (fun i e => mkApp2 cons (toExpr <| Sat.Literal.ofInt i) e) nil

中文:
定义 buildClause
  签名: (arr : Array 整数)
  定义体: let nil := mkConst ``Sat.Clause.nil
  let cons := mkConst ``Sat.Clause.cons
  arr.foldr (fun i e => mkApp2 cons (toExpr <| Sat.Literal.ofInt i) e) nil

Depends on / 依赖: CategoryTheory, CategoryTheory.Sheaf, Clause, IsGrothendieckAbelian, Literal, Sat.Clause.cons, Sat.Clause.nil, Sat.Literal.ofInt, arr.foldr, mkApp2, mkConst, toExpr
-/
def buildClause (arr : Array Int) : Expr :=
  let nil := mkConst ``Sat.Clause.nil
  let cons := mkConst ``Sat.Clause.cons
  arr.foldr (fun i e => mkApp2 cons (toExpr <| Sat.Literal.ofInt i) e) nil

/--
Definition of `buildConj` / `buildConj` 的定义

English:
definition buildConj
  signature: (arr : Array (Array Int)) (start stop : Nat)
  body: match stop - start with
  | 0 => panic! "empty"
  | 1 => mkApp (mkConst ``Sat.Fmla.one) (buildClause arr[start]!)
  | len =>
    let mid := start + len / 2
    mkApp2 (mkConst ``Sat.Fmla.and) (buildConj arr start mid) (buildConj arr mid stop)

中文:
定义 buildConj
  签名: (arr : Array (Array 整数)) (start stop : 自然数)
  定义体: match stop - start with
  | 0 => panic! "empty"
  | 1 => mkApp (mkConst ``Sat.Fmla.one) (buildClause arr[start]!)
  | len =>
    let mid := start + len / 2
    mkApp2 (mkConst ``Sat.Fmla.and) (buildConj arr start mid) (buildConj arr mid stop)

Depends on / 依赖: Additive, Functor, Functor.whiskeringLeft, OpenNhds, OpenNhds.inclusion, Presheaf, Presheaf.stalkFunctor, cat_disch, inclusion, infer_instance, stalkFunctor, whiskeringLeft
-/
partial def buildConj (arr : Array (Array Int)) (start stop : Nat) : Expr :=
  match stop - start with
  | 0 => panic! "empty"
  | 1 => mkApp (mkConst ``Sat.Fmla.one) (buildClause arr[start]!)
  | len =>
    let mid := start + len / 2
    mkApp2 (mkConst ``Sat.Fmla.and) (buildConj arr start mid) (buildConj arr mid stop)

/--
Definition of `buildClauses` / `buildClauses` 的定义

English:
definition buildClauses
  signature: (arr : Array (Array Int)) (ctx : Expr) (start stop : Nat)
  body: match stop - start with
  | 0 => panic! "empty"
  | 1 =>
    let c := f.appArg!
    let proof := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) ctx c p
    let n := accum.1 + 1
    (n, accum.2.insert n { lits := arr[start]!, expr := c, proof })
  | len =>
    let mid := start + len / 2
    let f₁ := 

中文:
定义 buildClauses
  签名: (arr : Array (Array 整数)) (ctx : Expr) (start stop : 自然数)
  定义体: match stop - start with
  | 0 => panic! "empty"
  | 1 =>
    let c := f.appArg!
    let proof := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) ctx c p
    let n := accum.1 + 1
    (n, accum.2.insert n { lits := arr[start]!, expr := c, proof })
  | len =>
    let mid := start + len / 2
    let f₁ := 
-/
partial def buildClauses (arr : Array (Array Int)) (ctx : Expr) (start stop : Nat)
    (f p : Expr) (accum : Nat × HashMap Nat Clause) : Nat × HashMap Nat Clause :=
  match stop - start with
  | 0 => panic! "empty"
  | 1 =>
    let c := f.appArg!
    let proof := mkApp3 (mkConst ``Sat.Fmla.proof_of_subsumes) ctx c p
    let n := accum.1 + 1
    (n, accum.2.insert n { lits := arr[start]!, expr := c, proof })
  | len =>
    let mid := start + len / 2
    let f₁ := f.appFn!.appArg!
    let f₂ := f.appArg!
    let p₁ := mkApp4 (mkConst ``Sat.Fmla.subsumes_left) ctx f₁ f₂ p
    let p₂ := mkApp4 (mkConst ``Sat.Fmla.subsumes_right) ctx f₁ f₂ p
    let accum := buildClauses arr ctx start mid f₁ p₁ accum
    buildClauses arr ctx mid stop f₂ p₂ accum

/--
Definition of `LClause` / `LClause` 的定义

English:
structure LClause
  parameters: where
  axioms and operations (3):
    - lits : Array Int
    - expr : Expr
    - depth : Nat

中文:
结构 LClause
  参数: where
  公理与运算 (3 个):
    - lits : Array 整数
    - expr : Expr
    - depth : 自然数

Depends on / 依赖: clause
-/
structure LClause where
  /-- The list of literals as read from the input file -/
  lits : Array Int
  /-- The clause expression of type `Clause` -/
  expr : Expr
  /-- The bound variable index of the hypothesis asserting `⊢ ctx.proof c`,
  _counting from the outside and 1-based_. (We use this numbering because we will need to
  reference the variable from multiple binder depths.) -/
  depth : Nat

/--
Definition of `buildProofStep` / `buildProofStep` 的定义

English:
definition buildProofStep
  signature: (db : HashMap Nat Clause)
  body: Id.run do
  let mut lams := #[]
  let mut args := #[]
  let mut gctx : HashMap Nat LClause := {}
  -- step 1
  for i in pf do
    let i := i.natAbs
    let some cl := db[i]? | return Except.error "missing clause"
    if !gctx.contains i then
      lams := lams.push (mkApp2 (mkConst ``Sat.Fmla.proof)

中文:
定义 buildProofStep
  签名: (db : HashMap 自然数 Clause)
  定义体: Id.run do
  let mut lams := #[]
  let mut args := #[]
  let mut gctx : HashMap Nat LClause := {}
  -- step 1
  for i in pf do
    let i := i.natAbs
    let some cl := db[i]? | return Except.error "missing clause"
    if !gctx.contains i then
      lams := lams.push (mkApp2 (mkConst ``Sat.Fmla.proof)
-/
partial def buildProofStep (db : HashMap Nat Clause)
    (ns pf : Array Int) (ctx clause : Expr) : Except String Expr := Id.run do
  let mut lams := #[]
  let mut args := #[]
  let mut gctx : HashMap Nat LClause := {}
  -- step 1
  for i in pf do
    let i := i.natAbs
    let some cl := db[i]? | return Except.error "missing clause"
    if !gctx.contains i then
      lams := lams.push (mkApp2 (mkConst ``Sat.Fmla.proof) ctx cl.expr)
      args := args.push cl.proof
      gctx := gctx.insert i {
        lits := cl.lits
        expr := cl.expr
        depth := args.size
      }
  let n := args.size
  -- step 2
  let mut f :=
    (mkAppN · args) ∘
    lams.foldr (mkLambda `c default) ∘
    mkLambda `v default (mkConst ``Sat.Valuation) ∘
    mkLambda `hv default (mkApp2 (mkConst ``Sat.Valuation.satisfies_fmla) (mkBVar 0) ctx)
  let v depth := mkBVar (depth + 1)
  let hv depth := mkBVar depth
  lams := #[]
  let mut clause := clause
  let mut depth := 0
  let mut lctx : HashMap Int Nat := {}
  for i in ns do
    let l := clause.appFn!.appArg!
    clause := clause.appArg!
    lams := lams.push (mkApp2 (mkConst ``Sat.Valuation.neg) (v depth) l)
    depth := depth.succ
    lctx := lctx.insert i depth
  f := f ∘ lams.foldr (mkLambda `h default)
  -- step 3
  for (step : Int) in pf do
    if step < 0 then return Except.error "unimplemented: RAT step"
    let some cl := gctx[step.toNat]? | return Except.error "missing clause"
    let mut unit := none
    for i in cl.lits do
      unless lctx.contains i do
        if unit.isSome then return Except.error s!"not unit: {cl.lits}"
        depth := depth.succ
        unit := some i
    let mut pr := mkApp2 (mkBVar (depth + n + 2 - cl.depth)) (v depth) (hv depth)
    for i in cl.lits do
pr := mkApp pr mkBVar (match lctx[i]? with | some k => depth - k | _ => 0)
let some u := unit | return Except.ok f pr
let lit := toExpr Sat.Literal.ofInt u
let nlit := toExpr Sat.Literal.ofInt (-u)
    let d1 := depth-1
let app := mkApp3 (mkConst ``Sat.Valuation.by_cases) (v d1) nlit
      mkLambda `h default (mkApp2 (mkConst ``Sat.Valuation.neg) (v d1) lit) pr
    let dom := mkApp2 (mkConst ``Sat.Valuation.neg) (v d1) nlit
f := fun e => f mkApp app mkLambda `h default dom e
    lctx := lctx.insert (-u) depth
  return Except.error s!"no refutation: {ns}, {pf}, {lctx.toList}"

/--
Inductive type `LRATStep` / 归纳类型 `LRATStep`

English:
inductive LRATStep
  constructors (2):
    - /--: An addition step, with the clause ID, the clause literal list, and the proof trace -/ add (id : Nat) (lits : Array Int) (proof : Array Int) : LRATStep
    - /--: A (multiple) deletion step, which deletes all the listed clause IDs from the context -/ del (ids : Array Nat) : LRATStep

中文:
归纳类型 LRATStep
  构造子 (2 个):
    - /--: An addition step, with the clause ID, the clause literal list, and the proof trace -/ add (id : 自然数) (lits : Array 整数) (proof : Array 整数) : LRATStep
    - /--: A (multiple) deletion step, which deletes all the listed clause IDs from the context -/ del (ids : Array 自然数) : LRATStep
-/
inductive LRATStep
  | /-- An addition step, with the clause ID, the clause literal list, and the proof trace -/
    add (id : Nat) (lits : Array Int) (proof : Array Int) : LRATStep
  | /-- A (multiple) deletion step, which deletes all the listed clause IDs from the context -/
    del (ids : Array Nat) : LRATStep

/--
Definition of `buildProof` / `buildProof` 的定义

English:
definition buildProof
  signature: (arr : Array (Array Int)) (ctx ctx' : Expr)
  body: do
  let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db := (buildClauses arr ctx 0 arr.size ctx' p default).2
  for step in steps do
    match step with
    | LRATStep.del ds => db := ds.foldl (·.erase ·) db
    | LRATStep.add i ns pf =>
      let e := buildClause ns
      match buil

中文:
定义 buildProof
  签名: (arr : Array (Array 整数)) (ctx ctx' : Expr)
  定义体: do
  let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db := (buildClauses arr ctx 0 arr.size ctx' p default).2
  for step in steps do
    match step with
    | LRATStep.del ds => db := ds.foldl (·.erase ·) db
    | LRATStep.add i ns pf =>
      let e := buildClause ns
      match buil
-/
partial def buildProof (arr : Array (Array Int)) (ctx ctx' : Expr)
    (steps : Array LRATStep) : MetaM Expr := do
  let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db := (buildClauses arr ctx 0 arr.size ctx' p default).2
  for step in steps do
    match step with
    | LRATStep.del ds => db := ds.foldl (·.erase ·) db
    | LRATStep.add i ns pf =>
      let e := buildClause ns
      match buildProofStep db ns pf ctx e with
      | Except.ok proof =>
        if ns.isEmpty then return proof
        db := db.insert i { lits := ns, expr := e, proof }
      | Except.error msg => throwError msg
  throwError "failed to prove empty clause"

/--
Definition of `buildReify` / `buildReify` 的定义

English:
definition buildReify
  signature: (ctx ctx' proof : Expr) (nvars : Nat)
  body: Id.run do
  let (e, pr) := reifyFmla ctx'
  let mut pr := pr
  for i in [0:nvars] do
    let j := nvars-i-1
    let ty := mkApp2 (mkConst ``Iff) (mkApp (mkBVar j) (mkRawNatLit j)) (mkBVar nvars)
    pr := mkLambda `h default ty pr
  pr := mkLambda `v default (mkConst ``Sat.Valuation) pr
  let mut e 

中文:
定义 buildReify
  签名: (ctx ctx' proof : Expr) (nvars : 自然数)
  定义体: Id.run do
  let (e, pr) := reifyFmla ctx'
  let mut pr := pr
  for i in [0:nvars] do
    let j := nvars-i-1
    let ty := mkApp2 (mkConst ``Iff) (mkApp (mkBVar j) (mkRawNatLit j)) (mkBVar nvars)
    pr := mkLambda `h default ty pr
  pr := mkLambda `v default (mkConst ``Sat.Valuation) pr
  let mut e 
-/
partial def buildReify (ctx ctx' proof : Expr) (nvars : Nat) : Expr × Expr := Id.run do
  let (e, pr) := reifyFmla ctx'
  let mut pr := pr
  for i in [0:nvars] do
    let j := nvars-i-1
    let ty := mkApp2 (mkConst ``Iff) (mkApp (mkBVar j) (mkRawNatLit j)) (mkBVar nvars)
    pr := mkLambda `h default ty pr
  pr := mkLambda `v default (mkConst ``Sat.Valuation) pr
  let mut e := e.lowerLooseBVars (nvars+1) (nvars+1)
  let cons := mkApp (mkConst ``List.cons [.zero]) (mkSort .zero)
  let nil := mkApp (mkConst ``List.nil [.zero]) (mkSort .zero)
  let rec mkPS depth e
  | 0 => e
  | n + 1 => mkPS (depth+1) (mkApp2 cons (mkBVar depth) e) n
  pr := mkApp5 (mkConst ``Sat.Fmla.refute) e (mkPS 0 nil nvars) ctx proof pr
  for _ in [0:nvars] do
    e := mkForall `a default (mkSort .zero) e
    pr := mkLambda `a default (mkSort .zero) pr
  pure (e, pr)
where
  /-- The `v` variable under the `a1 ... an, v, h1 ... hn` context -/
  v := mkBVar nvars
  /-- Returns `a` and `pr : reify v f a` given a formula `f` -/
  reifyFmla f :=
    match f.getAppFn.constName! with
    | ``Sat.Fmla.and =>
      let f₁ := f.appFn!.appArg!
      let f₂ := f.appArg!
      let (e₁, h₁) := reifyFmla f₁
      let (e₂, h₂) := reifyFmla f₂
      (mkApp2 (mkConst ``Or) e₁ e₂, mkApp7 (mkConst ``Sat.Fmla.reify_or) v f₁ e₁ f₂ e₂ h₁ h₂)
    | ``Sat.Fmla.one =>
      let c := f.appArg!
      let (e, h) := reifyClause c
      (e, mkApp4 (mkConst ``Sat.Fmla.reify_one) v c e h)
    | _ => panic! "not a valid formula"
  /-- Returns `a` and `pr : reify v c a` given a clause `c` -/
  reifyClause c :=
    if c.appFn!.isConst then
      (mkConst ``True, mkApp (mkConst ``Sat.Clause.reify_zero) v)
    else reifyClause1 c
  /-- Returns `a` and `pr : reify v c a` given a nonempty clause `c` -/
  reifyClause1 c :=
    let l := c.appFn!.appArg!
    let c := c.appArg!
    let (e₁, h₁) := reifyLiteral l
    if c.isConst then
      (e₁, mkApp4 (mkConst ``Sat.Clause.reify_one) v l e₁ h₁)
    else
      let (e₂, h₂) := reifyClause1 c
      (mkApp2 (mkConst ``And) e₁ e₂, mkApp7 (mkConst ``Sat.Clause.reify_and) v l e₁ c e₂ h₁ h₂)
  /-- Returns `a` and `pr : reify v l a` given a literal `c` -/
  reifyLiteral l :=
    let n := l.appArg!
    let (e, h) := reifyVar n
    match l.appFn!.constName! with
    | ``Sat.Literal.pos =>
      (mkApp (mkConst ``Not) e, mkApp4 (mkConst ``Sat.Literal.reify_pos) v e n h)
    | ``Sat.Literal.neg =>
      (e, mkApp4 (mkConst ``Sat.Literal.reify_neg) v e n h)
    | _ => panic! "not a valid literal"
  /-- Returns `a` and `pr : v n ↔ a` given a variable index `n`.
  These are both lookups into the context
  `(a0 .. a(n-1) : Prop) (v) (h1 : v 0 ↔ a0) ... (hn : v (n-1) ↔ a(n-1))`. -/
  reifyVar v :=
    let n := v.rawNatLit?.get!
    (mkBVar (2 * nvars - n), mkBVar (nvars - n - 1))
open Lean

namespace Parser
open Lean Std.Internal.Parsec String

/--
Definition of `parseNat` / `parseNat` 的定义

English:
definition parseNat
  signature: : String.Parser Nat
  body: Json.Parser.natMaybeZero

中文:
定义 parseNat
  签名: : String.Parser 自然数
  定义体: Json.Parser.natMaybeZero

Depends on / 依赖: Json.Parser.natMaybeZero, Parser, natMaybeZero
-/
def parseNat : String.Parser Nat := Json.Parser.natMaybeZero

/--
Definition of `parseInt` / `parseInt` 的定义

English:
definition parseInt
  signature: : String.Parser Int
  body: do
if (← peek!) = '-' then skip; pure -(← parseNat) else parseNat

中文:
定义 parseInt
  签名: : String.Parser 整数
  定义体: do
if (← peek!) = '-' then skip; pure -(← parseNat) else parseNat
-/
def parseInt : String.Parser Int := do
if (← peek!) = '-' then skip; pure -(← parseNat) else parseNat

/--
Definition of `parseInts` / `parseInts` 的定义

English:
definition parseInts
  signature: (arr : Array Int := #[])
  body: do
  match ← parseInt <* ws with
  | 0 => pure arr
  | n => parseInts (arr.push n)

中文:
定义 parseInts
  签名: (arr : Array 整数 := #[])
  定义体: do
  match ← parseInt <* ws with
  | 0 => pure arr
  | n => parseInts (arr.push n)
-/
partial def parseInts (arr : Array Int := #[]) : String.Parser (Array Int) := do
  match ← parseInt <* ws with
  | 0 => pure arr
  | n => parseInts (arr.push n)

/--
Definition of `parseNats` / `parseNats` 的定义

English:
definition parseNats
  signature: (arr : Array Nat := #[])
  body: do
  match ← parseNat <* ws with
  | 0 => pure arr
  | n => parseNats (arr.push n)

中文:
定义 parseNats
  签名: (arr : Array 自然数 := #[])
  定义体: do
  match ← parseNat <* ws with
  | 0 => pure arr
  | n => parseNats (arr.push n)
-/
partial def parseNats (arr : Array Nat := #[]) : String.Parser (Array Nat) := do
  match ← parseNat <* ws with
  | 0 => pure arr
  | n => parseNats (arr.push n)

/--
Definition of `parseDimacs` / `parseDimacs` 的定义

English:
definition parseDimacs
  signature: : String.Parser (Nat × Array (Array Int))
  body: do
  pstring "p cnf" *> ws
  let nvars ← parseNat <* ws
  let nclauses ← parseNat <* ws
  let mut clauses := Array.mkEmpty nclauses
  for _ in [:nclauses] do
    clauses := clauses.push (← parseInts)
  pure (nvars, clauses)

中文:
定义 parseDimacs
  签名: : String.Parser (自然数 × Array (Array 整数))
  定义体: do
  pstring "p cnf" *> ws
  let nvars ← parseNat <* ws
  let nclauses ← parseNat <* ws
  let mut clauses := Array.mkEmpty nclauses
  for _ in [:nclauses] do
    clauses := clauses.push (← parseInts)
  pure (nvars, clauses)
-/
def parseDimacs : String.Parser (Nat × Array (Array Int)) := do
  pstring "p cnf" *> ws
  let nvars ← parseNat <* ws
  let nclauses ← parseNat <* ws
  let mut clauses := Array.mkEmpty nclauses
  for _ in [:nclauses] do
    clauses := clauses.push (← parseInts)
  pure (nvars, clauses)

/--
Definition of `parseLRAT` / `parseLRAT` 的定义

English:
definition parseLRAT
  signature: : String.Parser (Array LRATStep)
  body: many do
  let step ← parseNat <* ws
if (← peek!) = 'd' then skip <* ws; pure LRATStep.del (← parseNats)
else ws; pure LRATStep.add step (← parseInts) (← parseInts)

中文:
定义 parseLRAT
  签名: : String.Parser (Array LRATStep)
  定义体: many do
  let step ← parseNat <* ws
if (← peek!) = 'd' then skip <* ws; pure LRATStep.del (← parseNats)
else ws; pure LRATStep.add step (← parseInts) (← parseInts)
-/
def parseLRAT : String.Parser (Array LRATStep) := many do
  let step ← parseNat <* ws
if (← peek!) = 'd' then skip <* ws; pure LRATStep.del (← parseNats)
else ws; pure LRATStep.add step (← parseInts) (← parseInts)

end Parser

open Std.Internal

/--
Definition of `fromLRATAux` / `fromLRATAux` 的定义

English:
definition fromLRATAux
  signature: (cnf lrat : String) (name : Name)
  body: do
  let Parsec.ParseResult.success _ (nvars, arr) := Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx' := buildConj arr 0 arr.size
  let ctxName ← mkAuxDeclName (name ++ `ctx)
addDecl Declaration.defnDecl {
    name := c

中文:
定义 fromLRATAux
  签名: (cnf lrat : String) (name : Name)
  定义体: do
  let Parsec.ParseResult.success _ (nvars, arr) := Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx' := buildConj arr 0 arr.size
  let ctxName ← mkAuxDeclName (name ++ `ctx)
addDecl Declaration.defnDecl {
    name := c
-/
def fromLRATAux (cnf lrat : String) (name : Name) : MetaM (Nat × Expr × Expr × Expr) := do
  let Parsec.ParseResult.success _ (nvars, arr) := Parser.parseDimacs ⟨_, cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx' := buildConj arr 0 arr.size
  let ctxName ← mkAuxDeclName (name ++ `ctx)
addDecl Declaration.defnDecl {
    name := ctxName
    levelParams := []
    type := mkConst ``Sat.Fmla
    value := ctx'
    hints := ReducibilityHints.regular 0
    safety := DefinitionSafety.safe
  }
  let ctx := mkConst ctxName
  let Parsec.ParseResult.success _ steps := Parser.parseLRAT ⟨_, lrat.startPos⟩
    | throwError "parse LRAT failed"
  let proof ← buildProof arr ctx ctx' steps
  let declName ← mkAuxDeclName (name ++ `proof)
addDecl Declaration.thmDecl {
    name := declName
    levelParams := []
    type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx (buildClause #[])
    value := proof
  }
  return (nvars, ctx, ctx', mkConst declName)

/--
Definition of `fromLRAT` / `fromLRAT` 的定义

English:
definition fromLRAT
  signature: (cnf lrat : String) (name : Name)
  body: do
  let (nvars, ctx, ctx', proof) ← fromLRATAux cnf lrat name
  let (type, value) := buildReify ctx ctx' proof nvars
addDecl Declaration.thmDecl { name, levelParams := [], type, value }

中文:
定义 fromLRAT
  签名: (cnf lrat : String) (name : Name)
  定义体: do
  let (nvars, ctx, ctx', proof) ← fromLRATAux cnf lrat name
  let (type, value) := buildReify ctx ctx' proof nvars
addDecl Declaration.thmDecl { name, levelParams := [], type, value }
-/
def fromLRAT (cnf lrat : String) (name : Name) : MetaM Unit := do
  let (nvars, ctx, ctx', proof) ← fromLRATAux cnf lrat name
  let (type, value) := buildReify ctx ctx' proof nvars
addDecl Declaration.thmDecl { name, levelParams := [], type, value }

open Elab Term


/--
A macro for producing SAT proofs from CNF / LRAT files.
These files are commonly used in the SAT community for writing proofs.

The input to the `lrat_proof` command is the name of the theorem to define,
and the statement (written in CNF format) and the proof (in LRAT format).
For example:
```
lrat_proof foo
  "p cnf 2 4 1 2 0 -1 2 0 1 -2 0 -1 -2 0"
  "5 -2 0 4 3 0 5 d 3 4 0 6 1 0 5 1 0 6 d 1 0 7 0 5 2 6 0"
```
produces a theorem:
```
foo : ∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1
```

* You can see the theorem statement by hovering over the word `foo`.
* You can use the `example` keyword in place of `foo` to avoid generating a theorem.
* You can use the `include_str` macro in place of the two strings
  to load CNF / LRAT files from disk.
-/
elab "lrat_proof " n:(ident <|> "example")
    ppSpace cnf:term:max ppSpace lrat:term:max : command => do
  let name := (← getCurrNamespace) ++ if n.1.isIdent then n.1.getId else `_example
  Command.liftTermElabM do
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    let go := do
      fromLRAT cnf lrat name
.run' addTermInfo' n (← mkConstWithLevelParams name) (isBinder := true)
    if n.1.isIdent then go else withoutModifyingEnv go

lrat_proof example
  -- The CNF file
  "p cnf 2 4
   1 2 0
   -1 2 0
   1 -2 0
   -1 -2 0"
  -- The LRAT file
  "5 -2 0 4 3 0
   5 d 3 4 0
   6 1 0 5 1 0
   6 d 1 0
   7 0 5 2 6 0"

-- lrat_proof full2
-- (include_str "full2.cnf")
-- (include_str "full2.lrat")

/--
A macro for producing SAT proofs from CNF / LRAT files.
These files are commonly used in the SAT community for writing proofs.

The input to the `from_lrat` term syntax is two string expressions with
the statement (written in CNF format) and the proof (in LRAT format).
For example:
```
def foo := from_lrat
  "p cnf 2 4 1 2 0 -1 2 0 1 -2 0 -1 -2 0"
  "5 -2 0 4 3 0 5 d 3 4 0 6 1 0 5 1 0 6 d 1 0 7 0 5 2 6 0"
```
produces a theorem:
```
foo : ∀ (a a_1 : Prop), (¬a ∧ ¬a_1 ∨ a ∧ ¬a_1) ∨ ¬a ∧ a_1 ∨ a ∧ a_1
```

* You can use this term after `have :=` or in `def foo :=` to produce the term
  without constraining the type.
* You can use it when a specific type is expected, but it currently does not
  pay any attention to the shape of the goal and always produces the same theorem,
  so you can only use this to do alpha renaming.
* You can use the `include_str` macro in place of the two strings
  to load CNF / LRAT files from disk.
-/
elab "from_lrat " cnf:term:max ppSpace lrat:term:max : term => do
  let cnf ← unsafe evalTerm String (mkConst ``String) cnf
  let lrat ← unsafe evalTerm String (mkConst ``String) lrat
  let name ← mkAuxName `lrat
  fromLRAT cnf lrat name
  return mkConst name

example : forall (a b : Prop), (¬a ∧ ¬b ∨ a ∧ ¬b) ∨ ¬a ∧ b ∨ a ∧ b := from_lrat
  "p cnf 2 4 1 2 0 -1 2 0 1 -2 0 -1 -2 0"
  "5 -2 0 4 3 0 5 d 3 4 0 6 1 0 5 1 0 6 d 1 0 7 0 5 2 6 0"

end Sat

end Mathlib.Tactic
