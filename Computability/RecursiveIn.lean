/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve, Elan Roth
-/
module

public import Mathlib.Computability.Partrec

/-!
# Oracle computability

This file defines oracle computability using partial recursive functions.

## Main definitions

* `Nat.RecursiveIn O f`: A partial function `f : ℕ →. ℕ` is partial recursive given access to
  oracles in the set `O`.
* `RecursiveIn O f`: Lifts `Nat.RecursiveIn` to partial functions between `Primcodable` types.
* `ComputableIn O f`: A total function `f : α → σ` is computable given access to oracles in `O`.

## Main results

* `Nat.Partrec.recursiveIn`: Every partial recursive function is recursive in any oracle set.
* `partrec_iff_forall_recursiveIn_singleton`: A function is partial recursive iff it is recursive
  in every singleton oracle set.
* `recursiveIn_empty_iff`: Being recursive in the empty set is equivalent to being
  partial recursive.
* `RecursiveIn.mono`: Monotonicity of `RecursiveIn` with respect to oracle sets.

## Implementation notes

The type of partial functions recursive in a set of oracles `O` is the smallest type containing
the constant zero, the successor, left and right projections, each oracle `g ∈ O`,
and is closed under pairing, composition, primitive recursion, and μ-recursion.

## References

* [Piergiorgio Odifreddi,
  *Classical Recursion Theory: The Theory of Functions and Sets of Natural
  Numbers*][odifreddi1989]

## Tags

Computability, Oracle, Turing Degrees, Reducibility, Equivalence Relation
-/

@[expose] public section

open Encodable Primrec Nat.Partrec Part

variable {α β γ σ : Type*}

namespace Nat

/--
Inductive type `RecursiveIn` / 归纳类型 `RecursiveIn`

English:
inductive RecursiveIn
  parameters: (O : Set (Nat ->. Nat))
  constructors (9):
    - zero: Nat.RecursiveIn O fun _ => 0
    - succ: Nat.RecursiveIn O Nat.succ
    - left: Nat.RecursiveIn O fun n => (Nat.unpair n).1
    - right: Nat.RecursiveIn O fun n => (Nat.unpair n).2
    - oracle: forall g in O, Nat.RecursiveIn O g
    - pair: {f h : Nat ->. Nat} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) : Nat.RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
    - comp: {f h : Nat ->. Nat} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) : Nat.RecursiveIn O fun n => h n >>= f
    - prec: {f h : Nat ->. Nat} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) : Nat.RecursiveIn O fun p => let (a, n) := Nat.unpair p n.rec (f a) fun y IH => do let i ← IH h (Nat.pair a (Nat.pair y i))
    - rfind: {f : Nat ->. Nat} (hf : Nat.RecursiveIn O f) : Nat.RecursiveIn O fun a =>

中文:
归纳类型 RecursiveIn
  参数: (O : 集合 (自然数 ->. 自然数))
  构造子 (9 个):
    - zero: 自然数.RecursiveIn O fun _ => 0
    - succ: 自然数.RecursiveIn O 自然数.succ
    - left: 自然数.RecursiveIn O fun n => (自然数.unpair n).1
    - right: 自然数.RecursiveIn O fun n => (自然数.unpair n).2
    - oracle: 对任意 g in O, 自然数.RecursiveIn O g
    - pair: {f h : 自然数 ->. 自然数} (hf : 自然数.RecursiveIn O f) (hh : 自然数.RecursiveIn O h) : 自然数.RecursiveIn O fun n => (自然数.pair <$> f n <*> h n)
    - comp: {f h : 自然数 ->. 自然数} (hf : 自然数.RecursiveIn O f) (hh : 自然数.RecursiveIn O h) : 自然数.RecursiveIn O fun n => h n >>= f
    - prec: {f h : 自然数 ->. 自然数} (hf : 自然数.RecursiveIn O f) (hh : 自然数.RecursiveIn O h) : 自然数.RecursiveIn O fun p => let (a, n) := 自然数.unpair p n.rec (f a) fun y IH => do let i ← IH h (自然数.pair a (自然数.pair y i))
    - rfind: {f : 自然数 ->. 自然数} (hf : 自然数.RecursiveIn O f) : 自然数.RecursiveIn O fun a =>
-/
protected inductive RecursiveIn (O : Set (Nat ->. Nat)) : (Nat ->. Nat) -> Prop
  | zero : Nat.RecursiveIn O fun _ => 0
  | succ : Nat.RecursiveIn O Nat.succ
  | left : Nat.RecursiveIn O fun n => (Nat.unpair n).1
  | right : Nat.RecursiveIn O fun n => (Nat.unpair n).2
  | oracle : forall g in O, Nat.RecursiveIn O g
  | pair {f h : Nat ->. Nat} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun n => (Nat.pair <$> f n <*> h n)
  | comp {f h : Nat ->. Nat} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun n => h n >>= f
  | prec {f h : Nat ->. Nat} (hf : Nat.RecursiveIn O f) (hh : Nat.RecursiveIn O h) :
      Nat.RecursiveIn O fun p =>
        let (a, n) := Nat.unpair p
        n.rec (f a) fun y IH => do
          let i ← IH
          h (Nat.pair a (Nat.pair y i))
  | rfind {f : Nat ->. Nat} (hf : Nat.RecursiveIn O f) :
      Nat.RecursiveIn O fun a =>
Nat.rfind fun n => (fun m => m = 0) < > f (Nat.pair a n)

end Nat

/--
Definition of `RecursiveIn` / `RecursiveIn` 的定义

English:
definition RecursiveIn
  signature: {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat)) (f : α ->. σ)
  body: Nat.RecursiveIn O fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

中文:
定义 RecursiveIn
  签名: {α σ} [Primcodable α] [Primcodable σ] (O : 集合 (自然数 ->. 自然数)) (f : α ->. σ)
  定义体: Nat.RecursiveIn O fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

Depends on / 依赖: Nat.RecursiveIn, Part.bind, RecursiveIn, decode, encode
-/
def RecursiveIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat)) (f : α ->. σ) : Prop :=
  Nat.RecursiveIn O fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode

/--
lemma `RecursiveIn.iff_nat` / 引理 `RecursiveIn.iff_nat`

English:
lemma RecursiveIn.iff_nat
  given: {f : Nat ->. Nat} {O}
  statement: RecursiveIn O f ↔ Nat.RecursiveIn O f
  proof: by
  simp [RecursiveIn, Part.map_id']

中文:
引理 RecursiveIn.iff_nat
  条件: {f : 自然数 ->. 自然数} {O}
  结论: RecursiveIn O f ↔ 自然数.RecursiveIn O f
  证明: by
  simp [RecursiveIn, Part.map_id']

Depends on / 依赖: Part.map_id, RecursiveIn, map_id
-/
lemma RecursiveIn.iff_nat {f : Nat ->. Nat} {O} : RecursiveIn O f ↔ Nat.RecursiveIn O f := by
  simp [RecursiveIn, Part.map_id']

/--
Definition of `RecursiveIn₂` / `RecursiveIn₂` 的定义

English:
definition RecursiveIn₂
  signature: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
  body: RecursiveIn O (fun p : α × β => f p.1 p.2)

中文:
定义 RecursiveIn₂
  签名: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
  定义体: RecursiveIn O (fun p : α × β => f p.1 p.2)

Depends on / 依赖: RecursiveIn
-/
def RecursiveIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (Nat ->. Nat)) (f : α -> β ->. σ) : Prop :=
  RecursiveIn O (fun p : α × β => f p.1 p.2)

/--
Definition of `ComputableIn` / `ComputableIn` 的定义

English:
definition ComputableIn
  signature: {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat)) (f : α -> σ)
  body: RecursiveIn O (fun a => Part.some (f a))

中文:
定义 ComputableIn
  签名: {α σ} [Primcodable α] [Primcodable σ] (O : 集合 (自然数 ->. 自然数)) (f : α -> σ)
  定义体: RecursiveIn O (fun a => Part.some (f a))

Depends on / 依赖: Part.some, RecursiveIn
-/
def ComputableIn {α σ} [Primcodable α] [Primcodable σ] (O : Set (Nat ->. Nat)) (f : α -> σ) : Prop :=
  RecursiveIn O (fun a => Part.some (f a))

/--
Definition of `ComputableIn₂` / `ComputableIn₂` 的定义

English:
definition ComputableIn₂
  signature: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
  body: ComputableIn O (fun p : α × β => f p.1 p.2)

中文:
定义 ComputableIn₂
  签名: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
  定义体: ComputableIn O (fun p : α × β => f p.1 p.2)

Depends on / 依赖: ComputableIn
-/
def ComputableIn₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ]
    (O : Set (Nat ->. Nat)) (f : α -> β -> σ) : Prop :=
  ComputableIn O (fun p : α × β => f p.1 p.2)

namespace Nat.RecursiveIn

variable {f g : Nat ->. Nat}

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {O} (hf : Nat.RecursiveIn O f) (H : forall n, f n = g n)
  proof: (funext H : f = g) ▸ hf

中文:
定理 of_eq
  条件: {O} (hf : 自然数.RecursiveIn O f) (H : 对任意 n, f n = g n)
  证明: (funext H : f = g) ▸ hf
-/
theorem of_eq {O} (hf : Nat.RecursiveIn O f) (H : forall n, f n = g n) :
    Nat.RecursiveIn O g :=
  (funext H : f = g) ▸ hf

/--
theorem `of_eq_tot` / 定理 `of_eq_tot`

English:
theorem of_eq_tot
  statement: {g : Nat -> Nat} {O} (hf : Nat.RecursiveIn O f)
  proof: of_eq hf fun n => eq_some_iff.2 (H n)

中文:
定理 of_eq_tot
  结论: {g : 自然数 -> 自然数} {O} (hf : 自然数.RecursiveIn O f)
  证明: of_eq hf fun n => eq_some_iff.2 (H n)

Depends on / 依赖: eq_some_iff, of_eq
-/
theorem of_eq_tot {g : Nat -> Nat} {O} (hf : Nat.RecursiveIn O f)
    (H : forall n, g n in f n) : Nat.RecursiveIn O g :=
  of_eq hf fun n => eq_some_iff.2 (H n)

/--
theorem `subst` / 定理 `subst`

English:
theorem subst
  statement: {O O'} {f : Nat ->. Nat} (hf : Nat.RecursiveIn O f)
  proof: by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

中文:
定理 subst
  结论: {O O'} {f : 自然数 ->. 自然数} (hf : 自然数.RecursiveIn O f)
  证明: by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

Depends on / 依赖: oracle
-/
theorem subst {O O'} {f : Nat ->. Nat} (hf : Nat.RecursiveIn O f)
    (hO : forall g, g in O -> Nat.RecursiveIn O' g) : Nat.RecursiveIn O' f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g hg => exact hO g hg
  | pair _ _ ihf ihg => exact .pair ihf ihg
  | comp _ _ ihf ihg => exact .comp ihf ihg
  | prec _ _ ihf ihg => exact .prec ihf ihg
  | rfind _ ihf => exact .rfind ihf

/--
theorem `partrec_of_oracle` / 定理 `partrec_of_oracle`

English:
theorem partrec_of_oracle
  statement: {f : Nat ->. Nat} {O}
  proof: by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g gIn => exact hO g gIn
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

中文:
定理 partrec_of_oracle
  结论: {f : 自然数 ->. 自然数} {O}
  证明: by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g gIn => exact hO g gIn
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

Depends on / 依赖: oracle
-/
theorem partrec_of_oracle {f : Nat ->. Nat} {O}
    (hO : forall g in O, Nat.Partrec g) (hf : Nat.RecursiveIn O f) : Nat.Partrec f := by
  induction hf with
  | zero | succ | left | right => constructor
  | oracle g gIn => exact hO g gIn
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

end Nat.RecursiveIn

/--
lemma `Nat.Partrec.recursiveIn` / 引理 `Nat.Partrec.recursiveIn`

English:
lemma Nat.Partrec.recursiveIn
  given: {f : Nat ->. Nat} {O} (pF : Nat.Partrec f)
  proof: by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

中文:
引理 自然数.Partrec.recursiveIn
  条件: {f : 自然数 ->. 自然数} {O} (pF : 自然数.Partrec f)
  证明: by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih
-/
lemma Nat.Partrec.recursiveIn {f : Nat ->. Nat} {O} (pF : Nat.Partrec f) :
    Nat.RecursiveIn O f := by
  induction pF with
  | zero | succ | left | right => constructor
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | comp _ _ ih₁ ih₂ => exact .comp ih₁ ih₂
  | prec _ _ ih₁ ih₂ => exact .prec ih₁ ih₂
  | rfind _ ih => exact .rfind ih

/--
lemma `Partrec.recursiveIn` / 引理 `Partrec.recursiveIn`

English:
lemma Partrec.recursiveIn
  statement: [Primcodable α] [Primcodable σ] {f : α ->. σ} {O}
  proof: Nat.Partrec.recursiveIn hf

中文:
引理 Partrec.recursiveIn
  结论: [Primcodable α] [Primcodable σ] {f : α ->. σ} {O}
  证明: Nat.Partrec.recursiveIn hf

Depends on / 依赖: Nat.Partrec.recursiveIn, Partrec, recursiveIn
-/
lemma Partrec.recursiveIn [Primcodable α] [Primcodable σ] {f : α ->. σ} {O}
    (hf : Partrec f) : RecursiveIn O f :=
  Nat.Partrec.recursiveIn hf

/--
theorem `Nat.Primrec.recursiveIn` / 定理 `Nat.Primrec.recursiveIn`

English:
theorem Nat.Primrec.recursiveIn
  given: {O} {f : Nat -> Nat} (hf : Nat.Primrec f)
  proof: Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

中文:
定理 自然数.Primrec.recursiveIn
  条件: {O} {f : 自然数 -> 自然数} (hf : 自然数.Primrec f)
  证明: Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

Depends on / 依赖: Nat.Partrec.of_primrec, Nat.Partrec.recursiveIn, Partrec, of_primrec, recursiveIn
-/
theorem Nat.Primrec.recursiveIn {O} {f : Nat -> Nat} (hf : Nat.Primrec f) :
    Nat.RecursiveIn O (fun n => f n) :=
  Nat.Partrec.recursiveIn (Nat.Partrec.of_primrec hf)

/--
theorem `Computable.computableIn` / 定理 `Computable.computableIn`

English:
theorem Computable.computableIn
  statement: [Primcodable α] [Primcodable β] {f : α -> β} {O}
  proof: hf.partrec.recursiveIn

中文:
定理 可计算.computableIn
  结论: [Primcodable α] [Primcodable β] {f : α -> β} {O}
  证明: hf.partrec.recursiveIn

Depends on / 依赖: hf.partrec.recursiveIn, partrec, recursiveIn
-/
theorem Computable.computableIn [Primcodable α] [Primcodable β] {f : α -> β} {O}
    (hf : Computable f) : ComputableIn O f :=
  hf.partrec.recursiveIn

/--
theorem `Primrec.computableIn` / 定理 `Primrec.computableIn`

English:
theorem Primrec.computableIn
  statement: [Primcodable α] [Primcodable σ]
  proof: (Primrec.to_comp hf).computableIn

nonrec theorem Primrec₂.computableIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α -> β -> σ} {O} (hf : Primrec₂ f) : ComputableIn₂ O f :=
  hf.computableIn

中文:
定理 Primrec.computableIn
  结论: [Primcodable α] [Primcodable σ]
  证明: (Primrec.to_comp hf).computableIn

nonrec theorem Primrec₂.computableIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α -> β -> σ} {O} (hf : Primrec₂ f) : ComputableIn₂ O f :=
  hf.computableIn

Depends on / 依赖: Primrec, Primrec.to_comp, computableIn, to_comp
-/
theorem Primrec.computableIn [Primcodable α] [Primcodable σ]
    {f : α -> σ} {O} (hf : Primrec f) : ComputableIn O f :=
  (Primrec.to_comp hf).computableIn

nonrec theorem Primrec₂.computableIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α -> β -> σ} {O} (hf : Primrec₂ f) : ComputableIn₂ O f :=
  hf.computableIn

/--
theorem `ComputableIn.recursiveIn` / 定理 `ComputableIn.recursiveIn`

English:
theorem ComputableIn.recursiveIn
  statement: [Primcodable α] [Primcodable σ]
  proof: hf

中文:
定理 ComputableIn.recursiveIn
  结论: [Primcodable α] [Primcodable σ]
  证明: hf
-/
protected theorem ComputableIn.recursiveIn [Primcodable α] [Primcodable σ]
    {f : α -> σ} {O} (hf : ComputableIn O f) :
    RecursiveIn O (fun a => Part.some (f a)) := hf

/--
theorem `ComputableIn₂.recursiveIn₂` / 定理 `ComputableIn₂.recursiveIn₂`

English:
theorem ComputableIn₂.recursiveIn₂
  statement: [Primcodable α] [Primcodable β] [Primcodable σ]
  proof: hf

中文:
定理 ComputableIn₂.recursiveIn₂
  结论: [Primcodable α] [Primcodable β] [Primcodable σ]
  证明: hf
-/
protected theorem ComputableIn₂.recursiveIn₂ [Primcodable α] [Primcodable β] [Primcodable σ]
    {f : α -> β -> σ} {O} (hf : ComputableIn₂ O f) :
    RecursiveIn₂ O fun a => (f a : β ->. σ) := hf

variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]
variable {f : α ->. σ} {O : Set (Nat ->. Nat)}

namespace RecursiveIn

/--
lemma `of_eq` / 引理 `of_eq`

English:
lemma of_eq
  statement: {f g : α ->. σ} (hf : RecursiveIn O f)
  proof: (funext H : f = g) ▸ hf

中文:
引理 of_eq
  结论: {f g : α ->. σ} (hf : RecursiveIn O f)
  证明: (funext H : f = g) ▸ hf
-/
lemma of_eq {f g : α ->. σ} (hf : RecursiveIn O f)
    (H : forall x, f x = g x) : RecursiveIn O g :=
  (funext H : f = g) ▸ hf

/--
lemma `of_eq_tot` / 引理 `of_eq_tot`

English:
lemma of_eq_tot
  statement: {f : α ->. σ} {g : α -> σ}
  proof: of_eq hf fun n => eq_some_iff.2 (H n)

中文:
引理 of_eq_tot
  结论: {f : α ->. σ} {g : α -> σ}
  证明: of_eq hf fun n => eq_some_iff.2 (H n)

Depends on / 依赖: eq_some_iff, of_eq
-/
lemma of_eq_tot {f : α ->. σ} {g : α -> σ}
    (hf : RecursiveIn O f) (H : forall n, g n in f n) : RecursiveIn O (g : α ->. σ) :=
  of_eq hf fun n => eq_some_iff.2 (H n)

/--
lemma `oracle` / 引理 `oracle`

English:
lemma oracle
  statement: forall g in O, RecursiveIn O g
  proof: by
  intro g hg; rw [iff_nat]; exact .oracle g hg

中文:
引理 oracle
  结论: 对任意 g in O, RecursiveIn O g
  证明: by
  intro g hg; rw [iff_nat]; exact .oracle g hg

Depends on / 依赖: iff_nat, oracle
-/
lemma oracle : forall g in O, RecursiveIn O g := by
  intro g hg; rw [iff_nat]; exact .oracle g hg

/--
theorem `some` / 定理 `some`

English:
theorem some
  statement: RecursiveIn O (Part.some : α ->. α)
  proof: Partrec.some.recursiveIn

中文:
定理 some
  结论: RecursiveIn O (Part.some : α ->. α)
  证明: Partrec.some.recursiveIn
-/
protected theorem some : RecursiveIn O (Part.some : α ->. α) :=
  Partrec.some.recursiveIn

/--
theorem `none` / 定理 `none`

English:
theorem none
  statement: RecursiveIn O (fun _ : α => (Part.none : Part σ))
  proof: Partrec.none.recursiveIn

中文:
定理 none
  结论: RecursiveIn O (fun _ : α => (Part.none : Part σ))
  证明: Partrec.none.recursiveIn
-/
protected theorem none : RecursiveIn O (fun _ : α => (Part.none : Part σ)) :=
  Partrec.none.recursiveIn

/--
theorem `subst` / 定理 `subst`

English:
theorem subst
  statement: {O O'} {f : α ->. σ} (hf : RecursiveIn O f)
  proof: Nat.RecursiveIn.subst hf (by simpa only [RecursiveIn.iff_nat] using hO)

中文:
定理 subst
  结论: {O O'} {f : α ->. σ} (hf : RecursiveIn O f)
  证明: Nat.RecursiveIn.subst hf (by simpa only [RecursiveIn.iff_nat] using hO)

Depends on / 依赖: Nat.RecursiveIn.subst, RecursiveIn, RecursiveIn.iff_nat, iff_nat
-/
theorem subst {O O'} {f : α ->. σ} (hf : RecursiveIn O f)
    (hO : forall g, g in O -> RecursiveIn O' g) : RecursiveIn O' f :=
  Nat.RecursiveIn.subst hf (by simpa only [RecursiveIn.iff_nat] using hO)

/-- Monotonicity of `RecursiveIn` with respect to oracle sets. -/
@[gcongr]
/--
theorem `mono` / 定理 `mono`

English:
theorem mono
  given: {O₁ O₂} (hsub : O₁ subseteq O₂) (hf : RecursiveIn O₁ f)
  statement: RecursiveIn O₂ f
  proof: hf.subst (fun g hg => .oracle g (hsub hg))

中文:
定理 mono
  条件: {O₁ O₂} (hsub : O₁ subseteq O₂) (hf : RecursiveIn O₁ f)
  结论: RecursiveIn O₂ f
  证明: hf.subst (fun g hg => .oracle g (hsub hg))

Depends on / 依赖: hf.subst, oracle
-/
theorem mono {O₁ O₂} (hsub : O₁ subseteq O₂) (hf : RecursiveIn O₁ f) : RecursiveIn O₂ f :=
  hf.subst (fun g hg => .oracle g (hsub hg))

/--
theorem `partrec_of_oracle` / 定理 `partrec_of_oracle`

English:
theorem partrec_of_oracle
  proof: Nat.RecursiveIn.partrec_of_oracle (by simpa only [Partrec.nat_iff] using hO) hf

中文:
定理 partrec_of_oracle
  证明: Nat.RecursiveIn.partrec_of_oracle (by simpa only [Partrec.nat_iff] using hO) hf

Depends on / 依赖: Nat.RecursiveIn.partrec_of_oracle, Partrec, Partrec.nat_iff, RecursiveIn, nat_iff, partrec_of_oracle
-/
theorem partrec_of_oracle
    (hO : forall g in O, Partrec g) (hf : RecursiveIn O f) : Partrec f :=
  Nat.RecursiveIn.partrec_of_oracle (by simpa only [Partrec.nat_iff] using hO) hf

/--
lemma `partrec_of_const` / 引理 `partrec_of_const`

English:
lemma partrec_of_const
  given: {s} (hf : RecursiveIn {fun _ => s} f)
  statement: Partrec f
  proof: hf.partrec_of_oracle
    (fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact .const' s)

中文:
引理 partrec_of_const
  条件: {s} (hf : RecursiveIn {fun _ => s} f)
  结论: Partrec f
  证明: hf.partrec_of_oracle
    (fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact .const' s)

Depends on / 依赖: Set.mem_singleton_iff.mp, hf.partrec_of_oracle, mem_singleton_iff, partrec_of_oracle
-/
lemma partrec_of_const {s} (hf : RecursiveIn {fun _ => s} f) : Partrec f :=
  hf.partrec_of_oracle
    (fun g hg => by rw [Set.mem_singleton_iff.mp hg]; exact .const' s)

end RecursiveIn

@[simp]
/--
lemma `recursiveIn_empty_iff` / 引理 `recursiveIn_empty_iff`

English:
lemma recursiveIn_empty_iff
  proof: ⟨fun hf => hf.partrec_of_oracle (Set.forall_mem_empty.mpr ⟨⟩), fun hf => hf.recursiveIn⟩

中文:
引理 recursiveIn_empty_iff
  证明: ⟨fun hf => hf.partrec_of_oracle (Set.forall_mem_empty.mpr ⟨⟩), fun hf => hf.recursiveIn⟩

Depends on / 依赖: Set.forall_mem_empty.mpr, forall_mem_empty, hf.partrec_of_oracle, hf.recursiveIn, partrec_of_oracle, recursiveIn
-/
lemma recursiveIn_empty_iff :
    RecursiveIn {} f ↔ Partrec f :=
  ⟨fun hf => hf.partrec_of_oracle (Set.forall_mem_empty.mpr ⟨⟩), fun hf => hf.recursiveIn⟩

/--
theorem `partrec_iff_forall_recursiveIn_singleton` / 定理 `partrec_iff_forall_recursiveIn_singleton`

English:
theorem partrec_iff_forall_recursiveIn_singleton
  proof: ⟨fun hf _ => hf.recursiveIn, fun hf => (hf (fun _ => .none)).partrec_of_const⟩

中文:
定理 partrec_iff_对任意_recursiveIn_singleton
  证明: ⟨fun hf _ => hf.recursiveIn, fun hf => (hf (fun _ => .none)).partrec_of_const⟩

Depends on / 依赖: hf.recursiveIn, partrec_of_const, recursiveIn
-/
theorem partrec_iff_forall_recursiveIn_singleton :
    Partrec f ↔ forall g, RecursiveIn {g} f :=
  ⟨fun hf _ => hf.recursiveIn, fun hf => (hf (fun _ => .none)).partrec_of_const⟩

namespace ComputableIn

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (s : σ)
  statement: ComputableIn O (fun _ : α => s)
  proof: (Primrec.const s).computableIn

中文:
定理 const
  条件: (s : σ)
  结论: ComputableIn O (fun _ : α => s)
  证明: (Primrec.const s).computableIn
-/
protected theorem const (s : σ) : ComputableIn O (fun _ : α => s) :=
  (Primrec.const s).computableIn

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: ComputableIn O (@id α)
  proof: Primrec.id.computableIn

中文:
定理 id
  结论: ComputableIn O (@id α)
  证明: Primrec.id.computableIn
-/
protected theorem id : ComputableIn O (@id α) :=
  Primrec.id.computableIn

/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  statement: ComputableIn O (@Prod.fst α β)
  proof: Primrec.fst.computableIn

中文:
定理 fst
  结论: ComputableIn O (@积类型.fst α β)
  证明: Primrec.fst.computableIn
-/
protected theorem fst : ComputableIn O (@Prod.fst α β) :=
  Primrec.fst.computableIn

/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  statement: ComputableIn O (@Prod.snd α β)
  proof: Primrec.snd.computableIn

中文:
定理 snd
  结论: ComputableIn O (@积类型.snd α β)
  证明: Primrec.snd.computableIn
-/
protected theorem snd : ComputableIn O (@Prod.snd α β) :=
  Primrec.snd.computableIn

/--
theorem `unpair` / 定理 `unpair`

English:
theorem unpair
  statement: ComputableIn O Nat.unpair
  proof: Primrec.unpair.computableIn

中文:
定理 unpair
  结论: ComputableIn O 自然数.unpair
  证明: Primrec.unpair.computableIn
-/
protected theorem unpair : ComputableIn O Nat.unpair :=
  Primrec.unpair.computableIn

/--
theorem `succ` / 定理 `succ`

English:
theorem succ
  statement: ComputableIn O Nat.succ
  proof: Primrec.succ.computableIn

中文:
定理 succ
  结论: ComputableIn O 自然数.succ
  证明: Primrec.succ.computableIn
-/
protected theorem succ : ComputableIn O Nat.succ :=
  Primrec.succ.computableIn

/--
theorem `sumInl` / 定理 `sumInl`

English:
theorem sumInl
  statement: ComputableIn O (@Sum.inl α β)
  proof: Primrec.sumInl.computableIn

中文:
定理 sumInl
  结论: ComputableIn O (@和.inl α β)
  证明: Primrec.sumInl.computableIn
-/
protected theorem sumInl : ComputableIn O (@Sum.inl α β) :=
  Primrec.sumInl.computableIn

/--
theorem `sumInr` / 定理 `sumInr`

English:
theorem sumInr
  statement: ComputableIn O (@Sum.inr α β)
  proof: Primrec.sumInr.computableIn

中文:
定理 sumInr
  结论: ComputableIn O (@和.inr α β)
  证明: Primrec.sumInr.computableIn
-/
protected theorem sumInr : ComputableIn O (@Sum.inr α β) :=
  Primrec.sumInr.computableIn

end ComputableIn
