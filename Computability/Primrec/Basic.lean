/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Denumerable

/-!
# The primitive recursive functions

The primitive recursive functions are the least collection of functions
`ℕ → ℕ` which are closed under projections (using the `pair`
pairing function), composition, zero, successor, and primitive recursion
(i.e. `Nat.rec` where the motive is `C n := ℕ`).

We can extend this definition to a large class of basic types by
using canonical encodings of types as natural numbers (Gödel numbering),
which we implement through the type class `Encodable`. (More precisely,
we need that the composition of encode with decode yields a
primitive recursive function, so we have the `Primcodable` type class
for this.)

In the above, the pairing function is primitive recursive by definition.
This deviates from the textbook definition of primitive recursive functions,
which instead work with *`n`-ary* functions. We formalize the textbook
definition in `Nat.Primrec'`. `Nat.Primrec'.prim_iff` then proves it is
equivalent to our chosen formulation. For more discussion of this and
other design choices in this formalization, see [carneiro2019].

## Main definitions

- `Nat.Primrec f`: `f` is primitive recursive, for functions `f : ℕ → ℕ`
- `Primrec f`: `f` is primitive recursive, for functions between `Primcodable` types
- `Primcodable α`: well-behaved encoding of `α` into `ℕ`, i.e. one such that roundtripping through
  the encoding functions adds no computational power

## References

* [Mario Carneiro, *Formalizing computability theory via partial recursive functions*][carneiro2019]
-/

@[expose] public section

open Denumerable Encodable Function

namespace Nat

/-- Calls the given function on a pair of entries `n`, encoded via the pairing function. -/
@[simp, reducible]
/--
Definition of `unpaired` / `unpaired` 的定义

English:
definition unpaired
  signature: {α} (f : Nat -> Nat -> α) (n : Nat)
  body: f n.unpair.1 n.unpair.2

中文:
定义 unpaired
  签名: {α} (f : 自然数 -> 自然数 -> α) (n : 自然数)
  定义体: f n.unpair.1 n.unpair.2

Depends on / 依赖: n.unpair, unpair
-/
def unpaired {α} (f : Nat -> Nat -> α) (n : Nat) : α :=
  f n.unpair.1 n.unpair.2

/--
Inductive type `Primrec` / 归纳类型 `Primrec`

English:
inductive Primrec
  parameters: : (Nat -> Nat) -> Prop
  constructors (7):
    - zero: Nat.Primrec fun _ => 0
    - protected: succ : Nat.Primrec succ
    - left: Nat.Primrec fun n => n.unpair.1
    - right: Nat.Primrec fun n => n.unpair.2
    - pair: {f g} : Nat.Primrec f -> Nat.Primrec g -> Nat.Primrec fun n => pair (f n) (g n)
    - comp: {f g} : Nat.Primrec f -> Nat.Primrec g -> Nat.Primrec fun n => f (g n)
    - prec: {f g} : Nat.Primrec f -> Nat.Primrec g -> Nat.Primrec (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

中文:
归纳类型 Primrec
  参数: : (自然数 -> 自然数) -> 命题
  构造子 (7 个):
    - zero: 自然数.Primrec fun _ => 0
    - protected: succ : 自然数.Primrec succ
    - left: 自然数.Primrec fun n => n.unpair.1
    - right: 自然数.Primrec fun n => n.unpair.2
    - pair: {f g} : 自然数.Primrec f -> 自然数.Primrec g -> 自然数.Primrec fun n => pair (f n) (g n)
    - comp: {f g} : 自然数.Primrec f -> 自然数.Primrec g -> 自然数.Primrec fun n => f (g n)
    - prec: {f g} : 自然数.Primrec f -> 自然数.Primrec g -> 自然数.Primrec (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)
-/
protected inductive Primrec : (Nat -> Nat) -> Prop
  | zero : Nat.Primrec fun _ => 0
  | protected succ : Nat.Primrec succ
  | left : Nat.Primrec fun n => n.unpair.1
  | right : Nat.Primrec fun n => n.unpair.2
  | pair {f g} : Nat.Primrec f -> Nat.Primrec g -> Nat.Primrec fun n => pair (f n) (g n)
  | comp {f g} : Nat.Primrec f -> Nat.Primrec g -> Nat.Primrec fun n => f (g n)
  | prec {f g} :
      Nat.Primrec f ->
        Nat.Primrec g ->
          Nat.Primrec (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

namespace Primrec

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : forall n, f n = g n)
  statement: Nat.Primrec g
  proof: (funext H : f = g) ▸ hf

中文:
定理 of_eq
  条件: {f g : 自然数 -> 自然数} (hf : 自然数.Primrec f) (H : 对任意 n, f n = g n)
  结论: 自然数.Primrec g
  证明: (funext H : f = g) ▸ hf
-/
theorem of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : forall n, f n = g n) : Nat.Primrec g :=
  (funext H : f = g) ▸ hf

/--
theorem `const` / 定理 `const`

English:
theorem const
  statement: forall n : Nat, Nat.Primrec fun _ => n

中文:
定理 const
  结论: 对任意 n : 自然数, 自然数.Primrec fun _ => n

Depends on / 依赖: left.pair, of_eq
-/
theorem const : forall n : Nat, Nat.Primrec fun _ => n
  | 0 => zero
  | n + 1 => Primrec.succ.comp (const n)

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: Nat.Primrec id
  proof: (left.pair right).of_eq fun n => by simp

中文:
定理 id
  结论: 自然数.Primrec id
  证明: (left.pair right).of_eq fun n => by simp
-/
protected theorem id : Nat.Primrec id :=
  (left.pair right).of_eq fun n => by simp

/--
theorem `prec1` / 定理 `prec1`

English:
theorem prec1
  given: {f} (m : Nat) (hf : Nat.Primrec f)
  proof: ((prec (const m) (hf.comp right)).comp (zero.pair Primrec.id)).of_eq fun n => by simp

中文:
定理 prec1
  条件: {f} (m : 自然数) (hf : 自然数.Primrec f)
  证明: ((prec (const m) (hf.comp right)).comp (zero.pair Primrec.id)).of_eq fun n => by simp

Depends on / 依赖: Primrec, Primrec.id, hf.comp, of_eq, zero.pair
-/
theorem prec1 {f} (m : Nat) (hf : Nat.Primrec f) :
Nat.Primrec fun n => n.rec m fun y IH => f Nat.pair y IH :=
  ((prec (const m) (hf.comp right)).comp (zero.pair Primrec.id)).of_eq fun n => by simp

/--
theorem `casesOn1` / 定理 `casesOn1`

English:
theorem casesOn1
  given: {f} (m : Nat) (hf : Nat.Primrec f)
  statement: Nat.Primrec (Nat.casesOn · m f)
  proof: (prec1 m (hf.comp left)).of_eq by simp

中文:
定理 casesOn1
  条件: {f} (m : 自然数) (hf : 自然数.Primrec f)
  结论: 自然数.Primrec (自然数.casesOn · m f)
  证明: (prec1 m (hf.comp left)).of_eq by simp

Depends on / 依赖: hf.comp, of_eq
-/
theorem casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.Primrec (Nat.casesOn · m f) :=
(prec1 m (hf.comp left)).of_eq by simp

/--
theorem `casesOn'` / 定理 `casesOn'`

English:
theorem casesOn'
  given: {f g} (hf : Nat.Primrec f) (hg : Nat.Primrec g)
  proof: (prec hf (hg.comp (pair left (left.comp right)))).of_eq fun n => by simp

中文:
定理 casesOn'
  条件: {f g} (hf : 自然数.Primrec f) (hg : 自然数.Primrec g)
  证明: (prec hf (hg.comp (pair left (left.comp right)))).of_eq fun n => by simp

Depends on / 依赖: hg.comp, left.comp, of_eq
-/
theorem casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair z y) :=
  (prec hf (hg.comp (pair left (left.comp right)))).of_eq fun n => by simp

/--
theorem `swap` / 定理 `swap`

English:
theorem swap
  statement: Nat.Primrec (unpaired (swap Nat.pair))
  proof: (pair right left).of_eq fun n => by simp

中文:
定理 swap
  结论: 自然数.Primrec (unpaired (swap 自然数.pair))
  证明: (pair right left).of_eq fun n => by simp
-/
protected theorem swap : Nat.Primrec (unpaired (swap Nat.pair)) :=
  (pair right left).of_eq fun n => by simp

/--
theorem `swap'` / 定理 `swap'`

English:
theorem swap'
  given: {f} (hf : Nat.Primrec (unpaired f))
  statement: Nat.Primrec (unpaired (swap f))
  proof: (hf.comp .swap).of_eq fun n => by simp

中文:
定理 swap'
  条件: {f} (hf : 自然数.Primrec (unpaired f))
  结论: 自然数.Primrec (unpaired (swap f))
  证明: (hf.comp .swap).of_eq fun n => by simp

Depends on / 依赖: hf.comp, of_eq
-/
theorem swap' {f} (hf : Nat.Primrec (unpaired f)) : Nat.Primrec (unpaired (swap f)) :=
  (hf.comp .swap).of_eq fun n => by simp

/--
theorem `pred` / 定理 `pred`

English:
theorem pred
  statement: Nat.Primrec pred
  proof: (casesOn1 0 Primrec.id).of_eq fun n => by cases n <;> simp [*]

中文:
定理 pred
  结论: 自然数.Primrec pred
  证明: (casesOn1 0 Primrec.id).of_eq fun n => by cases n <;> simp [*]

Depends on / 依赖: Primrec, Primrec.id, casesOn1, of_eq
-/
theorem pred : Nat.Primrec pred :=
  (casesOn1 0 Primrec.id).of_eq fun n => by cases n <;> simp [*]

/--
theorem `add` / 定理 `add`

English:
theorem add
  statement: Nat.Primrec (unpaired (· + ·))
  proof: (prec .id ((Primrec.succ.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.add_assoc]

中文:
定理 add
  结论: 自然数.Primrec (unpaired (· + ·))
  证明: (prec .id ((Primrec.succ.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.add_assoc]

Depends on / 依赖: Nat.add_assoc, Primrec, Primrec.succ.comp, add_assoc, of_eq, p.unpair, unpair
-/
theorem add : Nat.Primrec (unpaired (· + ·)) :=
  (prec .id ((Primrec.succ.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.add_assoc]

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: Nat.Primrec (unpaired (· - ·))
  proof: (prec .id ((pred.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.sub_add_eq]

中文:
定理 sub
  结论: 自然数.Primrec (unpaired (· - ·))
  证明: (prec .id ((pred.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.sub_add_eq]

Depends on / 依赖: Nat.sub_add_eq, of_eq, p.unpair, pred.comp, sub_add_eq, unpair
-/
theorem sub : Nat.Primrec (unpaired (· - ·)) :=
  (prec .id ((pred.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.sub_add_eq]

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  statement: Nat.Primrec (unpaired (· * ·))
  proof: (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, mul_succ, add_comm _ (unpair p).fst]

中文:
定理 mul
  结论: 自然数.Primrec (unpaired (· * ·))
  证明: (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, mul_succ, add_comm _ (unpair p).fst]

Depends on / 依赖: add.comp, add_comm, mul_succ, of_eq, p.unpair, right.comp, unpair
-/
theorem mul : Nat.Primrec (unpaired (· * ·)) :=
  (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, mul_succ, add_comm _ (unpair p).fst]

/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  statement: Nat.Primrec (unpaired (· ^ ·))
  proof: (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.pow_succ]

中文:
定理 pow
  结论: 自然数.Primrec (unpaired (· ^ ·))
  证明: (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.pow_succ]

Depends on / 依赖: Nat.pow_succ, mul.comp, of_eq, p.unpair, pow_succ, right.comp, unpair
-/
theorem pow : Nat.Primrec (unpaired (· ^ ·)) :=
  (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.pow_succ]

end Primrec

end Nat

/--
Definition of `Primcodable` / `Primcodable` 的定义

English:
class Primcodable
  parameters: (α : Type*)
  extends: Encodable α
  axioms and operations (1):
    - prim((α)) : Nat.Primrec fun n => Encodable.encode (decode n)

中文:
类 Primcodable
  参数: (α : 类型)
  继承: 可编码 α
  公理与运算 (1 个):
    - prim((α)) : 自然数.Primrec fun n => 可编码.encode (decode n)
-/
class Primcodable (α : Type*) extends Encodable α where
  prim (α) : Nat.Primrec fun n => Encodable.encode (decode n)

namespace Primcodable

open Nat.Primrec

instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α :=
⟨Nat.Primrec.succ.of_eq by simp⟩

/-- Builds a `Primcodable` instance from an equivalence to a `Primcodable` type. -/
@[instance_reducible]
/--
Definition of `ofEquiv` / `ofEquiv` 的定义

English:
definition ofEquiv
  signature: (α) {β} [Primcodable α] (e : β ≃ α)
  body: { __ := Encodable.ofEquiv α e
    prim := (Primcodable.prim α).of_eq fun n => by
      rw [decode_ofEquiv]
      cases (@decode α _ n) <;>
        simp [encode_ofEquiv] }

中文:
定义 ofEquiv
  签名: (α) {β} [Primcodable α] (e : β ≃ α)
  定义体: { __ := Encodable.ofEquiv α e
    prim := (Primcodable.prim α).of_eq fun n => by
      rw [decode_ofEquiv]
      cases (@decode α _ n) <;>
        simp [encode_ofEquiv] }

Depends on / 依赖: Encodable, Encodable.ofEquiv, Primcodable, Primcodable.prim, decode, decode_ofEquiv, encode_ofEquiv, ofEquiv, of_eq
-/
def ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β :=
  { __ := Encodable.ofEquiv α e
    prim := (Primcodable.prim α).of_eq fun n => by
      rw [decode_ofEquiv]
      cases (@decode α _ n) <;>
        simp [encode_ofEquiv] }

/--
Instance `empty` / 实例 `empty`

English:
instance empty
  signature: : Primcodable Empty
  body: ⟨zero⟩

中文:
实例 empty
  签名: : Primcodable 空
  定义体: ⟨zero⟩
-/
instance empty : Primcodable Empty :=
  ⟨zero⟩

/--
Instance `unit` / 实例 `unit`

English:
instance unit
  signature: : Primcodable PUnit
  body: ⟨(casesOn1 1 zero).of_eq fun n => by cases n <;> simp⟩

中文:
实例 unit
  签名: : Primcodable 命题单元
  定义体: ⟨(casesOn1 1 zero).of_eq fun n => by cases n <;> simp⟩

Depends on / 依赖: casesOn1, of_eq
-/
instance unit : Primcodable PUnit :=
  ⟨(casesOn1 1 zero).of_eq fun n => by cases n <;> simp⟩

/--
Instance `option` / 实例 `option`

English:
instance option
  signature: {α : Type*} [h : Primcodable α]
  body: ⟨(casesOn1 1 ((casesOn1 0 (.comp .succ .succ)).comp (Primcodable.prim α))).of_eq fun n => by
    cases n with
      | zero => rfl
      | succ n =>
        rw [decode_option_succ]
        cases H : @decode α _ n <;> simp [H]⟩

中文:
实例 option
  签名: {α : 类型} [h : Primcodable α]
  定义体: ⟨(casesOn1 1 ((casesOn1 0 (.comp .succ .succ)).comp (Primcodable.prim α))).of_eq fun n => by
    cases n with
      | zero => rfl
      | succ n =>
        rw [decode_option_succ]
        cases H : @decode α _ n <;> simp [H]⟩

Depends on / 依赖: Primcodable, Primcodable.prim, casesOn1, decode, decode_option_succ, of_eq
-/
instance option {α : Type*} [h : Primcodable α] : Primcodable (Option α) :=
  ⟨(casesOn1 1 ((casesOn1 0 (.comp .succ .succ)).comp (Primcodable.prim α))).of_eq fun n => by
    cases n with
      | zero => rfl
      | succ n =>
        rw [decode_option_succ]
        cases H : @decode α _ n <;> simp [H]⟩

/--
Instance `bool` / 实例 `bool`

English:
instance bool
  signature: : Primcodable Bool
  body: ⟨(casesOn1 1 (casesOn1 2 zero)).of_eq fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) => by rw [decode_ge_two] <;> simp⟩

中文:
实例 bool
  签名: : Primcodable 布尔值
  定义体: ⟨(casesOn1 1 (casesOn1 2 zero)).of_eq fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) => by rw [decode_ge_two] <;> simp⟩

Depends on / 依赖: casesOn1, decode_ge_two, of_eq
-/
instance bool : Primcodable Bool :=
  ⟨(casesOn1 1 (casesOn1 2 zero)).of_eq fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) => by rw [decode_ge_two] <;> simp⟩

end Primcodable

/--
Definition of `Primrec` / `Primrec` 的定义

English:
definition Primrec
  signature: {α β} [Primcodable α] [Primcodable β] (f : α -> β)
  body: Nat.Primrec fun n => encode ((@decode α _ n).map f)

中文:
定义 Primrec
  签名: {α β} [Primcodable α] [Primcodable β] (f : α -> β)
  定义体: Nat.Primrec fun n => encode ((@decode α _ n).map f)

Depends on / 依赖: Nat.Primrec, Primrec, decode, encode
-/
def Primrec {α β} [Primcodable α] [Primcodable β] (f : α -> β) : Prop :=
  Nat.Primrec fun n => encode ((@decode α _ n).map f)

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

/--
theorem `encode` / 定理 `encode`

English:
theorem encode
  statement: Primrec (@encode α _)
  proof: (Primcodable.prim α).of_eq fun n => by cases @decode α _ n <;> rfl

中文:
定理 encode
  结论: Primrec (@encode α _)
  证明: (Primcodable.prim α).of_eq fun n => by cases @decode α _ n <;> rfl
-/
protected theorem encode : Primrec (@encode α _) :=
  (Primcodable.prim α).of_eq fun n => by cases @decode α _ n <;> rfl

/--
theorem `decode` / 定理 `decode`

English:
theorem decode
  statement: Primrec (@decode α _)
  proof: Nat.Primrec.succ.comp (Primcodable.prim α)

中文:
定理 decode
  结论: Primrec (@decode α _)
  证明: Nat.Primrec.succ.comp (Primcodable.prim α)
-/
protected theorem decode : Primrec (@decode α _) :=
  Nat.Primrec.succ.comp (Primcodable.prim α)

/--
theorem `dom_denumerable` / 定理 `dom_denumerable`

English:
theorem dom_denumerable
  given: {α β} [Denumerable α] [Primcodable β] {f : α -> β}
  proof: ⟨fun h => (pred.comp h).of_eq fun n => by simp, fun h =>
    (Nat.Primrec.succ.comp h).of_eq fun n => by simp⟩

中文:
定理 dom_denumerable
  条件: {α β} [可枚举 α] [Primcodable β] {f : α -> β}
  证明: ⟨fun h => (pred.comp h).of_eq fun n => by simp, fun h =>
    (Nat.Primrec.succ.comp h).of_eq fun n => by simp⟩

Depends on / 依赖: Nat.Primrec.succ.comp, Primrec, of_eq, pred.comp
-/
theorem dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α -> β} :
    Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n)) :=
  ⟨fun h => (pred.comp h).of_eq fun n => by simp, fun h =>
    (Nat.Primrec.succ.comp h).of_eq fun n => by simp⟩

/--
theorem `nat_iff` / 定理 `nat_iff`

English:
theorem nat_iff
  given: {f : Nat -> Nat}
  statement: Primrec f ↔ Nat.Primrec f
  proof: dom_denumerable

中文:
定理 nat_iff
  条件: {f : 自然数 -> 自然数}
  结论: Primrec f ↔ 自然数.Primrec f
  证明: dom_denumerable

Depends on / 依赖: dom_denumerable
-/
theorem nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f :=
  dom_denumerable

/--
theorem `encdec` / 定理 `encdec`

English:
theorem encdec
  statement: Primrec fun n => encode (@decode α _ n)
  proof: nat_iff.2 (Primcodable.prim _)

中文:
定理 encdec
  结论: Primrec fun n => encode (@decode α _ n)
  证明: nat_iff.2 (Primcodable.prim _)

Depends on / 依赖: Primcodable, Primcodable.prim, nat_iff
-/
theorem encdec : Primrec fun n => encode (@decode α _ n) :=
  nat_iff.2 (Primcodable.prim _)

/--
theorem `option_some` / 定理 `option_some`

English:
theorem option_some
  statement: Primrec (@some α)
  proof: ((casesOn1 0 (Nat.Primrec.succ.comp .succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp

中文:
定理 option_some
  结论: Primrec (@some α)
  证明: ((casesOn1 0 (Nat.Primrec.succ.comp .succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp

Depends on / 依赖: Nat.Primrec.succ.comp, Primcodable, Primcodable.prim, Primrec, casesOn1, decode, of_eq
-/
theorem option_some : Primrec (@some α) :=
  ((casesOn1 0 (Nat.Primrec.succ.comp .succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {f g : α -> σ} (hf : Primrec f) (H : forall n, f n = g n)
  statement: Primrec g
  proof: (funext H : f = g) ▸ hf

中文:
定理 of_eq
  条件: {f g : α -> σ} (hf : Primrec f) (H : 对任意 n, f n = g n)
  结论: Primrec g
  证明: (funext H : f = g) ▸ hf
-/
theorem of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n = g n) : Primrec g :=
  (funext H : f = g) ▸ hf

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (x : σ)
  statement: Primrec fun _ : α => x
  proof: ((casesOn1 0 (.const (encode x).succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> rfl

中文:
定理 const
  条件: (x : σ)
  结论: Primrec fun _ : α => x
  证明: ((casesOn1 0 (.const (encode x).succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> rfl

Depends on / 依赖: Primcodable, Primcodable.prim, casesOn1, decode, encode, of_eq
-/
theorem const (x : σ) : Primrec fun _ : α => x :=
  ((casesOn1 0 (.const (encode x).succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> rfl

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: Primrec (@id α)
  proof: (Primcodable.prim α).of_eq by simp

中文:
定理 id
  结论: Primrec (@id α)
  证明: (Primcodable.prim α).of_eq by simp
-/
protected theorem id : Primrec (@id α) :=
(Primcodable.prim α).of_eq by simp

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Primrec g)
  statement: Primrec fun a => f (g a)
  proof: ((casesOn1 0 (.comp hf (pred.comp hg))).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp [encodek]

中文:
定理 comp
  条件: {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Primrec g)
  结论: Primrec fun a => f (g a)
  证明: ((casesOn1 0 (.comp hf (pred.comp hg))).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp [encodek]

Depends on / 依赖: Primcodable, Primcodable.prim, casesOn1, decode, encodek, of_eq, pred.comp
-/
theorem comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
  ((casesOn1 0 (.comp hf (pred.comp hg))).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp [encodek]

/--
theorem `succ` / 定理 `succ`

English:
theorem succ
  statement: Primrec Nat.succ
  proof: nat_iff.2 Nat.Primrec.succ

中文:
定理 succ
  结论: Primrec 自然数.succ
  证明: nat_iff.2 Nat.Primrec.succ

Depends on / 依赖: Nat.Primrec.succ, Primrec, nat_iff
-/
theorem succ : Primrec Nat.succ :=
  nat_iff.2 Nat.Primrec.succ

/--
theorem `pred` / 定理 `pred`

English:
theorem pred
  statement: Primrec Nat.pred
  proof: nat_iff.2 Nat.Primrec.pred

中文:
定理 pred
  结论: Primrec 自然数.pred
  证明: nat_iff.2 Nat.Primrec.pred

Depends on / 依赖: Nat.Primrec.pred, Primrec, nat_iff
-/
theorem pred : Primrec Nat.pred :=
  nat_iff.2 Nat.Primrec.pred

/--
theorem `encode_iff` / 定理 `encode_iff`

English:
theorem encode_iff
  given: {f : α -> σ}
  statement: (Primrec fun a => encode (f a)) ↔ Primrec f
  proof: ⟨fun h => Nat.Primrec.of_eq h fun n => by cases @decode α _ n <;> rfl, Primrec.encode.comp⟩

中文:
定理 encode_iff
  条件: {f : α -> σ}
  结论: (Primrec fun a => encode (f a)) ↔ Primrec f
  证明: ⟨fun h => Nat.Primrec.of_eq h fun n => by cases @decode α _ n <;> rfl, Primrec.encode.comp⟩

Depends on / 依赖: Nat.Primrec.of_eq, Primrec, Primrec.encode.comp, decode, encode, of_eq
-/
theorem encode_iff {f : α -> σ} : (Primrec fun a => encode (f a)) ↔ Primrec f :=
  ⟨fun h => Nat.Primrec.of_eq h fun n => by cases @decode α _ n <;> rfl, Primrec.encode.comp⟩

/--
theorem `ofNat_iff` / 定理 `ofNat_iff`

English:
theorem ofNat_iff
  given: {α β} [Denumerable α] [Primcodable β] {f : α -> β}
  proof: dom_denumerable.trans nat_iff.symm.trans encode_iff

中文:
定理 of自然数_iff
  条件: {α β} [可枚举 α] [Primcodable β] {f : α -> β}
  证明: dom_denumerable.trans nat_iff.symm.trans encode_iff

Depends on / 依赖: dom_denumerable, dom_denumerable.trans, encode_iff, nat_iff, nat_iff.symm.trans
-/
theorem ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : α -> β} :
    Primrec f ↔ Primrec fun n => f (ofNat α n) :=
dom_denumerable.trans nat_iff.symm.trans encode_iff

/--
theorem `ofNat` / 定理 `ofNat`

English:
theorem ofNat
  given: (α) [Denumerable α]
  statement: Primrec (ofNat α)
  proof: ofNat_iff.1 Primrec.id

中文:
定理 of自然数
  条件: (α) [可枚举 α]
  结论: Primrec (of自然数 α)
  证明: ofNat_iff.1 Primrec.id
-/
protected theorem ofNat (α) [Denumerable α] : Primrec (ofNat α) :=
  ofNat_iff.1 Primrec.id

/--
theorem `option_some_iff` / 定理 `option_some_iff`

English:
theorem option_some_iff
  given: {f : α -> σ}
  statement: (Primrec fun a => some (f a)) ↔ Primrec f
  proof: ⟨fun h => encode_iff.1 pred.comp encode_iff.2 h, option_some.comp⟩

中文:
定理 option_some_iff
  条件: {f : α -> σ}
  结论: (Primrec fun a => some (f a)) ↔ Primrec f
  证明: ⟨fun h => encode_iff.1 pred.comp encode_iff.2 h, option_some.comp⟩

Depends on / 依赖: encode_iff, option_some, option_some.comp, pred.comp
-/
theorem option_some_iff {f : α -> σ} : (Primrec fun a => some (f a)) ↔ Primrec f :=
⟨fun h => encode_iff.1 pred.comp encode_iff.2 h, option_some.comp⟩

/--
theorem `of_equiv` / 定理 `of_equiv`

English:
theorem of_equiv
  given: {β} {e : β ≃ α}
  proof: Primcodable.ofEquiv α e
    Primrec e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 Primrec.encode

中文:
定理 of_equiv
  条件: {β} {e : β ≃ α}
  证明: Primcodable.ofEquiv α e
    Primrec e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 Primrec.encode

Depends on / 依赖: Primcodable, Primcodable.ofEquiv, ofEquiv
-/
theorem of_equiv {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 Primrec.encode

/--
theorem `of_equiv_symm` / 定理 `of_equiv_symm`

English:
theorem of_equiv_symm
  given: {β} {e : β ≃ α}
  proof: Primcodable.ofEquiv α e
    Primrec e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show Primrec fun a => encode (e (e.symm a)) by simp [Primrec.encode])

中文:
定理 of_equiv_symm
  条件: {β} {e : β ≃ α}
  证明: Primcodable.ofEquiv α e
    Primrec e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show Primrec fun a => encode (e (e.symm a)) by simp [Primrec.encode])

Depends on / 依赖: Primcodable, Primcodable.ofEquiv, ofEquiv
-/
theorem of_equiv_symm {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show Primrec fun a => encode (e (e.symm a)) by simp [Primrec.encode])

/--
theorem `of_equiv_iff` / 定理 `of_equiv_iff`

English:
theorem of_equiv_iff
  given: {β} (e : β ≃ α) {f : σ -> β}
  proof: Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩

中文:
定理 of_equiv_iff
  条件: {β} (e : β ≃ α) {f : σ -> β}
  证明: Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩

Depends on / 依赖: Primcodable, Primcodable.ofEquiv, ofEquiv
-/
theorem of_equiv_iff {β} (e : β ≃ α) {f : σ -> β} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩

/--
theorem `of_equiv_symm_iff` / 定理 `of_equiv_symm_iff`

English:
theorem of_equiv_symm_iff
  given: {β} (e : β ≃ α) {f : σ -> α}
  proof: Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩

中文:
定理 of_equiv_symm_iff
  条件: {β} (e : β ≃ α) {f : σ -> α}
  证明: Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩

Depends on / 依赖: Primcodable, Primcodable.ofEquiv, ofEquiv
-/
theorem of_equiv_symm_iff {β} (e : β ≃ α) {f : σ -> α} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩

end Primrec

namespace Primcodable

open Nat.Primrec

/--
Instance `prod` / 实例 `prod`

English:
instance prod
  signature: {α β} [Primcodable α] [Primcodable β]
  body: ⟨((casesOn' zero ((casesOn' zero .succ).comp (pair right ((Primcodable.prim β).comp left)))).comp
          (pair right ((Primcodable.prim α).comp left))).of_eq
      fun n => by
      simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
      cases @decode α _ n.unpair.1; · simp
      cases @decode β _ n.unpair.2 <;> simp⟩

中文:
实例 乘积
  签名: {α β} [Primcodable α] [Primcodable β]
  定义体: ⟨((casesOn' zero ((casesOn' zero .succ).comp (pair right ((Primcodable.prim β).comp left)))).comp
          (pair right ((Primcodable.prim α).comp left))).of_eq
      fun n => by
      simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
      cases @decode α _ n.unpair.1; · simp
      cases @decode β _ n.unpair.2 <;> simp⟩

Depends on / 依赖: Nat.unpair_pair, Nat.unpaired, Primcodable, Primcodable.prim, casesOn, decode, decode_prod_val, n.unpair, of_eq, unpair, unpair_pair, unpaired
-/
instance prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β) :=
  ⟨((casesOn' zero ((casesOn' zero .succ).comp (pair right ((Primcodable.prim β).comp left)))).comp
          (pair right ((Primcodable.prim α).comp left))).of_eq
      fun n => by
      simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
      cases @decode α _ n.unpair.1; · simp
      cases @decode β _ n.unpair.2 <;> simp⟩

end Primcodable

namespace Primrec

variable {α : Type*} [Primcodable α]

open Nat.Primrec

/--
theorem `fst` / 定理 `fst`

English:
theorem fst
  given: {α β} [Primcodable α] [Primcodable β]
  statement: Primrec (@Prod.fst α β)
  proof: ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp left)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

中文:
定理 fst
  条件: {α β} [Primcodable α] [Primcodable β]
  结论: Primrec (@积类型.fst α β)
  证明: ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp left)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

Depends on / 依赖: Nat.Primrec.succ.comp, Nat.unpair_pair, Nat.unpaired, Primcodable, Primcodable.prim, Primrec, casesOn, decode, decode_prod_val, n.unpair, of_eq, unpair, unpair_pair, unpaired
-/
theorem fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.fst α β) :=
  ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp left)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

/--
theorem `snd` / 定理 `snd`

English:
theorem snd
  given: {α β} [Primcodable α] [Primcodable β]
  statement: Primrec (@Prod.snd α β)
  proof: ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp right)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

中文:
定理 snd
  条件: {α β} [Primcodable α] [Primcodable β]
  结论: Primrec (@积类型.snd α β)
  证明: ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp right)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

Depends on / 依赖: Nat.Primrec.succ.comp, Nat.unpair_pair, Nat.unpaired, Primcodable, Primcodable.prim, Primrec, casesOn, decode, decode_prod_val, n.unpair, of_eq, unpair, unpair_pair, unpaired
-/
theorem snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.snd α β) :=
  ((casesOn' zero
            ((casesOn' zero (Nat.Primrec.succ.comp right)).comp
              (pair right ((Primcodable.prim β).comp left)))).comp
        (pair right ((Primcodable.prim α).comp left))).of_eq
    fun n => by
    simp only [Nat.unpaired, Nat.unpair_pair, decode_prod_val]
    cases @decode α _ n.unpair.1 <;> simp
    cases @decode β _ n.unpair.2 <;> simp

/--
theorem `pair` / 定理 `pair`

English:
theorem pair
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α -> β} {g : α -> γ}
  proof: ((casesOn1 0
            (Nat.Primrec.succ.comp <|
              .pair (Nat.Primrec.pred.comp hf) (Nat.Primrec.pred.comp hg))).comp
        (Primcodable.prim α)).of_eq
    fun n => by cases @decode α _ n <;> simp [encodek]

中文:
定理 pair
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α -> β} {g : α -> γ}
  证明: ((casesOn1 0
            (Nat.Primrec.succ.comp <|
              .pair (Nat.Primrec.pred.comp hf) (Nat.Primrec.pred.comp hg))).comp
        (Primcodable.prim α)).of_eq
    fun n => by cases @decode α _ n <;> simp [encodek]

Depends on / 依赖: Nat.Primrec.pred.comp, Nat.Primrec.succ.comp, Primcodable, Primcodable.prim, Primrec, casesOn1, decode, encodek, of_eq
-/
theorem pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α -> β} {g : α -> γ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => (f a, g a) :=
  ((casesOn1 0
            (Nat.Primrec.succ.comp <|
              .pair (Nat.Primrec.pred.comp hf) (Nat.Primrec.pred.comp hg))).comp
        (Primcodable.prim α)).of_eq
    fun n => by cases @decode α _ n <;> simp [encodek]

/--
theorem `unpair` / 定理 `unpair`

English:
theorem unpair
  statement: Primrec Nat.unpair
  proof: (pair (nat_iff.2 .left) (nat_iff.2 .right)).of_eq fun n => by simp

中文:
定理 unpair
  结论: Primrec 自然数.unpair
  证明: (pair (nat_iff.2 .left) (nat_iff.2 .right)).of_eq fun n => by simp

Depends on / 依赖: nat_iff, of_eq
-/
theorem unpair : Primrec Nat.unpair :=
  (pair (nat_iff.2 .left) (nat_iff.2 .right)).of_eq fun n => by simp

/--
theorem `list_getElem?₁` / 定理 `list_getElem?₁`

English:
theorem list_getElem?₁
  statement: forall l : List α, Primrec (l[·]? : Nat -> Option α)

中文:
定理 list_getElem?₁
  结论: 对任意 l : 列表 α, Primrec (l[·]? : 自然数 -> 选项类型 α)
-/
theorem list_getElem?₁ : forall l : List α, Primrec (l[·]? : Nat -> Option α)
  | [] => dom_denumerable.2 zero
  | a :: l =>
dom_denumerable.2
      (casesOn1 (encode a).succ <| dom_denumerable.1 <| list_getElem?₁ l).of_eq fun n => by
        cases n <;> simp

end Primrec

/--
Definition of `Primrec₂` / `Primrec₂` 的定义

English:
definition Primrec₂
  signature: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β -> σ)
  body: Primrec fun p : α × β => f p.1 p.2

中文:
定义 Primrec₂
  签名: {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β -> σ)
  定义体: Primrec fun p : α × β => f p.1 p.2

Depends on / 依赖: Primrec
-/
def Primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α -> β -> σ) :=
  Primrec fun p : α × β => f p.1 p.2

/--
Definition of `PrimrecPred` / `PrimrecPred` 的定义

English:
definition PrimrecPred
  signature: {α} [Primcodable α] (p : α -> Prop)
  body: exists (_ : DecidablePred p), Primrec fun a => decide (p a)

中文:
定义 PrimrecPred
  签名: {α} [Primcodable α] (p : α -> 命题)
  定义体: exists (_ : DecidablePred p), Primrec fun a => decide (p a)

Depends on / 依赖: DecidablePred, Primrec
-/
def PrimrecPred {α} [Primcodable α] (p : α -> Prop) :=
  exists (_ : DecidablePred p), Primrec fun a => decide (p a)

/--
Definition of `PrimrecRel` / `PrimrecRel` 的定义

English:
definition PrimrecRel
  signature: {α β} [Primcodable α] [Primcodable β] (s : α -> β -> Prop)
  body: PrimrecPred fun p : α × β => s p.1 p.2

中文:
定义 PrimrecRel
  签名: {α β} [Primcodable α] [Primcodable β] (s : α -> β -> 命题)
  定义体: PrimrecPred fun p : α × β => s p.1 p.2

Depends on / 依赖: PrimrecPred
-/
def PrimrecRel {α β} [Primcodable α] [Primcodable β] (s : α -> β -> Prop) :=
  PrimrecPred fun p : α × β => s p.1 p.2

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: {f : α -> β -> σ} (hf : Primrec fun p : α × β => f p.1 p.2)
  statement: Primrec₂ f
  proof: hf

中文:
定理 mk
  条件: {f : α -> β -> σ} (hf : Primrec fun p : α × β => f p.1 p.2)
  结论: Primrec₂ f
  证明: hf
-/
theorem mk {f : α -> β -> σ} (hf : Primrec fun p : α × β => f p.1 p.2) : Primrec₂ f := hf

/--
theorem `of_eq` / 定理 `of_eq`

English:
theorem of_eq
  given: {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall a b, f a b = g a b)
  statement: Primrec₂ g
  proof: (by funext a b; apply H : f = g) ▸ hg

中文:
定理 of_eq
  条件: {f g : α -> β -> σ} (hg : Primrec₂ f) (H : 对任意 a b, f a b = g a b)
  结论: Primrec₂ g
  证明: (by funext a b; apply H : f = g) ▸ hg
-/
theorem of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall a b, f a b = g a b) : Primrec₂ g :=
  (by funext a b; apply H : f = g) ▸ hg

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (x : σ)
  statement: Primrec₂ fun (_ : α) (_ : β) => x
  proof: Primrec.const _

中文:
定理 const
  条件: (x : σ)
  结论: Primrec₂ fun (_ : α) (_ : β) => x
  证明: Primrec.const _

Depends on / 依赖: Primrec, Primrec.const
-/
theorem const (x : σ) : Primrec₂ fun (_ : α) (_ : β) => x :=
  Primrec.const _

/--
theorem `pair` / 定理 `pair`

English:
theorem pair
  statement: Primrec₂ (@Prod.mk α β)
  proof: Primrec.pair .fst .snd

中文:
定理 pair
  结论: Primrec₂ (@积类型.mk α β)
  证明: Primrec.pair .fst .snd
-/
protected theorem pair : Primrec₂ (@Prod.mk α β) :=
  Primrec.pair .fst .snd

/--
theorem `left` / 定理 `left`

English:
theorem left
  statement: Primrec₂ fun (a : α) (_ : β) => a
  proof: .fst

中文:
定理 left
  结论: Primrec₂ fun (a : α) (_ : β) => a
  证明: .fst
-/
theorem left : Primrec₂ fun (a : α) (_ : β) => a :=
  .fst

/--
theorem `right` / 定理 `right`

English:
theorem right
  statement: Primrec₂ fun (_ : α) (b : β) => b
  proof: .snd

中文:
定理 right
  结论: Primrec₂ fun (_ : α) (b : β) => b
  证明: .snd
-/
theorem right : Primrec₂ fun (_ : α) (b : β) => b :=
  .snd

/--
theorem `natPair` / 定理 `natPair`

English:
theorem natPair
  statement: Primrec₂ Nat.pair
  proof: by simp [Primrec₂, Primrec]; constructor

中文:
定理 natPair
  结论: Primrec₂ 自然数.pair
  证明: by simp [Primrec₂, Primrec]; constructor

Depends on / 依赖: Primrec
-/
theorem natPair : Primrec₂ Nat.pair := by simp [Primrec₂, Primrec]; constructor

/--
theorem `unpaired` / 定理 `unpaired`

English:
theorem unpaired
  given: {f : Nat -> Nat -> α}
  statement: Primrec (Nat.unpaired f) ↔ Primrec₂ f
  proof: ⟨fun h => by simpa using! h.comp natPair, fun h => h.comp Primrec.unpair⟩

中文:
定理 unpaired
  条件: {f : 自然数 -> 自然数 -> α}
  结论: Primrec (自然数.unpaired f) ↔ Primrec₂ f
  证明: ⟨fun h => by simpa using! h.comp natPair, fun h => h.comp Primrec.unpair⟩

Depends on / 依赖: Primrec, Primrec.unpair, h.comp, natPair, unpair
-/
theorem unpaired {f : Nat -> Nat -> α} : Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  ⟨fun h => by simpa using! h.comp natPair, fun h => h.comp Primrec.unpair⟩

/--
theorem `unpaired'` / 定理 `unpaired'`

English:
theorem unpaired'
  given: {f : Nat -> Nat -> Nat}
  statement: Nat.Primrec (Nat.unpaired f) ↔ Primrec₂ f
  proof: Primrec.nat_iff.symm.trans unpaired

中文:
定理 unpaired'
  条件: {f : 自然数 -> 自然数 -> 自然数}
  结论: 自然数.Primrec (自然数.unpaired f) ↔ Primrec₂ f
  证明: Primrec.nat_iff.symm.trans unpaired

Depends on / 依赖: Primrec, Primrec.nat_iff.symm.trans, nat_iff, unpaired
-/
theorem unpaired' {f : Nat -> Nat -> Nat} : Nat.Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  Primrec.nat_iff.symm.trans unpaired

/--
theorem `encode_iff` / 定理 `encode_iff`

English:
theorem encode_iff
  given: {f : α -> β -> σ}
  statement: (Primrec₂ fun a b => encode (f a b)) ↔ Primrec₂ f
  proof: Primrec.encode_iff

中文:
定理 encode_iff
  条件: {f : α -> β -> σ}
  结论: (Primrec₂ fun a b => encode (f a b)) ↔ Primrec₂ f
  证明: Primrec.encode_iff

Depends on / 依赖: Primrec, Primrec.encode_iff, encode_iff
-/
theorem encode_iff {f : α -> β -> σ} : (Primrec₂ fun a b => encode (f a b)) ↔ Primrec₂ f :=
  Primrec.encode_iff

/--
theorem `option_some_iff` / 定理 `option_some_iff`

English:
theorem option_some_iff
  given: {f : α -> β -> σ}
  statement: (Primrec₂ fun a b => some (f a b)) ↔ Primrec₂ f
  proof: Primrec.option_some_iff

中文:
定理 option_some_iff
  条件: {f : α -> β -> σ}
  结论: (Primrec₂ fun a b => some (f a b)) ↔ Primrec₂ f
  证明: Primrec.option_some_iff

Depends on / 依赖: Primrec, Primrec.option_some_iff, option_some_iff
-/
theorem option_some_iff {f : α -> β -> σ} : (Primrec₂ fun a b => some (f a b)) ↔ Primrec₂ f :=
  Primrec.option_some_iff

/--
theorem `ofNat_iff` / 定理 `ofNat_iff`

English:
theorem ofNat_iff
  given: {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α -> β -> σ}
  proof: (Primrec.ofNat_iff.trans <| by simp).trans unpaired

中文:
定理 of自然数_iff
  条件: {α β σ} [可枚举 α] [可枚举 β] [Primcodable σ] {f : α -> β -> σ}
  证明: (Primrec.ofNat_iff.trans <| by simp).trans unpaired

Depends on / 依赖: Primrec, Primrec.ofNat_iff.trans, ofNat_iff, unpaired
-/
theorem ofNat_iff {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α -> β -> σ} :
    Primrec₂ f ↔ Primrec₂ fun m n : Nat => f (ofNat α m) (ofNat β n) :=
  (Primrec.ofNat_iff.trans <| by simp).trans unpaired

/--
theorem `uncurry` / 定理 `uncurry`

English:
theorem uncurry
  given: {f : α -> β -> σ}
  statement: Primrec (Function.uncurry f) ↔ Primrec₂ f
  proof: by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a]; rw [b⟩ => rfl]; rfl

中文:
定理 uncurry
  条件: {f : α -> β -> σ}
  结论: Primrec (函数.uncurry f) ↔ Primrec₂ f
  证明: by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a]; rw [b⟩ => rfl]; rfl

Depends on / 依赖: Function, Function.uncurry, uncurry
-/
theorem uncurry {f : α -> β -> σ} : Primrec (Function.uncurry f) ↔ Primrec₂ f := by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a]; rw [b⟩ => rfl]; rfl

/--
theorem `curry` / 定理 `curry`

English:
theorem curry
  given: {f : α × β -> σ}
  statement: Primrec₂ (Function.curry f) ↔ Primrec f
  proof: by
  rw [← uncurry]; rw [Function.uncurry_curry]

中文:
定理 curry
  条件: {f : α × β -> σ}
  结论: Primrec₂ (函数.curry f) ↔ Primrec f
  证明: by
  rw [← uncurry]; rw [Function.uncurry_curry]

Depends on / 依赖: Function, Function.uncurry_curry, uncurry, uncurry_curry
-/
theorem curry {f : α × β -> σ} : Primrec₂ (Function.curry f) ↔ Primrec f := by
  rw [← uncurry]; rw [Function.uncurry_curry]

end Primrec₂

section Comp

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/--
theorem `Primrec.comp₂` / 定理 `Primrec.comp₂`

English:
theorem Primrec.comp₂
  given: {f : γ -> σ} {g : α -> β -> γ} (hf : Primrec f) (hg : Primrec₂ g)
  proof: hf.comp hg

中文:
定理 Primrec.comp₂
  条件: {f : γ -> σ} {g : α -> β -> γ} (hf : Primrec f) (hg : Primrec₂ g)
  证明: hf.comp hg

Depends on / 依赖: hf.comp
-/
theorem Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a b => f (g a b) :=
  hf.comp hg

/--
theorem `Primrec₂.comp` / 定理 `Primrec₂.comp`

English:
theorem Primrec₂.comp
  statement: {f : β -> γ -> σ} {g : α -> β} {h : α -> γ} (hf : Primrec₂ f) (hg : Primrec g)
  proof: Primrec.comp hf (hg.pair hh)

中文:
定理 Primrec₂.comp
  结论: {f : β -> γ -> σ} {g : α -> β} {h : α -> γ} (hf : Primrec₂ f) (hg : Primrec g)
  证明: Primrec.comp hf (hg.pair hh)

Depends on / 依赖: Primrec, Primrec.comp, hg.pair
-/
theorem Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ} (hf : Primrec₂ f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => f (g a) (h a) :=
  Primrec.comp hf (hg.pair hh)

/--
theorem `Primrec₂.comp₂` / 定理 `Primrec₂.comp₂`

English:
theorem Primrec₂.comp₂
  statement: {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Primrec₂ f)
  proof: hf.comp hg hh

中文:
定理 Primrec₂.comp₂
  结论: {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Primrec₂ f)
  证明: hf.comp hg hh

Depends on / 依赖: hf.comp
-/
theorem Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : α -> β -> δ} (hf : Primrec₂ f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh

/--
lemma `PrimrecPred.decide` / 引理 `PrimrecPred.decide`

English:
lemma PrimrecPred.decide
  given: {p : α -> Prop} [DecidablePred p] (hp : PrimrecPred p)
  proof: by
  convert! hp.choose_spec

中文:
引理 PrimrecPred.decide
  条件: {p : α -> 命题} [DecidablePred p] (hp : PrimrecPred p)
  证明: by
  convert! hp.choose_spec
-/
protected lemma PrimrecPred.decide {p : α -> Prop} [DecidablePred p] (hp : PrimrecPred p) :
    Primrec (fun a => decide (p a)) := by
  convert! hp.choose_spec

/--
lemma `Primrec.primrecPred` / 引理 `Primrec.primrecPred`

English:
lemma Primrec.primrecPred
  statement: {p : α -> Prop} [DecidablePred p]
  proof: ⟨inferInstance, hp⟩

中文:
引理 Primrec.primrecPred
  结论: {p : α -> 命题} [DecidablePred p]
  证明: ⟨inferInstance, hp⟩
-/
lemma Primrec.primrecPred {p : α -> Prop} [DecidablePred p]
    (hp : Primrec (fun a => decide (p a))) : PrimrecPred p :=
  ⟨inferInstance, hp⟩

/--
lemma `primrecPred_iff_primrec_decide` / 引理 `primrecPred_iff_primrec_decide`

English:
lemma primrecPred_iff_primrec_decide
  given: {p : α -> Prop} [DecidablePred p]
  proof: PrimrecPred.decide
  mpr := Primrec.primrecPred

中文:
引理 primrecPred_iff_primrec_decide
  条件: {p : α -> 命题} [DecidablePred p]
  证明: PrimrecPred.decide
  mpr := Primrec.primrecPred

Depends on / 依赖: PrimrecPred, PrimrecPred.decide
-/
lemma primrecPred_iff_primrec_decide {p : α -> Prop} [DecidablePred p] :
    PrimrecPred p ↔ Primrec (fun a => decide (p a)) where
  mp := PrimrecPred.decide
  mpr := Primrec.primrecPred

/--
theorem `PrimrecPred.comp` / 定理 `PrimrecPred.comp`

English:
theorem PrimrecPred.comp
  given: {p : β -> Prop} {f : α -> β}

中文:
定理 PrimrecPred.comp
  条件: {p : β -> 命题} {f : α -> β}

Depends on / 依赖: PrimrecPred, PrimrecPred.decide
-/
theorem PrimrecPred.comp {p : β -> Prop} {f : α -> β} :
    (hp : PrimrecPred p) -> (hf : Primrec f) -> PrimrecPred fun a => p (f a)
.primrecPred | ⟨_i, hp⟩, hf => hp.comp hf

/--
lemma `PrimrecRel.decide` / 引理 `PrimrecRel.decide`

English:
lemma PrimrecRel.decide
  given: {R : α -> β -> Prop} [DecidableRel R] (hR : PrimrecRel R)
  proof: PrimrecPred.decide hR

中文:
引理 PrimrecRel.decide
  条件: {R : α -> β -> 命题} [DecidableRel R] (hR : PrimrecRel R)
  证明: PrimrecPred.decide hR
-/
protected lemma PrimrecRel.decide {R : α -> β -> Prop} [DecidableRel R] (hR : PrimrecRel R) :
    Primrec₂ (fun a b => decide (R a b)) :=
  PrimrecPred.decide hR

/--
lemma `Primrec₂.primrecRel` / 引理 `Primrec₂.primrecRel`

English:
lemma Primrec₂.primrecRel
  statement: {R : α -> β -> Prop} [DecidableRel R]
  proof: Primrec.primrecPred hp

中文:
引理 Primrec₂.primrecRel
  结论: {R : α -> β -> 命题} [DecidableRel R]
  证明: Primrec.primrecPred hp

Depends on / 依赖: Primrec, Primrec.primrecPred, primrecPred
-/
lemma Primrec₂.primrecRel {R : α -> β -> Prop} [DecidableRel R]
    (hp : Primrec₂ (fun a b => decide (R a b))) : PrimrecRel R :=
  Primrec.primrecPred hp

/--
lemma `primrecRel_iff_primrec_decide` / 引理 `primrecRel_iff_primrec_decide`

English:
lemma primrecRel_iff_primrec_decide
  given: {R : α -> β -> Prop} [DecidableRel R]
  proof: PrimrecRel.decide
  mpr := Primrec₂.primrecRel

中文:
引理 primrecRel_iff_primrec_decide
  条件: {R : α -> β -> 命题} [DecidableRel R]
  证明: PrimrecRel.decide
  mpr := Primrec₂.primrecRel

Depends on / 依赖: PrimrecRel, PrimrecRel.decide
-/
lemma primrecRel_iff_primrec_decide {R : α -> β -> Prop} [DecidableRel R] :
    PrimrecRel R ↔ Primrec₂ (fun a b => decide (R a b)) where
  mp := PrimrecRel.decide
  mpr := Primrec₂.primrecRel

/--
theorem `PrimrecRel.comp` / 定理 `PrimrecRel.comp`

English:
theorem PrimrecRel.comp
  statement: {R : β -> γ -> Prop} {f : α -> β} {g : α -> γ}
  proof: PrimrecPred.comp hR (hf.pair hg)

中文:
定理 PrimrecRel.comp
  结论: {R : β -> γ -> 命题} {f : α -> β} {g : α -> γ}
  证明: PrimrecPred.comp hR (hf.pair hg)

Depends on / 依赖: PrimrecPred, PrimrecPred.comp, hf.pair
-/
theorem PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : α -> γ}
    (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a => R (f a) (g a) :=
  PrimrecPred.comp hR (hf.pair hg)

/--
theorem `PrimrecRel.comp₂` / 定理 `PrimrecRel.comp₂`

English:
theorem PrimrecRel.comp₂
  given: {R : γ -> δ -> Prop} {f : α -> β -> γ} {g : α -> β -> δ}
  proof: PrimrecRel.comp

中文:
定理 PrimrecRel.comp₂
  条件: {R : γ -> δ -> 命题} {f : α -> β -> γ} {g : α -> β -> δ}
  证明: PrimrecRel.comp

Depends on / 依赖: PrimrecRel, PrimrecRel.comp
-/
theorem PrimrecRel.comp₂ {R : γ -> δ -> Prop} {f : α -> β -> γ} {g : α -> β -> δ} :
    PrimrecRel R -> Primrec₂ f -> Primrec₂ g -> PrimrecRel fun a b => R (f a b) (g a b) :=
  PrimrecRel.comp

end Comp

/--
theorem `PrimrecPred.of_eq` / 定理 `PrimrecPred.of_eq`

English:
theorem PrimrecPred.of_eq
  statement: {α} [Primcodable α] {p q : α -> Prop}
  proof: funext (fun a => propext (H a)) ▸ hp

中文:
定理 PrimrecPred.of_eq
  结论: {α} [Primcodable α] {p q : α -> 命题}
  证明: funext (fun a => propext (H a)) ▸ hp

Depends on / 依赖: propext
-/
theorem PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Prop}
    (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q :=
  funext (fun a => propext (H a)) ▸ hp

/--
theorem `PrimrecRel.of_eq` / 定理 `PrimrecRel.of_eq`

English:
theorem PrimrecRel.of_eq
  statement: {α β} [Primcodable α] [Primcodable β] {r s : α -> β -> Prop}
  proof: funext₂ (fun a b => propext (H a b)) ▸ hr

中文:
定理 PrimrecRel.of_eq
  结论: {α β} [Primcodable α] [Primcodable β] {r s : α -> β -> 命题}
  证明: funext₂ (fun a b => propext (H a b)) ▸ hr

Depends on / 依赖: propext
-/
theorem PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β] {r s : α -> β -> Prop}
    (hr : PrimrecRel r) (H : forall a b, r a b ↔ s a b) : PrimrecRel s :=
  funext₂ (fun a b => propext (H a b)) ▸ hr

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

/--
theorem `swap` / 定理 `swap`

English:
theorem swap
  given: {f : α -> β -> σ} (h : Primrec₂ f)
  statement: Primrec₂ (swap f)
  proof: h.comp₂ Primrec₂.right Primrec₂.left

中文:
定理 swap
  条件: {f : α -> β -> σ} (h : Primrec₂ f)
  结论: Primrec₂ (swap f)
  证明: h.comp₂ Primrec₂.right Primrec₂.left
-/
protected theorem swap {f : α -> β -> σ} (h : Primrec₂ f) : Primrec₂ (swap f) :=
  h.comp₂ Primrec₂.right Primrec₂.left

/--
theorem `_root_.PrimrecRel.swap` / 定理 `_root_.PrimrecRel.swap`

English:
theorem _root_.PrimrecRel.swap
  given: {r : α -> β -> Prop} (h : PrimrecRel r)
  proof: h.comp₂ Primrec₂.right Primrec₂.left

中文:
定理 _root_.PrimrecRel.swap
  条件: {r : α -> β -> 命题} (h : PrimrecRel r)
  证明: h.comp₂ Primrec₂.right Primrec₂.left
-/
protected theorem _root_.PrimrecRel.swap {r : α -> β -> Prop} (h : PrimrecRel r) :
    PrimrecRel (swap r) :=
  h.comp₂ Primrec₂.right Primrec₂.left

/--
theorem `nat_iff` / 定理 `nat_iff`

English:
theorem nat_iff
  given: {f : α -> β -> σ}
  statement: Primrec₂ f ↔ Nat.Primrec
  proof: by
  have :
    forall (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b := fun a b => by
          cases a <;> cases b <;> rfl
  simp [Primrec₂, Primrec, this]

中文:
定理 nat_iff
  条件: {f : α -> β -> σ}
  结论: Primrec₂ f ↔ 自然数.Primrec
  证明: by
  have :
    forall (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b := fun a b => by
          cases a <;> cases b <;> rfl
  simp [Primrec₂, Primrec, this]

Depends on / 依赖: Option.bind, Option.map, Primrec, Prod.mk
-/
theorem nat_iff {f : α -> β -> σ} : Primrec₂ f ↔ Nat.Primrec
    (.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map (f a)) := by
  have :
    forall (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b := fun a b => by
          cases a <;> cases b <;> rfl
  simp [Primrec₂, Primrec, this]

/--
theorem `nat_iff'` / 定理 `nat_iff'`

English:
theorem nat_iff'
  given: {f : α -> β -> σ}
  proof: nat_iff.trans unpaired'.trans encode_iff

中文:
定理 nat_iff'
  条件: {f : α -> β -> σ}
  证明: nat_iff.trans unpaired'.trans encode_iff

Depends on / 依赖: encode_iff, nat_iff, nat_iff.trans, unpaired
-/
theorem nat_iff' {f : α -> β -> σ} :
    Primrec₂ f ↔
      Primrec₂ fun m n : Nat => (@decode α _ m).bind fun a => Option.map (f a) (@decode β _ n) :=
nat_iff.trans unpaired'.trans encode_iff

end Primrec₂

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

/--
theorem `to₂` / 定理 `to₂`

English:
theorem to₂
  given: {f : α × β -> σ} (hf : Primrec f)
  statement: Primrec₂ fun a b => f (a, b)
  proof: hf

中文:
定理 to₂
  条件: {f : α × β -> σ} (hf : Primrec f)
  结论: Primrec₂ fun a b => f (a, b)
  证明: hf
-/
theorem to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b => f (a, b) :=
  hf

/--
lemma `_root_.PrimrecPred.primrecRel` / 引理 `_root_.PrimrecPred.primrecRel`

English:
lemma _root_.PrimrecPred.primrecRel
  given: {p : α × β -> Prop} (hp : PrimrecPred p)
  proof: hp

中文:
引理 _root_.PrimrecPred.primrecRel
  条件: {p : α × β -> 命题} (hp : PrimrecPred p)
  证明: hp
-/
lemma _root_.PrimrecPred.primrecRel {p : α × β -> Prop} (hp : PrimrecPred p) :
    PrimrecRel fun a b => p (a, b) :=
  hp

/--
theorem `nat_rec` / 定理 `nat_rec`

English:
theorem nat_rec
  given: {f : α -> β} {g : α -> Nat × β -> β} (hf : Primrec f) (hg : Primrec₂ g)
  proof: Primrec₂.nat_iff.2
    ((Nat.Primrec.casesOn' .zero <|
              (Nat.Primrec.prec hf <|
.comp hg
Nat.Primrec.left.pair
(Nat.Primrec.left.comp .right).pair
Nat.Primrec.pred.comp Nat.Primrec.right.comp .right).comp <|
Nat.Primrec.right.pair Nat.Primrec.right.comp Nat.Primrec.left).comp <|
Nat.Primrec.id.pair (Primcodable.prim α).comp Nat.Primrec.left).of_eq
      fun n => by
      simp only [Nat.unpaired, id_eq, Nat.unpair_pair, decode_prod_val, decode_nat,
        Option.bind_some, Option.map_map, Option.map_some]
      rcases @decode α _ n.unpair.1 with - | a; · rfl
      simp only [Nat.pred_eq_sub_one, encode_some, Nat.succ_eq_add_one, encodek, Option.map_some,
        Option.bind_some, Option.map_map]
      induction n.unpair.2 <;> simp [*, encodek]

中文:
定理 nat_rec
  条件: {f : α -> β} {g : α -> 自然数 × β -> β} (hf : Primrec f) (hg : Primrec₂ g)
  证明: Primrec₂.nat_iff.2
    ((Nat.Primrec.casesOn' .zero <|
              (Nat.Primrec.prec hf <|
.comp hg
Nat.Primrec.left.pair
(Nat.Primrec.left.comp .right).pair
Nat.Primrec.pred.comp Nat.Primrec.right.comp .right).comp <|
Nat.Primrec.right.pair Nat.Primrec.right.comp Nat.Primrec.left).comp <|
Nat.Primrec.id.pair (Primcodable.prim α).comp Nat.Primrec.left).of_eq
      fun n => by
      simp only [Nat.unpaired, id_eq, Nat.unpair_pair, decode_prod_val, decode_nat,
        Option.bind_some, Option.map_map, Option.map_some]
      rcases @decode α _ n.unpair.1 with - | a; · rfl
      simp only [Nat.pred_eq_sub_one, encode_some, Nat.succ_eq_add_one, encodek, Option.map_some,
        Option.bind_some, Option.map_map]
      induction n.unpair.2 <;> simp [*, encodek]
-/
theorem nat_rec {f : α -> β} {g : α -> Nat × β -> β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : Nat) => n.rec (motive := fun _ => β) (f a) fun n IH => g a (n, IH) :=
Primrec₂.nat_iff.2
    ((Nat.Primrec.casesOn' .zero <|
              (Nat.Primrec.prec hf <|
.comp hg
Nat.Primrec.left.pair
(Nat.Primrec.left.comp .right).pair
Nat.Primrec.pred.comp Nat.Primrec.right.comp .right).comp <|
Nat.Primrec.right.pair Nat.Primrec.right.comp Nat.Primrec.left).comp <|
Nat.Primrec.id.pair (Primcodable.prim α).comp Nat.Primrec.left).of_eq
      fun n => by
      simp only [Nat.unpaired, id_eq, Nat.unpair_pair, decode_prod_val, decode_nat,
        Option.bind_some, Option.map_map, Option.map_some]
      rcases @decode α _ n.unpair.1 with - | a; · rfl
      simp only [Nat.pred_eq_sub_one, encode_some, Nat.succ_eq_add_one, encodek, Option.map_some,
        Option.bind_some, Option.map_map]
      induction n.unpair.2 <;> simp [*, encodek]

/--
theorem `nat_rec'` / 定理 `nat_rec'`

English:
theorem nat_rec'
  statement: {f : α -> Nat} {g : α -> β} {h : α -> Nat × β -> β}
  proof: (nat_rec hg hh).comp .id hf

中文:
定理 nat_rec'
  结论: {f : α -> 自然数} {g : α -> β} {h : α -> 自然数 × β -> β}
  证明: (nat_rec hg hh).comp .id hf
-/
theorem nat_rec' {f : α -> Nat} {g : α -> β} {h : α -> Nat × β -> β}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).rec (motive := fun _ => β) (g a) fun n IH => h a (n, IH) :=
  (nat_rec hg hh).comp .id hf

/--
theorem `nat_rec₁` / 定理 `nat_rec₁`

English:
theorem nat_rec₁
  given: {f : Nat -> α -> α} (a : α) (hf : Primrec₂ f)
  statement: Primrec (Nat.rec a f)
  proof: nat_rec' .id (const a) comp₂ hf Primrec₂.right

中文:
定理 nat_rec₁
  条件: {f : 自然数 -> α -> α} (a : α) (hf : Primrec₂ f)
  结论: Primrec (自然数.rec a f)
  证明: nat_rec' .id (const a) comp₂ hf Primrec₂.right

Depends on / 依赖: nat_rec
-/
theorem nat_rec₁ {f : Nat -> α -> α} (a : α) (hf : Primrec₂ f) : Primrec (Nat.rec a f) :=
nat_rec' .id (const a) comp₂ hf Primrec₂.right

/--
theorem `nat_casesOn'` / 定理 `nat_casesOn'`

English:
theorem nat_casesOn'
  given: {f : α -> β} {g : α -> Nat -> β} (hf : Primrec f) (hg : Primrec₂ g)
  proof: nat_rec hf hg.comp₂ Primrec₂.left comp₂ fst Primrec₂.right

中文:
定理 nat_casesOn'
  条件: {f : α -> β} {g : α -> 自然数 -> β} (hf : Primrec f) (hg : Primrec₂ g)
  证明: nat_rec hf hg.comp₂ Primrec₂.left comp₂ fst Primrec₂.right

Depends on / 依赖: hg.comp, nat_rec
-/
theorem nat_casesOn' {f : α -> β} {g : α -> Nat -> β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : Nat) => (n.casesOn (f a) (g a) : β) :=
nat_rec hf hg.comp₂ Primrec₂.left comp₂ fst Primrec₂.right

/--
theorem `nat_casesOn` / 定理 `nat_casesOn`

English:
theorem nat_casesOn
  statement: {f : α -> Nat} {g : α -> β} {h : α -> Nat -> β} (hf : Primrec f) (hg : Primrec g)
  proof: (nat_casesOn' hg hh).comp .id hf

中文:
定理 nat_casesOn
  结论: {f : α -> 自然数} {g : α -> β} {h : α -> 自然数 -> β} (hf : Primrec f) (hg : Primrec g)
  证明: (nat_casesOn' hg hh).comp .id hf

Depends on / 依赖: nat_casesOn
-/
theorem nat_casesOn {f : α -> Nat} {g : α -> β} {h : α -> Nat -> β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => ((f a).casesOn (g a) (h a) : β) :=
  (nat_casesOn' hg hh).comp .id hf

/--
theorem `nat_casesOn₁` / 定理 `nat_casesOn₁`

English:
theorem nat_casesOn₁
  given: {f : Nat -> α} (a : α) (hf : Primrec f)
  proof: nat_casesOn .id (const a) (comp₂ hf .right)

中文:
定理 nat_casesOn₁
  条件: {f : 自然数 -> α} (a : α) (hf : Primrec f)
  证明: nat_casesOn .id (const a) (comp₂ hf .right)

Depends on / 依赖: nat_casesOn
-/
theorem nat_casesOn₁ {f : Nat -> α} (a : α) (hf : Primrec f) :
    Primrec (fun (n : Nat) => (n.casesOn a f : α)) :=
  nat_casesOn .id (const a) (comp₂ hf .right)

/--
theorem `nat_iterate` / 定理 `nat_iterate`

English:
theorem nat_iterate
  statement: {f : α -> Nat} {g : α -> β} {h : α -> β -> β} (hf : Primrec f) (hg : Primrec g)
  proof: (nat_rec' hf hg (hh.comp₂ Primrec₂.left <| snd.comp₂ Primrec₂.right)).of_eq fun a => by
    induction f a <;> simp [*, -Function.iterate_succ, Function.iterate_succ']

中文:
定理 nat_iterate
  结论: {f : α -> 自然数} {g : α -> β} {h : α -> β -> β} (hf : Primrec f) (hg : Primrec g)
  证明: (nat_rec' hf hg (hh.comp₂ Primrec₂.left <| snd.comp₂ Primrec₂.right)).of_eq fun a => by
    induction f a <;> simp [*, -Function.iterate_succ, Function.iterate_succ']

Depends on / 依赖: Function, Function.iterate_succ, hh.comp, iterate_succ, nat_rec, of_eq, snd.comp
-/
theorem nat_iterate {f : α -> Nat} {g : α -> β} {h : α -> β -> β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (h a)^[f a] (g a) :=
  (nat_rec' hf hg (hh.comp₂ Primrec₂.left <| snd.comp₂ Primrec₂.right)).of_eq fun a => by
    induction f a <;> simp [*, -Function.iterate_succ, Function.iterate_succ']

/--
theorem `option_casesOn` / 定理 `option_casesOn`

English:
theorem option_casesOn
  statement: {o : α -> Option β} {f : α -> σ} {g : α -> β -> σ} (ho : Primrec o)
  proof: encode_iff.1
    (nat_casesOn (encode_iff.2 ho) (encode_iff.2 hf) <|
pred.comp₂
Primrec₂.encode_iff.2
              (Primrec₂.nat_iff'.1 hg).comp₂ ((@Primrec.encode α _).comp fst).to₂
                Primrec₂.right).of_eq
      fun a => by rcases o a with - | b <;> simp [encodek]

中文:
定理 option_casesOn
  结论: {o : α -> 选项类型 β} {f : α -> σ} {g : α -> β -> σ} (ho : Primrec o)
  证明: encode_iff.1
    (nat_casesOn (encode_iff.2 ho) (encode_iff.2 hf) <|
pred.comp₂
Primrec₂.encode_iff.2
              (Primrec₂.nat_iff'.1 hg).comp₂ ((@Primrec.encode α _).comp fst).to₂
                Primrec₂.right).of_eq
      fun a => by rcases o a with - | b <;> simp [encodek]

Depends on / 依赖: Primrec, Primrec.encode, encode, encode_iff, encodek, nat_casesOn, nat_iff, of_eq, pred.comp
-/
theorem option_casesOn {o : α -> Option β} {f : α -> σ} {g : α -> β -> σ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec₂ g) :
    @Primrec _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
encode_iff.1
    (nat_casesOn (encode_iff.2 ho) (encode_iff.2 hf) <|
pred.comp₂
Primrec₂.encode_iff.2
              (Primrec₂.nat_iff'.1 hg).comp₂ ((@Primrec.encode α _).comp fst).to₂
                Primrec₂.right).of_eq
      fun a => by rcases o a with - | b <;> simp [encodek]

/--
theorem `option_bind` / 定理 `option_bind`

English:
theorem option_bind
  given: {f : α -> Option β} {g : α -> β -> Option σ} (hf : Primrec f) (hg : Primrec₂ g)
  proof: (option_casesOn hf (const none) hg).of_eq fun a => by cases f a <;> rfl

中文:
定理 option_bind
  条件: {f : α -> 选项类型 β} {g : α -> β -> 选项类型 σ} (hf : Primrec f) (hg : Primrec₂ g)
  证明: (option_casesOn hf (const none) hg).of_eq fun a => by cases f a <;> rfl

Depends on / 依赖: of_eq, option_casesOn
-/
theorem option_bind {f : α -> Option β} {g : α -> β -> Option σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).bind (g a) :=
  (option_casesOn hf (const none) hg).of_eq fun a => by cases f a <;> rfl

/--
theorem `option_bind₁` / 定理 `option_bind₁`

English:
theorem option_bind₁
  given: {f : α -> Option σ} (hf : Primrec f)
  statement: Primrec fun o => Option.bind o f
  proof: option_bind .id (hf.comp snd).to₂

中文:
定理 option_bind₁
  条件: {f : α -> 选项类型 σ} (hf : Primrec f)
  结论: Primrec fun o => 选项类型.bind o f
  证明: option_bind .id (hf.comp snd).to₂

Depends on / 依赖: hf.comp, option_bind
-/
theorem option_bind₁ {f : α -> Option σ} (hf : Primrec f) : Primrec fun o => Option.bind o f :=
  option_bind .id (hf.comp snd).to₂

/--
theorem `option_map` / 定理 `option_map`

English:
theorem option_map
  given: {f : α -> Option β} {g : α -> β -> σ} (hf : Primrec f) (hg : Primrec₂ g)
  proof: (option_bind hf (option_some.comp₂ hg)).of_eq fun x => by cases f x <;> rfl

中文:
定理 option_map
  条件: {f : α -> 选项类型 β} {g : α -> β -> σ} (hf : Primrec f) (hg : Primrec₂ g)
  证明: (option_bind hf (option_some.comp₂ hg)).of_eq fun x => by cases f x <;> rfl

Depends on / 依赖: of_eq, option_bind, option_some, option_some.comp
-/
theorem option_map {f : α -> Option β} {g : α -> β -> σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (option_bind hf (option_some.comp₂ hg)).of_eq fun x => by cases f x <;> rfl

/--
theorem `option_map₁` / 定理 `option_map₁`

English:
theorem option_map₁
  given: {f : α -> σ} (hf : Primrec f)
  statement: Primrec (Option.map f)
  proof: option_map .id (hf.comp snd).to₂

中文:
定理 option_map₁
  条件: {f : α -> σ} (hf : Primrec f)
  结论: Primrec (选项类型.map f)
  证明: option_map .id (hf.comp snd).to₂

Depends on / 依赖: hf.comp, option_map
-/
theorem option_map₁ {f : α -> σ} (hf : Primrec f) : Primrec (Option.map f) :=
  option_map .id (hf.comp snd).to₂

/--
theorem `option_getD` / 定理 `option_getD`

English:
theorem option_getD
  statement: Primrec₂ (@Option.getD α)
  proof: Primrec.of_eq (option_casesOn Primrec₂.left Primrec₂.right .right) fun ⟨o, a⟩ => by
    cases o <;> rfl

中文:
定理 option_getD
  结论: Primrec₂ (@选项类型.getD α)
  证明: Primrec.of_eq (option_casesOn Primrec₂.left Primrec₂.right .right) fun ⟨o, a⟩ => by
    cases o <;> rfl

Depends on / 依赖: Primrec, Primrec.of_eq, of_eq, option_casesOn
-/
theorem option_getD : Primrec₂ (@Option.getD α) :=
  Primrec.of_eq (option_casesOn Primrec₂.left Primrec₂.right .right) fun ⟨o, a⟩ => by
    cases o <;> rfl

/--
theorem `option_getD_default` / 定理 `option_getD_default`

English:
theorem option_getD_default
  given: [Inhabited α]
  statement: Primrec (fun o : Option α => o.getD default)
  proof: option_getD.comp .id (const default)

@[deprecated option_getD_default (since := "2026-01-05")]

中文:
定理 option_getD_default
  条件: [可居 α]
  结论: Primrec (fun o : 选项类型 α => o.getD default)
  证明: option_getD.comp .id (const default)

@[deprecated option_getD_default (since := "2026-01-05")]

Depends on / 依赖: option_getD, option_getD.comp
-/
theorem option_getD_default [Inhabited α] : Primrec (fun o : Option α => o.getD default) :=
  option_getD.comp .id (const default)

@[deprecated option_getD_default (since := "2026-01-05")]
/--
theorem `option_iget` / 定理 `option_iget`

English:
theorem option_iget
  given: [Inhabited α]
  statement: Primrec (@Option.iget α _)
  proof: option_getD_default

中文:
定理 option_iget
  条件: [可居 α]
  结论: Primrec (@选项类型.iget α _)
  证明: option_getD_default

Depends on / 依赖: option_getD_default
-/
theorem option_iget [Inhabited α] : Primrec (@Option.iget α _) :=
  option_getD_default

/--
theorem `option_isSome` / 定理 `option_isSome`

English:
theorem option_isSome
  statement: Primrec (@Option.isSome α)
  proof: (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl

中文:
定理 option_isSome
  结论: Primrec (@选项类型.isSome α)
  证明: (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl

Depends on / 依赖: of_eq, option_casesOn
-/
theorem option_isSome : Primrec (@Option.isSome α) :=
  (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl

/--
theorem `bind_decode_iff` / 定理 `bind_decode_iff`

English:
theorem bind_decode_iff
  given: {f : α -> β -> Option σ}
  proof: ⟨fun h => by simpa [encodek] using! h.comp fst ((@Primrec.encode β _).comp snd), fun h =>
option_bind (Primrec.decode.comp snd) h.comp (fst.comp fst) snd⟩

中文:
定理 bind_decode_iff
  条件: {f : α -> β -> 选项类型 σ}
  证明: ⟨fun h => by simpa [encodek] using! h.comp fst ((@Primrec.encode β _).comp snd), fun h =>
option_bind (Primrec.decode.comp snd) h.comp (fst.comp fst) snd⟩

Depends on / 依赖: Primrec, Primrec.decode.comp, Primrec.encode, decode, encode, encodek, fst.comp, h.comp, option_bind
-/
theorem bind_decode_iff {f : α -> β -> Option σ} :
    (Primrec₂ fun a n => (@decode β _ n).bind (f a)) ↔ Primrec₂ f :=
  ⟨fun h => by simpa [encodek] using! h.comp fst ((@Primrec.encode β _).comp snd), fun h =>
option_bind (Primrec.decode.comp snd) h.comp (fst.comp fst) snd⟩

/--
theorem `map_decode_iff` / 定理 `map_decode_iff`

English:
theorem map_decode_iff
  given: {f : α -> β -> σ}
  proof: by
  simp only [Option.map_eq_bind]
  exact bind_decode_iff.trans Primrec₂.option_some_iff

中文:
定理 map_decode_iff
  条件: {f : α -> β -> σ}
  证明: by
  simp only [Option.map_eq_bind]
  exact bind_decode_iff.trans Primrec₂.option_some_iff

Depends on / 依赖: Option.map_eq_bind, bind_decode_iff, bind_decode_iff.trans, map_eq_bind, option_some_iff
-/
theorem map_decode_iff {f : α -> β -> σ} :
    (Primrec₂ fun a n => (@decode β _ n).map (f a)) ↔ Primrec₂ f := by
  simp only [Option.map_eq_bind]
  exact bind_decode_iff.trans Primrec₂.option_some_iff

/--
theorem `nat_add` / 定理 `nat_add`

English:
theorem nat_add
  statement: Primrec₂ ((· + ·) : Nat -> Nat -> Nat)
  proof: Primrec₂.unpaired'.1 Nat.Primrec.add

中文:
定理 nat_add
  结论: Primrec₂ ((· + ·) : 自然数 -> 自然数 -> 自然数)
  证明: Primrec₂.unpaired'.1 Nat.Primrec.add

Depends on / 依赖: Nat.Primrec.add, Primrec, unpaired
-/
theorem nat_add : Primrec₂ ((· + ·) : Nat -> Nat -> Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.add

/--
theorem `nat_sub` / 定理 `nat_sub`

English:
theorem nat_sub
  statement: Primrec₂ ((· - ·) : Nat -> Nat -> Nat)
  proof: Primrec₂.unpaired'.1 Nat.Primrec.sub

中文:
定理 nat_sub
  结论: Primrec₂ ((· - ·) : 自然数 -> 自然数 -> 自然数)
  证明: Primrec₂.unpaired'.1 Nat.Primrec.sub

Depends on / 依赖: Nat.Primrec.sub, Primrec, unpaired
-/
theorem nat_sub : Primrec₂ ((· - ·) : Nat -> Nat -> Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.sub

/--
theorem `nat_mul` / 定理 `nat_mul`

English:
theorem nat_mul
  statement: Primrec₂ ((· * ·) : Nat -> Nat -> Nat)
  proof: Primrec₂.unpaired'.1 Nat.Primrec.mul

中文:
定理 nat_mul
  结论: Primrec₂ ((· * ·) : 自然数 -> 自然数 -> 自然数)
  证明: Primrec₂.unpaired'.1 Nat.Primrec.mul

Depends on / 依赖: Nat.Primrec.mul, Primrec, unpaired
-/
theorem nat_mul : Primrec₂ ((· * ·) : Nat -> Nat -> Nat) :=
  Primrec₂.unpaired'.1 Nat.Primrec.mul

/--
theorem `cond` / 定理 `cond`

English:
theorem cond
  statement: {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primrec c) (hf : Primrec f)
  proof: (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

中文:
定理 cond
  结论: {c : α -> 布尔值} {f : α -> σ} {g : α -> σ} (hc : Primrec c) (hf : Primrec f)
  证明: (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

Depends on / 依赖: encode_iff, hf.comp, nat_casesOn, of_eq
-/
theorem cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) else (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl

/--
theorem `ite` / 定理 `ite`

English:
theorem ite
  statement: {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -> σ} (hc : PrimrecPred c)
  proof: by
  simpa [Bool.cond_decide] using cond hc.decide hf hg

中文:
定理 ite
  结论: {c : α -> 命题} [DecidablePred c] {f : α -> σ} {g : α -> σ} (hc : PrimrecPred c)
  证明: by
  simpa [Bool.cond_decide] using cond hc.decide hf hg

Depends on / 依赖: Bool.cond_decide, cond_decide, hc.decide
-/
theorem ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -> σ} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a else g a := by
  simpa [Bool.cond_decide] using cond hc.decide hf hg

/--
theorem `nat_le` / 定理 `nat_le`

English:
theorem nat_le
  statement: PrimrecRel ((· <= ·) : Nat -> Nat -> Prop)
  proof: Primrec₂.primrecRel ((nat_casesOn nat_sub (const true) (const false).to₂).of_eq fun p => by
    dsimp [swap]
    rcases e : p.1 - p.2 with - | n
    · simp [Nat.sub_eq_zero_iff_le.1 e]
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)])

中文:
定理 nat_le
  结论: PrimrecRel ((· <= ·) : 自然数 -> 自然数 -> 命题)
  证明: Primrec₂.primrecRel ((nat_casesOn nat_sub (const true) (const false).to₂).of_eq fun p => by
    dsimp [swap]
    rcases e : p.1 - p.2 with - | n
    · simp [Nat.sub_eq_zero_iff_le.1 e]
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)])

Depends on / 依赖: Nat.lt_of_sub_eq_succ, Nat.sub_eq_zero_iff_le, lt_of_sub_eq_succ, nat_casesOn, nat_sub, not_le, of_eq, primrecRel, sub_eq_zero_iff_le
-/
theorem nat_le : PrimrecRel ((· <= ·) : Nat -> Nat -> Prop) :=
  Primrec₂.primrecRel ((nat_casesOn nat_sub (const true) (const false).to₂).of_eq fun p => by
    dsimp [swap]
    rcases e : p.1 - p.2 with - | n
    · simp [Nat.sub_eq_zero_iff_le.1 e]
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)])

/--
theorem `nat_min` / 定理 `nat_min`

English:
theorem nat_min
  statement: Primrec₂ (@min Nat _)
  proof: ite nat_le fst snd

中文:
定理 nat_min
  结论: Primrec₂ (@最小值 自然数 _)
  证明: ite nat_le fst snd

Depends on / 依赖: nat_le
-/
theorem nat_min : Primrec₂ (@min Nat _) :=
  ite nat_le fst snd

/--
theorem `nat_max` / 定理 `nat_max`

English:
theorem nat_max
  statement: Primrec₂ (@max Nat _)
  proof: ite (nat_le.comp fst snd) snd fst

中文:
定理 nat_max
  结论: Primrec₂ (@最大值 自然数 _)
  证明: ite (nat_le.comp fst snd) snd fst

Depends on / 依赖: nat_le, nat_le.comp
-/
theorem nat_max : Primrec₂ (@max Nat _) :=
  ite (nat_le.comp fst snd) snd fst

/--
theorem `dom_bool` / 定理 `dom_bool`

English:
theorem dom_bool
  given: (f : Bool -> α)
  statement: Primrec f
  proof: (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl

中文:
定理 dom_bool
  条件: (f : 布尔值 -> α)
  结论: Primrec f
  证明: (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl

Depends on / 依赖: of_eq
-/
theorem dom_bool (f : Bool -> α) : Primrec f :=
  (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl

/--
theorem `dom_bool₂` / 定理 `dom_bool₂`

English:
theorem dom_bool₂
  given: (f : Bool -> Bool -> α)
  statement: Primrec₂ f
  proof: (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl

中文:
定理 dom_bool₂
  条件: (f : 布尔值 -> 布尔值 -> α)
  结论: Primrec₂ f
  证明: (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl

Depends on / 依赖: dom_bool, of_eq
-/
theorem dom_bool₂ (f : Bool -> Bool -> α) : Primrec₂ f :=
  (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl

/--
theorem `not` / 定理 `not`

English:
theorem not
  statement: Primrec not
  proof: dom_bool _

中文:
定理 not
  结论: Primrec not
  证明: dom_bool _
-/
protected theorem not : Primrec not :=
  dom_bool _

/--
theorem `and` / 定理 `and`

English:
theorem and
  statement: Primrec₂ and
  proof: dom_bool₂ _

中文:
定理 and
  结论: Primrec₂ and
  证明: dom_bool₂ _
-/
protected theorem and : Primrec₂ and :=
  dom_bool₂ _

/--
theorem `or` / 定理 `or`

English:
theorem or
  statement: Primrec₂ or
  proof: dom_bool₂ _

中文:
定理 or
  结论: Primrec₂ or
  证明: dom_bool₂ _
-/
protected theorem or : Primrec₂ or :=
  dom_bool₂ _

/--
theorem `_root_.PrimrecPred.not` / 定理 `_root_.PrimrecPred.not`

English:
theorem _root_.PrimrecPred.not
  given: {p : α -> Prop}

中文:
定理 _root_.PrimrecPred.not
  条件: {p : α -> 命题}
-/
protected theorem _root_.PrimrecPred.not {p : α -> Prop} :
    (hp : PrimrecPred p) -> PrimrecPred fun a => ¬p a
| ⟨_, hp⟩ => Primrec.primrecPred .of_eq by simp Primrec.not.comp hp

/--
theorem `_root_.PrimrecPred.and` / 定理 `_root_.PrimrecPred.and`

English:
theorem _root_.PrimrecPred.and
  given: {p q : α -> Prop}

中文:
定理 _root_.PrimrecPred.and
  条件: {p q : α -> 命题}
-/
protected theorem _root_.PrimrecPred.and {p q : α -> Prop} :
    (hp : PrimrecPred p) -> (hq : PrimrecPred q) -> PrimrecPred fun a => p a ∧ q a
| ⟨_, hp⟩, ⟨_, hq⟩ => Primrec.primrecPred .of_eq by simp Primrec.and.comp hp hq

/--
theorem `_root_.PrimrecPred.or` / 定理 `_root_.PrimrecPred.or`

English:
theorem _root_.PrimrecPred.or
  given: {p q : α -> Prop}

中文:
定理 _root_.PrimrecPred.or
  条件: {p q : α -> 命题}
-/
protected theorem _root_.PrimrecPred.or {p q : α -> Prop} :
    (hp : PrimrecPred p) -> (hq : PrimrecPred q) -> PrimrecPred fun a => p a ∨ q a
| ⟨_, hp⟩, ⟨_, hq⟩ => Primrec.primrecPred .of_eq by simp Primrec.or.comp hp hq

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  statement: PrimrecRel (@Eq α)
  proof: have : PrimrecRel fun a b : Nat => a = b :=
    (PrimrecPred.and nat_le nat_le.swap).of_eq fun a => by simp [le_antisymm_iff]
  (this.decide.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
      (Primrec.encode.comp₂ Primrec₂.right)).primrecRel.of_eq
    fun _ _ => encode_injective.eq_iff

中文:
定理 eq
  结论: PrimrecRel (@相等 α)
  证明: have : PrimrecRel fun a b : Nat => a = b :=
    (PrimrecPred.and nat_le nat_le.swap).of_eq fun a => by simp [le_antisymm_iff]
  (this.decide.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
      (Primrec.encode.comp₂ Primrec₂.right)).primrecRel.of_eq
    fun _ _ => encode_injective.eq_iff
-/
protected theorem eq : PrimrecRel (@Eq α) :=
  have : PrimrecRel fun a b : Nat => a = b :=
    (PrimrecPred.and nat_le nat_le.swap).of_eq fun a => by simp [le_antisymm_iff]
  (this.decide.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
      (Primrec.encode.comp₂ Primrec₂.right)).primrecRel.of_eq
    fun _ _ => encode_injective.eq_iff

/--
theorem `beq` / 定理 `beq`

English:
theorem beq
  given: [DecidableEq α]
  statement: Primrec₂ (@BEq.beq α _)
  proof: Primrec.eq.decide

中文:
定理 beq
  条件: [DecidableEq α]
  结论: Primrec₂ (@BEq.beq α _)
  证明: Primrec.eq.decide
-/
protected theorem beq [DecidableEq α] : Primrec₂ (@BEq.beq α _) := Primrec.eq.decide

/--
theorem `nat_lt` / 定理 `nat_lt`

English:
theorem nat_lt
  statement: PrimrecRel ((· < ·) : Nat -> Nat -> Prop)
  proof: (nat_le.comp snd fst).not.of_eq fun p => by simp

中文:
定理 nat_lt
  结论: PrimrecRel ((· < ·) : 自然数 -> 自然数 -> 命题)
  证明: (nat_le.comp snd fst).not.of_eq fun p => by simp

Depends on / 依赖: nat_le, nat_le.comp, not.of_eq, of_eq
-/
theorem nat_lt : PrimrecRel ((· < ·) : Nat -> Nat -> Prop) :=
  (nat_le.comp snd fst).not.of_eq fun p => by simp

/--
theorem `option_guard` / 定理 `option_guard`

English:
theorem option_guard
  statement: {p : α -> β -> Prop} [DecidableRel p] (hp : PrimrecRel p) {f : α -> β}
  proof: ite (by simpa using hp.comp Primrec.id hf) (option_some_iff.2 hf) (const none)

中文:
定理 option_guard
  结论: {p : α -> β -> 命题} [DecidableRel p] (hp : PrimrecRel p) {f : α -> β}
  证明: ite (by simpa using hp.comp Primrec.id hf) (option_some_iff.2 hf) (const none)

Depends on / 依赖: Primrec, Primrec.id, hp.comp, option_some_iff
-/
theorem option_guard {p : α -> β -> Prop} [DecidableRel p] (hp : PrimrecRel p) {f : α -> β}
    (hf : Primrec f) : Primrec fun a => Option.guard (p a) (f a) :=
  ite (by simpa using hp.comp Primrec.id hf) (option_some_iff.2 hf) (const none)

/--
theorem `option_orElse` / 定理 `option_orElse`

English:
theorem option_orElse
  statement: Primrec₂ ((· <|> ·) : Option α -> Option α -> Option α)
  proof: (option_casesOn fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl

中文:
定理 option_orElse
  结论: Primrec₂ ((· <|> ·) : 选项类型 α -> 选项类型 α -> 选项类型 α)
  证明: (option_casesOn fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl

Depends on / 依赖: fst.comp, of_eq, option_casesOn
-/
theorem option_orElse : Primrec₂ ((· <|> ·) : Option α -> Option α -> Option α) :=
  (option_casesOn fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl

/--
theorem `decode₂` / 定理 `decode₂`

English:
theorem decode₂
  statement: Primrec (decode₂ α)
  proof: option_bind .decode
    option_guard (Primrec.eq.comp₂ (by exact encode_iff.mpr snd) (by exact fst.comp fst)) snd

中文:
定理 decode₂
  结论: Primrec (decode₂ α)
  证明: option_bind .decode
    option_guard (Primrec.eq.comp₂ (by exact encode_iff.mpr snd) (by exact fst.comp fst)) snd
-/
protected theorem decode₂ : Primrec (decode₂ α) :=
option_bind .decode
    option_guard (Primrec.eq.comp₂ (by exact encode_iff.mpr snd) (by exact fst.comp fst)) snd

/--
theorem `list_findIdx₁` / 定理 `list_findIdx₁`

English:
theorem list_findIdx₁
  given: {p : α -> β -> Bool} (hp : Primrec₂ p)

中文:
定理 list_findIdx₁
  条件: {p : α -> β -> 布尔值} (hp : Primrec₂ p)
-/
theorem list_findIdx₁ {p : α -> β -> Bool} (hp : Primrec₂ p) :
    forall l : List β, Primrec fun a => l.findIdx (p a)
| [] => const 0
| a :: l => (cond (hp.comp .id (const a)) (const 0) (succ.comp (list_findIdx₁ hp l))).of_eq fun n =>
  by simp [List.findIdx_cons]

/--
theorem `list_idxOf₁` / 定理 `list_idxOf₁`

English:
theorem list_idxOf₁
  given: [DecidableEq α] (l : List α)
  statement: Primrec fun a => l.idxOf a
  proof: list_findIdx₁ (.swap .beq) l

中文:
定理 list_idxOf₁
  条件: [DecidableEq α] (l : 列表 α)
  结论: Primrec fun a => l.idxOf a
  证明: list_findIdx₁ (.swap .beq) l
-/
theorem list_idxOf₁ [DecidableEq α] (l : List α) : Primrec fun a => l.idxOf a :=
  list_findIdx₁ (.swap .beq) l

/--
theorem `dom_finite` / 定理 `dom_finite`

English:
theorem dom_finite
  given: [Finite α] (f : α -> σ)
  statement: Primrec f
  proof: let ⟨l, _, m⟩ := Finite.exists_univ_list α
option_some_iff.1 by
    have := decidableEqOfEncodable α
    refine ((list_getElem?₁ (l.map f)).comp (list_idxOf₁ l)).of_eq fun a => ?_
    rw [List.getElem?_map]; rw [List.getElem?_idxOf (m a)]; rw [Option.map_some]

中文:
定理 dom_finite
  条件: [有限 α] (f : α -> σ)
  结论: Primrec f
  证明: let ⟨l, _, m⟩ := Finite.exists_univ_list α
option_some_iff.1 by
    have := decidableEqOfEncodable α
    refine ((list_getElem?₁ (l.map f)).comp (list_idxOf₁ l)).of_eq fun a => ?_
    rw [List.getElem?_map]; rw [List.getElem?_idxOf (m a)]; rw [Option.map_some]

Depends on / 依赖: Finite, Finite.exists_univ_list, List.getElem, Option.map_some, _idxOf, _map, decidableEqOfEncodable, exists_univ_list, getElem, l.map, list_getElem, map_some, of_eq, option_some_iff
-/
theorem dom_finite [Finite α] (f : α -> σ) : Primrec f :=
  let ⟨l, _, m⟩ := Finite.exists_univ_list α
option_some_iff.1 by
    have := decidableEqOfEncodable α
    refine ((list_getElem?₁ (l.map f)).comp (list_idxOf₁ l)).of_eq fun a => ?_
    rw [List.getElem?_map]; rw [List.getElem?_idxOf (m a)]; rw [Option.map_some]

/--
Definition of `PrimrecBounded` / `PrimrecBounded` 的定义

English:
definition PrimrecBounded
  signature: (f : α -> β)
  body: exists g : α -> Nat, Primrec g ∧ forall x, encode (f x) <= g x

中文:
定义 PrimrecBounded
  签名: (f : α -> β)
  定义体: exists g : α -> Nat, Primrec g ∧ forall x, encode (f x) <= g x

Depends on / 依赖: Primrec, encode
-/
def PrimrecBounded (f : α -> β) : Prop :=
  exists g : α -> Nat, Primrec g ∧ forall x, encode (f x) <= g x

/--
theorem `nat_findGreatest` / 定理 `nat_findGreatest`

English:
theorem nat_findGreatest
  statement: {f : α -> Nat} {p : α -> Nat -> Prop} [DecidableRel p]
  proof: (nat_rec' (h := fun x nih => if p x (nih.1 + 1) then nih.1 + 1 else nih.2)
    hf (const 0) (ite (hp.comp fst (snd |> fst.comp |> succ.comp))
      (snd |> fst.comp |> succ.comp) (snd.comp snd))).of_eq fun x => by
        induction f x <;> simp [Nat.findGreatest, *]

中文:
定理 nat_findGreatest
  结论: {f : α -> 自然数} {p : α -> 自然数 -> 命题} [DecidableRel p]
  证明: (nat_rec' (h := fun x nih => if p x (nih.1 + 1) then nih.1 + 1 else nih.2)
    hf (const 0) (ite (hp.comp fst (snd |> fst.comp |> succ.comp))
      (snd |> fst.comp |> succ.comp) (snd.comp snd))).of_eq fun x => by
        induction f x <;> simp [Nat.findGreatest, *]

Depends on / 依赖: Nat.findGreatest, findGreatest, fst.comp, hp.comp, nat_rec, of_eq, snd.comp, succ.comp
-/
theorem nat_findGreatest {f : α -> Nat} {p : α -> Nat -> Prop} [DecidableRel p]
    (hf : Primrec f) (hp : PrimrecRel p) : Primrec fun x => (f x).findGreatest (p x) :=
  (nat_rec' (h := fun x nih => if p x (nih.1 + 1) then nih.1 + 1 else nih.2)
    hf (const 0) (ite (hp.comp fst (snd |> fst.comp |> succ.comp))
      (snd |> fst.comp |> succ.comp) (snd.comp snd))).of_eq fun x => by
        induction f x <;> simp [Nat.findGreatest, *]

/--
theorem `of_graph` / 定理 `of_graph`

English:
theorem of_graph
  statement: {f : α -> Nat} (h₁ : PrimrecBounded f)
  proof: by
  rcases h₁ with ⟨g, pg, hg : forall x, f x <= g x⟩
  refine (nat_findGreatest pg h₂).of_eq fun n => ?_
  exact (Nat.findGreatest_spec (P := fun b => f n = b) (hg n) rfl).symm

中文:
定理 of_graph
  结论: {f : α -> 自然数} (h₁ : PrimrecBounded f)
  证明: by
  rcases h₁ with ⟨g, pg, hg : forall x, f x <= g x⟩
  refine (nat_findGreatest pg h₂).of_eq fun n => ?_
  exact (Nat.findGreatest_spec (P := fun b => f n = b) (hg n) rfl).symm

Depends on / 依赖: Nat.findGreatest_spec, findGreatest_spec, nat_findGreatest, of_eq
-/
theorem of_graph {f : α -> Nat} (h₁ : PrimrecBounded f)
    (h₂ : PrimrecRel fun a b => f a = b) : Primrec f := by
  rcases h₁ with ⟨g, pg, hg : forall x, f x <= g x⟩
  refine (nat_findGreatest pg h₂).of_eq fun n => ?_
  exact (Nat.findGreatest_spec (P := fun b => f n = b) (hg n) rfl).symm

-- We show that division is primitive recursive by showing that the graph is
/--
theorem `nat_div` / 定理 `nat_div`

English:
theorem nat_div
  statement: Primrec₂ ((· / ·) : Nat -> Nat -> Nat)
  proof: by
  refine of_graph ⟨_, fst, fun p => Nat.div_le_self _ _⟩ ?_
  have : PrimrecRel fun (a : Nat × Nat) (b : Nat) => (a.2 = 0 ∧ b = 0) ∨
      (0 < a.2 ∧ b * a.2 <= a.1 ∧ a.1 < (b + 1) * a.2) :=
    PrimrecPred.or
      (.and (const 0 |> Primrec.eq.comp (fst |> snd.comp)) (const 0 |> Primrec.eq.comp snd))
      (.and (nat_lt.comp (const 0) (fst |> snd.comp)) <|
          .and (nat_le.comp (nat_mul.comp snd (fst |> snd.comp)) (fst |> fst.comp))
          (nat_lt.comp (fst.comp fst) (nat_mul.comp (Primrec.succ.comp snd) (snd.comp fst))))
  refine this.of_eq ?_
  rintro ⟨a, k⟩ q
  if H : k = 0 then simp [H, eq_comm]
  else
    have : q * k <= a ∧ a < (q + 1) * k ↔ q = a / k := by
      rw [le_antisymm_iff]; rw [← (@Nat.lt_succ_iff _ q)]; rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero H)]; rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero H)]
    simpa [H, zero_lt_iff, eq_comm (b := q)]

中文:
定理 nat_div
  结论: Primrec₂ ((· / ·) : 自然数 -> 自然数 -> 自然数)
  证明: by
  refine of_graph ⟨_, fst, fun p => Nat.div_le_self _ _⟩ ?_
  have : PrimrecRel fun (a : Nat × Nat) (b : Nat) => (a.2 = 0 ∧ b = 0) ∨
      (0 < a.2 ∧ b * a.2 <= a.1 ∧ a.1 < (b + 1) * a.2) :=
    PrimrecPred.or
      (.and (const 0 |> Primrec.eq.comp (fst |> snd.comp)) (const 0 |> Primrec.eq.comp snd))
      (.and (nat_lt.comp (const 0) (fst |> snd.comp)) <|
          .and (nat_le.comp (nat_mul.comp snd (fst |> snd.comp)) (fst |> fst.comp))
          (nat_lt.comp (fst.comp fst) (nat_mul.comp (Primrec.succ.comp snd) (snd.comp fst))))
  refine this.of_eq ?_
  rintro ⟨a, k⟩ q
  if H : k = 0 then simp [H, eq_comm]
  else
    have : q * k <= a ∧ a < (q + 1) * k ↔ q = a / k := by
      rw [le_antisymm_iff]; rw [← (@Nat.lt_succ_iff _ q)]; rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero H)]; rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero H)]
    simpa [H, zero_lt_iff, eq_comm (b := q)]

Depends on / 依赖: Nat.div_le_self, Primrec, Primrec.eq.comp, Primrec.succ.comp, PrimrecPred, PrimrecPred.or, PrimrecRel, div_le_self, fst.comp, nat_le, nat_le.comp, nat_lt, nat_lt.comp, nat_mul, nat_mul.comp, of_graph, snd.comp
-/
theorem nat_div : Primrec₂ ((· / ·) : Nat -> Nat -> Nat) := by
  refine of_graph ⟨_, fst, fun p => Nat.div_le_self _ _⟩ ?_
  have : PrimrecRel fun (a : Nat × Nat) (b : Nat) => (a.2 = 0 ∧ b = 0) ∨
      (0 < a.2 ∧ b * a.2 <= a.1 ∧ a.1 < (b + 1) * a.2) :=
    PrimrecPred.or
      (.and (const 0 |> Primrec.eq.comp (fst |> snd.comp)) (const 0 |> Primrec.eq.comp snd))
      (.and (nat_lt.comp (const 0) (fst |> snd.comp)) <|
          .and (nat_le.comp (nat_mul.comp snd (fst |> snd.comp)) (fst |> fst.comp))
          (nat_lt.comp (fst.comp fst) (nat_mul.comp (Primrec.succ.comp snd) (snd.comp fst))))
  refine this.of_eq ?_
  rintro ⟨a, k⟩ q
  if H : k = 0 then simp [H, eq_comm]
  else
    have : q * k <= a ∧ a < (q + 1) * k ↔ q = a / k := by
      rw [le_antisymm_iff]; rw [← (@Nat.lt_succ_iff _ q)]; rw [Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero H)]; rw [Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero H)]
    simpa [H, zero_lt_iff, eq_comm (b := q)]

/--
theorem `nat_mod` / 定理 `nat_mod`

English:
theorem nat_mod
  statement: Primrec₂ ((· % ·) : Nat -> Nat -> Nat)
  proof: (nat_sub.comp fst (nat_mul.comp snd nat_div)).to₂.of_eq fun m n => by
    apply Nat.sub_eq_of_eq_add
    simp [add_comm (m % n), Nat.div_add_mod]

中文:
定理 nat_mod
  结论: Primrec₂ ((· % ·) : 自然数 -> 自然数 -> 自然数)
  证明: (nat_sub.comp fst (nat_mul.comp snd nat_div)).to₂.of_eq fun m n => by
    apply Nat.sub_eq_of_eq_add
    simp [add_comm (m % n), Nat.div_add_mod]

Depends on / 依赖: Nat.div_add_mod, Nat.sub_eq_of_eq_add, add_comm, div_add_mod, nat_div, nat_mul, nat_mul.comp, nat_sub, nat_sub.comp, of_eq, sub_eq_of_eq_add
-/
theorem nat_mod : Primrec₂ ((· % ·) : Nat -> Nat -> Nat) :=
  (nat_sub.comp fst (nat_mul.comp snd nat_div)).to₂.of_eq fun m n => by
    apply Nat.sub_eq_of_eq_add
    simp [add_comm (m % n), Nat.div_add_mod]

/--
theorem `nat_bodd` / 定理 `nat_bodd`

English:
theorem nat_bodd
  statement: Primrec Nat.bodd
  proof: (Primrec.beq.comp (nat_mod.comp .id (const 2)) (const 1)).of_eq fun n => by
    cases H : n.bodd <;> simp [Nat.mod_two_of_bodd, H]

中文:
定理 nat_bodd
  结论: Primrec 自然数.bodd
  证明: (Primrec.beq.comp (nat_mod.comp .id (const 2)) (const 1)).of_eq fun n => by
    cases H : n.bodd <;> simp [Nat.mod_two_of_bodd, H]

Depends on / 依赖: Nat.mod_two_of_bodd, Primrec, Primrec.beq.comp, mod_two_of_bodd, n.bodd, nat_mod, nat_mod.comp, of_eq
-/
theorem nat_bodd : Primrec Nat.bodd :=
  (Primrec.beq.comp (nat_mod.comp .id (const 2)) (const 1)).of_eq fun n => by
    cases H : n.bodd <;> simp [Nat.mod_two_of_bodd, H]

/--
theorem `nat_div2` / 定理 `nat_div2`

English:
theorem nat_div2
  statement: Primrec Nat.div2
  proof: (nat_div.comp .id (const 2)).of_eq fun n => n.div2_val.symm

中文:
定理 nat_div2
  结论: Primrec 自然数.div2
  证明: (nat_div.comp .id (const 2)).of_eq fun n => n.div2_val.symm

Depends on / 依赖: div2_val, n.div2_val.symm, nat_div, nat_div.comp, of_eq
-/
theorem nat_div2 : Primrec Nat.div2 :=
  (nat_div.comp .id (const 2)).of_eq fun n => n.div2_val.symm

/--
theorem `nat_double` / 定理 `nat_double`

English:
theorem nat_double
  statement: Primrec (fun n : Nat => 2 * n)
  proof: nat_mul.comp (const _) Primrec.id

中文:
定理 nat_double
  结论: Primrec (fun n : 自然数 => 2 * n)
  证明: nat_mul.comp (const _) Primrec.id

Depends on / 依赖: Primrec, Primrec.id, nat_mul, nat_mul.comp
-/
theorem nat_double : Primrec (fun n : Nat => 2 * n) :=
  nat_mul.comp (const _) Primrec.id

/--
theorem `nat_double_succ` / 定理 `nat_double_succ`

English:
theorem nat_double_succ
  statement: Primrec (fun n : Nat => 2 * n + 1)
  proof: Primrec.succ.comp nat_double

中文:
定理 nat_double_succ
  结论: Primrec (fun n : 自然数 => 2 * n + 1)
  证明: Primrec.succ.comp nat_double

Depends on / 依赖: Primrec, Primrec.succ.comp, nat_double
-/
theorem nat_double_succ : Primrec (fun n : Nat => 2 * n + 1) :=
Primrec.succ.comp nat_double

end Primrec

namespace Primcodable

variable {α : Type*} {β : Type*}
variable [Primcodable α] [Primcodable β]

open Primrec

/--
Instance `sum` / 实例 `sum`

English:
instance sum
  signature: : Primcodable (α oplus β)
  body: ⟨Primrec.nat_iff.1
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
to₂ nat_double_succ.comp (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
to₂ nat_double.comp (Primrec.encode.comp snd)))).of_eq
        fun n =>
        show _ = encode (decodeSum n) by
          simp only [decodeSum]
          cases Nat.bodd n <;> simp
          · cases @decode α _ n.div2 <;> rfl
          · cases @decode β _ n.div2 <;> rfl⟩

中文:
实例 求和
  签名: : Primcodable (α oplus β)
  定义体: ⟨Primrec.nat_iff.1
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
to₂ nat_double_succ.comp (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
to₂ nat_double.comp (Primrec.encode.comp snd)))).of_eq
        fun n =>
        show _ = encode (decodeSum n) by
          simp only [decodeSum]
          cases Nat.bodd n <;> simp
          · cases @decode α _ n.div2 <;> rfl
          · cases @decode β _ n.div2 <;> rfl⟩

Depends on / 依赖: Nat.bodd, Primrec, Primrec.decode, Primrec.encode.comp, Primrec.nat_iff, decode, decodeSum, encode, encode_iff, n.div2, nat_bodd, nat_div2, nat_double, nat_double.comp, nat_double_succ, nat_double_succ.comp, nat_iff, of_eq, option_map
-/
instance sum : Primcodable (α oplus β) :=
⟨Primrec.nat_iff.1
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
to₂ nat_double_succ.comp (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
to₂ nat_double.comp (Primrec.encode.comp snd)))).of_eq
        fun n =>
        show _ = encode (decodeSum n) by
          simp only [decodeSum]
          cases Nat.bodd n <;> simp
          · cases @decode α _ n.div2 <;> rfl
          · cases @decode β _ n.div2 <;> rfl⟩

end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {γ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable σ]


/--
theorem `sumInl` / 定理 `sumInl`

English:
theorem sumInl
  statement: Primrec (@Sum.inl α β)
  proof: encode_iff.1 nat_double.comp Primrec.encode

中文:
定理 sumInl
  结论: Primrec (@和.inl α β)
  证明: encode_iff.1 nat_double.comp Primrec.encode

Depends on / 依赖: Primrec, Primrec.encode, encode, encode_iff, nat_double, nat_double.comp
-/
theorem sumInl : Primrec (@Sum.inl α β) :=
encode_iff.1 nat_double.comp Primrec.encode

/--
theorem `sumInr` / 定理 `sumInr`

English:
theorem sumInr
  statement: Primrec (@Sum.inr α β)
  proof: encode_iff.1 nat_double_succ.comp Primrec.encode

中文:
定理 sumInr
  结论: Primrec (@和.inr α β)
  证明: encode_iff.1 nat_double_succ.comp Primrec.encode

Depends on / 依赖: Primrec, Primrec.encode, encode, encode_iff, nat_double_succ, nat_double_succ.comp
-/
theorem sumInr : Primrec (@Sum.inr α β) :=
encode_iff.1 nat_double_succ.comp Primrec.encode

/--
theorem `sumCasesOn` / 定理 `sumCasesOn`

English:
theorem sumCasesOn
  statement: {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ -> σ} (hf : Primrec f)
  proof: option_some_iff.1
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by rcases f a with b | c <;> simp [Nat.div2_val, encodek]

中文:
定理 sumCasesOn
  结论: {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ -> σ} (hf : Primrec f)
  证明: option_some_iff.1
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by rcases f a with b | c <;> simp [Nat.div2_val, encodek]

Depends on / 依赖: Nat.div2_val, Primrec, Primrec.decode.comp, decode, div2_val, encode_iff, encodek, nat_bodd, nat_bodd.comp, nat_div2, nat_div2.comp, of_eq, option_map, option_some_iff
-/
theorem sumCasesOn {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ -> σ} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
option_some_iff.1
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by rcases f a with b | c <;> simp [Nat.div2_val, encodek]

end Primrec

namespace PrimrecRel

open Primrec List PrimrecPred

variable {α β : Type*} {R : α -> β -> Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/--
theorem `not` / 定理 `not`

English:
theorem not
  given: (hf : PrimrecRel R)
  statement: PrimrecRel fun a b => ¬ R a b
  proof: PrimrecPred.not hf

中文:
定理 not
  条件: (hf : PrimrecRel R)
  结论: PrimrecRel fun a b => ¬ R a b
  证明: PrimrecPred.not hf
-/
protected theorem not (hf : PrimrecRel R) : PrimrecRel fun a b => ¬ R a b := PrimrecPred.not hf

end PrimrecRel

namespace Primcodable

variable {α : Type*} [Primcodable α]

open Primrec

/-- A subtype of a primitive recursive predicate is `Primcodable`. -/
@[instance_reducible]
/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: {p : α -> Prop} [DecidablePred p] (hp : PrimrecPred p)
  body: ⟨have : Primrec fun n => (@decode α _ n).bind fun a => Option.guard p a :=
    option_bind .decode (option_guard (hp.comp snd).primrecRel snd)
nat_iff.1 (encode_iff.2 this).of_eq fun n =>
    show _ = encode ((@decode α _ n).bind fun _ => _) by
      rcases @decode α _ n with - | a; · rfl
      dsimp [Option.guard]
      by_cases h : p a <;> simp [h]; rfl⟩

中文:
定义 subtype
  签名: {p : α -> 命题} [DecidablePred p] (hp : PrimrecPred p)
  定义体: ⟨have : Primrec fun n => (@decode α _ n).bind fun a => Option.guard p a :=
    option_bind .decode (option_guard (hp.comp snd).primrecRel snd)
nat_iff.1 (encode_iff.2 this).of_eq fun n =>
    show _ = encode ((@decode α _ n).bind fun _ => _) by
      rcases @decode α _ n with - | a; · rfl
      dsimp [Option.guard]
      by_cases h : p a <;> simp [h]; rfl⟩

Depends on / 依赖: Option.guard, Primrec, decode, encode, encode_iff, hp.comp, nat_iff, of_eq, option_bind, option_guard, primrecRel
-/
def subtype {p : α -> Prop} [DecidablePred p] (hp : PrimrecPred p) : Primcodable (Subtype p) :=
  ⟨have : Primrec fun n => (@decode α _ n).bind fun a => Option.guard p a :=
    option_bind .decode (option_guard (hp.comp snd).primrecRel snd)
nat_iff.1 (encode_iff.2 this).of_eq fun n =>
    show _ = encode ((@decode α _ n).bind fun _ => _) by
      rcases @decode α _ n with - | a; · rfl
      dsimp [Option.guard]
      by_cases h : p a <;> simp [h]; rfl⟩

/--
Instance `fin` / 实例 `fin`

English:
instance fin
  signature: {n}
  body: letI : Primcodable { i : Nat // i < n } := subtype nat_lt.comp .id (const n)
  ofEquiv { i : Nat // i < n } Fin.equivSubtype

example (n) : (fin (n := n)).toEncodable = Fin.encodable n := by
  with_reducible_and_instances rfl

中文:
实例 fin
  签名: {n}
  定义体: letI : Primcodable { i : Nat // i < n } := subtype nat_lt.comp .id (const n)
  ofEquiv { i : Nat // i < n } Fin.equivSubtype

example (n) : (fin (n := n)).toEncodable = Fin.encodable n := by
  with_reducible_and_instances rfl

Depends on / 依赖: Fin.equivSubtype, Primcodable, equivSubtype, nat_lt, nat_lt.comp, ofEquiv, subtype
-/
instance fin {n} : Primcodable (Fin n) :=
letI : Primcodable { i : Nat // i < n } := subtype nat_lt.comp .id (const n)
  ofEquiv { i : Nat // i < n } Fin.equivSubtype

example (n) : (fin (n := n)).toEncodable = Fin.encodable n := by
  with_reducible_and_instances rfl

section ULower

attribute [local instance] Encodable.decidableRangeEncode Encodable.decidableEqOfEncodable

/--
theorem `mem_range_encode` / 定理 `mem_range_encode`

English:
theorem mem_range_encode
  statement: PrimrecPred (fun n => n in Set.range (encode : α -> Nat))
  proof: have : PrimrecPred fun n => Encodable.decode₂ α n != none :=
    .not
      (Primrec.eq.comp
        (.option_bind .decode
          (.ite (by simpa using Primrec.eq.comp (Primrec.encode.comp .snd) .fst)
            (Primrec.option_some.comp .snd) (.const _)))
        (.const _))
  this.of_eq fun _ => decode₂_ne_none_iff

中文:
定理 mem_range_encode
  结论: PrimrecPred (fun n => n in 集合.range (encode : α -> 自然数))
  证明: have : PrimrecPred fun n => Encodable.decode₂ α n != none :=
    .not
      (Primrec.eq.comp
        (.option_bind .decode
          (.ite (by simpa using Primrec.eq.comp (Primrec.encode.comp .snd) .fst)
            (Primrec.option_some.comp .snd) (.const _)))
        (.const _))
  this.of_eq fun _ => decode₂_ne_none_iff

Depends on / 依赖: Encodable, Encodable.decode, Primrec, Primrec.encode.comp, Primrec.eq.comp, Primrec.option_some.comp, PrimrecPred, decode, encode, of_eq, option_bind, option_some, this.of_eq
-/
theorem mem_range_encode : PrimrecPred (fun n => n in Set.range (encode : α -> Nat)) :=
  have : PrimrecPred fun n => Encodable.decode₂ α n != none :=
    .not
      (Primrec.eq.comp
        (.option_bind .decode
          (.ite (by simpa using Primrec.eq.comp (Primrec.encode.comp .snd) .fst)
            (Primrec.option_some.comp .snd) (.const _)))
        (.const _))
  this.of_eq fun _ => decode₂_ne_none_iff

/--
Instance `ulower` / 实例 `ulower`

English:
instance ulower
  signature: : Primcodable (ULower α)
  body: fast_instance% Primcodable.subtype mem_range_encode

中文:
实例 ulower
  签名: : Primcodable (ULower α)
  定义体: fast_instance% Primcodable.subtype mem_range_encode

Depends on / 依赖: Primcodable, Primcodable.subtype, fast_instance, mem_range_encode, subtype
-/
instance ulower : Primcodable (ULower α) :=
  fast_instance% Primcodable.subtype mem_range_encode

end ULower


end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

/--
theorem `subtype_val` / 定理 `subtype_val`

English:
theorem subtype_val
  given: {p : α -> Prop} [DecidablePred p] {hp : PrimrecPred p}
  proof: Primcodable.subtype hp
    Primrec (@Subtype.val α p) := by
  let := Primcodable.subtype hp
  refine (Primcodable.prim (Subtype p)).of_eq fun n => ?_
  rcases @decode (Subtype p) _ n with (_ | ⟨a, h⟩) <;> rfl

中文:
定理 subtype_val
  条件: {p : α -> 命题} [DecidablePred p] {hp : PrimrecPred p}
  证明: Primcodable.subtype hp
    Primrec (@Subtype.val α p) := by
  let := Primcodable.subtype hp
  refine (Primcodable.prim (Subtype p)).of_eq fun n => ?_
  rcases @decode (Subtype p) _ n with (_ | ⟨a, h⟩) <;> rfl

Depends on / 依赖: Primcodable, Primcodable.subtype, subtype
-/
theorem subtype_val {p : α -> Prop} [DecidablePred p] {hp : PrimrecPred p} :
    haveI := Primcodable.subtype hp
    Primrec (@Subtype.val α p) := by
  let := Primcodable.subtype hp
  refine (Primcodable.prim (Subtype p)).of_eq fun n => ?_
  rcases @decode (Subtype p) _ n with (_ | ⟨a, h⟩) <;> rfl

/--
theorem `subtype_val_iff` / 定理 `subtype_val_iff`

English:
theorem subtype_val_iff
  given: {p : β -> Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α -> Subtype p}
  proof: Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f := by
  let := Primcodable.subtype hp
  refine ⟨fun h => ?_, fun hf => subtype_val.comp hf⟩
  refine Nat.Primrec.of_eq h fun n => ?_
  rcases @decode α _ n with - | a; · rfl
  simp; rfl

中文:
定理 subtype_val_iff
  条件: {p : β -> 命题} [DecidablePred p] {hp : PrimrecPred p} {f : α -> 子类型 p}
  证明: Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f := by
  let := Primcodable.subtype hp
  refine ⟨fun h => ?_, fun hf => subtype_val.comp hf⟩
  refine Nat.Primrec.of_eq h fun n => ?_
  rcases @decode α _ n with - | a; · rfl
  simp; rfl

Depends on / 依赖: Primcodable, Primcodable.subtype, subtype
-/
theorem subtype_val_iff {p : β -> Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α -> Subtype p} :
    haveI := Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f := by
  let := Primcodable.subtype hp
  refine ⟨fun h => ?_, fun hf => subtype_val.comp hf⟩
  refine Nat.Primrec.of_eq h fun n => ?_
  rcases @decode α _ n with - | a; · rfl
  simp; rfl

/--
theorem `subtype_mk` / 定理 `subtype_mk`

English:
theorem subtype_mk
  statement: {p : β -> Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α -> β}
  proof: Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) :=
  subtype_val_iff.1 hf

中文:
定理 subtype_mk
  结论: {p : β -> 命题} [DecidablePred p] {hp : PrimrecPred p} {f : α -> β}
  证明: Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) :=
  subtype_val_iff.1 hf

Depends on / 依赖: Primcodable, Primcodable.subtype, subtype
-/
theorem subtype_mk {p : β -> Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α -> β}
    {h : forall a, p (f a)} (hf : Primrec f) :
    haveI := Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) :=
  subtype_val_iff.1 hf

/--
theorem `option_get` / 定理 `option_get`

English:
theorem option_get
  given: {f : α -> Option β} {h : forall a, (f a).isSome}
  proof: by
  intro hf
  refine (Nat.Primrec.pred.comp hf).of_eq fun n => ?_
  generalize hx : @decode α _ n = x
  cases x <;> simp

中文:
定理 option_get
  条件: {f : α -> 选项类型 β} {h : 对任意 a, (f a).isSome}
  证明: by
  intro hf
  refine (Nat.Primrec.pred.comp hf).of_eq fun n => ?_
  generalize hx : @decode α _ n = x
  cases x <;> simp

Depends on / 依赖: Nat.Primrec.pred.comp, Primrec, decode, generalize, of_eq
-/
theorem option_get {f : α -> Option β} {h : forall a, (f a).isSome} :
    Primrec f -> Primrec fun a => (f a).get (h a) := by
  intro hf
  refine (Nat.Primrec.pred.comp hf).of_eq fun n => ?_
  generalize hx : @decode α _ n = x
  cases x <;> simp

/--
theorem `ulower_down` / 定理 `ulower_down`

English:
theorem ulower_down
  statement: Primrec (ULower.down : α -> ULower α)
  proof: letI : forall a, Decidable (a in Set.range (encode : α -> Nat)) := decidableRangeEncode _
  subtype_mk .encode (hp := Primcodable.mem_range_encode)

中文:
定理 ulower_down
  结论: Primrec (ULower.down : α -> ULower α)
  证明: letI : forall a, Decidable (a in Set.range (encode : α -> Nat)) := decidableRangeEncode _
  subtype_mk .encode (hp := Primcodable.mem_range_encode)

Depends on / 依赖: Decidable, Primcodable, Primcodable.mem_range_encode, Set.range, decidableRangeEncode, encode, mem_range_encode, subtype_mk
-/
theorem ulower_down : Primrec (ULower.down : α -> ULower α) :=
  letI : forall a, Decidable (a in Set.range (encode : α -> Nat)) := decidableRangeEncode _
  subtype_mk .encode (hp := Primcodable.mem_range_encode)

/--
theorem `ulower_up` / 定理 `ulower_up`

English:
theorem ulower_up
  statement: Primrec (ULower.up : ULower α -> α)
  proof: letI : forall a, Decidable (a in Set.range (encode : α -> Nat)) := decidableRangeEncode _
  option_get (Primrec.decode₂.comp (subtype_val (hp := Primcodable.mem_range_encode)))

中文:
定理 ulower_up
  结论: Primrec (ULower.up : ULower α -> α)
  证明: letI : forall a, Decidable (a in Set.range (encode : α -> Nat)) := decidableRangeEncode _
  option_get (Primrec.decode₂.comp (subtype_val (hp := Primcodable.mem_range_encode)))

Depends on / 依赖: Decidable, Primcodable, Primcodable.mem_range_encode, Primrec, Primrec.decode, Set.range, decidableRangeEncode, encode, mem_range_encode, option_get, subtype_val
-/
theorem ulower_up : Primrec (ULower.up : ULower α -> α) :=
  letI : forall a, Decidable (a in Set.range (encode : α -> Nat)) := decidableRangeEncode _
  option_get (Primrec.decode₂.comp (subtype_val (hp := Primcodable.mem_range_encode)))

/--
theorem `fin_val_iff` / 定理 `fin_val_iff`

English:
theorem fin_val_iff
  given: {n} {f : α -> Fin n}
  statement: (Primrec fun a => (f a).1) ↔ Primrec f
  proof: by
  let : Primcodable { a // a < n } := Primcodable.subtype (nat_lt.comp .id (const _))
  exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)

中文:
定理 fin_val_iff
  条件: {n} {f : α -> 有限集 n}
  结论: (Primrec fun a => (f a).1) ↔ Primrec f
  证明: by
  let : Primcodable { a // a < n } := Primcodable.subtype (nat_lt.comp .id (const _))
  exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)

Depends on / 依赖: Iff.trans, Primcodable, Primcodable.subtype, nat_lt, nat_lt.comp, of_equiv_iff, subtype, subtype_val_iff
-/
theorem fin_val_iff {n} {f : α -> Fin n} : (Primrec fun a => (f a).1) ↔ Primrec f := by
  let : Primcodable { a // a < n } := Primcodable.subtype (nat_lt.comp .id (const _))
  exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)

/--
theorem `fin_val` / 定理 `fin_val`

English:
theorem fin_val
  given: {n}
  statement: Primrec (fun (i : Fin n) => (i : Nat))
  proof: fin_val_iff.2 .id

中文:
定理 fin_val
  条件: {n}
  结论: Primrec (fun (i : 有限集 n) => (i : 自然数))
  证明: fin_val_iff.2 .id

Depends on / 依赖: fin_val_iff
-/
theorem fin_val {n} : Primrec (fun (i : Fin n) => (i : Nat)) :=
  fin_val_iff.2 .id

/--
theorem `fin_succ` / 定理 `fin_succ`

English:
theorem fin_succ
  given: {n}
  statement: Primrec (@Fin.succ n)
  proof: fin_val_iff.1 by simp [succ.comp fin_val]

中文:
定理 fin_succ
  条件: {n}
  结论: Primrec (@有限集.succ n)
  证明: fin_val_iff.1 by simp [succ.comp fin_val]

Depends on / 依赖: fin_val, fin_val_iff, succ.comp
-/
theorem fin_succ {n} : Primrec (@Fin.succ n) :=
fin_val_iff.1 by simp [succ.comp fin_val]

end Primrec
