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
/-
**Nat.unpaired** 是 Mathlib 中的一个定义，位于命名空间 `Nat`。
形式化陈述：unpaired {α} (f : Nat -> Nat -> α) (n : Nat) : α
参数：f : Nat -> Nat -> α；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Calls the given function on a pair of entries `n`, encoded via the pairing funct
ion.
-/
def unpaired {α} (f : ℕ → ℕ → α) (n : ℕ) : α :=
  f n.unpair.1 n.unpair.2

/-- The primitive recursive functions `ℕ → ℕ`. -/
/-
**Nat.Primrec** 是 Mathlib 中的一个归纳类型，位于命名空间 `Nat`。
形式化陈述：(ℕ → ℕ) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The primitive recursive functions `ℕ → ℕ`.
-/
protected inductive Primrec : (ℕ → ℕ) → Prop
  | zero : Nat.Primrec fun _ => 0
  | protected succ : Nat.Primrec succ
  | left : Nat.Primrec fun n => n.unpair.1
  | right : Nat.Primrec fun n => n.unpair.2
  | pair {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => pair (f n) (g n)
  | comp {f g} : Nat.Primrec f → Nat.Primrec g → Nat.Primrec fun n => f (g n)
  | prec {f g} :
      Nat.Primrec f →
        Nat.Primrec g →
          Nat.Primrec (unpaired fun z n => n.rec (f z) fun y IH => g <| pair z <| pair y IH)

namespace Primrec

/-
**Nat.Primrec.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : forall n, f n = g n) : 
Nat.Primrec g
参数：hf : Nat.Primrec f；H : forall n, f n = g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem of_eq {f g : ℕ → ℕ} (hf : Nat.Primrec f) (H : ∀ n, f n = g n) : Nat.Primrec g :=
  (funext H : f = g) ▸ hf
/-
**Nat.Primrec.const** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：const : forall n : Nat, Nat.Primrec fun _ => n | 0 => zero | n + 1 => Prim
rec.succ.comp (const n)  protected theorem id : Nat.Primrec id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const : ∀ n : ℕ, Nat.Primrec fun _ => n
  | 0 => zero
  | n + 1 => Primrec.succ.comp (const n)
/-
**Nat.Primrec.id** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：Nat.Primrec id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.pair_unpair`：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 
= n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem id : Nat.Primrec id :=
  (left.pair right).of_eq fun n => by simp
/-
**Nat.Primrec.prec1** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：prec1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.Primrec fun n => n.rec m fu
n y IH => f Nat.pair y IH
参数：m : Nat；hf : Nat.Primrec f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.const`：const : forall n : Nat, Nat.Primrec fun _ => n | 0 =>
 zero | n + 1 => Primrec.succ.comp (const n)  protected theorem id : Nat.Primrec
 id
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prec1 {f} (m : ℕ) (hf : Nat.Primrec f) :
    Nat.Primrec fun n => n.rec m fun y IH => f <| Nat.pair y IH :=
  ((prec (const m) (hf.comp right)).comp (zero.pair Primrec.id)).of_eq fun n => by simp
/-
**Nat.Primrec.casesOn1** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.Primrec (Nat.casesOn · m
 f)
参数：m : Nat；hf : Nat.Primrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.prec1`：prec1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.Primre
c fun n => n.rec m fun y IH => f Nat.pair y IH
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem casesOn1 {f} (m : ℕ) (hf : Nat.Primrec f) : Nat.Primrec (Nat.casesOn · m f) :=
  (prec1 m (hf.comp left)).of_eq <| by simp
/-
**Nat.Primrec.casesOn'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Primrec g) : Nat.Primrec (un
paired fun z n => n.casesOn (f z) fun y => g <| Nat.pair z y)
参数：hf : Nat.Primrec f；hg : Nat.Primrec g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Primrec g) :
    Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair z y) :=
  (prec hf (hg.comp (pair left (left.comp right)))).of_eq fun n => by simp
/-
**Nat.Primrec.swap** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：Nat.Primrec (Nat.unpaired (Function.swap Nat.pair))
参数：Nat.unpaired (Function.swap Nat.pair)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem swap : Nat.Primrec (unpaired (swap Nat.pair)) :=
  (pair right left).of_eq fun n => by simp
/-
**Nat.Primrec.swap'** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：swap' {f} (hf : Nat.Primrec (unpaired f)) : Nat.Primrec (unpaired (swap f)
)
参数：hf : Nat.Primrec (unpaired f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.swap`：Nat.Primrec (Nat.unpaired (Function.swap Nat.pair))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem swap' {f} (hf : Nat.Primrec (unpaired f)) : Nat.Primrec (unpaired (swap f)) :=
  (hf.comp .swap).of_eq fun n => by simp
/-
**Nat.Primrec.pred** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：pred : Nat.Primrec pred
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn1`：casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.
Primrec (Nat.casesOn · m f)
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem pred : Nat.Primrec pred :=
  (casesOn1 0 Primrec.id).of_eq fun n => by cases n <;> simp [*]
/-
**Nat.Primrec.add** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：add : Nat.Primrec (unpaired (· + ·))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_assoc`：∀ (n m k : ℕ), n + m + k = n + (m + k)
-/
theorem add : Nat.Primrec (unpaired (· + ·)) :=
  (prec .id ((Primrec.succ.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.add_assoc]
/-
**Nat.Primrec.sub** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：sub : Nat.Primrec (unpaired (· - ·))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sub_add_eq`：∀ (a b c : ℕ), a - (b + c) = a - b - c
-/
theorem sub : Nat.Primrec (unpaired (· - ·)) :=
  (prec .id ((pred.comp right).comp right)).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.sub_add_eq]
/-
**Nat.Primrec.mul** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：mul : Nat.Primrec (unpaired (· * ·))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.add`：add : Nat.Primrec (unpaired (· + ·))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mul : Nat.Primrec (unpaired (· * ·)) :=
  (prec zero (add.comp (pair left (right.comp right)))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, mul_succ, add_comm _ (unpair p).fst]
/-
**Nat.Primrec.pow** 是 Mathlib 中的一个定理，位于命名空间 `Nat.Primrec`。
形式化陈述：pow : Nat.Primrec (unpaired (· ^ ·))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.const`：const : forall n : Nat, Nat.Primrec fun _ => n | 0 =>
 zero | n + 1 => Primrec.succ.comp (const n)  protected theorem id : Nat.Primrec
 id
· 使用定理 `Nat.Primrec.mul`：mul : Nat.Primrec (unpaired (· * ·))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow : Nat.Primrec (unpaired (· ^ ·)) :=
  (prec (const 1) (mul.comp (pair (right.comp right) left))).of_eq fun p => by
    simp; induction p.unpair.2 <;> simp [*, Nat.pow_succ]

end Primrec

end Nat

/-- A `Primcodable` type is, essentially, an `Encodable` type for which
the encode/decode functions are primitive recursive.
However, such a definition is circular.

Instead, we ask that the composition of `decode : ℕ → Option α` with
`encode : Option α → ℕ` is primitive recursive. Said composition is
the identity function, restricted to the image of `encode`.
Thus, in a way, the added requirement ensures that no predicates
can be smuggled in through a cunning choice of the subset of `ℕ` into
which the type is encoded. -/
/-
**Primcodable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Primcodable` type is, essentially, an `Encodable` type for which
the encode/decode functions are primitive recursive.
However, such a definition is circular.

Instead, we ask that the composition of `decode : ℕ → Option α` with
`encode : Option α → ℕ` is primitive recursive. Said composition is
the identity function, restricted to the image of `encode`.
Thus, in a way, the added requirement ensures that no predicates
can be smuggled in through a cunning choice of the subset of `ℕ` into
which the type is encoded.
-/
class Primcodable (α : Type*) extends Encodable α where
  prim (α) : Nat.Primrec fun n => Encodable.encode (decode n)

namespace Primcodable

open Nat.Primrec

/-
**Primcodable.** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) ofDenumerable (α) [Denumerable α] : Primcodable α :=
  ⟨Nat.Primrec.succ.of_eq <| by simp⟩

/-- Builds a `Primcodable` instance from an equivalence to a `Primcodable` type. -/
@[instance_reducible]
/-
**Primcodable.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Primcodable`。
形式化陈述：ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β
参数：α；e : β ≃ α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Builds a `Primcodable` instance from an equivalence to a `Primcodable` type.
-/
def ofEquiv (α) {β} [Primcodable α] (e : β ≃ α) : Primcodable β :=
  { __ := Encodable.ofEquiv α e
    prim := (Primcodable.prim α).of_eq fun n => by
      rw [decode_ofEquiv]
      cases (@decode α _ n) <;>
        simp [encode_ofEquiv] }
/-
**Primcodable.empty** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：empty : Primcodable Empty
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance empty : Primcodable Empty :=
  ⟨zero⟩
/-
**Primcodable.unit** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：unit : Primcodable PUnit
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unit : Primcodable PUnit :=
  ⟨(casesOn1 1 zero).of_eq fun n => by cases n <;> simp⟩
/-
**Primcodable.option** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：option {α : Type*} [h : Primcodable α] : Primcodable (Option α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance option {α : Type*} [h : Primcodable α] : Primcodable (Option α) :=
  ⟨(casesOn1 1 ((casesOn1 0 (.comp .succ .succ)).comp (Primcodable.prim α))).of_eq fun n => by
    cases n with
      | zero => rfl
      | succ n =>
        rw [decode_option_succ]
        cases H : @decode α _ n <;> simp [H]⟩
/-
**Primcodable.bool** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：bool : Primcodable Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance bool : Primcodable Bool :=
  ⟨(casesOn1 1 (casesOn1 2 zero)).of_eq fun n => match n with
    | 0 => rfl
    | 1 => rfl
    | (n + 2) => by rw [decode_ge_two] <;> simp⟩

end Primcodable

/-- `Primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers). -/
/-
**Primrec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Primrec {α β} [Primcodable α] [Primcodable β] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Primrec f` means `f` is primitive recursive (after
  encoding its input and output as natural numbers).
-/
def Primrec {α β} [Primcodable α] [Primcodable β] (f : α → β) : Prop :=
  Nat.Primrec fun n => encode ((@decode α _ n).map f)

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

/-
**Primrec.encode** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodable.encode
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem encode : Primrec (@encode α _) :=
  (Primcodable.prim α).of_eq fun n => by cases @decode α _ n <;> rfl
/-
**Primrec.decode** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodable.decode
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
-/
protected theorem decode : Primrec (@decode α _) :=
  Nat.Primrec.succ.comp (Primcodable.prim α)
/-
**Primrec.dom_denumerable** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α -> β} : Primr
ec f ↔ Nat.Primrec fun n => encode (f (ofNat α n))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dom_denumerable {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n)) :=
  ⟨fun h => (pred.comp h).of_eq fun n => by simp, fun h =>
    (Nat.Primrec.succ.comp h).of_eq fun n => by simp⟩
/-
**Primrec.nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.dom_denumerable`：dom_denumerable {α β} [Denumerable α] [Primcoda
ble β] {f : α -> β} : Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n))
-/
theorem nat_iff {f : ℕ → ℕ} : Primrec f ↔ Nat.Primrec f :=
  dom_denumerable
/-
**Primrec.encdec** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：encdec : Primrec fun n => encode (@decode α _ n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.nat_iff`：nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
-/
theorem encdec : Primrec fun n => encode (@decode α _ n) :=
  nat_iff.2 (Primcodable.prim _)
/-
**Primrec.option_some** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_some : Primrec (@some α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn1`：casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.
Primrec (Nat.casesOn · m f)
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem option_some : Primrec (@some α) :=
  ((casesOn1 0 (Nat.Primrec.succ.comp .succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp
/-
**Primrec.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n = g n) : Primrec 
g
参数：hf : Primrec f；H : forall n, f n = g n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem of_eq {f g : α → σ} (hf : Primrec f) (H : ∀ n, f n = g n) : Primrec g :=
  (funext H : f = g) ▸ hf
/-
**Primrec.const** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：const (x : σ) : Primrec fun _ : α => x
参数：x : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn1`：casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.
Primrec (Nat.casesOn · m f)
· 使用定理 `Nat.Primrec.const`：const : forall n : Nat, Nat.Primrec fun _ => n | 0 =>
 zero | n + 1 => Primrec.succ.comp (const n)  protected theorem id : Nat.Primrec
 id
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem const (x : σ) : Primrec fun _ : α => x :=
  ((casesOn1 0 (.const (encode x).succ)).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> rfl
/-
**Primrec.id** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Option.map_id`：∀ {α : Type u_1}, Option.map id = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem id : Primrec (@id α) :=
  (Primcodable.prim α).of_eq <| by simp
/-
**Primrec.comp** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Primrec g) : Primrec
 fun a => f (g a)
参数：hf : Primrec f；hg : Primrec g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn1`：casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.
Primrec (Nat.casesOn · m f)
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem comp {f : β → σ} {g : α → β} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => f (g a) :=
  ((casesOn1 0 (.comp hf (pred.comp hg))).comp (Primcodable.prim α)).of_eq fun n => by
    cases @decode α _ n <;> simp [encodek]
/-
**Primrec.succ** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：succ : Primrec Nat.succ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.nat_iff`：nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f
-/
theorem succ : Primrec Nat.succ :=
  nat_iff.2 Nat.Primrec.succ
/-
**Primrec.pred** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：pred : Primrec Nat.pred
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.nat_iff`：nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
-/
theorem pred : Primrec Nat.pred :=
  nat_iff.2 Nat.Primrec.pred
/-
**Primrec.encode_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：encode_iff {f : α -> σ} : (Primrec fun a => encode (f a)) ↔ Primrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
-/
theorem encode_iff {f : α → σ} : (Primrec fun a => encode (f a)) ↔ Primrec f :=
  ⟨fun h => Nat.Primrec.of_eq h fun n => by cases @decode α _ n <;> rfl, Primrec.encode.comp⟩
/-
**Primrec.ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : α -> β} : Primrec f ↔
 Primrec fun n => f (ofNat α n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Primrec.dom_denumerable`：dom_denumerable {α β} [Denumerable α] [Primcoda
ble β] {f : α -> β} : Primrec f ↔ Nat.Primrec fun n => encode (f (ofNat α n))
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Primrec.nat_iff`：nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
-/
theorem ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : α → β} :
    Primrec f ↔ Primrec fun n => f (ofNat α n) :=
  dom_denumerable.trans <| nat_iff.symm.trans encode_iff
/-
**Primrec.ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：∀ (α : Type u_4) [inst : Denumerable α], Primrec (Denumerable.ofNat α)
参数：α : Type u_4；Denumerable.ofNat α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.ofNat_iff`：ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : 
α -> β} : Primrec f ↔ Primrec fun n => f (ofNat α n)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
-/
protected theorem ofNat (α) [Denumerable α] : Primrec (ofNat α) :=
  ofNat_iff.1 Primrec.id
/-
**Primrec.option_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_some_iff {f : α -> σ} : (Primrec fun a => some (f a)) ↔ Primrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.pred`：pred : Primrec Nat.pred
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.option_some`：option_some : Primrec (@some α)
-/
theorem option_some_iff {f : α → σ} : (Primrec fun a => some (f a)) ↔ Primrec f :=
  ⟨fun h => encode_iff.1 <| pred.comp <| encode_iff.2 h, option_some.comp⟩
/-
**Primrec.of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：of_equiv {β} {e : β ≃ α} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
-/
theorem of_equiv {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e :=
  letI : Primcodable β := Primcodable.ofEquiv α e
  encode_iff.1 Primrec.encode
/-
**Primrec.of_equiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：of_equiv_symm {β} {e : β ≃ α} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem of_equiv_symm {β} {e : β ≃ α} :
    haveI := Primcodable.ofEquiv α e
    Primrec e.symm :=
  letI := Primcodable.ofEquiv α e
  encode_iff.1 (show Primrec fun a => encode (e (e.symm a)) by simp [Primrec.encode])
/-
**Primrec.of_equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：of_equiv_iff {β} (e : β ≃ α) {f : σ -> β} : haveI
参数：e : β ≃ α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.of_equiv_symm`：of_equiv_symm {β} {e : β ≃ α} : haveI
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Primrec.of_equiv`：of_equiv {β} {e : β ≃ α} : haveI
-/
theorem of_equiv_iff {β} (e : β ≃ α) {f : σ → β} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv_symm.comp h).of_eq fun a => by simp, of_equiv.comp⟩
/-
**Primrec.of_equiv_symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：of_equiv_symm_iff {β} (e : β ≃ α) {f : σ -> α} : haveI
参数：e : β ≃ α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.of_equiv`：of_equiv {β} {e : β ≃ α} : haveI
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Primrec.of_equiv_symm`：of_equiv_symm {β} {e : β ≃ α} : haveI
-/
theorem of_equiv_symm_iff {β} (e : β ≃ α) {f : σ → α} :
    haveI := Primcodable.ofEquiv α e
    (Primrec fun a => e.symm (f a)) ↔ Primrec f :=
  letI := Primcodable.ofEquiv α e
  ⟨fun h => (of_equiv.comp h).of_eq fun a => by simp, of_equiv_symm.comp⟩

end Primrec

namespace Primcodable

open Nat.Primrec

/-
**Primcodable.prod** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：prod {α β} [Primcodable α] [Primcodable β] : Primcodable (α × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**Primrec.fst** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.fst α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn'`：casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Prim
rec g) : Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair
 z y)
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
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
/-
**Primrec.snd** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.snd α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn'`：casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Prim
rec g) : Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair
 z y)
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Option.map_id`：∀ {α : Type u_1}, Option.map id = id
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
/-
**Primrec.pair** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α -> β} 
{g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a => (f a, g a)
参数：hf : Primrec f；hg : Primrec g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn1`：casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.
Primrec (Nat.casesOn · m f)
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {f : α → β} {g : α → γ}
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => (f a, g a) :=
  ((casesOn1 0
            (Nat.Primrec.succ.comp <|
              .pair (Nat.Primrec.pred.comp hf) (Nat.Primrec.pred.comp hg))).comp
        (Primcodable.prim α)).of_eq
    fun n => by cases @decode α _ n <;> simp [encodek]
/-
**Primrec.unpair** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：unpair : Primrec Nat.unpair
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.pair`：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable 
γ] {f : α -> β} {g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a =
> …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.nat_iff`：nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unpair : Primrec Nat.unpair :=
  (pair (nat_iff.2 .left) (nat_iff.2 .right)).of_eq fun n => by simp
/-
**Primrec.list_getElem** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_getElem? : Primrec₂ ((·[·]? : List α -> Nat -> Option α))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem list_getElem?₁ : ∀ l : List α, Primrec (l[·]? : ℕ → Option α)
  | [] => dom_denumerable.2 zero
  | a :: l =>
    dom_denumerable.2 <|
      (casesOn1 (encode a).succ <| dom_denumerable.1 <| list_getElem?₁ l).of_eq fun n => by
        cases n <;> simp

end Primrec

/-- `Primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly. -/
/-
**Primrec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Primrec {α β} [Primcodable α] [Primcodable β] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Primrec₂ f` means `f` is a binary primitive recursive function.
  This is technically unnecessary since we can always curry all
  the arguments together, but there are enough natural two-arg
  functions that it is convenient to express this directly.
-/
def Primrec₂ {α β σ} [Primcodable α] [Primcodable β] [Primcodable σ] (f : α → β → σ) :=
  Primrec fun p : α × β => f p.1 p.2

/-- `PrimrecPred p` means `p : α → Prop` is a
  primitive recursive predicate, which is to say that
  `decide ∘ p : α → Bool` is primitive recursive. -/
/-
**PrimrecPred** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimrecPred {α} [Primcodable α] (p : α -> Prop)
参数：p : α -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PrimrecPred p` means `p : α → Prop` is a
  primitive recursive predicate, which is to say that
  `decide ∘ p : α → Bool` is primitive recursive.
-/
def PrimrecPred {α} [Primcodable α] (p : α → Prop) :=
  ∃ (_ : DecidablePred p), Primrec fun a => decide (p a)

/-- `PrimrecRel p` means `p : α → β → Prop` is a
  primitive recursive relation, which is to say that
  `decide ∘ p : α → β → Bool` is primitive recursive. -/
/-
**PrimrecRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PrimrecRel {α β} [Primcodable α] [Primcodable β] (s : α -> β -> Prop)
参数：s : α -> β -> Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PrimrecRel p` means `p : α → β → Prop` is a
  primitive recursive relation, which is to say that
  `decide ∘ p : α → β → Bool` is primitive recursive.
-/
def PrimrecRel {α β} [Primcodable α] [Primcodable β] (s : α → β → Prop) :=
  PrimrecPred fun p : α × β => s p.1 p.2

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

/-
**Primrec₂.mk** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：mk {f : α -> β -> σ} (hf : Primrec fun p : α × β => f p.1 p.2) : Primrec₂ 
f
参数：hf : Primrec fun p : α × β => f p.1 p.2。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk {f : α → β → σ} (hf : Primrec fun p : α × β => f p.1 p.2) : Primrec₂ f := hf
/-
**Primrec₂.of_eq** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall a b, f a b = g a b
) : Primrec₂ g
参数：hg : Primrec₂ f；H : forall a b, f a b = g a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem of_eq {f g : α → β → σ} (hg : Primrec₂ f) (H : ∀ a b, f a b = g a b) : Primrec₂ g :=
  (by funext a b; apply H : f = g) ▸ hg
/-
**Primrec₂.const** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：const (x : σ) : Primrec₂ fun (_ : α) (_ : β) => x
参数：x : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem const (x : σ) : Primrec₂ fun (_ : α) (_ : β) => x :=
  Primrec.const _
/-
**Primrec₂.pair** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le β], Primrec₂ Prod.mk
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.pair`：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable 
γ] {f : α -> β} {g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a =
> …
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
-/
protected theorem pair : Primrec₂ (@Prod.mk α β) :=
  Primrec.pair .fst .snd
/-
**Primrec₂.left** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：left : Primrec₂ fun (a : α) (_ : β) => a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
-/
theorem left : Primrec₂ fun (a : α) (_ : β) => a :=
  .fst
/-
**Primrec₂.right** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：right : Primrec₂ fun (_ : α) (b : β) => b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
-/
theorem right : Primrec₂ fun (_ : α) (b : β) => b :=
  .snd
/-
**Primrec₂.natPair** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：natPair : Primrec₂ Nat.pair
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Denumerable.decode_eq_ofNat`：decode_eq_ofNat (α) [Denumerable α] (n : Na
t) : decode (α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Denumerable.ofEquiv_ofNat`：ofEquiv_ofNat (α) {β} [Denumerable α] (e : β 
≃ α) (n) : @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n)
· 使用定理 `Denumerable.sigma_ofNat_val`：sigma_ofNat_val (n : Nat) : ofNat (Sigma γ)
 n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Nat.pair_unpair`：pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 
= n
-/
theorem natPair : Primrec₂ Nat.pair := by simp [Primrec₂, Primrec]; constructor
/-
**Primrec₂.unpaired** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：unpaired {f : Nat -> Nat -> α} : Primrec (Nat.unpaired f) ↔ Primrec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec₂.natPair`：natPair : Primrec₂ Nat.pair
· 使用定理 `Primrec.unpair`：unpair : Primrec Nat.unpair
-/
theorem unpaired {f : ℕ → ℕ → α} : Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  ⟨fun h => by simpa using! h.comp natPair, fun h => h.comp Primrec.unpair⟩
/-
**Primrec₂.unpaired'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：unpaired' {f : Nat -> Nat -> Nat} : Nat.Primrec (Nat.unpaired f) ↔ Primrec
₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Primrec.nat_iff`：nat_iff {f : Nat -> Nat} : Primrec f ↔ Nat.Primrec f
· 使用定理 `Primrec₂.unpaired`：unpaired {f : Nat -> Nat -> α} : Primrec (Nat.unpaire
d f) ↔ Primrec₂ f
-/
theorem unpaired' {f : ℕ → ℕ → ℕ} : Nat.Primrec (Nat.unpaired f) ↔ Primrec₂ f :=
  Primrec.nat_iff.symm.trans unpaired
/-
**Primrec₂.encode_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：encode_iff {f : α -> β -> σ} : (Primrec₂ fun a b => encode (f a b)) ↔ Prim
rec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
-/
theorem encode_iff {f : α → β → σ} : (Primrec₂ fun a b => encode (f a b)) ↔ Primrec₂ f :=
  Primrec.encode_iff
/-
**Primrec₂.option_some_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：option_some_iff {f : α -> β -> σ} : (Primrec₂ fun a b => some (f a b)) ↔ P
rimrec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
-/
theorem option_some_iff {f : α → β → σ} : (Primrec₂ fun a b => some (f a b)) ↔ Primrec₂ f :=
  Primrec.option_some_iff
/-
**Primrec₂.ofNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：ofNat_iff {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α -
> β -> σ} : Primrec₂ f ↔ Primrec₂ fun m n : Nat => f (ofNat α m) (ofNat β n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Primrec.ofNat_iff`：ofNat_iff {α β} [Denumerable α] [Primcodable β] {f : 
α -> β} : Primrec f ↔ Primrec fun n => f (ofNat α n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Denumerable.ofEquiv_ofNat`：ofEquiv_ofNat (α) {β} [Denumerable α] (e : β 
≃ α) (n) : @ofNat β (ofEquiv _ e) n = e.symm (ofNat α n)
· 使用定理 `Denumerable.sigma_ofNat_val`：sigma_ofNat_val (n : Nat) : ofNat (Sigma γ)
 n = ⟨ofNat α (unpair n).1, ofNat (γ _) (unpair n).2⟩
· 使用定理 `Equiv.sigmaEquivProd_apply`：∀ (α : Type u_1) (β : Type u_2) (a : (_ : α)
 × β), (Equiv.sigmaEquivProd α β) a = (a.fst, a.snd)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Primrec₂.unpaired`：unpaired {f : Nat -> Nat -> α} : Primrec (Nat.unpaire
d f) ↔ Primrec₂ f
-/
theorem ofNat_iff {α β σ} [Denumerable α] [Denumerable β] [Primcodable σ] {f : α → β → σ} :
    Primrec₂ f ↔ Primrec₂ fun m n : ℕ => f (ofNat α m) (ofNat β n) :=
  (Primrec.ofNat_iff.trans <| by simp).trans unpaired
/-
**Primrec₂.uncurry** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：uncurry {f : α -> β -> σ} : Primrec (Function.uncurry f) ↔ Primrec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem uncurry {f : α → β → σ} : Primrec (Function.uncurry f) ↔ Primrec₂ f := by
  rw [show Function.uncurry f = fun p : α × β => f p.1 p.2 from funext fun ⟨a, b⟩ => rfl]; rfl
/-
**Primrec₂.curry** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：curry {f : α × β -> σ} : Primrec₂ (Function.curry f) ↔ Primrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Primrec₂.uncurry`：uncurry {f : α -> β -> σ} : Primrec (Function.uncurry 
f) ↔ Primrec₂ f
· 使用定理 `Function.uncurry_curry`：∀ {α : Type u_1} {β : Type u_2} {φ : Sort u_3} (
f : α × β → φ), Function.uncurry (Function.curry f) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem curry {f : α × β → σ} : Primrec₂ (Function.curry f) ↔ Primrec f := by
  rw [← uncurry, Function.uncurry_curry]

end Primrec₂

section Comp

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ] [Primcodable σ]

/-
**Primrec.comp** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Primrec g) : Primrec
 fun a => f (g a)
参数：hf : Primrec f；hg : Primrec g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn1`：casesOn1 {f} (m : Nat) (hf : Nat.Primrec f) : Nat.
Primrec (Nat.casesOn · m f)
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem Primrec.comp₂ {f : γ → σ} {g : α → β → γ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a b => f (g a b) :=
  hf.comp hg
/-
**Primrec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Primrec {α β} [Primcodable α] [Primcodable β] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Primrec₂.comp {f : β → γ → σ} {g : α → β} {h : α → γ} (hf : Primrec₂ f) (hg : Primrec g)
    (hh : Primrec h) : Primrec fun a => f (g a) (h a) :=
  Primrec.comp hf (hg.pair hh)
/-
**Primrec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Primrec {α β} [Primcodable α] [Primcodable β] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Primrec₂.comp₂ {f : γ → δ → σ} {g : α → β → γ} {h : α → β → δ} (hf : Primrec₂ f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fun a b => f (g a b) (h a b) :=
  hf.comp hg hh
/-
**PrimrecPred.decide** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecPred`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Prop} [inst_1 : Decidable
Pred p],   PrimrecPred p → Primrec fun a => decide (p a)
参数：p a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
protected lemma PrimrecPred.decide {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) :
    Primrec (fun a => decide (p a)) := by
  convert! hp.choose_spec
/-
**Primrec.primrecPred** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Primrec.primrecPred {p : α -> Prop} [DecidablePred p] (hp : Primrec (fun a
 => decide (p a))) : PrimrecPred p
参数：hp : Primrec (fun a => decide (p a))。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Primrec.primrecPred {p : α → Prop} [DecidablePred p]
    (hp : Primrec (fun a => decide (p a))) : PrimrecPred p :=
  ⟨inferInstance, hp⟩
/-
**primrecPred_iff_primrec_decide** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：primrecPred_iff_primrec_decide {p : α -> Prop} [DecidablePred p] : Primrec
Pred p ↔ Primrec (fun a => decide (p a)) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.decide`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Pro
p} [inst_1 : DecidablePred p],   PrimrecPred p → Primrec fun a => decide (p a)
· 使用引理 `Primrec.primrecPred`：Primrec.primrecPred {p : α -> Prop} [DecidablePred 
p] (hp : Primrec (fun a => decide (p a))) : PrimrecPred p
-/
lemma primrecPred_iff_primrec_decide {p : α → Prop} [DecidablePred p] :
    PrimrecPred p ↔ Primrec (fun a => decide (p a)) where
  mp := PrimrecPred.decide
  mpr := Primrec.primrecPred
/-
**PrimrecPred.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PrimrecPred.comp {p : β -> Prop} {f : α -> β} : (hp : PrimrecPred p) -> (h
f : Primrec f) -> PrimrecPred fun a => p (f a) .primrecPred | ⟨_i, hp⟩, hf => hp
.comp hf  protected lemma PrimrecRel.decide {R : α -> β -> Prop} [DecidableRel R
] (hR : PrimrecRel R) : Primrec₂ (fun a b => decide (R a b))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Primrec.primrecPred`：Primrec.primrecPred {p : α -> Prop} [DecidablePred 
p] (hp : Primrec (fun a => decide (p a))) : PrimrecPred p
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
-/
theorem PrimrecPred.comp {p : β → Prop} {f : α → β} :
    (hp : PrimrecPred p) → (hf : Primrec f) → PrimrecPred fun a => p (f a)
  | ⟨_i, hp⟩, hf => hp.comp hf |>.primrecPred
/-
**PrimrecRel.decide** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] [inst_1 : Primcodab
le β] {R : α → β → Prop}   [inst_2 : DecidableRel R], PrimrecRel R → Primrec₂ fu
n a b => decide (R a b)
参数：R a b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.decide`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Pro
p} [inst_1 : DecidablePred p],   PrimrecPred p → Primrec fun a => decide (p a)
-/
protected lemma PrimrecRel.decide {R : α → β → Prop} [DecidableRel R] (hR : PrimrecRel R) :
    Primrec₂ (fun a b => decide (R a b)) :=
  PrimrecPred.decide hR
/-
**Primrec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Primrec {α β} [Primcodable α] [Primcodable β] (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Primrec₂.primrecRel {R : α → β → Prop} [DecidableRel R]
    (hp : Primrec₂ (fun a b => decide (R a b))) : PrimrecRel R :=
  Primrec.primrecPred hp
/-
**primrecRel_iff_primrec_decide** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：primrecRel_iff_primrec_decide {R : α -> β -> Prop} [DecidableRel R] : Prim
recRel R ↔ Primrec₂ (fun a b => decide (R a b)) where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecRel.decide`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α
] [inst_1 : Primcodable β] {R : α → β → Prop}   [inst_2 : DecidableRel R], Primr
ecRel R…
· 使用引理 `Primrec₂.primrecRel`：Primrec₂.primrecRel {R : α -> β -> Prop} [Decidable
Rel R] (hp : Primrec₂ (fun a b => decide (R a b))) : PrimrecRel R
-/
lemma primrecRel_iff_primrec_decide {R : α → β → Prop} [DecidableRel R] :
    PrimrecRel R ↔ Primrec₂ (fun a b => decide (R a b)) where
  mp := PrimrecRel.decide
  mpr := Primrec₂.primrecRel
/-
**PrimrecRel.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : α -> γ} (hR : Primr
ecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a => R (f a) (g a)
参数：hR : PrimrecRel R；hf : Primrec f；hg : Primrec g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.comp`：PrimrecPred.comp {p : β -> Prop} {f : α -> β} : (hp : 
PrimrecPred p) -> (hf : Primrec f) -> PrimrecPred fun a => p (f a) .primrecPred 
| ⟨_i,…
· 使用定理 `Primrec.pair`：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable 
γ] {f : α -> β} {g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a =
> …
-/
theorem PrimrecRel.comp {R : β → γ → Prop} {f : α → β} {g : α → γ}
    (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a => R (f a) (g a) :=
  PrimrecPred.comp hR (hf.pair hg)
/-
**PrimrecRel.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : α -> γ} (hR : Primr
ecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun a => R (f a) (g a)
参数：hR : PrimrecRel R；hf : Primrec f；hg : Primrec g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.comp`：PrimrecPred.comp {p : β -> Prop} {f : α -> β} : (hp : 
PrimrecPred p) -> (hf : Primrec f) -> PrimrecPred fun a => p (f a) .primrecPred 
| ⟨_i,…
· 使用定理 `Primrec.pair`：pair {α β γ} [Primcodable α] [Primcodable β] [Primcodable 
γ] {f : α -> β} {g : α -> γ} (hf : Primrec f) (hg : Primrec g) : Primrec fun a =
> …
-/
theorem PrimrecRel.comp₂ {R : γ → δ → Prop} {f : α → β → γ} {g : α → β → δ} :
    PrimrecRel R → Primrec₂ f → Primrec₂ g → PrimrecRel fun a b => R (f a b) (g a b) :=
  PrimrecRel.comp

end Comp

/-
**PrimrecPred.of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Prop} (hp : PrimrecPred 
p) (H : forall a, p a ↔ q a) : PrimrecPred q
参数：hp : PrimrecPred p；H : forall a, p a ↔ q a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem PrimrecPred.of_eq {α} [Primcodable α] {p q : α → Prop}
    (hp : PrimrecPred p) (H : ∀ a, p a ↔ q a) : PrimrecPred q :=
  funext (fun a => propext (H a)) ▸ hp
/-
**PrimrecRel.of_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β] {r s : α -> β -> Pr
op} (hr : PrimrecRel r) (H : forall a b, r a b ↔ s a b) : PrimrecRel s
参数：hr : PrimrecRel r；H : forall a b, r a b ↔ s a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
-/
theorem PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β] {r s : α → β → Prop}
    (hr : PrimrecRel r) (H : ∀ a b, r a b ↔ s a b) : PrimrecRel s :=
  funext₂ (fun a b => propext (H a b)) ▸ hr

namespace Primrec₂

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Nat.Primrec

/-
**Primrec₂.swap** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {σ : Type u_3} [inst : Primcodable α] [ins
t_1 : Primcodable β] [inst_2 : Primcodable σ]   {f : α → β → σ}, Primrec₂ f → Pr
imrec₂ (Function.swap f)
参数：Function.swap f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `Primrec₂.left`：left : Primrec₂ fun (a : α) (_ : β) => a
-/
protected theorem swap {f : α → β → σ} (h : Primrec₂ f) : Primrec₂ (swap f) :=
  h.comp₂ Primrec₂.right Primrec₂.left
/-
**Primrec₂._root_.PrimrecRel.swap** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.PrimrecRel.swap {r : α → β → Prop} (h : PrimrecRel r) :
    PrimrecRel (swap r) :=
  h.comp₂ Primrec₂.right Primrec₂.left
/-
**Primrec₂.nat_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：nat_iff {f : α -> β -> σ} : Primrec₂ f ↔ Nat.Primrec (.unpaired fun m n =>
 encode <| (@decode α _ m).bind fun a => (@decode β _ n).map (f a))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nat_iff {f : α → β → σ} : Primrec₂ f ↔ Nat.Primrec
    (.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map (f a)) := by
  have :
    ∀ (a : Option α) (b : Option β),
      Option.map (fun p : α × β => f p.1 p.2)
          (Option.bind a fun a : α => Option.map (Prod.mk a) b) =
        Option.bind a fun a => Option.map (f a) b := fun a b => by
          cases a <;> cases b <;> rfl
  simp [Primrec₂, Primrec, this]
/-
**Primrec₂.nat_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec₂`。
形式化陈述：nat_iff' {f : α -> β -> σ} : Primrec₂ f ↔ Primrec₂ fun m n : Nat => (@deco
de α _ m).bind fun a => Option.map (f a) (@decode β _ n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Primrec₂.nat_iff`：nat_iff {f : α -> β -> σ} : Primrec₂ f ↔ Nat.Primrec (
.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map
 (f a)…
· 使用定理 `Primrec₂.unpaired'`：unpaired' {f : Nat -> Nat -> Nat} : Nat.Primrec (Nat
.unpaired f) ↔ Primrec₂ f
· 使用定理 `Primrec₂.encode_iff`：encode_iff {f : α -> β -> σ} : (Primrec₂ fun a b =>
 encode (f a b)) ↔ Primrec₂ f
-/
theorem nat_iff' {f : α → β → σ} :
    Primrec₂ f ↔
      Primrec₂ fun m n : ℕ => (@decode α _ m).bind fun a => Option.map (f a) (@decode β _ n) :=
  nat_iff.trans <| unpaired'.trans encode_iff

end Primrec₂

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

/-
**Primrec.to** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to₂ {f : α × β → σ} (hf : Primrec f) : Primrec₂ fun a b => f (a, b) :=
  hf
/-
**Primrec._root_.PrimrecPred.primrecRel** 是 Mathlib 中的一个引理，位于命名空间 `Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.PrimrecPred.primrecRel {p : α × β → Prop} (hp : PrimrecPred p) :
    PrimrecRel fun a b => p (a, b) :=
  hp
/-
**Primrec.nat_rec** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_rec {f : α -> β} {g : α -> Nat × β -> β} (hf : Primrec f) (hg : Primre
c₂ g) : Primrec₂ fun a (n : Nat) => n.rec (motive
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec₂.nat_iff`：nat_iff {f : α -> β -> σ} : Primrec₂ f ↔ Nat.Primrec (
.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map
 (f a)…
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn'`：casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Prim
rec g) : Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair
 z y)
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem nat_rec {f : α → β} {g : α → ℕ × β → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => n.rec (motive := fun _ => β) (f a) fun n IH => g a (n, IH) :=
  Primrec₂.nat_iff.2 <|
    ((Nat.Primrec.casesOn' .zero <|
              (Nat.Primrec.prec hf <|
                    .comp hg <|
                      Nat.Primrec.left.pair <|
                        (Nat.Primrec.left.comp .right).pair <|
                          Nat.Primrec.pred.comp <| Nat.Primrec.right.comp .right).comp <|
                Nat.Primrec.right.pair <| Nat.Primrec.right.comp Nat.Primrec.left).comp <|
          Nat.Primrec.id.pair <| (Primcodable.prim α).comp Nat.Primrec.left).of_eq
      fun n => by
      simp only [Nat.unpaired, id_eq, Nat.unpair_pair, decode_prod_val, decode_nat,
        Option.bind_some, Option.map_map, Option.map_some]
      rcases @decode α _ n.unpair.1 with - | a; · rfl
      simp only [Nat.pred_eq_sub_one, encode_some, Nat.succ_eq_add_one, encodek, Option.map_some,
        Option.bind_some, Option.map_map]
      induction n.unpair.2 <;> simp [*, encodek]
/-
**Primrec.nat_rec'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_rec' {f : α -> Nat} {g : α -> β} {h : α -> Nat × β -> β} (hf : Primrec
 f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (f a).rec (motive
参数：hf : Primrec f；hg : Primrec g；hh : Primrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.nat_rec`：nat_rec {f : α -> β} {g : α -> Nat × β -> β} (hf : Prim
rec f) (hg : Primrec₂ g) : Primrec₂ fun a (n : Nat) => n.rec (motive
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
-/
theorem nat_rec' {f : α → ℕ} {g : α → β} {h : α → ℕ × β → β}
    (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) :
    Primrec fun a => (f a).rec (motive := fun _ => β) (g a) fun n IH => h a (n, IH) :=
  (nat_rec hg hh).comp .id hf
/-
**Primrec.nat_rec** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_rec {f : α -> β} {g : α -> Nat × β -> β} (hf : Primrec f) (hg : Primre
c₂ g) : Primrec₂ fun a (n : Nat) => n.rec (motive
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec₂.nat_iff`：nat_iff {f : α -> β -> σ} : Primrec₂ f ↔ Nat.Primrec (
.unpaired fun m n => encode <| (@decode α _ m).bind fun a => (@decode β _ n).map
 (f a)…
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.casesOn'`：casesOn' {f g} (hf : Nat.Primrec f) (hg : Nat.Prim
rec g) : Nat.Primrec (unpaired fun z n => n.casesOn (f z) fun y => g <| Nat.pair
 z y)
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `Nat.Primrec.id`：Nat.Primrec id
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.unpair_pair`：unpair_pair (a b : Nat) : unpair (pair a b) = (a, b)
· 使用定理 `Encodable.decode_prod_val`：decode_prod_val (n : Nat) : (@decode (α × β) 
_ n : Option (α × β)) = (decode n.unpair.1).bind fun a => (decode n.unpair.2).ma
p Prod.mk a
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Option.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} (h : β → 
γ) (g : α → β) (x : Option α),   Option.map h (Option.map g x) = Option.map (h ∘
 g) …
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem nat_rec₁ {f : ℕ → α → α} (a : α) (hf : Primrec₂ f) : Primrec (Nat.rec a f) :=
  nat_rec' .id (const a) <| comp₂ hf Primrec₂.right
/-
**Primrec.nat_casesOn'** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_casesOn' {f : α -> β} {g : α -> Nat -> β} (hf : Primrec f) (hg : Primr
ec₂ g) : Primrec₂ fun a (n : Nat) => (n.casesOn (f a) (g a) : β)
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.nat_rec`：nat_rec {f : α -> β} {g : α -> Nat × β -> β} (hf : Prim
rec f) (hg : Primrec₂ g) : Primrec₂ fun a (n : Nat) => n.rec (motive
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec₂.left`：left : Primrec₂ fun (a : α) (_ : β) => a
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
-/
theorem nat_casesOn' {f : α → β} {g : α → ℕ → β} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec₂ fun a (n : ℕ) => (n.casesOn (f a) (g a) : β) :=
  nat_rec hf <| hg.comp₂ Primrec₂.left <| comp₂ fst Primrec₂.right
/-
**Primrec.nat_casesOn** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_casesOn {f : α -> Nat} {g : α -> β} {h : α -> Nat -> β} (hf : Primrec 
f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => ((f a).casesOn (g a) (h
 a) : β)
参数：hf : Primrec f；hg : Primrec g；hh : Primrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.nat_casesOn'`：nat_casesOn' {f : α -> β} {g : α -> Nat -> β} (hf 
: Primrec f) (hg : Primrec₂ g) : Primrec₂ fun a (n : Nat) => (n.casesOn (f a) (g
 a) : β)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
-/
theorem nat_casesOn {f : α → ℕ} {g : α → β} {h : α → ℕ → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => ((f a).casesOn (g a) (h a) : β) :=
  (nat_casesOn' hg hh).comp .id hf
/-
**Primrec.nat_casesOn** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_casesOn {f : α -> Nat} {g : α -> β} {h : α -> Nat -> β} (hf : Primrec 
f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => ((f a).casesOn (g a) (h
 a) : β)
参数：hf : Primrec f；hg : Primrec g；hh : Primrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.nat_casesOn'`：nat_casesOn' {f : α -> β} {g : α -> Nat -> β} (hf 
: Primrec f) (hg : Primrec₂ g) : Primrec₂ fun a (n : Nat) => (n.casesOn (f a) (g
 a) : β)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
-/
theorem nat_casesOn₁ {f : ℕ → α} (a : α) (hf : Primrec f) :
    Primrec (fun (n : ℕ) => (n.casesOn a f : α)) :=
  nat_casesOn .id (const a) (comp₂ hf .right)
/-
**Primrec.nat_iterate** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_iterate {f : α -> Nat} {g : α -> β} {h : α -> β -> β} (hf : Primrec f)
 (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (h a)^[f a] (g a)
参数：hf : Primrec f；hg : Primrec g；hh : Primrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_rec'`：nat_rec' {f : α -> Nat} {g : α -> β} {h : α -> Nat × β
 -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (f
 a).re…
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec₂.left`：left : Primrec₂ fun (a : α) (_ : β) => a
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.iterate_succ'`：iterate_succ' (n : Nat) : f^[n.succ] = f ∘ f^[n]
-/
theorem nat_iterate {f : α → ℕ} {g : α → β} {h : α → β → β} (hf : Primrec f) (hg : Primrec g)
    (hh : Primrec₂ h) : Primrec fun a => (h a)^[f a] (g a) :=
  (nat_rec' hf hg (hh.comp₂ Primrec₂.left <| snd.comp₂ Primrec₂.right)).of_eq fun a => by
    induction f a <;> simp [*, -Function.iterate_succ, Function.iterate_succ']
/-
**Primrec.option_casesOn** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_casesOn {o : α -> Option β} {f : α -> σ} {g : α -> β -> σ} (ho : Pr
imrec o) (hf : Primrec f) (hg : Primrec₂ g) : @Primrec _ σ _ _ fun a => Option.c
asesOn (o a) (f a) (g a)
参数：ho : Primrec o；hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_casesOn`：nat_casesOn {f : α -> Nat} {g : α -> β} {h : α -> N
at -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => 
((f a).ca…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.pred`：pred : Primrec Nat.pred
· 使用定理 `Primrec₂.encode_iff`：encode_iff {f : α -> β -> σ} : (Primrec₂ fun a b =>
 encode (f a b)) ↔ Primrec₂ f
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec₂.nat_iff'`：nat_iff' {f : α -> β -> σ} : Primrec₂ f ↔ Primrec₂ fu
n m n : Nat => (@decode α _ m).bind fun a => Option.map (f a) (@decode β _ n)
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem option_casesOn {o : α → Option β} {f : α → σ} {g : α → β → σ} (ho : Primrec o)
    (hf : Primrec f) (hg : Primrec₂ g) :
    @Primrec _ σ _ _ fun a => Option.casesOn (o a) (f a) (g a) :=
  encode_iff.1 <|
    (nat_casesOn (encode_iff.2 ho) (encode_iff.2 hf) <|
          pred.comp₂ <|
            Primrec₂.encode_iff.2 <|
              (Primrec₂.nat_iff'.1 hg).comp₂ ((@Primrec.encode α _).comp fst).to₂
                Primrec₂.right).of_eq
      fun a => by rcases o a with - | b <;> simp [encodek]
/-
**Primrec.option_bind** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_bind {f : α -> Option β} {g : α -> β -> Option σ} (hf : Primrec f) 
(hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.option_casesOn`：option_casesOn {o : α -> Option β} {f : α -> σ} 
{g : α -> β -> σ} (ho : Primrec o) (hf : Primrec f) (hg : Primrec₂ g) : @Primrec
 _ σ _ _ fun…
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_bind {f : α → Option β} {g : α → β → Option σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).bind (g a) :=
  (option_casesOn hf (const none) hg).of_eq fun a => by cases f a <;> rfl
/-
**Primrec.option_bind** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_bind {f : α -> Option β} {g : α -> β -> Option σ} (hf : Primrec f) 
(hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.option_casesOn`：option_casesOn {o : α -> Option β} {f : α -> σ} 
{g : α -> β -> σ} (ho : Primrec o) (hf : Primrec f) (hg : Primrec₂ g) : @Primrec
 _ σ _ _ fun…
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_bind₁ {f : α → Option σ} (hf : Primrec f) : Primrec fun o => Option.bind o f :=
  option_bind .id (hf.comp snd).to₂
/-
**Primrec.option_map** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_map {f : α -> Option β} {g : α -> β -> σ} (hf : Primrec f) (hg : Pr
imrec₂ g) : Primrec fun a => (f a).map (g a)
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> Opti
on σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.option_some`：option_some : Primrec (@some α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_map {f : α → Option β} {g : α → β → σ} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec fun a => (f a).map (g a) :=
  (option_bind hf (option_some.comp₂ hg)).of_eq fun x => by cases f x <;> rfl
/-
**Primrec.option_map** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_map {f : α -> Option β} {g : α -> β -> σ} (hf : Primrec f) (hg : Pr
imrec₂ g) : Primrec fun a => (f a).map (g a)
参数：hf : Primrec f；hg : Primrec₂ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> Opti
on σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.option_some`：option_some : Primrec (@some α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_map₁ {f : α → σ} (hf : Primrec f) : Primrec (Option.map f) :=
  option_map .id (hf.comp snd).to₂
/-
**Primrec.option_getD** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_getD : Primrec₂ (@Option.getD α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.option_casesOn`：option_casesOn {o : α -> Option β} {f : α -> σ} 
{g : α -> β -> σ} (ho : Primrec o) (hf : Primrec f) (hg : Primrec₂ g) : @Primrec
 _ σ _ _ fun…
· 使用定理 `Primrec₂.left`：left : Primrec₂ fun (a : α) (_ : β) => a
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_getD : Primrec₂ (@Option.getD α) :=
  Primrec.of_eq (option_casesOn Primrec₂.left Primrec₂.right .right) fun ⟨o, a⟩ => by
    cases o <;> rfl
/-
**Primrec.option_getD_default** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_getD_default [Inhabited α] : Primrec (fun o : Option α => o.getD de
fault)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.option_getD`：option_getD : Primrec₂ (@Option.getD α)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem option_getD_default [Inhabited α] : Primrec (fun o : Option α => o.getD default) :=
  option_getD.comp .id (const default)

@[deprecated option_getD_default (since := "2026-01-05")]
/-
**Primrec.option_iget** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_iget [Inhabited α] : Primrec (@Option.iget α _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.option_getD_default`：option_getD_default [Inhabited α] : Primrec
 (fun o : Option α => o.getD default)
-/
theorem option_iget [Inhabited α] : Primrec (@Option.iget α _) :=
  option_getD_default
/-
**Primrec.option_isSome** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_isSome : Primrec (@Option.isSome α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.option_casesOn`：option_casesOn {o : α -> Option β} {f : α -> σ} 
{g : α -> β -> σ} (ho : Primrec o) (hf : Primrec f) (hg : Primrec₂ g) : @Primrec
 _ σ _ _ fun…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_isSome : Primrec (@Option.isSome α) :=
  (option_casesOn .id (const false) (const true).to₂).of_eq fun o => by cases o <;> rfl
/-
**Primrec.bind_decode_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：bind_decode_iff {f : α -> β -> Option σ} : (Primrec₂ fun a n => (@decode β
 _ n).bind (f a)) ↔ Primrec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.bind_congr'`：bind_congr' {f g : α -> Option β} {x y : Option α} (
hx : x = y) (hf : forall a in y, f a = g a) : x.bind f = y.bind g
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> Opti
on σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)
· 使用定理 `Primrec.decode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.decode
-/
theorem bind_decode_iff {f : α → β → Option σ} :
    (Primrec₂ fun a n => (@decode β _ n).bind (f a)) ↔ Primrec₂ f :=
  ⟨fun h => by simpa [encodek] using! h.comp fst ((@Primrec.encode β _).comp snd), fun h =>
    option_bind (Primrec.decode.comp snd) <| h.comp (fst.comp fst) snd⟩
/-
**Primrec.map_decode_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：map_decode_iff {f : α -> β -> σ} : (Primrec₂ fun a n => (@decode β _ n).ma
p (f a)) ↔ Primrec₂ f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Option.map_eq_bind`：∀ {α : Type u_1} {α_1 : Type u_2} {f : α → α_1} {x :
 Option α}, Option.map f x = x.bind (some ∘ f)
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Primrec.bind_decode_iff`：bind_decode_iff {f : α -> β -> Option σ} : (Pri
mrec₂ fun a n => (@decode β _ n).bind (f a)) ↔ Primrec₂ f
· 使用定理 `Primrec₂.option_some_iff`：option_some_iff {f : α -> β -> σ} : (Primrec₂ 
fun a b => some (f a b)) ↔ Primrec₂ f
-/
theorem map_decode_iff {f : α → β → σ} :
    (Primrec₂ fun a n => (@decode β _ n).map (f a)) ↔ Primrec₂ f := by
  simp only [Option.map_eq_bind]
  exact bind_decode_iff.trans Primrec₂.option_some_iff
/-
**Primrec.nat_add** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_add : Primrec₂ ((· + ·) : Nat -> Nat -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec₂.unpaired'`：unpaired' {f : Nat -> Nat -> Nat} : Nat.Primrec (Nat
.unpaired f) ↔ Primrec₂ f
· 使用定理 `Nat.Primrec.add`：add : Nat.Primrec (unpaired (· + ·))
-/
theorem nat_add : Primrec₂ ((· + ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.add
/-
**Primrec.nat_sub** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_sub : Primrec₂ ((· - ·) : Nat -> Nat -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec₂.unpaired'`：unpaired' {f : Nat -> Nat -> Nat} : Nat.Primrec (Nat
.unpaired f) ↔ Primrec₂ f
· 使用定理 `Nat.Primrec.sub`：sub : Nat.Primrec (unpaired (· - ·))
-/
theorem nat_sub : Primrec₂ ((· - ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.sub
/-
**Primrec.nat_mul** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_mul : Primrec₂ ((· * ·) : Nat -> Nat -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec₂.unpaired'`：unpaired' {f : Nat -> Nat -> Nat} : Nat.Primrec (Nat
.unpaired f) ↔ Primrec₂ f
· 使用定理 `Nat.Primrec.mul`：mul : Nat.Primrec (unpaired (· * ·))
-/
theorem nat_mul : Primrec₂ ((· * ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.mul
/-
**Primrec.cond** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primrec c) (hf : Prim
rec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) else (g a)
参数：hc : Primrec c；hf : Primrec f；hg : Primrec g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_casesOn`：nat_casesOn {f : α -> Nat} {g : α -> β} {h : α -> N
at -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => 
((f a).ca…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cond {c : α → Bool} {f : α → σ} {g : α → σ} (hc : Primrec c) (hf : Primrec f)
    (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) else (g a) :=
  (nat_casesOn (encode_iff.2 hc) hg (hf.comp fst).to₂).of_eq fun a => by cases c a <;> rfl
/-
**Primrec.ite** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -> σ} (hc : Prim
recPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a 
else g a
参数：hc : PrimrecPred c；hf : Primrec f；hg : Primrec g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Bool.cond_decide`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (t e 
: α), (bif decide p then t else e) = if p then t else e
· 使用定理 `Primrec.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primr
ec c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) 
el…
· 使用定理 `PrimrecPred.decide`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Pro
p} [inst_1 : DecidablePred p],   PrimrecPred p → Primrec fun a => decide (p a)
-/
theorem ite {c : α → Prop} [DecidablePred c] {f : α → σ} {g : α → σ} (hc : PrimrecPred c)
    (hf : Primrec f) (hg : Primrec g) : Primrec fun a => if c a then f a else g a := by
  simpa [Bool.cond_decide] using cond hc.decide hf hg
/-
**Primrec.nat_le** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_le : PrimrecRel ((· <= ·) : Nat -> Nat -> Prop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Primrec₂.primrecRel`：Primrec₂.primrecRel {R : α -> β -> Prop} [Decidable
Rel R] (hp : Primrec₂ (fun a b => decide (R a b))) : PrimrecRel R
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_casesOn`：nat_casesOn {f : α -> Nat} {g : α -> β} {h : α -> N
at -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => 
((f a).ca…
· 使用定理 `Primrec.nat_sub`：nat_sub : Primrec₂ ((· - ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.sub_eq_zero_iff_le`：∀ {n m : ℕ}, n - m = 0 ↔ n ≤ m
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.lt_of_sub_eq_succ`：∀ {m n l : ℕ}, m - n = l.succ → n < m
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
-/
theorem nat_le : PrimrecRel ((· ≤ ·) : ℕ → ℕ → Prop) :=
  Primrec₂.primrecRel ((nat_casesOn nat_sub (const true) (const false).to₂).of_eq fun p => by
    dsimp [swap]
    rcases e : p.1 - p.2 with - | n
    · simp [Nat.sub_eq_zero_iff_le.1 e]
    · simp [not_le.2 (Nat.lt_of_sub_eq_succ e)])
/-
**Primrec.nat_min** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_min : Primrec₂ (@min Nat _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `Primrec.nat_le`：nat_le : PrimrecRel ((· <= ·) : Nat -> Nat -> Prop)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
-/
theorem nat_min : Primrec₂ (@min ℕ _) :=
  ite nat_le fst snd
/-
**Primrec.nat_max** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_max : Primrec₂ (@max Nat _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.nat_le`：nat_le : PrimrecRel ((· <= ·) : Nat -> Nat -> Prop)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
-/
theorem nat_max : Primrec₂ (@max ℕ _) :=
  ite (nat_le.comp fst snd) snd fst
/-
**Primrec.dom_bool** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：dom_bool (f : Bool -> α) : Primrec f
参数：f : Bool -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primr
ec c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) 
el…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dom_bool (f : Bool → α) : Primrec f :=
  (cond .id (const (f true)) (const (f false))).of_eq fun b => by cases b <;> rfl
/-
**Primrec.dom_bool** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：dom_bool (f : Bool -> α) : Primrec f
参数：f : Bool -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primr
ec c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) 
el…
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem dom_bool₂ (f : Bool → Bool → α) : Primrec₂ f :=
  (cond fst ((dom_bool (f true)).comp snd) ((dom_bool (f false)).comp snd)).of_eq fun ⟨a, b⟩ => by
    cases a <;> rfl
/-
**Primrec.not** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：Primrec not
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.dom_bool`：dom_bool (f : Bool -> α) : Primrec f
-/
protected theorem not : Primrec not :=
  dom_bool _
/-
**Primrec.and** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：Primrec₂ and
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.dom_bool₂`：dom_bool₂ (f : Bool -> Bool -> α) : Primrec₂ f
-/
protected theorem and : Primrec₂ and :=
  dom_bool₂ _
/-
**Primrec.or** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：Primrec₂ or
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.dom_bool₂`：dom_bool₂ (f : Bool -> Bool -> α) : Primrec₂ f
-/
protected theorem or : Primrec₂ or :=
  dom_bool₂ _
/-
**Primrec._root_.PrimrecPred.not** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.PrimrecPred.not {p : α → Prop} :
    (hp : PrimrecPred p) → PrimrecPred fun a => ¬p a
  | ⟨_, hp⟩ => Primrec.primrecPred <| Primrec.not.comp hp |>.of_eq <| by simp
/-
**Primrec._root_.PrimrecPred.and** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.PrimrecPred.and {p q : α → Prop} :
    (hp : PrimrecPred p) → (hq : PrimrecPred q) → PrimrecPred fun a => p a ∧ q a
  | ⟨_, hp⟩, ⟨_, hq⟩ => Primrec.primrecPred <| Primrec.and.comp hp hq |>.of_eq <| by simp
/-
**Primrec._root_.PrimrecPred.or** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.PrimrecPred.or {p q : α → Prop} :
    (hp : PrimrecPred p) → (hq : PrimrecPred q) → PrimrecPred fun a => p a ∨ q a
  | ⟨_, hp⟩, ⟨_, hq⟩ => Primrec.primrecPred <| Primrec.or.comp hp hq |>.of_eq <| by simp
/-
**Primrec.eq** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `PrimrecPred.and`：∀ {α : Type u_1} [inst : Primcodable α] {p q : α → Prop
}, PrimrecPred p → PrimrecPred q → PrimrecPred fun a => p a ∧ q a
· 使用定理 `Primrec.nat_le`：nat_le : PrimrecRel ((· <= ·) : Nat -> Nat -> Prop)
· 使用定理 `PrimrecRel.swap`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α] 
[inst_1 : Primcodable β] {r : α → β → Prop},   PrimrecRel r → PrimrecRel (Functi
on.sw…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `PrimrecRel.of_eq`：PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β]
 {r s : α -> β -> Prop} (hr : PrimrecRel r) (H : forall a b, r a b ↔ s a b) : Pr
imrecR…
· 使用引理 `Primrec₂.primrecRel`：Primrec₂.primrecRel {R : α -> β -> Prop} [Decidable
Rel R] (hp : Primrec₂ (fun a b => decide (R a b))) : PrimrecRel R
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `PrimrecRel.decide`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α
] [inst_1 : Primcodable β] {R : α → β → Prop}   [inst_2 : DecidableRel R], Primr
ecRel R…
· 使用定理 `Primrec.comp₂`：Primrec.comp₂ {f : γ -> σ} {g : α -> β -> γ} (hf : Primre
c f) (hg : Primrec₂ g) : Primrec₂ fun a b => f (g a b)
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
· 使用定理 `Primrec₂.left`：left : Primrec₂ fun (a : α) (_ : β) => a
· 使用定理 `Primrec₂.right`：right : Primrec₂ fun (_ : α) (b : β) => b
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Encodable.encode_injective`：∀ {α : Type u_1} [inst : Encodable α], Funct
ion.Injective Encodable.encode
-/
protected theorem eq : PrimrecRel (@Eq α) :=
  have : PrimrecRel fun a b : ℕ => a = b :=
    (PrimrecPred.and nat_le nat_le.swap).of_eq fun a => by simp [le_antisymm_iff]
  (this.decide.comp₂ (Primrec.encode.comp₂ Primrec₂.left)
      (Primrec.encode.comp₂ Primrec₂.right)).primrecRel.of_eq
    fun _ _ => encode_injective.eq_iff
/-
**Primrec.beq** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α] [inst_1 : DecidableEq α], Primrec₂
 BEq.beq
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecRel.decide`：∀ {α : Type u_1} {β : Type u_2} [inst : Primcodable α
] [inst_1 : Primcodable β] {R : α → β → Prop}   [inst_2 : DecidableRel R], Primr
ecRel R…
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
-/
protected theorem beq [DecidableEq α] : Primrec₂ (@BEq.beq α _) := Primrec.eq.decide
/-
**Primrec.nat_lt** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_lt : PrimrecRel ((· < ·) : Nat -> Nat -> Prop)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `PrimrecPred.not`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Prop},
 PrimrecPred p → PrimrecPred fun a => ¬p a
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.nat_le`：nat_le : PrimrecRel ((· <= ·) : Nat -> Nat -> Prop)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nat_lt : PrimrecRel ((· < ·) : ℕ → ℕ → Prop) :=
  (nat_le.comp snd fst).not.of_eq fun p => by simp
/-
**Primrec.option_guard** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_guard {p : α -> β -> Prop} [DecidableRel p] (hp : PrimrecRel p) {f 
: α -> β} (hf : Primrec f) : Primrec fun a => Option.guard (p a) (f a)
参数：hp : PrimrecRel p；hf : Primrec f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
-/
theorem option_guard {p : α → β → Prop} [DecidableRel p] (hp : PrimrecRel p) {f : α → β}
    (hf : Primrec f) : Primrec fun a => Option.guard (p a) (f a) :=
  ite (by simpa using hp.comp Primrec.id hf) (option_some_iff.2 hf) (const none)
/-
**Primrec.option_orElse** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_orElse : Primrec₂ ((· <|> ·) : Option α -> Option α -> Option α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.option_casesOn`：option_casesOn {o : α -> Option β} {f : α -> σ} 
{g : α -> β -> σ} (ho : Primrec o) (hf : Primrec f) (hg : Primrec₂ g) : @Primrec
 _ σ _ _ fun…
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem option_orElse : Primrec₂ ((· <|> ·) : Option α → Option α → Option α) :=
  (option_casesOn fst snd (fst.comp fst).to₂).of_eq fun ⟨o₁, o₂⟩ => by cases o₁ <;> cases o₂ <;> rfl
/-
**Primrec.decode** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodable.decode
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
-/
protected theorem decode₂ : Primrec (decode₂ α) :=
  option_bind .decode <|
    option_guard (Primrec.eq.comp₂ (by exact encode_iff.mpr snd) (by exact fst.comp fst)) snd
/-
**Primrec.list_findIdx** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_findIdx {f : α -> List β} {p : α -> β -> Bool} (hf : Primrec f) (hp :
 Primrec₂ p) : Primrec fun a => (f a).findIdx (p a)
参数：hf : Primrec f；hp : Primrec₂ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.list_foldr`：list_foldr {f : α -> List β} {g : α -> σ} {h : α -> 
β × σ -> σ} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a 
=> (f a)…
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primr
ec c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) 
el…
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.findIdx_cons`：∀ {α : Type u_1} {p : α → Bool} {b : α} {l : List α},
 List.findIdx p (b :: l) = bif p b then 0 else List.findIdx p l + 1
-/
theorem list_findIdx₁ {p : α → β → Bool} (hp : Primrec₂ p) :
    ∀ l : List β, Primrec fun a => l.findIdx (p a)
| [] => const 0
| a :: l => (cond (hp.comp .id (const a)) (const 0) (succ.comp (list_findIdx₁ hp l))).of_eq fun n =>
  by simp [List.findIdx_cons]
/-
**Primrec.list_idxOf** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：list_idxOf [DecidableEq α] : Primrec₂ (@List.idxOf α _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec.list_findIdx`：list_findIdx {f : α -> List β} {p : α -> β -> Bool
} (hf : Primrec f) (hp : Primrec₂ p) : Primrec fun a => (f a).findIdx (p a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec₂.comp₂`：Primrec₂.comp₂ {f : γ -> δ -> σ} {g : α -> β -> γ} {h : 
α -> β -> δ} (hf : Primrec₂ f) (hg : Primrec₂ g) (hh : Primrec₂ h) : Primrec₂ fu
n a …
· 使用定理 `Primrec.beq`：∀ {α : Type u_1} [inst : Primcodable α] [inst_1 : Decidable
Eq α], Primrec₂ BEq.beq
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
-/
theorem list_idxOf₁ [DecidableEq α] (l : List α) : Primrec fun a => l.idxOf a :=
  list_findIdx₁ (.swap .beq) l
/-
**Primrec.dom_finite** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：dom_finite [Finite α] (f : α -> σ) : Primrec f
参数：f : α -> σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_univ_list`：Finite.exists_univ_list (α) [Finite α] : exists
 l : List α, l.Nodup ∧ forall x : α, x in l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.list_getElem?₁`：∀ {α : Type u_1} [inst : Primcodable α] (l : Lis
t α), Primrec fun x => l[x]?
· 使用定理 `Primrec.list_idxOf₁`：list_idxOf₁ [DecidableEq α] (l : List α) : Primrec 
fun a => l.idxOf a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem?_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List
 α} {i : ℕ}, (List.map f l)[i]? = Option.map f l[i]?
· 使用定理 `List.getElem?_idxOf`：∀ {α : Type u} [inst : BEq α] [LawfulBEq α] {a : α}
 {l : List α}, a ∈ l → l[List.idxOf a l]? = some a
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Option.map_some`：∀ {α : Type u_1} {β : Type u_2} (a : α) (f : α → β), Op
tion.map f (some a) = some (f a)
-/
theorem dom_finite [Finite α] (f : α → σ) : Primrec f :=
  let ⟨l, _, m⟩ := Finite.exists_univ_list α
  option_some_iff.1 <| by
    have := decidableEqOfEncodable α
    refine ((list_getElem?₁ (l.map f)).comp (list_idxOf₁ l)).of_eq fun a => ?_
    rw [List.getElem?_map, List.getElem?_idxOf (m a), Option.map_some]

/-- A function is `PrimrecBounded` if its size is bounded by a primitive recursive function -/
/-
**Primrec.PrimrecBounded** 是 Mathlib 中的一个定义，位于命名空间 `Primrec`。
形式化陈述：PrimrecBounded (f : α -> β) : Prop
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is `PrimrecBounded` if its size is bounded by a primitive recursive f
unction
-/
def PrimrecBounded (f : α → β) : Prop :=
  ∃ g : α → ℕ, Primrec g ∧ ∀ x, encode (f x) ≤ g x
/-
**Primrec.nat_findGreatest** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_findGreatest {f : α -> Nat} {p : α -> Nat -> Prop} [DecidableRel p] (h
f : Primrec f) (hp : PrimrecRel p) : Primrec fun x => (f x).findGreatest (p x)
参数：hf : Primrec f；hp : PrimrecRel p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_rec'`：nat_rec' {f : α -> Nat} {g : α -> β} {h : α -> Nat × β
 -> β} (hf : Primrec f) (hg : Primrec g) (hh : Primrec₂ h) : Primrec fun a => (f
 a).re…
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nat_findGreatest {f : α → ℕ} {p : α → ℕ → Prop} [DecidableRel p]
    (hf : Primrec f) (hp : PrimrecRel p) : Primrec fun x => (f x).findGreatest (p x) :=
  (nat_rec' (h := fun x nih => if p x (nih.1 + 1) then nih.1 + 1 else nih.2)
    hf (const 0) (ite (hp.comp fst (snd |> fst.comp |> succ.comp))
      (snd |> fst.comp |> succ.comp) (snd.comp snd))).of_eq fun x => by
        induction f x <;> simp [Nat.findGreatest, *]

/-- To show a function `f : α → ℕ` is primitive recursive, it is enough to show that the function
  is bounded by a primitive recursive function and that its graph is primitive recursive -/
/-
**Primrec.of_graph** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：of_graph {f : α -> Nat} (h₁ : PrimrecBounded f) (h₂ : PrimrecRel fun a b =
> f a = b) : Primrec f
参数：h₁ : PrimrecBounded f；h₂ : PrimrecRel fun a b => f a = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.nat_findGreatest`：nat_findGreatest {f : α -> Nat} {p : α -> Nat 
-> Prop} [DecidableRel p] (hf : Primrec f) (hp : PrimrecRel p) : Primrec fun x =
> (f x).findGr…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Nat.findGreatest_spec`：findGreatest_spec (hmb : m <= n) (hm : P m) : P (
Nat.findGreatest P n)

--- 原说明 ---
To show a function `f : α → ℕ` is primitive recursive, it is enough to show that
 the function
  is bounded by a primitive recursive function and that its graph is primitive r
ecursive
-/
theorem of_graph {f : α → ℕ} (h₁ : PrimrecBounded f)
    (h₂ : PrimrecRel fun a b => f a = b) : Primrec f := by
  rcases h₁ with ⟨g, pg, hg : ∀ x, f x ≤ g x⟩
  refine (nat_findGreatest pg h₂).of_eq fun n => ?_
  exact (Nat.findGreatest_spec (P := fun b => f n = b) (hg n) rfl).symm

-- We show that division is primitive recursive by showing that the graph is
/-
**Primrec.nat_div** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_div : Primrec₂ ((· / ·) : Nat -> Nat -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_graph`：of_graph {f : α -> Nat} (h₁ : PrimrecBounded f) (h₂ : 
PrimrecRel fun a b => f a = b) : Primrec f
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Nat.div_le_self`：∀ (n k : ℕ), n / k ≤ n
· 使用定理 `PrimrecPred.or`：∀ {α : Type u_1} [inst : Primcodable α] {p q : α → Prop}
, PrimrecPred p → PrimrecPred q → PrimrecPred fun a => p a ∨ q a
· 使用定理 `PrimrecPred.and`：∀ {α : Type u_1} [inst : Primcodable α] {p q : α → Prop
}, PrimrecPred p → PrimrecPred q → PrimrecPred fun a => p a ∧ q a
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.nat_lt`：nat_lt : PrimrecRel ((· < ·) : Nat -> Nat -> Prop)
· 使用定理 `Primrec.nat_le`：nat_le : PrimrecRel ((· <= ·) : Nat -> Nat -> Prop)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.nat_mul`：nat_mul : Primrec₂ ((· * ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `PrimrecRel.of_eq`：PrimrecRel.of_eq {α β} [Primcodable α] [Primcodable β]
 {r s : α -> β -> Prop} (hr : PrimrecRel r) (H : forall a b, r a b ↔ s a b) : Pr
imrecR…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
（共 42 条，此处仅展示前 30 条）
-/
theorem nat_div : Primrec₂ ((· / ·) : ℕ → ℕ → ℕ) := by
  refine of_graph ⟨_, fst, fun p => Nat.div_le_self _ _⟩ ?_
  have : PrimrecRel fun (a : ℕ × ℕ) (b : ℕ) => (a.2 = 0 ∧ b = 0) ∨
      (0 < a.2 ∧ b * a.2 ≤ a.1 ∧ a.1 < (b + 1) * a.2) :=
    PrimrecPred.or
      (.and (const 0 |> Primrec.eq.comp (fst |> snd.comp)) (const 0 |> Primrec.eq.comp snd))
      (.and (nat_lt.comp (const 0) (fst |> snd.comp)) <|
          .and (nat_le.comp (nat_mul.comp snd (fst |> snd.comp)) (fst |> fst.comp))
          (nat_lt.comp (fst.comp fst) (nat_mul.comp (Primrec.succ.comp snd) (snd.comp fst))))
  refine this.of_eq ?_
  rintro ⟨a, k⟩ q
  if H : k = 0 then simp [H, eq_comm]
  else
    have : q * k ≤ a ∧ a < (q + 1) * k ↔ q = a / k := by
      rw [le_antisymm_iff, ← (@Nat.lt_succ_iff _ q), Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero H),
          Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero H)]
    simpa [H, zero_lt_iff, eq_comm (b := q)]
/-
**Primrec.nat_mod** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_mod : Primrec₂ ((· % ·) : Nat -> Nat -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.of_eq`：of_eq {f g : α -> β -> σ} (hg : Primrec₂ f) (H : forall 
a b, f a b = g a b) : Primrec₂ g
· 使用定理 `Primrec.to₂`：to₂ {f : α × β -> σ} (hf : Primrec f) : Primrec₂ fun a b =>
 f (a, b)
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.nat_sub`：nat_sub : Primrec₂ ((· - ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.nat_mul`：nat_mul : Primrec₂ ((· * ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.nat_div`：nat_div : Primrec₂ ((· / ·) : Nat -> Nat -> Nat)
· 使用定理 `Nat.sub_eq_of_eq_add`：∀ {a b c : ℕ}, a = c + b → a - b = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.div_add_mod`：∀ (m n : ℕ), n * (m / n) + m % n = m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem nat_mod : Primrec₂ ((· % ·) : ℕ → ℕ → ℕ) :=
  (nat_sub.comp fst (nat_mul.comp snd nat_div)).to₂.of_eq fun m n => by
    apply Nat.sub_eq_of_eq_add
    simp [add_comm (m % n), Nat.div_add_mod]
/-
**Primrec.nat_bodd** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_bodd : Primrec Nat.bodd
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.beq`：∀ {α : Type u_1} [inst : Primcodable α] [inst_1 : Decidable
Eq α], Primrec₂ BEq.beq
· 使用定理 `Primrec.nat_mod`：nat_mod : Primrec₂ ((· % ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.mod_two_of_bodd`：mod_two_of_bodd (n : Nat) : n % 2 = (bodd n).toNat
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BEq.rfl`：∀ {α : Type u_1} [inst : BEq α] [ReflBEq α] {a : α}, (a == a) =
 true
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `Std.LawfulBEqOrd.equivBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord α
] [Std.LawfulBEqOrd α] [Std.TransOrd α], EquivBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Nat.instTransOrd`：Std.TransOrd ℕ
-/
theorem nat_bodd : Primrec Nat.bodd :=
  (Primrec.beq.comp (nat_mod.comp .id (const 2)) (const 1)).of_eq fun n => by
    cases H : n.bodd <;> simp [Nat.mod_two_of_bodd, H]
/-
**Primrec.nat_div2** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_div2 : Primrec Nat.div2
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.nat_div`：nat_div : Primrec₂ ((· / ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div2_val`：div2_val (n : Nat) : div2 n = n / 2
-/
theorem nat_div2 : Primrec Nat.div2 :=
  (nat_div.comp .id (const 2)).of_eq fun n => n.div2_val.symm
/-
**Primrec.nat_double** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_double : Primrec (fun n : Nat => 2 * n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec₂.comp`：Primrec₂.comp {f : β -> γ -> σ} {g : α -> β} {h : α -> γ}
 (hf : Primrec₂ f) (hg : Primrec g) (hh : Primrec h) : Primrec fun a => f (g a) 
(h …
· 使用定理 `Primrec.nat_mul`：nat_mul : Primrec₂ ((· * ·) : Nat -> Nat -> Nat)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
-/
theorem nat_double : Primrec (fun n : ℕ => 2 * n) :=
  nat_mul.comp (const _) Primrec.id
/-
**Primrec.nat_double_succ** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：nat_double_succ : Primrec (fun n : Nat => 2 * n + 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `Primrec.nat_double`：nat_double : Primrec (fun n : Nat => 2 * n)
-/
theorem nat_double_succ : Primrec (fun n : ℕ => 2 * n + 1) :=
  nat_double |> Primrec.succ.comp

end Primrec

namespace Primcodable

variable {α : Type*} {β : Type*}
variable [Primcodable α] [Primcodable β]

open Primrec

/-
**Primcodable.sum** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：sum : Primcodable (α oplus β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sum : Primcodable (α ⊕ β) :=
  ⟨Primrec.nat_iff.1 <|
      (encode_iff.2
            (cond nat_bodd
              (((@Primrec.decode β _).comp nat_div2).option_map <|
                to₂ <| nat_double_succ.comp (Primrec.encode.comp snd))
              (((@Primrec.decode α _).comp nat_div2).option_map <|
                to₂ <| nat_double.comp (Primrec.encode.comp snd)))).of_eq
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


/-
**Primrec.sumInl** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：sumInl : Primrec (@Sum.inl α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.nat_double`：nat_double : Primrec (fun n : Nat => 2 * n)
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
-/
theorem sumInl : Primrec (@Sum.inl α β) :=
  encode_iff.1 <| nat_double.comp Primrec.encode
/-
**Primrec.sumInr** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：sumInr : Primrec (@Sum.inr α β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.nat_double_succ`：nat_double_succ : Primrec (fun n : Nat => 2 * n
 + 1)
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
-/
theorem sumInr : Primrec (@Sum.inr α β) :=
  encode_iff.1 <| nat_double_succ.comp Primrec.encode
/-
**Primrec.sumCasesOn** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：sumCasesOn {f : α -> β oplus γ} {g : α -> β -> σ} {h : α -> γ -> σ} (hf : 
Primrec f) (hg : Primrec₂ g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Sum.c
asesOn (f a) (g a) (h a)
参数：hf : Primrec f；hg : Primrec₂ g；hh : Primrec₂ h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.option_some_iff`：option_some_iff {f : α -> σ} : (Primrec fun a =
> some (f a)) ↔ Primrec f
· 使用定理 `Primrec.of_eq`：of_eq {f g : α -> σ} (hf : Primrec f) (H : forall n, f n 
= g n) : Primrec g
· 使用定理 `Primrec.cond`：cond {c : α -> Bool} {f : α -> σ} {g : α -> σ} (hc : Primr
ec c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => bif (c a) then (f a) 
el…
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.nat_bodd`：nat_bodd : Primrec Nat.bodd
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.encode_iff`：encode_iff {f : α -> σ} : (Primrec fun a => encode (
f a)) ↔ Primrec f
· 使用定理 `Primrec.option_map`：option_map {f : α -> Option β} {g : α -> β -> σ} (hf
 : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).map (g a)
· 使用定理 `Primrec.decode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.decode
· 使用定理 `Primrec.nat_div2`：nat_div2 : Primrec Nat.div2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.bodd_mul`：bodd_mul (m n : Nat) : bodd (m * n) = (bodd m && bodd n)
· 使用引理 `Nat.bodd_succ`：bodd_succ (n : Nat) : bodd (succ n) = not (bodd n)
· 使用定理 `Bool.not_false`：(!false) = true
· 使用定理 `Bool.not_true`：(!true) = false
· 使用定理 `Bool.false_and`：∀ (b : Bool), (false && b) = false
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Encodable.encodek`：∀ {α : Type u_1} [self : Encodable α] (a : α), Encoda
ble.decode (Encodable.encode a) = some a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Nat.div2_succ`：div2_succ (n : Nat) : div2 (n + 1) = cond (bodd n) (succ 
(div2 n)) (div2 n)
-/
theorem sumCasesOn {f : α → β ⊕ γ} {g : α → β → σ} {h : α → γ → σ} (hf : Primrec f)
    (hg : Primrec₂ g) (hh : Primrec₂ h) : @Primrec _ σ _ _ fun a => Sum.casesOn (f a) (g a) (h a) :=
  option_some_iff.1 <|
    (cond (nat_bodd.comp <| encode_iff.2 hf)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hh)
          (option_map (Primrec.decode.comp <| nat_div2.comp <| encode_iff.2 hf) hg)).of_eq
      fun a => by rcases f a with b | c <;> simp [Nat.div2_val, encodek]

end Primrec

namespace PrimrecRel

open Primrec List PrimrecPred

variable {α β : Type*} {R : α → β → Prop} {L : List α} {b : β}

variable [Primcodable α] [Primcodable β]

/-
**PrimrecRel.not** 是 Mathlib 中的一个定理，位于命名空间 `PrimrecRel`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} [inst : Primcodable α] 
[inst_1 : Primcodable β],   PrimrecRel R → PrimrecRel fun a b => ¬R a b
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.not`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Prop},
 PrimrecPred p → PrimrecPred fun a => ¬p a
-/
protected theorem not (hf : PrimrecRel R) : PrimrecRel fun a b ↦ ¬ R a b := PrimrecPred.not hf

end PrimrecRel

namespace Primcodable

variable {α : Type*} [Primcodable α]

open Primrec

/-- A subtype of a primitive recursive predicate is `Primcodable`. -/
@[instance_reducible]
/-
**Primcodable.subtype** 是 Mathlib 中的一个定义，位于命名空间 `Primcodable`。
形式化陈述：subtype {p : α -> Prop} [DecidablePred p] (hp : PrimrecPred p) : Primcodab
le (Subtype p)
参数：hp : PrimrecPred p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subtype of a primitive recursive predicate is `Primcodable`.
-/
def subtype {p : α → Prop} [DecidablePred p] (hp : PrimrecPred p) : Primcodable (Subtype p) :=
  ⟨have : Primrec fun n => (@decode α _ n).bind fun a => Option.guard p a :=
    option_bind .decode (option_guard (hp.comp snd).primrecRel snd)
  nat_iff.1 <| (encode_iff.2 this).of_eq fun n =>
    show _ = encode ((@decode α _ n).bind fun _ => _) by
      rcases @decode α _ n with - | a; · rfl
      dsimp [Option.guard]
      by_cases h : p a <;> simp [h]; rfl⟩
/-
**Primcodable.fin** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：fin {n} : Primcodable (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance fin {n} : Primcodable (Fin n) :=
  letI : Primcodable { i : ℕ // i < n } := subtype <| nat_lt.comp .id (const n)
  ofEquiv { i : ℕ // i < n } Fin.equivSubtype
/-
**Primcodable.** 是 Mathlib 中的一个示例，位于命名空间 `Primcodable`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example (n) : (fin (n := n)).toEncodable = Fin.encodable n := by
  with_reducible_and_instances rfl

section ULower

attribute [local instance] Encodable.decidableRangeEncode Encodable.decidableEqOfEncodable

/-
**Primcodable.mem_range_encode** 是 Mathlib 中的一个定理，位于命名空间 `Primcodable`。
形式化陈述：mem_range_encode : PrimrecPred (fun n => n in Set.range (encode : α -> Nat
))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecPred.not`：∀ {α : Type u_1} [inst : Primcodable α] {p : α → Prop},
 PrimrecPred p → PrimrecPred fun a => ¬p a
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.eq`：∀ {α : Type u_1} [inst : Primcodable α], PrimrecRel Eq
· 使用定理 `Primrec.option_bind`：option_bind {f : α -> Option β} {g : α -> β -> Opti
on σ} (hf : Primrec f) (hg : Primrec₂ g) : Primrec fun a => (f a).bind (g a)
· 使用定理 `Primrec.decode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.decode
· 使用定理 `Primrec.ite`：ite {c : α -> Prop} [DecidablePred c] {f : α -> σ} {g : α -
> σ} (hc : PrimrecPred c) (hf : Primrec f) (hg : Primrec g) : Primrec fun a => i
f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
· 使用定理 `Primrec.snd`：snd {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
snd α β)
· 使用定理 `Primrec.fst`：fst {α β} [Primcodable α] [Primcodable β] : Primrec (@Prod.
fst α β)
· 使用定理 `Primrec.option_some`：option_some : Primrec (@some α)
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `PrimrecPred.of_eq`：PrimrecPred.of_eq {α} [Primcodable α] {p q : α -> Pro
p} (hp : PrimrecPred p) (H : forall a, p a ↔ q a) : PrimrecPred q
· 使用定理 `Encodable.decode₂_ne_none_iff`：decode₂_ne_none_iff [Encodable α] {n : Na
t} : decode₂ α n != none ↔ n in Set.range (encode : α -> Nat)
-/
theorem mem_range_encode : PrimrecPred (fun n => n ∈ Set.range (encode : α → ℕ)) :=
  have : PrimrecPred fun n => Encodable.decode₂ α n ≠ none :=
    .not
      (Primrec.eq.comp
        (.option_bind .decode
          (.ite (by simpa using Primrec.eq.comp (Primrec.encode.comp .snd) .fst)
            (Primrec.option_some.comp .snd) (.const _)))
        (.const _))
  this.of_eq fun _ => decode₂_ne_none_iff
/-
**Primcodable.ulower** 是 Mathlib 中的一个实例，位于命名空间 `Primcodable`。
形式化陈述：ulower : Primcodable (ULower α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ulower : Primcodable (ULower α) :=
  fast_instance% Primcodable.subtype mem_range_encode

end ULower


end Primcodable

namespace Primrec

variable {α : Type*} {β : Type*} {σ : Type*}
variable [Primcodable α] [Primcodable β] [Primcodable σ]

/-
**Primrec.subtype_val** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：subtype_val {p : α -> Prop} [DecidablePred p] {hp : PrimrecPred p} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Primcodable.prim`：∀ (α : Type u_1) [self : Primcodable α], Nat.Primrec f
un n => Encodable.encode (Encodable.decode n)
-/
theorem subtype_val {p : α → Prop} [DecidablePred p] {hp : PrimrecPred p} :
    haveI := Primcodable.subtype hp
    Primrec (@Subtype.val α p) := by
  let := Primcodable.subtype hp
  refine (Primcodable.prim (Subtype p)).of_eq fun n => ?_
  rcases @decode (Subtype p) _ n with (_ | ⟨a, h⟩) <;> rfl
/-
**Primrec.subtype_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：subtype_val_iff {p : β -> Prop} [DecidablePred p] {hp : PrimrecPred p} {f 
: α -> Subtype p} : haveI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.subtype_val`：subtype_val {p : α -> Prop} [DecidablePred p] {hp :
 PrimrecPred p} : haveI
-/
theorem subtype_val_iff {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → Subtype p} :
    haveI := Primcodable.subtype hp
    (Primrec fun a => (f a).1) ↔ Primrec f := by
  let := Primcodable.subtype hp
  refine ⟨fun h => ?_, fun hf => subtype_val.comp hf⟩
  refine Nat.Primrec.of_eq h fun n => ?_
  rcases @decode α _ n with - | a; · rfl
  simp; rfl
/-
**Primrec.subtype_mk** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：subtype_mk {p : β -> Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α -
> β} {h : forall a, p (f a)} (hf : Primrec f) : haveI
参数：f a；hf : Primrec f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.subtype_val_iff`：subtype_val_iff {p : β -> Prop} [DecidablePred 
p] {hp : PrimrecPred p} {f : α -> Subtype p} : haveI
-/
theorem subtype_mk {p : β → Prop} [DecidablePred p] {hp : PrimrecPred p} {f : α → β}
    {h : ∀ a, p (f a)} (hf : Primrec f) :
    haveI := Primcodable.subtype hp
    Primrec fun a => @Subtype.mk β p (f a) (h a) :=
  subtype_val_iff.1 hf
/-
**Primrec.option_get** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：option_get {f : α -> Option β} {h : forall a, (f a).isSome} : Primrec f ->
 Primrec fun a => (f a).get (h a)
参数：f a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Primrec.of_eq`：of_eq {f g : Nat -> Nat} (hf : Nat.Primrec f) (H : fo
rall n, f n = g n) : Nat.Primrec g
· 使用定理 `Nat.Primrec.pred`：pred : Nat.Primrec pred
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_eq_zero_of_le`：∀ {n m : ℕ}, n ≤ m → n - m = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Option.some_get`：∀ {α : Type u_1} {x : Option α} (h : x.isSome = true), 
some (x.get h) = x
-/
theorem option_get {f : α → Option β} {h : ∀ a, (f a).isSome} :
    Primrec f → Primrec fun a => (f a).get (h a) := by
  intro hf
  refine (Nat.Primrec.pred.comp hf).of_eq fun n => ?_
  generalize hx : @decode α _ n = x
  cases x <;> simp
/-
**Primrec.ulower_down** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：ulower_down : Primrec (ULower.down : α -> ULower α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.subtype_mk`：subtype_mk {p : β -> Prop} [DecidablePred p] {hp : P
rimrecPred p} {f : α -> β} {h : forall a, p (f a)} (hf : Primrec f) : haveI
· 使用定理 `Primcodable.mem_range_encode`：mem_range_encode : PrimrecPred (fun n => n
 in Set.range (encode : α -> Nat))
· 使用定理 `Primrec.encode`：∀ {α : Type u_1} [inst : Primcodable α], Primrec Encodab
le.encode
-/
theorem ulower_down : Primrec (ULower.down : α → ULower α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidableRangeEncode _
  subtype_mk .encode (hp := Primcodable.mem_range_encode)
/-
**Primrec.ulower_up** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：ulower_up : Primrec (ULower.up : ULower α -> α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Primrec.option_get`：option_get {f : α -> Option β} {h : forall a, (f a).
isSome} : Primrec f -> Primrec fun a => (f a).get (h a)
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.decode₂`：∀ {α : Type u_1} [inst : Primcodable α], Primrec (Encod
able.decode₂ α)
· 使用定理 `Primrec.subtype_val`：subtype_val {p : α -> Prop} [DecidablePred p] {hp :
 PrimrecPred p} : haveI
· 使用定理 `Primcodable.mem_range_encode`：mem_range_encode : PrimrecPred (fun n => n
 in Set.range (encode : α -> Nat))
-/
theorem ulower_up : Primrec (ULower.up : ULower α → α) :=
  letI : ∀ a, Decidable (a ∈ Set.range (encode : α → ℕ)) := decidableRangeEncode _
  option_get (Primrec.decode₂.comp (subtype_val (hp := Primcodable.mem_range_encode)))
/-
**Primrec.fin_val_iff** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：fin_val_iff {n} {f : α -> Fin n} : (Primrec fun a => (f a).1) ↔ Primrec f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimrecRel.comp`：PrimrecRel.comp {R : β -> γ -> Prop} {f : α -> β} {g : 
α -> γ} (hR : PrimrecRel R) (hf : Primrec f) (hg : Primrec g) : PrimrecPred fun 
a => …
· 使用定理 `Primrec.nat_lt`：nat_lt : PrimrecRel ((· < ·) : Nat -> Nat -> Prop)
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
· 使用定理 `Primrec.const`：const (x : σ) : Primrec fun _ : α => x
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Primrec.subtype_val_iff`：subtype_val_iff {p : β -> Prop} [DecidablePred 
p] {hp : PrimrecPred p} {f : α -> Subtype p} : haveI
· 使用定理 `Primrec.of_equiv_iff`：of_equiv_iff {β} (e : β ≃ α) {f : σ -> β} : haveI
-/
theorem fin_val_iff {n} {f : α → Fin n} : (Primrec fun a => (f a).1) ↔ Primrec f := by
  let : Primcodable { a // a < n } := Primcodable.subtype (nat_lt.comp .id (const _))
  exact (Iff.trans (by rfl) subtype_val_iff).trans (of_equiv_iff _)
/-
**Primrec.fin_val** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：fin_val {n} : Primrec (fun (i : Fin n) => (i : Nat))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Primrec.fin_val_iff`：fin_val_iff {n} {f : α -> Fin n} : (Primrec fun a =
> (f a).1) ↔ Primrec f
· 使用定理 `Primrec.id`：∀ {α : Type u_1} [inst : Primcodable α], Primrec id
-/
theorem fin_val {n} : Primrec (fun (i : Fin n) => (i : ℕ)) :=
  fin_val_iff.2 .id
/-
**Primrec.fin_succ** 是 Mathlib 中的一个定理，位于命名空间 `Primrec`。
形式化陈述：fin_succ {n} : Primrec (@Fin.succ n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Primrec.fin_val_iff`：fin_val_iff {n} {f : α -> Fin n} : (Primrec fun a =
> (f a).1) ↔ Primrec f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Primrec.comp`：comp {f : β -> σ} {g : α -> β} (hf : Primrec f) (hg : Prim
rec g) : Primrec fun a => f (g a)
· 使用定理 `Primrec.succ`：succ : Primrec Nat.succ
· 使用定理 `Primrec.fin_val`：fin_val {n} : Primrec (fun (i : Fin n) => (i : Nat))
-/
theorem fin_succ {n} : Primrec (@Fin.succ n) :=
  fin_val_iff.1 <| by simp [succ.comp fin_val]

end Primrec

