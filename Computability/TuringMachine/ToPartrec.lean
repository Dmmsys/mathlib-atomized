/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.Num.Lemmas
public import Mathlib.Tactic.DeriveFintype  -- shake: keep (deriving handlers not tracked yet)
public import Mathlib.Computability.TuringMachine.Config

/-!
# Modelling partial recursive functions using Turing machines

The files `Config` and `ToPartrec` define a simplified basis for partial recursive functions,
and a `Turing.TM2` model
Turing machine for evaluating these functions. This amounts to a constructive proof that every
`Partrec` function can be evaluated by a Turing machine.

## Main definitions

* `PartrecToTM2.tr`: A TM2 Turing machine which can evaluate `code` programs

-/

@[expose] public section

open List (Vector)

open Function (update)

open Relation StateTransition

namespace Turing

/-!
## Simulating sequentialized partial recursive functions in TM2

At this point we have a sequential model of partial recursive functions: the `Cfg` type and
`step : Cfg → Option Cfg` function from `TMConfig.lean`. The key feature of this model is that
it does a finite amount of computation (in fact, an amount which is statically bounded by the size
of the program) between each step, and no individual step can diverge (unlike the compositional
semantics, where every sub-part of the computation is potentially divergent). So we can utilize the
same techniques as in the other TM simulations in `Computability.TuringMachine` to prove that
each step corresponds to a finite number of steps in a lower level model. (We don't prove it here,
but in anticipation of the complexity class P, the simulation is actually polynomial-time as well.)

The target model is `Turing.TM2`, which has a fixed finite set of stacks, a bit of local storage,
with programs selected from a potentially infinite (but finitely accessible) set of program
positions, or labels `Λ`, each of which executes a finite sequence of basic stack commands.

For this program we will need four stacks, each on an alphabet `Γ'` like so:

```
    inductive Γ'  | consₗ | cons | bit0 | bit1
```

We represent a number as a bit sequence, lists of numbers by putting `cons` after each element, and
lists of lists of natural numbers by putting `consₗ` after each list. For example:

```
    0 ~> []
    1 ~> [bit1]
    6 ~> [bit0, bit1, bit1]
    [1, 2] ~> [bit1, cons, bit0, bit1, cons]
    [[], [1, 2]] ~> [consₗ, bit1, cons, bit0, bit1, cons, consₗ]
```

The four stacks are `main`, `rev`, `aux`, `stack`. In normal mode, `main` contains the input to the
current program (a `List ℕ`) and `stack` contains data (a `List (List ℕ)`) associated to the
current continuation, and in `ret` mode `main` contains the value that is being passed to the
continuation and `stack` contains the data for the continuation. The `rev` and `aux` stacks are
usually empty; `rev` is used to store reversed data when e.g. moving a value from one stack to
another, while `aux` is used as a temporary for a `main`/`stack` swap that happens during `cons₁`
evaluation.

The only local store we need is `Option Γ'`, which stores the result of the last pop
operation. (Most of our working data are natural numbers, which are too large to fit in the local
store.)

The continuations from the previous section are data-carrying, containing all the values that have
been computed and are awaiting other arguments. In order to have only a finite number of
continuations appear in the program so that they can be used in machine states, we separate the
data part (anything with type `List ℕ`) from the `Cont` type, producing a `Cont'` type that lacks
this information. The data is kept on the `stack` stack.

Because we want to have subroutines for e.g. moving an entire stack to another place, we use an
infinite inductive type `Λ'` so that we can execute a program and then return to do something else
without having to define too many different kinds of intermediate states. (We must nevertheless
prove that only finitely many labels are accessible.) The labels are:

* `move p k₁ k₂ q`: move elements from stack `k₁` to `k₂` while `p` holds of the value being moved.
  The last element, that fails `p`, is placed in neither stack but left in the local store.
  At the end of the operation, `k₂` will have the elements of `k₁` in reverse order. Then do `q`.
* `clear p k q`: delete elements from stack `k` until `p` is true. Like `move`, the last element is
  left in the local storage. Then do `q`.
* `copy q`: Move all elements from `rev` to both `main` and `stack` (in reverse order),
  then do `q`. That is, it takes `(a, b, c, d)` to `(b.reverse ++ a, [], c, b.reverse ++ d)`.
* `push k f q`: push `f s`, where `s` is the local store, to stack `k`, then do `q`. This is a
  duplicate of the `push` instruction that is part of the TM2 model, but by having a subroutine
  just for this purpose we can build up programs to execute inside a `goto` statement, where we
  have the flexibility to be general recursive.
* `read (f : Option Γ' → Λ')`: go to state `f s` where `s` is the local store. Again this is only
  here for convenience.
* `succ q`: perform a successor operation. Assuming `[n]` is encoded on `main` before,
  `[n+1]` will be on main after. This implements successor for binary natural numbers.
* `pred q₁ q₂`: perform a predecessor operation or `case` statement. If `[]` is encoded on
  `main` before, then we transition to `q₁` with `[]` on main; if `(0 :: v)` is on `main` before
  then `v` will be on `main` after and we transition to `q₁`; and if `(n+1 :: v)` is on `main`
  before then `n :: v` will be on `main` after and we transition to `q₂`.
* `ret k`: call continuation `k`. Each continuation has its own interpretation of the data in
  `stack` and sets up the data for the next continuation.
  * `ret (cons₁ fs k)`: `v :: KData` on `stack` and `ns` on `main`, and the next step expects
    `v` on `main` and `ns :: KData` on `stack`. So we have to do a little dance here with six
    reverse-moves using the `aux` stack to perform a three-point swap, each of which involves two
    reversals.
  * `ret (cons₂ k)`: `ns :: KData` is on `stack` and `v` is on `main`, and we have to put
    `ns.headI :: v` on `main` and `KData` on `stack`. This is done using the `head` subroutine.
  * `ret (fix f k)`: This stores no data, so we just check if `main` starts with `0` and
    if so, remove it and call `k`, otherwise `clear` the first value and call `f`.
  * `ret halt`: the stack is empty, and `main` has the output. Do nothing and halt.

In addition to these basic states, we define some additional subroutines that are used in the
above:
* `push'`, `peek'`, `pop'` are special versions of the builtins that use the local store to supply
  inputs and outputs.
* `unrev`: special case `move false rev main` to move everything from `rev` back to `main`. Used as
  a cleanup operation in several functions.
* `moveExcl p k₁ k₂ q`: same as `move` but pushes the last value read back onto the source stack.
* `move₂ p k₁ k₂ q`: double `move`, so that the result comes out in the right order at the target
  stack. Implemented as `moveExcl p k rev; move false rev k₂`. Assumes that neither `k₁` nor `k₂`
  is `rev` and `rev` is initially empty.
* `head k q`: get the first natural number from stack `k` and reverse-move it to `rev`, then clear
  the rest of the list at `k` and then `unrev` to reverse-move the head value to `main`. This is
  used with `k = main` to implement regular `head`, i.e. if `v` is on `main` before then `[v.headI]`
  will be on `main` after; and also with `k = stack` for the `cons` operation, which has `v` on
  `main` and `ns :: KData` on `stack`, and results in `KData` on `stack` and `ns.headI :: v` on
  `main`.
* `trNormal` is the main entry point, defining states that perform a given `code` computation.
  It mostly just dispatches to functions written above.

The main theorem of this section is `tr_eval`, which asserts that for each that for each code `c`,
the state `init c v` steps to `halt v'` in finitely many steps if and only if
`Code.eval c v = some v'`.
-/



namespace PartrecToTM2

section

open ToPartrec

set_option backward.isDefEq.respectTransparency false in
/-- The alphabet for the stacks in the program. `bit0` and `bit1` are used to represent `ℕ` values
as lists of binary digits, `cons` is used to separate `List ℕ` values, and `consₗ` is used to
separate `List (List ℕ)` values. See the section documentation. -/
/-
**Turing.PartrecToTM2.** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The alphabet for the stacks in the program. `bit0` and `bit1` are used to repres
ent `ℕ` values
as lists of binary digits, `cons` is used to separate `List ℕ` values, and `cons
ₗ` is used to
separate `List (List ℕ)` values. See the section documentation.
-/
inductive Γ'
  | consₗ
  | cons
  | bit0
  | bit1
  deriving DecidableEq, Inhabited, Fintype

-- A proof below relies on the value of that `deriving Inhabited` picks here.
/-
**Turing.PartrecToTM2.default_** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem default_Γ' : (default : Γ') = .consₗ := rfl

/-- The four stacks used by the program. `main` is used to store the input value in `trNormal`
mode and the output value in `Λ'.ret` mode, while `stack` is used to keep all the data for the
continuations. `rev` is used to store reversed lists when transferring values between stacks, and
`aux` is only used once in `cons₁`. See the section documentation. -/
/-
**Turing.PartrecToTM2.K'** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：K'.elim_main (a b c d) : K'.elim a b c d K'.main = a
参数：a b c d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The four stacks used by the program. `main` is used to store the input value in 
`trNormal`
mode and the output value in `Λ'.ret` mode, while `stack` is used to keep all th
e data for the
continuations. `rev` is used to store reversed lists when transferring values be
tween stacks, and
`aux` is only used once in `cons₁`. See the section documentation.
-/
inductive K'
  | main
  | rev
  | aux
  | stack
  deriving DecidableEq, Inhabited

open K'

/-- Continuations as in `ToPartrec.Cont` but with the data removed. This is done because we want
the set of all continuations in the program to be finite (so that it can ultimately be encoded into
the finite state machine of a Turing machine), but a continuation can handle a potentially infinite
number of data values during execution. -/
/-
**Turing.PartrecToTM2.Cont'** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Continuations as in `ToPartrec.Cont` but with the data removed. This is done bec
ause we want
the set of all continuations in the program to be finite (so that it can ultimat
ely be encoded into
the finite state machine of a Turing machine), but a continuation can handle a p
otentially infinite
number of data values during execution.
-/
inductive Cont'
  | halt
  | cons₁ : Code → Cont' → Cont'
  | cons₂ : Cont' → Cont'
  | comp : Code → Cont' → Cont'
  | fix : Code → Cont' → Cont'
  deriving DecidableEq, Inhabited

/-- The set of program positions. We make extensive use of inductive types here to let us describe
"subroutines"; for example `clear p k q` is a program that clears stack `k`, then does `q` where
`q` is another label. In order to prevent this from resulting in an infinite number of distinct
accessible states, we are careful to be non-recursive (although loops are okay). See the section
documentation for a description of all the programs. -/
/-
**Turing.PartrecToTM2.** 是 Mathlib 中的一个归纳类型，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of program positions. We make extensive use of inductive types here to l
et us describe
"subroutines"; for example `clear p k q` is a program that clears stack `k`, the
n does `q` where
`q` is another label. In order to prevent this from resulting in an infinite num
ber of distinct
accessible states, we are careful to be non-recursive (although loops are okay).
 See the section
documentation for a description of all the programs.
-/
inductive Λ'
  | move (p : Γ' → Bool) (k₁ k₂ : K') (q : Λ')
  | clear (p : Γ' → Bool) (k : K') (q : Λ')
  | copy (q : Λ')
  | push (k : K') (s : Option Γ' → Option Γ') (q : Λ')
  | read (f : Option Γ' → Λ')
  | succ (q : Λ')
  | pred (q₁ q₂ : Λ')
  | ret (k : Cont')

compile_inductive% Code
compile_inductive% Cont'
compile_inductive% K'
compile_inductive% Λ'
/-
**Turing.PartrecToTM2.** 是 Mathlib 中的一个实例，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Λ'.instInhabited : Inhabited Λ' :=
  ⟨Λ'.ret Cont'.halt⟩
/-
**Turing.PartrecToTM2.** 是 Mathlib 中的一个实例，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Λ'.instDecidableEq : DecidableEq Λ' := fun a b => by
  induction a generalizing b <;> cases b
  case move.move p k₁ k₂ q _ p' k₁' k₂' q' =>
    exact decidable_of_iff' (p = p' ∧ k₁ = k₁' ∧ k₂ = k₂' ∧ q = q') (by simp)
  case clear.clear p k q _ p' k' q' => exact decidable_of_iff' (p = p' ∧ k = k' ∧ q = q') (by simp)
  case copy.copy q _ q' => exact decidable_of_iff' (q = q') (by simp)
  case push.push k s q _ k' s' q' => exact decidable_of_iff' (k = k' ∧ s = s' ∧ q = q') (by simp)
  case read.read f _ f' => exact decidable_of_iff' (∀ a, f a = f' a) (by simp [funext_iff])
  case succ.succ q _ q' => exact decidable_of_iff' (q = q') (by simp)
  case pred.pred q₁ q₂ _ _ q₁' q₂' => exact decidable_of_iff' (q₁ = q₁' ∧ q₂ = q₂') (by simp)
  case ret.ret k k' => exact decidable_of_iff' (k = k') (by simp)
  all_goals exact .isFalse (by rintro ⟨⟨⟩⟩)

/-- The type of TM2 statements used by this machine. -/
/-
**Turing.PartrecToTM2.Stmt'** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Stmt'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
The type of TM2 statements used by this machine.
-/
def Stmt' :=
  TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

/-- The type of TM2 configurations used by this machine. -/
/-
**Turing.PartrecToTM2.Cfg'** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Cfg'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
The type of TM2 configurations used by this machine.
-/
def Cfg' :=
  TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

open TM2.Stmt

/-- A predicate that detects the end of a natural number, either `Γ'.cons` or `Γ'.consₗ` (or
implicitly the end of the list), for use in predicate-taking functions like `move` and `clear`. -/
@[simp]
/-
**Turing.PartrecToTM2.natEnd** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Turing.PartrecToTM2.Γ' → Bool
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A predicate that detects the end of a natural number, either `Γ'.cons` or `Γ'.co
nsₗ` (or
implicitly the end of the list), for use in predicate-taking functions like `mov
e` and `clear`.
-/
def natEnd : Γ' → Bool
  | Γ'.consₗ => true
  | Γ'.cons => true
  | _ => false
attribute [nolint simpNF] natEnd.eq_3

/-- Pop a value from the stack and place the result in local store. -/
@[simp]
/-
**Turing.PartrecToTM2.pop'** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：pop' (k : K') : Stmt' -> Stmt'
参数：k : K'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
Pop a value from the stack and place the result in local store.
-/
def pop' (k : K') : Stmt' → Stmt' :=
  pop k fun _ v => v

/-- Peek a value from the stack and place the result in local store. -/
@[simp]
/-
**Turing.PartrecToTM2.peek'** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：peek' (k : K') : Stmt' -> Stmt'
参数：k : K'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
Peek a value from the stack and place the result in local store.
-/
def peek' (k : K') : Stmt' → Stmt' :=
  peek k fun _ v => v

/-- Push the value in the local store to the given stack. -/
@[simp]
/-
**Turing.PartrecToTM2.push'** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：push' (k : K') : Stmt' -> Stmt'
参数：k : K'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
Push the value in the local store to the given stack.
-/
def push' (k : K') : Stmt' → Stmt' :=
  push k fun x => x.getD default

/-- Move everything from the `rev` stack to the `main` stack (reversed). -/
/-
**Turing.PartrecToTM2.unrev** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：unrev
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Move everything from the `rev` stack to the `main` stack (reversed).
-/
def unrev :=
  Λ'.move (fun _ => false) rev main

/-- Move elements from `k₁` to `k₂` while `p` holds, with the last element being left on `k₁`. -/
/-
**Turing.PartrecToTM2.moveExcl** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：moveExcl (p k₁ k₂ q)
参数：p k₁ k₂ q。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
Move elements from `k₁` to `k₂` while `p` holds, with the last element being lef
t on `k₁`.
-/
def moveExcl (p k₁ k₂ q) :=
  Λ'.move p k₁ k₂ <| Λ'.push k₁ id q

/-- Move elements from `k₁` to `k₂` without reversion, by performing a double move via the `rev`
stack. -/
/-
**Turing.PartrecToTM2.move** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Move elements from `k₁` to `k₂` without reversion, by performing a double move v
ia the `rev`
stack.
-/
def move₂ (p k₁ k₂ q) :=
  moveExcl p k₁ rev <| Λ'.move (fun _ => false) rev k₂ q

/-- Assuming `trList v` is on the front of stack `k`, remove it, and push `v.headI` onto `main`.
See the section documentation. -/
/-
**Turing.PartrecToTM2.head** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：head (k : K') (q : Λ') : Λ'
参数：k : K'；q : Λ'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
Assuming `trList v` is on the front of stack `k`, remove it, and push `v.headI` 
onto `main`.
See the section documentation.
-/
def head (k : K') (q : Λ') : Λ' :=
  Λ'.move natEnd k rev <|
    (Λ'.push rev fun _ => some Γ'.cons) <|
      Λ'.read fun s =>
        (if s = some Γ'.consₗ then id else Λ'.clear (fun x => x = Γ'.consₗ) k) <| unrev q

/-- The program that evaluates code `c` with continuation `k`. This expects an initial state where
`trList v` is on `main`, `trContStack k` is on `stack`, and `aux` and `rev` are empty.
See the section documentation for details. -/
@[simp]
/-
**Turing.PartrecToTM2.trNormal** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Turing.ToPartrec.Code → Turing.PartrecToTM2.Cont' → Turing.PartrecToTM2.Λ'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The program that evaluates code `c` with continuation `k`. This expects an initi
al state where
`trList v` is on `main`, `trContStack k` is on `stack`, and `aux` and `rev` are 
empty.
See the section documentation for details.
-/
def trNormal : Code → Cont' → Λ'
  | Code.zero', k => (Λ'.push main fun _ => some Γ'.cons) <| Λ'.ret k
  | Code.succ, k => head main <| Λ'.succ <| Λ'.ret k
  | Code.tail, k => Λ'.clear natEnd main <| Λ'.ret k
  | Code.cons f fs, k =>
    (Λ'.push stack fun _ => some Γ'.consₗ) <|
      Λ'.move (fun _ => false) main rev <| Λ'.copy <| trNormal f (Cont'.cons₁ fs k)
  | Code.comp f g, k => trNormal g (Cont'.comp f k)
  | Code.case f g, k => Λ'.pred (trNormal f k) (trNormal g k)
  | Code.fix f, k => trNormal f (Cont'.fix f k)

/-- The main program. See the section documentation for details. -/
/-
**Turing.PartrecToTM2.tr** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Turing.PartrecToTM2.Λ' → Turing.PartrecToTM2.Stmt'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
The main program. See the section documentation for details.
-/
def tr : Λ' → Stmt'
  | Λ'.move p k₁ k₂ q =>
    pop' k₁ <|
      branch (fun s => s.elim true p) (goto fun _ => q)
        (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)
  | Λ'.push k f q =>
    branch (fun s => (f s).isSome) ((push k fun s => (f s).getD default) <| goto fun _ => q)
      (goto fun _ => q)
  | Λ'.read q => goto q
  | Λ'.clear p k q =>
    pop' k <| branch (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)
  | Λ'.copy q =>
    pop' rev <|
      branch Option.isSome (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)
  | Λ'.succ q =>
    pop' main <|
      branch (fun s => s = some Γ'.bit1) ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q) <|
        branch (fun s => s = some Γ'.cons)
          ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
          ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
  | Λ'.pred q₁ q₂ =>
    pop' main <|
      branch (fun s => s = some Γ'.bit0)
          ((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂) <|
        branch (fun s => natEnd (s.getD default)) (goto fun _ => q₁)
          (peek' main <|
            branch (fun s => natEnd (s.getD default)) (goto fun _ => unrev q₂)
              ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))
  | Λ'.ret (Cont'.cons₁ fs k) =>
    goto fun _ =>
      move₂ (fun _ => false) main aux <|
        move₂ (fun s => s = Γ'.consₗ) stack main <|
          move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)
  | Λ'.ret (Cont'.cons₂ k) => goto fun _ => head stack <| Λ'.ret k
  | Λ'.ret (Cont'.comp f k) => goto fun _ => trNormal f k
  | Λ'.ret (Cont'.fix f k) =>
    pop' main <|
      goto fun s =>
        cond (natEnd (s.getD default)) (Λ'.ret k) <|
          Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)
  | Λ'.ret Cont'.halt => (load fun _ => none) <| halt

@[simp]
/-
**Turing.PartrecToTM2.tr_move** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_move (p k₁ k₂ q) : tr (Λ'.move p k₁ k₂ q) = pop' k₁ (branch (fun s => s
.elim true p) (goto fun _ => q) (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q))
参数：p k₁ k₂ q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
-/
theorem tr_move (p k₁ k₂ q) : tr (Λ'.move p k₁ k₂ q) =
    pop' k₁ (branch (fun s => s.elim true p) (goto fun _ => q)
      (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)) := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_push** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_push (k f q) : tr (Λ'.push k f q) = branch (fun s => (f s).isSome) ((pu
sh k fun s => (f s).getD default) <| goto fun _ => q) (goto fun _ => q)
参数：k f q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
-/
theorem tr_push (k f q) : tr (Λ'.push k f q) = branch (fun s => (f s).isSome)
    ((push k fun s => (f s).getD default) <| goto fun _ => q) (goto fun _ => q) := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_read** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_read (q) : tr (Λ'.read q) = goto q
参数：q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_read (q) : tr (Λ'.read q) = goto q := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_clear** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_clear (p k q) : tr (Λ'.clear p k q) = pop' k (branch (fun s => s.elim t
rue p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q))
参数：p k q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
-/
theorem tr_clear (p k q) : tr (Λ'.clear p k q) = pop' k (branch
    (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)) := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_copy** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_copy (q) : tr (Λ'.copy q) = pop' rev (branch Option.isSome (push' main 
<| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q))
参数：q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_copy (q) : tr (Λ'.copy q) = pop' rev (branch Option.isSome
    (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)) := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_succ** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_succ (q) : tr (Λ'.succ q) = pop' main (branch (fun s => s = some Γ'.bit
1) ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q) branch (fun s => s =
 some Γ'.cons) ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| 
goto fun _ => unrev q) ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q))
参数：q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_succ (q) : tr (Λ'.succ q) = pop' main (branch (fun s => s = some Γ'.bit1)
    ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q) <|
      branch (fun s => s = some Γ'.cons)
        ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
        ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)) := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_pred** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_pred (q₁ q₂) : tr (Λ'.pred q₁ q₂) = pop' main (branch (fun s => s = som
e Γ'.bit0) ((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂) branch (
fun s => natEnd (s.getD default)) (goto fun _ => q₁) (peek' main <| branch (fun 
s => natEnd (s.getD default)) (goto fun _ => unrev q₂) ((push rev fun _ => Γ'.bi
t0) <| goto fun _ => unrev q₂)))
参数：q₁ q₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_pred (q₁ q₂) : tr (Λ'.pred q₁ q₂) = pop' main (branch (fun s => s = some Γ'.bit0)
    ((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂) <|
    branch (fun s => natEnd (s.getD default)) (goto fun _ => q₁)
      (peek' main <|
        branch (fun s => natEnd (s.getD default)) (goto fun _ => unrev q₂)
          ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))) := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_ret_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_ret_cons₁ (fs k) : tr (Λ'.ret (Cont'.cons₁ fs k)) = goto fun _ =>
    move₂ (fun _ => false) main aux <|
      move₂ (fun s => s = Γ'.consₗ) stack main <|
        move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k) := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_ret_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_ret_cons₂ (k) : tr (Λ'.ret (Cont'.cons₂ k)) =
    goto fun _ => head stack <| Λ'.ret k := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_ret_comp** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2
`。
形式化陈述：tr_ret_comp (f k) : tr (Λ'.ret (Cont'.comp f k)) = goto fun _ => trNormal 
f k
参数：f k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_ret_comp (f k) : tr (Λ'.ret (Cont'.comp f k)) = goto fun _ => trNormal f k := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_ret_fix** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`
。
形式化陈述：tr_ret_fix (f k) : tr (Λ'.ret (Cont'.fix f k)) = pop' main (goto fun s => 
cond (natEnd (s.getD default)) (Λ'.ret k) Λ'.clear natEnd main trNormal f (Cont'
.fix f k))
参数：f k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_ret_fix (f k) : tr (Λ'.ret (Cont'.fix f k)) = pop' main (goto fun s =>
    cond (natEnd (s.getD default)) (Λ'.ret k) <|
      Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) := rfl

@[simp]
/-
**Turing.PartrecToTM2.tr_ret_halt** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2
`。
形式化陈述：tr_ret_halt : tr (Λ'.ret Cont'.halt) = (load fun _ => none) halt
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tr_ret_halt : tr (Λ'.ret Cont'.halt) = (load fun _ => none) halt := rfl

/-- Translating a `Cont` continuation to a `Cont'` continuation simply entails dropping all the
data. This data is instead encoded in `trContStack` in the configuration. -/
/-
**Turing.PartrecToTM2.trCont** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Turing.ToPartrec.Cont → Turing.PartrecToTM2.Cont'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Translating a `Cont` continuation to a `Cont'` continuation simply entails dropp
ing all the
data. This data is instead encoded in `trContStack` in the configuration.
-/
def trCont : Cont → Cont'
  | Cont.halt => Cont'.halt
  | Cont.cons₁ c _ k => Cont'.cons₁ c (trCont k)
  | Cont.cons₂ _ k => Cont'.cons₂ (trCont k)
  | Cont.comp c k => Cont'.comp c (trCont k)
  | Cont.fix c k => Cont'.fix c (trCont k)

/-- We use `PosNum` to define the translation of binary natural numbers. A natural number is
represented as a little-endian list of `bit0` and `bit1` elements:

```
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
```

In particular, this representation guarantees no trailing `bit0`'s at the end of the list. -/
/-
**Turing.PartrecToTM2.trPosNum** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：PosNum → List Turing.PartrecToTM2.Γ'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We use `PosNum` to define the translation of binary natural numbers. A natural n
umber is
represented as a little-endian list of `bit0` and `bit1` elements:

```
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
```

In particular, this representation guarantees no trailing `bit0`'s at the end of
 the list.
-/
def trPosNum : PosNum → List Γ'
  | PosNum.one => [Γ'.bit1]
  | PosNum.bit0 n => Γ'.bit0 :: trPosNum n
  | PosNum.bit1 n => Γ'.bit1 :: trPosNum n

/-- We use `Num` to define the translation of binary natural numbers. Positive numbers are
translated using `trPosNum`, and `trNum 0 = []`. So there are never any trailing `bit0`'s in
a translated `Num`.

```
    0 = []
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
```
-/
/-
**Turing.PartrecToTM2.trNum** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Num → List Turing.PartrecToTM2.Γ'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We use `Num` to define the translation of binary natural numbers. Positive numbe
rs are
translated using `trPosNum`, and `trNum 0 = []`. So there are never any trailing
 `bit0`'s in
a translated `Num`.

```
    0 = []
    1 = [bit1]
    2 = [bit0, bit1]
    3 = [bit1, bit1]
    4 = [bit0, bit0, bit1]
```
-/
def trNum : Num → List Γ'
  | Num.zero => []
  | Num.pos n => trPosNum n

/-- Because we use binary encoding, we define `trNat` in terms of `trNum`, using `Num`, which are
binary natural numbers. (We could also use `Nat.binaryRecOn`, but `Num` and `PosNum` make for
easy inductions.) -/
/-
**Turing.PartrecToTM2.trNat** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：trNat (n : Nat) : List Γ'
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Because we use binary encoding, we define `trNat` in terms of `trNum`, using `Nu
m`, which are
binary natural numbers. (We could also use `Nat.binaryRecOn`, but `Num` and `Pos
Num` make for
easy inductions.)
-/
def trNat (n : ℕ) : List Γ' :=
  trNum n

@[simp]
/-
**Turing.PartrecToTM2.trNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`
。
形式化陈述：trNat_zero : trNat 0 = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.PartrecToTM2.trNat.eq_1`：∀ (n : ℕ), Turing.PartrecToTM2.trNat n =
 Turing.PartrecToTM2.trNum ↑n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem trNat_zero : trNat 0 = [] := by rw [trNat, Nat.cast_zero]; rfl
/-
**Turing.PartrecToTM2.trNat_default** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：trNat_default : trNat default = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.trNat_zero`：trNat_zero : trNat 0 = []
-/
theorem trNat_default : trNat default = [] :=
  trNat_zero

/-- Lists are translated with a `cons` after each encoded number.
For example:

```
    [] = []
    [0] = [cons]
    [1] = [bit1, cons]
    [6, 0] = [bit0, bit1, bit1, cons, cons]
```
-/
@[simp]
/-
**Turing.PartrecToTM2.trList** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：List ℕ → List Turing.PartrecToTM2.Γ'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lists are translated with a `cons` after each encoded number.
For example:

```
    [] = []
    [0] = [cons]
    [1] = [bit1, cons]
    [6, 0] = [bit0, bit1, bit1, cons, cons]
```
-/
def trList : List ℕ → List Γ'
  | [] => []
  | n::ns => trNat n ++ Γ'.cons :: trList ns

/-- Lists of lists are translated with a `consₗ` after each encoded list.
For example:

```
    [] = []
    [[]] = [consₗ]
    [[], []] = [consₗ, consₗ]
    [[0]] = [cons, consₗ]
    [[1, 2], [0]] = [bit1, cons, bit0, bit1, cons, consₗ, cons, consₗ]
```
-/
@[simp]
/-
**Turing.PartrecToTM2.trLList** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：List (List ℕ) → List Turing.PartrecToTM2.Γ'
参数：List ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lists of lists are translated with a `consₗ` after each encoded list.
For example:

```
    [] = []
    [[]] = [consₗ]
    [[], []] = [consₗ, consₗ]
    [[0]] = [cons, consₗ]
    [[1, 2], [0]] = [bit1, cons, bit0, bit1, cons, consₗ, cons, consₗ]
```
-/
def trLList : List (List ℕ) → List Γ'
  | [] => []
  | l::ls => trList l ++ Γ'.consₗ :: trLList ls

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `trLList`. -/
@[simp]
/-
**Turing.PartrecToTM2.contStack** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Turing.ToPartrec.Cont → List (List ℕ)
参数：List ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data part of a continuation is a list of lists, which is encoded on the `sta
ck` stack
using `trLList`.
-/
def contStack : Cont → List (List ℕ)
  | Cont.halt => []
  | Cont.cons₁ _ ns k => ns :: contStack k
  | Cont.cons₂ ns k => ns :: contStack k
  | Cont.comp _ k => contStack k
  | Cont.fix _ k => contStack k

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `trLList`. -/
/-
**Turing.PartrecToTM2.trContStack** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2
`。
形式化陈述：trContStack (k : Cont)
参数：k : Cont。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data part of a continuation is a list of lists, which is encoded on the `sta
ck` stack
using `trLList`.
-/
def trContStack (k : Cont) :=
  trLList (contStack k)

/-- This is the nondependent eliminator for `K'`, but we use it specifically here in order to
represent the stack data as four lists rather than as a function `K' → List Γ'`, because this makes
rewrites easier. The theorems `K'.elim_update_main` et. al. show how such a function is updated
after an `update` to one of the components. -/
/-
**Turing.PartrecToTM2.K'.elim** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2.K'`
。
形式化陈述：List Turing.PartrecToTM2.Γ' →   List Turing.PartrecToTM2.Γ' →     List Tur
ing.PartrecToTM2.Γ' → List Turing.PartrecToTM2.Γ' → Turing.PartrecToTM2.K' → Lis
t Turing.PartrecToTM2.Γ'
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
This is the nondependent eliminator for `K'`, but we use it specifically here in
 order to
represent the stack data as four lists rather than as a function `K' → List Γ'`,
 because this makes
rewrites easier. The theorems `K'.elim_update_main` et. al. show how such a func
tion is updated
after an `update` to one of the components.
-/
def K'.elim (a b c d : List Γ') : K' → List Γ'
  | K'.main => a
  | K'.rev => b
  | K'.aux => c
  | K'.stack => d

-- The equation lemma of `elim` simplifies to `match` structures.
/-
**Turing.PartrecToTM2.K'.elim_main** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM
2.K'`。
形式化陈述：∀ (a b c d : List Turing.PartrecToTM2.Γ'), Turing.PartrecToTM2.K'.elim a b
 c d Turing.PartrecToTM2.K'.main = a
参数：a b c d : List Turing.PartrecToTM2.Γ'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem K'.elim_main (a b c d) : K'.elim a b c d K'.main = a := rfl
/-
**Turing.PartrecToTM2.K'.elim_rev** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2
.K'`。
形式化陈述：∀ (a b c d : List Turing.PartrecToTM2.Γ'), Turing.PartrecToTM2.K'.elim a b
 c d Turing.PartrecToTM2.K'.rev = b
参数：a b c d : List Turing.PartrecToTM2.Γ'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem K'.elim_rev (a b c d) : K'.elim a b c d K'.rev = b := rfl
/-
**Turing.PartrecToTM2.K'.elim_aux** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2
.K'`。
形式化陈述：∀ (a b c d : List Turing.PartrecToTM2.Γ'), Turing.PartrecToTM2.K'.elim a b
 c d Turing.PartrecToTM2.K'.aux = c
参数：a b c d : List Turing.PartrecToTM2.Γ'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem K'.elim_aux (a b c d) : K'.elim a b c d K'.aux = c := rfl
/-
**Turing.PartrecToTM2.K'.elim_stack** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2.K'`。
形式化陈述：∀ (a b c d : List Turing.PartrecToTM2.Γ'), Turing.PartrecToTM2.K'.elim a b
 c d Turing.PartrecToTM2.K'.stack = d
参数：a b c d : List Turing.PartrecToTM2.Γ'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem K'.elim_stack (a b c d) : K'.elim a b c d K'.stack = d := rfl

attribute [simp] K'.elim

@[simp]
/-
**Turing.PartrecToTM2.K'.elim_update_main** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Part
recToTM2.K'`。
形式化陈述：∀ {a b c d a' : List Turing.PartrecToTM2.Γ'},   Function.update (Turing.Pa
rtrecToTM2.K'.elim a b c d) Turing.PartrecToTM2.K'.main a' =     Turing.PartrecT
oTM2.K'.elim a' b c d
参数：Turing.PartrecToTM2.K'.elim a b c d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem K'.elim_update_main {a b c d a'} : update (K'.elim a b c d) main a' = K'.elim a' b c d := by
  funext x; cases x <;> rfl

@[simp]
/-
**Turing.PartrecToTM2.K'.elim_update_rev** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partr
ecToTM2.K'`。
形式化陈述：∀ {a b c d b' : List Turing.PartrecToTM2.Γ'},   Function.update (Turing.Pa
rtrecToTM2.K'.elim a b c d) Turing.PartrecToTM2.K'.rev b' =     Turing.PartrecTo
TM2.K'.elim a b' c d
参数：Turing.PartrecToTM2.K'.elim a b c d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem K'.elim_update_rev {a b c d b'} : update (K'.elim a b c d) rev b' = K'.elim a b' c d := by
  funext x; cases x <;> rfl

@[simp]
/-
**Turing.PartrecToTM2.K'.elim_update_aux** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partr
ecToTM2.K'`。
形式化陈述：∀ {a b c d c' : List Turing.PartrecToTM2.Γ'},   Function.update (Turing.Pa
rtrecToTM2.K'.elim a b c d) Turing.PartrecToTM2.K'.aux c' =     Turing.PartrecTo
TM2.K'.elim a b c' d
参数：Turing.PartrecToTM2.K'.elim a b c d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem K'.elim_update_aux {a b c d c'} : update (K'.elim a b c d) aux c' = K'.elim a b c' d := by
  funext x; cases x <;> rfl

@[simp]
/-
**Turing.PartrecToTM2.K'.elim_update_stack** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Par
trecToTM2.K'`。
形式化陈述：∀ {a b c d d' : List Turing.PartrecToTM2.Γ'},   Function.update (Turing.Pa
rtrecToTM2.K'.elim a b c d) Turing.PartrecToTM2.K'.stack d' =     Turing.Partrec
ToTM2.K'.elim a b c d'
参数：Turing.PartrecToTM2.K'.elim a b c d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem K'.elim_update_stack {a b c d d'} :
    update (K'.elim a b c d) stack d' = K'.elim a b c d' := by funext x; cases x <;> rfl

/-- The halting state corresponding to a `List ℕ` output value. -/
/-
**Turing.PartrecToTM2.halt** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：halt (v : List Nat) : Cfg'
参数：v : List Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
The halting state corresponding to a `List ℕ` output value.
-/
def halt (v : List ℕ) : Cfg' :=
  ⟨none, none, K'.elim (trList v) [] [] []⟩

/-- The `Cfg` states map to `Cfg'` states almost one to one, except that in normal operation the
local store contains an arbitrary garbage value. To make the final theorem cleaner we explicitly
clear it in the halt state so that there is exactly one configuration corresponding to output `v`.
-/
/-
**Turing.PartrecToTM2.TrCfg** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Turing.ToPartrec.Cfg → Turing.PartrecToTM2.Cfg' → Prop
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
The `Cfg` states map to `Cfg'` states almost one to one, except that in normal o
peration the
local store contains an arbitrary garbage value. To make the final theorem clean
er we explicitly
clear it in the halt state so that there is exactly one configuration correspond
ing to output `v`.
-/
def TrCfg : Cfg → Cfg' → Prop
  | Cfg.ret k v, c' =>
    ∃ s, c' = ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩
  | Cfg.halt v, c' => c' = halt v

/-- This could be a general list definition, but it is also somewhat specialized to this
application. `splitAtPred p L` will search `L` for the first element satisfying `p`.
If it is found, say `L = l₁ ++ a :: l₂` where `a` satisfies `p` but `l₁` does not, then it returns
`(l₁, some a, l₂)`. Otherwise, if there is no such element, it returns `(L, none, [])`. -/
/-
**Turing.PartrecToTM2.splitAtPred** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2
`。
形式化陈述：splitAtPred {α} (p : α -> Bool) : List α -> List α × Option α × List α | [
] => ([], none, []) | a :: as => cond (p a) ([], some a, as) let ⟨l₁, o, l₂⟩
参数：p : α -> Bool。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This could be a general list definition, but it is also somewhat specialized to 
this
application. `splitAtPred p L` will search `L` for the first element satisfying 
`p`.
If it is found, say `L = l₁ ++ a :: l₂` where `a` satisfies `p` but `l₁` does no
t, then it returns
`(l₁, some a, l₂)`. Otherwise, if there is no such element, it returns `(L, none
, [])`.
-/
def splitAtPred {α} (p : α → Bool) : List α → List α × Option α × List α
  | [] => ([], none, [])
  | a :: as =>
    cond (p a) ([], some a, as) <|
      let ⟨l₁, o, l₂⟩ := splitAtPred p as
      ⟨a::l₁, o, l₂⟩
/-
**Turing.PartrecToTM2.splitAtPred_eq** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecTo
TM2`。
形式化陈述：splitAtPred_eq {α} (p : α -> Bool) : forall L l₁ o l₂, (forall x in l₁, p 
x = false) -> Option.elim' (L = l₁ ∧ l₂ = []) (fun a => p a = true ∧ L = l₁ ++ a
::l₂) o -> splitAtPred p L = (l₁, o, l₂) | [], _, none, _, _, ⟨rfl, rfl⟩ => rfl 
| [], l₁, some o, l₂, _, ⟨_, h₃⟩ => by simp at h₃ | a :: L, l₁, o, l₂, h₁, h₂ =>
 by rw [splitAtPred] have IH
参数：p : α -> Bool。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
-/
theorem splitAtPred_eq {α} (p : α → Bool) :
    ∀ L l₁ o l₂,
      (∀ x ∈ l₁, p x = false) →
        Option.elim' (L = l₁ ∧ l₂ = []) (fun a => p a = true ∧ L = l₁ ++ a::l₂) o →
          splitAtPred p L = (l₁, o, l₂)
  | [], _, none, _, _, ⟨rfl, rfl⟩ => rfl
  | [], l₁, some o, l₂, _, ⟨_, h₃⟩ => by simp at h₃
  | a :: L, l₁, o, l₂, h₁, h₂ => by
    rw [splitAtPred]
    have IH := splitAtPred_eq p L
    rcases o with - | o
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨⟨⟩, rfl⟩
      rw [h₁ a (List.Mem.head _), cond, IH L none [] _ ⟨rfl, rfl⟩]
      exact fun x h => h₁ x (List.Mem.tail _ h)
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨h₂, ⟨⟩⟩
      · rw [h₂, cond]
      rw [h₁ a (List.Mem.head _), cond, IH l₁ (some o) l₂ _ ⟨h₂, _⟩] <;> try rfl
      exact fun x h => h₁ x (List.Mem.tail _ h)
/-
**Turing.PartrecToTM2.splitAtPred_false** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partre
cToTM2`。
形式化陈述：splitAtPred_false {α} (L : List α) : splitAtPred (fun _ => false) L = (L, 
none, [])
参数：L : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.splitAtPred_eq`：splitAtPred_eq {α} (p : α -> Bool) :
 forall L l₁ o l₂, (forall x in l₁, p x = false) -> Option.elim' (L = l₁ ∧ l₂ = 
[]) (fun a => p a = true…
-/
theorem splitAtPred_false {α} (L : List α) : splitAtPred (fun _ => false) L = (L, none, []) :=
  splitAtPred_eq _ _ _ _ _ (fun _ _ => rfl) ⟨rfl, rfl⟩
/-
**Turing.PartrecToTM2.move_ok** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' -> List Γ'} (h₁ : k₁ != k₂) (e : spl
itAtPred p (S k₁) = (L₁, o, L₂)) : Reaches₁ (TM2.step tr) ⟨some (Λ'.move p k₁ k₂
 q), s, S⟩ ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverseAux (S k₂))⟩
参数：h₁ : k₁ != k₂；e : splitAtPred p (S k₁) = (L₁, o, L₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `List.reverseAux_nil`：∀ {α : Type u_1} {r : List α}, [].reverseAux r = r
· 使用定理 `Function.update_eq_self`：update_eq_self (a : α) (f : forall a, β a) : up
date f a (f a) = f
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.TM2.stepAux.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `Turing.PartrecToTM2.tr.eq_1`：∀ (p : Turing.PartrecToTM2.Γ' → Bool) (k₁ k
₂ : Turing.PartrecToTM2.K') (q : Turing.PartrecToTM2.Λ'),   Turing.PartrecToTM2.
tr (Turing.Partre…
· 使用定理 `Turing.PartrecToTM2.splitAtPred.eq_1`：∀ {α : Type u_1} (p : α → Bool), T
uring.PartrecToTM2.splitAtPred p [] = ([], none, [])
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Turing.PartrecToTM2.splitAtPred.eq_2`：∀ {α : Type u_1} (p : α → Bool) (a
 : α) (as : List α),   Turing.PartrecToTM2.splitAtPred p (a :: as) =     bif p a
 then ([], some a, as)    …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.reverseAux_eq`：∀ {α : Type u_1} {as bs : List α}, as.reverseAux bs 
= as.reverse ++ bs
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_comm`：update_comm {α} [DecidableEq α] {β : α -> Sort*} {
a b : α} (h : a != b) (v : β a) (w : β b) (f : forall a, β a) : update (update f
 a v) b w …
· 使用定理 `Function.update_idem`：update_idem {α} [DecidableEq α] {β : α -> Sort*} {
a : α} (v w : β a) (f : forall a, β a) : update (update f a v) a w = update f a 
w
-/
theorem move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ k₂)
    (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.move p k₁ k₂ q), s, S⟩
      ⟨some q, o, update (update S k₁ L₂) k₂ (L₁.reverseAux (S k₂))⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    swap
    · rw [Function.update_of_ne h₁.symm, List.reverseAux_nil]
    refine TransGen.head' rfl ?_
    simp only [tr_move, pop', TM2.stepAux]
    grind [splitAtPred.eq_def]
  | cons a L₁ IH =>
    refine TransGen.head rfl ?_
    rw [tr]; simp only [pop', Option.elim, TM2.stepAux, push']
    rcases e₁ : S k₁ with - | ⟨a', Sk⟩ <;> rw [e₁, splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, cond_false]
    convert! @IH _ (update (update S k₁ Sk) k₂ (a :: S k₂)) _ using 2 <;>
      simp [Function.update_of_ne, h₁, h₁.symm, e₃, List.reverseAux]
    simp [Function.update_comm h₁.symm]
/-
**Turing.PartrecToTM2.unrev_ok** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：unrev_ok {q s} {S : K' -> List Γ'} : Reaches₁ (TM2.step tr) ⟨some (unrev q
), s, S⟩ ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (
S main))⟩
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Turing.PartrecToTM2.move_ok`：move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' -> Li
st Γ'} (h₁ : k₁ != k₂) (e : splitAtPred p (S k₁) = (L₁, o, L₂)) : Reaches₁ (TM2.
step tr) ⟨some (Λ…
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Turing.PartrecToTM2.splitAtPred_false`：splitAtPred_false {α} (L : List α
) : splitAtPred (fun _ => false) L = (L, none, [])
-/
theorem unrev_ok {q s} {S : K' → List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (unrev q), s, S⟩
      ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (S main))⟩ :=
  move_ok (by decide) <| splitAtPred_false _
/-
**Turing.PartrecToTM2.move** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' → List Γ'} (h₁ : k₁ ≠ rev ∧ k₂ ≠ rev ∧ k₁ ≠ k₂)
    (h₂ : S rev = []) (e : splitAtPred p (S k₁) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (move₂ p k₁ k₂ q), s, S⟩
      ⟨some q, none, update (update S k₁ (o.elim id List.cons L₂)) k₂ (L₁ ++ S k₂)⟩ := by
  refine (move_ok h₁.1 e).trans (TransGen.head rfl ?_)
  simp only [TM2.step, Option.mem_def, Option.elim]
  cases o <;> simp only <;> rw [tr]
    <;> simp only [id, TM2.stepAux, Option.isSome, cond_true, cond_false]
  · convert! move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [Function.update_comm h₁.1, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.2.2.symm, Function.update_of_ne h₁.2.1,
      Function.update_of_ne h₁.1.symm, List.reverseAux_eq, h₂, Function.update_self,
      List.append_nil, List.reverse_reverse]
  · simp only [Option.getD_some]
    convert! move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [h₂, Function.update_comm h₁.1, List.reverseAux_eq, Function.update_self,
      List.append_nil, Function.update_idem]
    rw [show update S rev [] = S by rw [← h₂, Function.update_eq_self]]
    simp only [Function.update_of_ne h₁.1.symm, Function.update_of_ne h₁.2.2.symm,
      Function.update_of_ne h₁.2.1, Function.update_self, List.reverse_reverse]
/-
**Turing.PartrecToTM2.clear_ok** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：clear_ok {p k q s L₁ o L₂} {S : K' -> List Γ'} (e : splitAtPred p (S k) = 
(L₁, o, L₂)) : Reaches₁ (TM2.step tr) ⟨some (Λ'.clear p k q), s, S⟩ ⟨some q, o, 
update S k L₂⟩
参数：e : splitAtPred p (S k) = (L₁, o, L₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.PartrecToTM2.tr.eq_4`：∀ (p : Turing.PartrecToTM2.Γ' → Bool) (k : 
Turing.PartrecToTM2.K') (q : Turing.PartrecToTM2.Λ'),   Turing.PartrecToTM2.tr (
Turing.PartrecToT…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Turing.TM2.stepAux.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `Turing.PartrecToTM2.splitAtPred.eq_1`：∀ {α : Type u_1} (p : α → Bool), T
uring.PartrecToTM2.splitAtPred p [] = ([], none, [])
· 使用定理 `Turing.PartrecToTM2.splitAtPred.eq_2`：∀ {α : Type u_1} (p : α → Bool) (a
 : α) (as : List α),   Turing.PartrecToTM2.splitAtPred p (a :: as) =     bif p a
 then ([], some a, as)    …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_idem`：update_idem {α} [DecidableEq α] {β : α -> Sort*} {
a : α} (v w : β a) (f : forall a, β a) : update (update f a v) a w = update f a 
w
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem clear_ok {p k q s L₁ o L₂} {S : K' → List Γ'} (e : splitAtPred p (S k) = (L₁, o, L₂)) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.clear p k q), s, S⟩ ⟨some q, o, update S k L₂⟩ := by
  induction L₁ generalizing S s with
  | nil =>
    refine TransGen.head' rfl ?_
    rw [tr]; simp only [pop', TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    revert e; rcases S k with - | ⟨a, Sk⟩ <;> intro e
    · cases e
      rfl
    simp only [splitAtPred, List.head?, List.tail_cons] at e ⊢
    revert e; cases p a <;> intro e <;>
      simp only [cond_false, cond_true, Prod.mk.injEq, true_and, false_and, reduceCtorEq] at e ⊢
    rcases e with ⟨e₁, e₂⟩
    rw [e₁, e₂]
  | cons a L₁ IH =>
    refine TransGen.head rfl ?_
    rw [tr]; simp only [pop', TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    rcases e₁ : S k with - | ⟨a', Sk⟩ <;> rw [e₁, splitAtPred] at e
    · cases e
    cases e₂ : p a' <;> simp only [e₂, cond] at e
    swap
    · cases e
    rcases e₃ : splitAtPred p Sk with ⟨_, _, _⟩
    rw [e₃] at e
    cases e
    simp only [List.head?_cons, e₂, List.tail_cons, cond_false]
    convert! @IH _ (update S k Sk) _ using 2 <;> simp [e₃]

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.PartrecToTM2.copy_ok** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：copy_ok (q s a b c d) : Reaches₁ (TM2.step tr) ⟨some (Λ'.copy q), s, K'.el
im a b c d⟩ ⟨some q, none, K'.elim (List.reverseAux b a) [] c (List.reverseAux b
 d)⟩
参数：q s a b c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.TM2.step.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3}
 {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (l : Λ)
 (v : σ) (…
· 使用定理 `Turing.TM2.stepAux.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_rev`：∀ {a b c d b' : List Turing.Part
recToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Par
trecToTM2.K'.rev b' =     Tu…
· 使用定理 `Turing.TM2.stepAux.eq_5`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (f : σ → Boo…
· 使用定理 `Turing.TM2.stepAux.eq_1`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_main`：∀ {a b c d a' : List Turing.Par
trecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Pa
rtrecToTM2.K'.main a' =     T…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_stack`：∀ {a b c d d' : List Turing.Pa
rtrecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.P
artrecToTM2.K'.stack d' =     …
· 使用定理 `Turing.TM2.stepAux.eq_6`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (f : σ → Λ),…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reverseAux_eq`：∀ {α : Type u_1} {as bs : List α}, as.reverseAux bs 
= as.reverse ++ bs
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `Turing.PartrecToTM2.tr.eq_5`：∀ (q : Turing.PartrecToTM2.Λ'),   Turing.Pa
rtrecToTM2.tr q.copy =     Turing.PartrecToTM2.pop' Turing.PartrecToTM2.K'.rev  
     (Turing.TM2.…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
-/
theorem copy_ok (q s a b c d) :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.copy q), s, K'.elim a b c d⟩
      ⟨some q, none, K'.elim (List.reverseAux b a) [] c (List.reverseAux b d)⟩ := by
  induction b generalizing a d s with
  | nil =>
    refine TransGen.single ?_
    simp
  | cons x b IH =>
    refine TransGen.head rfl ?_
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_rev, List.head?_cons, Option.isSome_some,
      List.tail_cons, elim_update_rev, elim_main, elim_update_main,
      elim_stack, elim_update_stack, cond_true, List.reverseAux_cons, pop', push']
    exact IH _ _ _
/-
**Turing.PartrecToTM2.trPosNum_natEnd** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecT
oTM2`。
形式化陈述：∀ (n : PosNum), ∀ x ∈ Turing.PartrecToTM2.trPosNum n, Turing.PartrecToTM2.
natEnd x = false
参数：n : PosNum。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trPosNum_natEnd : ∀ (n), ∀ x ∈ trPosNum n, natEnd x = false
  | PosNum.one, _, List.Mem.head _ => rfl
  | PosNum.bit0 _, _, List.Mem.head _ => rfl
  | PosNum.bit0 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h
  | PosNum.bit1 _, _, List.Mem.head _ => rfl
  | PosNum.bit1 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h
/-
**Turing.PartrecToTM2.trNum_natEnd** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM
2`。
形式化陈述：∀ (n : Num), ∀ x ∈ Turing.PartrecToTM2.trNum n, Turing.PartrecToTM2.natEnd
 x = false
参数：n : Num。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.trPosNum_natEnd`：∀ (n : PosNum), ∀ x ∈ Turing.Partre
cToTM2.trPosNum n, Turing.PartrecToTM2.natEnd x = false
-/
theorem trNum_natEnd : ∀ (n), ∀ x ∈ trNum n, natEnd x = false
  | Num.pos n, x, h => trPosNum_natEnd n x h
/-
**Turing.PartrecToTM2.trNat_natEnd** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM
2`。
形式化陈述：trNat_natEnd (n) : forall x in trNat n, natEnd x = false
参数：n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.trNum_natEnd`：∀ (n : Num), ∀ x ∈ Turing.PartrecToTM2
.trNum n, Turing.PartrecToTM2.natEnd x = false
-/
theorem trNat_natEnd (n) : ∀ x ∈ trNat n, natEnd x = false :=
  trNum_natEnd _
/-
**Turing.PartrecToTM2.trList_ne_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecTo
TM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trList_ne_consₗ : ∀ (l), ∀ x ∈ trList l, x ≠ Γ'.consₗ
  | a :: l, x, h => by
    simp only [trList, List.mem_append, List.mem_cons] at h
    obtain h | rfl | h := h
    · rintro rfl
      cases trNat_natEnd _ _ h
    · rintro ⟨⟩
    · exact trList_ne_consₗ l _ h
/-
**Turing.PartrecToTM2.head_main_ok** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM
2`。
形式化陈述：head_main_ok {q s L} {c d : List Γ'} : Reaches₁ (TM2.step tr) ⟨some (head 
main q), s, K'.elim (trList L) [] c d⟩ ⟨some q, none, K'.elim (trList [L.headI])
 [] c d⟩
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.trans`：∀ {α : Sort u} {r : α → α → Prop} {a b c : α}, 
  Relation.TransGen r a b → Relation.TransGen r b c → Relation.TransGen r a c
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Turing.PartrecToTM2.move_ok`：move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' -> Li
st Γ'} (h₁ : k₁ != k₂) (e : splitAtPred p (S k₁) = (L₁, o, L₂)) : Reaches₁ (TM2.
step tr) ⟨some (Λ…
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Turing.PartrecToTM2.splitAtPred_eq`：splitAtPred_eq {α} (p : α -> Bool) :
 forall L l₁ o l₂, (forall x in l₁, p x = false) -> Option.elim' (L = l₁ ∧ l₂ = 
[]) (fun a => p a = true…
· 使用定理 `Turing.PartrecToTM2.trNat_natEnd`：trNat_natEnd (n) : forall x in trNat n
, natEnd x = false
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Turing.PartrecToTM2.trNat_zero`：trNat_zero : trNat 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Turing.PartrecToTM2.trList.eq_1`：Turing.PartrecToTM2.trList [] = []
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `List.append_cancel_left_eq`：∀ {α : Type u_1} (as bs cs : List α), (as ++
 bs = as ++ cs) = (bs = cs)
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `Turing.PartrecToTM2.tr.eq_3`：∀ (q : Option Turing.PartrecToTM2.Γ' → Turi
ng.PartrecToTM2.Λ'),   Turing.PartrecToTM2.tr (Turing.PartrecToTM2.Λ'.read q) = 
Turing.TM2.Stmt.g…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_main`：∀ {a b c d a' : List Turing.Par
trecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Pa
rtrecToTM2.K'.main a' =     T…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_rev`：∀ {a b c d b' : List Turing.Part
recToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Par
trecToTM2.K'.rev b' =     Tu…
（共 46 条，此处仅展示前 30 条）
-/
theorem head_main_ok {q s L} {c d : List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (head main q), s, K'.elim (trList L) [] c d⟩
      ⟨some q, none, K'.elim (trList [L.headI]) [] c d⟩ := by
  let o : Option Γ' := List.casesOn L none fun _ _ => some Γ'.cons
  refine
    (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat L.headI) o (trList L.tail) (trNat_natEnd _) ?_)).trans
      (TransGen.head rfl (TransGen.head rfl ?_))
  · cases L <;> simp [o]
  rw [tr]
  simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_update_main, elim_rev, elim_update_rev,
    Function.update_self, trList]
  rw [if_neg (show o ≠ some Γ'.consₗ by cases L <;> simp [o])]
  refine (clear_ok (splitAtPred_eq _ _ _ none [] ?_ ⟨rfl, rfl⟩)).trans ?_
  · exact fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)
  convert! unrev_ok using 2; simp [List.reverseAux_eq]
/-
**Turing.PartrecToTM2.head_stack_ok** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：head_stack_ok {q s L₁ L₂ L₃} : Reaches₁ (TM2.step tr) ⟨some (head stack q)
, s, K'.elim (trList L₁) [] [] (trList L₂ ++ Γ'.consₗ :: L₃)⟩ ⟨some q, none, K'.
elim (trList (L₂.headI :: L₁)) [] [] L₃⟩
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Relation.TransGen.trans`：∀ {α : Sort u} {r : α → α → Prop} {a b c : α}, 
  Relation.TransGen r a b → Relation.TransGen r b c → Relation.TransGen r a c
· 使用定理 `Turing.PartrecToTM2.move_ok`：move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' -> Li
st Γ'} (h₁ : k₁ != k₂) (e : splitAtPred p (S k₁) = (L₁, o, L₂)) : Reaches₁ (TM2.
step tr) ⟨some (Λ…
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Turing.PartrecToTM2.splitAtPred_eq`：splitAtPred_eq {α} (p : α -> Bool) :
 forall L l₁ o l₂, (forall x in l₁, p x = false) -> Option.elim' (L = l₁ ∧ l₂ = 
[]) (fun a => p a = true…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.PartrecToTM2.tr.eq_3`：∀ (q : Option Turing.PartrecToTM2.Γ' → Turi
ng.PartrecToTM2.Λ'),   Turing.PartrecToTM2.tr (Turing.PartrecToTM2.Λ'.read q) = 
Turing.TM2.Stmt.g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_stack`：∀ {a b c d d' : List Turing.Pa
rtrecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.P
artrecToTM2.K'.stack d' =     …
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_rev`：∀ {a b c d b' : List Turing.Part
recToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Par
trecToTM2.K'.rev b' =     Tu…
· 使用定理 `Function.update.congr_simp`：∀ {α : Sort u} {β : α → Sort v} {inst : Deci
dableEq α} [inst_1 : DecidableEq α] (f f_1 : (a : α) → β a),   f = f_1 → ∀ (a' :
 α) (v v_1 : β a…
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Turing.PartrecToTM2.trNat_default`：trNat_default : trNat default = []
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.reverseAux_eq`：∀ {α : Type u_1} {as bs : List α}, as.reverseAux bs 
= as.reverse ++ bs
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_main`：∀ {a b c d a' : List Turing.Par
trecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Pa
rtrecToTM2.K'.main a' =     T…
· 使用定理 `Turing.PartrecToTM2.unrev_ok`：unrev_ok {q s} {S : K' -> List Γ'} : Reach
es₁ (TM2.step tr) ⟨some (unrev q), s, S⟩ ⟨some q, none, update (update S rev [])
 main (List.revers…
· 使用定理 `Turing.PartrecToTM2.trNat_natEnd`：trNat_natEnd (n) : forall x in trNat n
, natEnd x = false
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
（共 39 条，此处仅展示前 30 条）
-/
theorem head_stack_ok {q s L₁ L₂ L₃} :
    Reaches₁ (TM2.step tr)
      ⟨some (head stack q), s, K'.elim (trList L₁) [] [] (trList L₂ ++ Γ'.consₗ :: L₃)⟩
      ⟨some q, none, K'.elim (trList (L₂.headI :: L₁)) [] [] L₃⟩ := by
  rcases L₂ with - | ⟨a, L₂⟩
  · refine
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ [] (some Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
        (TransGen.head rfl (TransGen.head rfl ?_))
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, ite_true, id_eq, trList, List.nil_append,
      elim_update_stack, elim_rev, List.reverseAux_nil, elim_update_rev, Function.update_self,
      List.headI_nil, trNat_default]
    convert! unrev_ok using 2
    simp
  · refine
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat a) (some Γ'.cons) (trList L₂ ++ Γ'.consₗ :: L₃)
            (trNat_natEnd _) ⟨rfl, by simp⟩))
        (TransGen.head rfl (TransGen.head rfl ?_))
    simp only [TM2.step, Option.mem_def, trList, List.append_assoc,
      List.cons_append, elim_update_stack, elim_rev, elim_update_rev, Function.update_self,
      List.headI_cons]
    refine
      TransGen.trans
        (clear_ok
          (splitAtPred_eq _ _ (trList L₂) (some Γ'.consₗ) L₃
            (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, by simp⟩))
        ?_
    convert! unrev_ok using 2
    simp [List.reverseAux_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.PartrecToTM2.succ_ok** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：succ_ok {q s n} {c d : List Γ'} : Reaches₁ (TM2.step tr) ⟨some (Λ'.succ q)
, s, K'.elim (trList [n]) [] c d⟩ ⟨some q, none, K'.elim (trList [n.succ]) [] c 
d⟩
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.PartrecToTM2.trNat.eq_1`：∀ (n : ℕ), Turing.PartrecToTM2.trNat n =
 Turing.PartrecToTM2.trNum ↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Num.add_one`：∀ (n : Num), n + 1 = n.succ
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_main`：∀ {a b c d a' : List Turing.Par
trecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Pa
rtrecToTM2.K'.main a' =     T…
· 使用引理 `Function.update_congr`：update_congr {β : Sort*} {f₁ f₂ : α -> β} (hf : f
₁ = f₂) {a'₁ a'₂ : α} (ha' : a'₁ = a'₂) {v₁ v₂ : β} (hv : v₁ = v₂) {a₁ a₂ : α} (
ha : a₁ = a…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_rev`：∀ {a b c d b' : List Turing.Part
recToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Par
trecToTM2.K'.rev b' =     Tu…
· 使用定理 `Turing.PartrecToTM2.unrev_ok`：unrev_ok {q s} {S : K' -> List Γ'} : Reach
es₁ (TM2.step tr) ⟨some (unrev q), s, S⟩ ⟨some q, none, update (update S rev [])
 main (List.revers…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Turing.TM2.stepAux.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `Turing.TM2.stepAux.eq_5`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (f : σ → Boo…
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `decide_true`：∀ (h : Decidable True), decide True = true
· 使用定理 `Turing.TM2.stepAux.eq_1`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `Turing.TM2.stepAux.eq_6`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (f : σ → Λ),…
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Turing.TM2.step.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3}
 {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (l : Λ)
 (v : σ) (…
（共 38 条，此处仅展示前 30 条）
-/
theorem succ_ok {q s n} {c d : List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (Λ'.succ q), s, K'.elim (trList [n]) [] c d⟩
      ⟨some q, none, K'.elim (trList [n.succ]) [] c d⟩ := by
  simp only [trList, trNat.eq_1, Nat.cast_succ, Num.add_one]
  rcases (n : Num) with - | a
  · refine TransGen.head rfl ?_
    simp only [Option.mem_def]
    convert! unrev_ok using 1
    simp only [elim_update_rev, elim_rev, elim_main, List.reverseAux_nil, elim_update_main]
    rfl
  simp only [trNum, Num.succ, Num.succ']
  suffices ∀ l₁, ∃ l₁' l₂' s',
      List.reverseAux l₁ (trPosNum a.succ) = List.reverseAux l₁' l₂' ∧
        Reaches₁ (TM2.step tr) ⟨some q.succ, s, K'.elim (trPosNum a ++ [Γ'.cons]) l₁ c d⟩
          ⟨some (unrev q), s', K'.elim (l₂' ++ [Γ'.cons]) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp only [List.reverseAux] at e
    refine h.trans ?_
    convert! unrev_ok using 2
    simp [e, List.reverseAux_eq]
  induction a generalizing s with intro l₁
  | one =>
    refine ⟨Γ'.bit0 :: l₁, [Γ'.bit1], some Γ'.cons, rfl, TransGen.head rfl (TransGen.single ?_)⟩
    simp [trPosNum]
  | bit1 m IH =>
    obtain ⟨l₁', l₂', s', e, h⟩ := IH (Γ'.bit0 :: l₁)
    refine ⟨l₁', l₂', s', e, TransGen.head ?_ h⟩
    simp [trPosNum]
    rfl
  | bit0 m _ =>
    refine ⟨l₁, _, some Γ'.bit0, rfl, TransGen.single ?_⟩
    simp only [TM2.step]; rw [tr]
    simp only [TM2.stepAux, pop', elim_main, elim_update_main,
      elim_rev, elim_update_rev, Function.update_self, Option.mem_def, Option.some.injEq]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.PartrecToTM2.pred_ok** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：pred_ok (q₁ q₂ s v) (c d : List Γ') : exists s', Reaches₁ (TM2.step tr) ⟨s
ome (Λ'.pred q₁ q₂), s, K'.elim (trList v) [] c d⟩ (v.headI.rec ⟨some q₁, s', K'
.elim (trList v.tail) [] c d⟩ fun n _ => ⟨some q₂, s', K'.elim (trList (n::v.tai
l)) [] c d⟩)
参数：q₁ q₂ s v；c d : List Γ'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.TM2.step.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3}
 {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (l : Λ)
 (v : σ) (…
· 使用定理 `Turing.TM2.stepAux.eq_3`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_main`：∀ {a b c d a' : List Turing.Par
trecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Pa
rtrecToTM2.K'.main a' =     T…
· 使用定理 `Turing.TM2.stepAux.eq_5`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (f : σ → Boo…
· 使用定理 `Decidable.decide.congr_simp`：∀ (p p_1 : Prop), p = p_1 → ∀ {h : Decidabl
e p} [h_1 : Decidable p_1], decide p = decide p_1
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `decide_false`：∀ (h : Decidable False), decide False = false
· 使用定理 `Turing.TM2.stepAux.eq_1`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_rev`：∀ {a b c d b' : List Turing.Part
recToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Par
trecToTM2.K'.rev b' =     Tu…
· 使用定理 `Turing.TM2.stepAux.eq_6`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (f : σ → Λ),…
· 使用定理 `Turing.TM2.stepAux.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.PartrecToTM2.trList.eq_1`：Turing.PartrecToTM2.trList [] = []
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Turing.PartrecToTM2.trNat_zero`：trNat_zero : trNat 0 = []
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Turing.PartrecToTM2.trNat.eq_1`：∀ (n : ℕ), Turing.PartrecToTM2.trNat n =
 Turing.PartrecToTM2.trNum ↑n
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `Num.add_one`：∀ (n : Num), n + 1 = n.succ
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `Turing.PartrecToTM2.tr.eq_7`：∀ (q₁ q₂ : Turing.PartrecToTM2.Λ'),   Turin
g.PartrecToTM2.tr (q₁.pred q₂) =     Turing.PartrecToTM2.pop' Turing.PartrecToTM
2.K'.main       (…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 45 条，此处仅展示前 30 条）
-/
theorem pred_ok (q₁ q₂ s v) (c d : List Γ') : ∃ s',
    Reaches₁ (TM2.step tr) ⟨some (Λ'.pred q₁ q₂), s, K'.elim (trList v) [] c d⟩
      (v.headI.rec ⟨some q₁, s', K'.elim (trList v.tail) [] c d⟩ fun n _ =>
        ⟨some q₂, s', K'.elim (trList (n::v.tail)) [] c d⟩) := by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine ⟨none, TransGen.single ?_⟩
    simp
  · refine ⟨some Γ'.cons, TransGen.single ?_⟩
    simp
  refine ⟨none, ?_⟩
  simp only [trList, trNat.eq_1, trNum, Nat.cast_succ, Num.add_one, Num.succ,
    List.tail_cons, List.headI_cons]
  rcases (n : Num) with - | a
  · simp only [trPosNum, Num.succ', List.singleton_append, List.nil_append]
    refine TransGen.head rfl ?_
    rw [tr]; simp only [pop', TM2.stepAux]
    convert! unrev_ok using 2
    simp
  simp only [Num.succ']
  suffices ∀ l₁, ∃ l₁' l₂' s',
    List.reverseAux l₁ (trPosNum a) = List.reverseAux l₁' l₂' ∧
      Reaches₁ (TM2.step tr)
        ⟨some (q₁.pred q₂), s, K'.elim (trPosNum a.succ ++ Γ'.cons :: trList v) l₁ c d⟩
        ⟨some (unrev q₂), s', K'.elim (l₂' ++ Γ'.cons :: trList v) l₁' c d⟩ by
    obtain ⟨l₁', l₂', s', e, h⟩ := this []
    simp only [List.reverseAux] at e
    refine h.trans ?_
    convert! unrev_ok using 2
    simp [e, List.reverseAux_eq]
  induction a generalizing s with intro l₁
  | one =>
    refine ⟨Γ'.bit1::l₁, [], some Γ'.cons, rfl, TransGen.head rfl (TransGen.single ?_)⟩
    simp [trPosNum, show PosNum.one.succ = PosNum.one.bit0 from rfl]
  | bit1 m IH =>
    obtain ⟨l₁', l₂', s', e, h⟩ := IH (some Γ'.bit0) (Γ'.bit1 :: l₁)
    refine ⟨l₁', l₂', s', e, TransGen.head ?_ h⟩
    simp
    rfl
  | bit0 m IH =>
    obtain ⟨a, l, e, h⟩ : ∃ a l, (trPosNum m = a::l) ∧ natEnd a = false := by
      cases m <;> refine ⟨_, _, rfl, rfl⟩
    refine ⟨Γ'.bit0 :: l₁, _, some a, rfl, TransGen.single ?_⟩
    simp [trPosNum, PosNum.succ, e, h, show some Γ'.bit1 ≠ some Γ'.bit0 by decide,
      Option.getD, -natEnd]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.PartrecToTM2.trNormal_respects** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partre
cToTM2`。
形式化陈述：trNormal_respects (c k v s) : exists b₂, TrCfg (stepNormal c k v) b₂ ∧ Rea
ches₁ (TM2.step tr) ⟨some (trNormal c (trCont k)), s, K'.elim (trList v) [] [] (
trContStack k)⟩ b₂
参数：c k v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Turing.ToPartrec.Code.zero'`：zero'_eval : zero'.eval = fun v => pure (0 
:: v)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.TM2.step.eq_2`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u_3}
 {σ : Type u_4} [inst : DecidableEq K] (M : Λ → Turing.TM2.Stmt Γ Λ σ)   (l : Λ)
 (v : σ) (…
· 使用定理 `Turing.TM2.stepAux.eq_5`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (f : σ → Boo…
· 使用定理 `Turing.TM2.stepAux.eq_1`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (k : K) (f :…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_main`：∀ {a b c d a' : List Turing.Par
trecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Pa
rtrecToTM2.K'.main a' =     T…
· 使用定理 `Turing.TM2.stepAux.eq_6`：∀ {K : Type u_1} {Γ : K → Type u_2} {Λ : Type u
_3} {σ : Type u_4} [inst : DecidableEq K] (x : σ)   (x_1 : (k : K) → List (Γ k))
 (f : σ → Λ),…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.PartrecToTM2.trNat_zero`：trNat_zero : trNat 0 = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Relation.TransGen.trans`：∀ {α : Sort u} {r : α → α → Prop} {a b c : α}, 
  Relation.TransGen r a b → Relation.TransGen r b c → Relation.TransGen r a c
· 使用定理 `Turing.PartrecToTM2.head_main_ok`：head_main_ok {q s L} {c d : List Γ'} :
 Reaches₁ (TM2.step tr) ⟨some (head main q), s, K'.elim (trList L) [] c d⟩ ⟨some
 q, none, K'.elim (trL…
· 使用定理 `Turing.PartrecToTM2.succ_ok`：succ_ok {q s n} {c d : List Γ'} : Reaches₁ 
(TM2.step tr) ⟨some (Λ'.succ q), s, K'.elim (trList [n]) [] c d⟩ ⟨some q, none, 
K'.elim (trList […
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Turing.PartrecToTM2.clear_ok`：clear_ok {p k q s L₁ o L₂} {S : K' -> List
 Γ'} (e : splitAtPred p (S k) = (L₁, o, L₂)) : Reaches₁ (TM2.step tr) ⟨some (Λ'.
clear p k q), s, S…
· 使用定理 `Turing.PartrecToTM2.splitAtPred_eq`：splitAtPred_eq {α} (p : α -> Bool) :
 forall L l₁ o l₂, (forall x in l₁, p x = false) -> Option.elim' (L = l₁ ∧ l₂ = 
[]) (fun a => p a = true…
· 使用定理 `Turing.PartrecToTM2.trNat_natEnd`：trNat_natEnd (n) : forall x in trNat n
, natEnd x = false
· 使用引理 `Option.elim'`：elim'_update {α : Type*} {β : Type*} [DecidableEq α] (f : 
β) (g : α -> β) (a : α) (x : β) : Option.elim' f (update g a x) = update (Option
.e…
· 使用定理 `Turing.PartrecToTM2.trList.eq_1`：Turing.PartrecToTM2.trList [] = []
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
（共 47 条，此处仅展示前 30 条）
-/
theorem trNormal_respects (c k v s) :
    ∃ b₂,
      TrCfg (stepNormal c k v) b₂ ∧
        Reaches₁ (TM2.step tr)
          ⟨some (trNormal c (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩ b₂ := by
  induction c generalizing k v s with
  | zero' => refine ⟨_, ⟨s, rfl⟩, TransGen.single ?_⟩; simp
  | succ => refine ⟨_, ⟨none, rfl⟩, head_main_ok.trans succ_ok⟩
  | tail =>
    let o : Option Γ' := List.casesOn v none fun _ _ => some Γ'.cons
    refine ⟨_, ⟨o, rfl⟩, ?_⟩; convert! clear_ok _ using 2
    · simp; rfl
    swap
    refine splitAtPred_eq _ _ (trNat v.headI) _ _ (trNat_natEnd _) ?_
    cases v <;> simp [o]
  | cons f fs IHf _ =>
    obtain ⟨c, h₁, h₂⟩ := IHf (Cont.cons₁ fs v k) v none
    refine ⟨c, h₁, TransGen.head rfl <| (move_ok (by decide) (splitAtPred_false _)).trans ?_⟩
    simp only [TM2.step, Option.mem_def, elim_stack, elim_update_stack, elim_update_main,
      elim_main, elim_rev, elim_update_rev]
    refine (copy_ok _ none [] (trList v).reverse _ _).trans ?_
    convert! h₂ using 2
    simp [List.reverseAux_eq, trContStack]
  | comp f _ _ IHg => exact IHg (Cont.comp f k) v s
  | case f g IHf IHg =>
    rw [stepNormal]
    simp only
    obtain ⟨s', h⟩ := pred_ok _ _ s v _ _
    revert h; rcases v.headI with - | n <;> intro h
    · obtain ⟨c, h₁, h₂⟩ := IHf k _ s'
      exact ⟨_, h₁, h.trans h₂⟩
    · obtain ⟨c, h₁, h₂⟩ := IHg k _ s'
      exact ⟨_, h₁, h.trans h₂⟩
  | fix f IH => apply IH

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Turing.PartrecToTM2.tr_ret_respects** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecT
oTM2`。
形式化陈述：tr_ret_respects (k v s) : exists b₂, TrCfg (stepRet k v) b₂ ∧ Reaches₁ (TM
2.step tr) ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k
)⟩ b₂
参数：k v s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Turing.PartrecToTM2.trNormal_respects`：trNormal_respects (c k v s) : exi
sts b₂, TrCfg (stepNormal c k v) b₂ ∧ Reaches₁ (TM2.step tr) ⟨some (trNormal c (
trCont k)), s, K'.elim (trL…
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Relation.TransGen.trans`：∀ {α : Sort u} {r : α → α → Prop} {a b c : α}, 
  Relation.TransGen r a b → Relation.TransGen r b c → Relation.TransGen r a c
· 使用定理 `Turing.PartrecToTM2.move₂_ok`：move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' -> 
List Γ'} (h₁ : k₁ != rev ∧ k₂ != rev ∧ k₁ != k₂) (h₂ : S rev = []) (e : splitAtP
red p (S k₁) = (L₁…
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Turing.PartrecToTM2.splitAtPred_false`：splitAtPred_false {α} (L : List α
) : splitAtPred (fun _ => false) L = (L, none, [])
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_main`：∀ {a b c d a' : List Turing.Par
trecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Pa
rtrecToTM2.K'.main a' =     T…
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_aux`：∀ {a b c d c' : List Turing.Part
recToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.Par
trecToTM2.K'.aux c' =     Tu…
· 使用定理 `Turing.PartrecToTM2.splitAtPred_eq`：splitAtPred_eq {α} (p : α -> Bool) :
 forall L l₁ o l₂, (forall x in l₁, p x = false) -> Option.elim' (L = l₁ ∧ l₂ = 
[]) (fun a => p a = true…
· 使用定理 `Bool.decide_false`：decide_false {p : Prop} [Decidable p] : ¬p -> decide 
p = false
· 使用定理 `Turing.PartrecToTM2.trList_ne_consₗ`：trList_ne_consₗ : forall (l), foral
l x in trList l, x != Γ'.consₗ | a :: l, x, h => by simp only [trList, List.mem_
append, List.mem_cons] at…
· 使用定理 `Turing.PartrecToTM2.K'.elim_update_stack`：∀ {a b c d d' : List Turing.Pa
rtrecToTM2.Γ'},   Function.update (Turing.PartrecToTM2.K'.elim a b c d) Turing.P
artrecToTM2.K'.stack d' =     …
· 使用定理 `Function.update.congr_simp`：∀ {α : Sort u} {β : α → Sort v} {inst : Deci
dableEq α} [inst_1 : DecidableEq α] (f f_1 : (a : α) → β a),   f = f_1 → ∀ (a' :
 α) (v v_1 : β a…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Turing.PartrecToTM2.head_stack_ok`：head_stack_ok {q s L₁ L₂ L₃} : Reache
s₁ (TM2.step tr) ⟨some (head stack q), s, K'.elim (trList L₁) [] [] (trList L₂ +
+ Γ'.consₗ :: L₃)⟩ ⟨som…
· 使用定理 `Turing.ToPartrec.stepRet.eq_5`：∀ (x : List ℕ) (f : Turing.ToPartrec.Code
) (k : Turing.ToPartrec.Cont),   Turing.ToPartrec.stepRet (Turing.ToPartrec.Cont
.fix f k) x =     i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Turing.PartrecToTM2.trNat_zero`：trNat_zero : trNat 0 = []
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Turing.PartrecToTM2.trList.eq_2`：∀ (n : ℕ) (ns : List ℕ),   Turing.Partr
ecToTM2.trList (n :: ns) =     Turing.PartrecToTM2.trNat n ++ Turing.PartrecToTM
2.Γ'.cons :: Turing.P…
· 使用定理 `List.headI.eq_2`：∀ {α : Type u_1} [inst : Inhabited α] (a : α) (tail : L
ist α), (a :: tail).headI = a
（共 47 条，此处仅展示前 30 条）
-/
theorem tr_ret_respects (k v s) : ∃ b₂,
    TrCfg (stepRet k v) b₂ ∧
      Reaches₁ (TM2.step tr)
        ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩ b₂ := by
  induction k generalizing v s with
  | halt => exact ⟨_, rfl, TransGen.single rfl⟩
  | cons₁ fs as k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects fs (Cont.cons₂ v k) as none
    refine ⟨s', h₁, TransGen.head rfl ?_⟩; simp
    refine (move₂_ok (by decide) ?_ (splitAtPred_false _)).trans ?_; · rfl
    simp only [TM2.step, Option.mem_def, Option.elim, id_eq, elim_update_main, elim_main, elim_aux,
      List.append_nil, elim_update_aux]
    refine (move₂_ok (L₁ := ?_) (o := ?_) (L₂ := ?_) (by decide) rfl ?_).trans ?_
    pick_goal 4
    · exact splitAtPred_eq _ _ _ (some Γ'.consₗ) _
        (fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)) ⟨rfl, rfl⟩
    refine (move₂_ok (by decide) ?_ (splitAtPred_false _)).trans ?_; · rfl
    simp only [TM2.step, Option.mem_def, Option.elim, elim_update_stack, elim_main,
      List.append_nil, elim_update_main, id_eq, elim_update_aux,
      elim_aux, elim_stack]
    exact h₂
  | cons₂ ns k IH =>
    obtain ⟨c, h₁, h₂⟩ := IH (ns.headI :: v) none
    exact ⟨c, h₁, TransGen.head rfl <| head_stack_ok.trans h₂⟩
  | comp f k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects f k v s
    exact ⟨_, h₁, TransGen.head rfl h₂⟩
  | fix f k IH =>
    rw [stepRet]
    have :
      if v.headI = 0 then natEnd ((trList v).head?.getD default) = true ∧
          (trList v).tail = trList v.tail
      else
        natEnd ((trList v).head?.getD default) = false ∧
          (trList v).tail = (trNat v.headI).tail ++ Γ'.cons :: trList v.tail := by
      obtain - | n := v
      · exact ⟨rfl, rfl⟩
      rcases n with - | n
      · simp
      rw [trList, List.headI, trNat, Nat.cast_succ, Num.add_one, Num.succ, List.tail]
      cases (n : Num).succ' <;> exact ⟨rfl, rfl⟩
    by_cases h : v.headI = 0 <;> simp only [h, ite_true, ite_false] at this ⊢
    · obtain ⟨c, h₁, h₂⟩ := IH v.tail (trList v).head?
      refine ⟨c, h₁, TransGen.head rfl ?_⟩
      rw [trCont, tr]; simp only [pop', TM2.stepAux, elim_main, this, elim_update_main]
      exact h₂
    · obtain ⟨s', h₁, h₂⟩ := trNormal_respects f (Cont.fix f k) v.tail (some Γ'.cons)
      refine ⟨_, h₁, TransGen.head rfl <| TransGen.trans ?_ h₂⟩
      rw [trCont, tr]; simp only [pop', TM2.stepAux, elim_main, this.1]
      convert! clear_ok (splitAtPred_eq _ _ (trNat v.headI).tail (some Γ'.cons) _ _ _) using 2
      · simp
        convert! rfl
      · exact fun x h => trNat_natEnd _ _ (List.tail_subset _ h)
      · exact ⟨rfl, this.2⟩
/-
**Turing.PartrecToTM2.tr_respects** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2
`。
形式化陈述：StateTransition.Respects Turing.ToPartrec.step (Turing.TM2.step Turing.Par
trecToTM2.tr) Turing.PartrecToTM2.TrCfg
参数：Turing.TM2.step Turing.PartrecToTM2.tr。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Turing.PartrecToTM2.tr_ret_respects`：tr_ret_respects (k v s) : exists b₂
, TrCfg (stepRet k v) b₂ ∧ Reaches₁ (TM2.step tr) ⟨some (Λ'.ret (trCont k)), s, 
K'.elim (trList v) [] [] …
-/
theorem tr_respects : Respects step (TM2.step tr) TrCfg
  | Cfg.ret _ _, _, ⟨_, rfl⟩ => tr_ret_respects _ _ _
  | Cfg.halt _, _, rfl => rfl

/-- The initial state, evaluating function `c` on input `v`. -/
/-
**Turing.PartrecToTM2.init** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：init (c : Code) (v : List Nat) : Cfg'
参数：c : Code；v : List Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
The initial state, evaluating function `c` on input `v`.
-/
def init (c : Code) (v : List ℕ) : Cfg' :=
  ⟨some (trNormal c Cont'.halt), none, K'.elim (trList v) [] [] []⟩
/-
**Turing.PartrecToTM2.tr_init** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_init (c v) : exists b, TrCfg (stepNormal c Cont.halt v) b ∧ Reaches₁ (T
M2.step tr) (init c v) b
参数：c v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.trNormal_respects`：trNormal_respects (c k v s) : exi
sts b₂, TrCfg (stepNormal c k v) b₂ ∧ Reaches₁ (TM2.step tr) ⟨some (trNormal c (
trCont k)), s, K'.elim (trL…
-/
theorem tr_init (c v) :
    ∃ b, TrCfg (stepNormal c Cont.halt v) b ∧ Reaches₁ (TM2.step tr) (init c v) b :=
  trNormal_respects _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-
**Turing.PartrecToTM2.tr_eval** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：tr_eval (c v) : eval (TM2.step tr) (init c v) = halt < > Code.eval c v
参数：c v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Turing.PartrecToTM2.tr_init`：tr_init (c v) : exists b, TrCfg (stepNormal
 c Cont.halt v) b ∧ Reaches₁ (TM2.step tr) (init c v) b
· 使用定理 `Part.ext`：ext {o p : Part α} (H : forall a, a in o ↔ a in p) : o = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StateTransition.reaches_eval`：reaches_eval {σ} {f : σ -> Option σ} {a b}
 (ab : Reaches f a b) : eval f a = eval f b
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
· 使用定理 `StateTransition.tr_eval_rev`：tr_eval_rev {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ ->
 Prop} (H : Respects f₁ f₂ tr) {a₁ b₂ a₂} (aa : tr a₁ a₂) (ab : b₂ in eval f₂ a₂
) : exists b₁, tr…
· 使用定理 `Turing.PartrecToTM2.tr_respects`：StateTransition.Respects Turing.ToPartr
ec.step (Turing.TM2.step Turing.PartrecToTM2.tr) Turing.PartrecToTM2.TrCfg
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.ToPartrec.stepNormal_eval`：stepNormal_eval (c v) : eval step (ste
pNormal c Cont.halt v) = Cfg.halt < > c.eval v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `StateTransition.tr_eval`：tr_eval {σ₁ σ₂ f₁ f₂} {tr : σ₁ -> σ₂ -> Prop} (
H : Respects f₁ f₂ tr) {a₁ b₁ a₂} (aa : tr a₁ a₂) (ab : b₁ in eval f₁ a₁) : exis
ts b₂, tr b₁ …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Turing.ToPartrec.Cfg.halt.injEq`：∀ (a a_1 : List ℕ), (Turing.ToPartrec.C
fg.halt a = Turing.ToPartrec.Cfg.halt a_1) = (a = a_1)
-/
theorem tr_eval (c v) : eval (TM2.step tr) (init c v) = halt <$> Code.eval c v := by
  obtain ⟨i, h₁, h₂⟩ := tr_init c v
  refine Part.ext fun x => ?_
  rw [reaches_eval h₂.to_reflTransGen]; simp only [Part.map_eq_map, Part.mem_map_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, hc₁, hc₂⟩ := tr_eval_rev tr_respects h₁ h
    simp only [stepNormal_eval, Part.map_eq_map, Part.mem_map_iff] at hc₂
    obtain ⟨v', hv, rfl⟩ := hc₂
    exact ⟨_, hv, hc₁.symm⟩
  · rintro ⟨v', hv, rfl⟩
    have := StateTransition.tr_eval (b₁ := Cfg.halt v') tr_respects h₁
    simp only [stepNormal_eval, Part.map_eq_map, Part.mem_map_iff, Cfg.halt.injEq,
      exists_eq_right] at this
    obtain ⟨_, ⟨⟩, h⟩ := this hv
    exact h

/-- The set of machine states reachable via downward label jumps, discounting jumps via `ret`. -/
/-
**Turing.PartrecToTM2.trStmts** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of machine states reachable via downward label jumps, discounting jumps 
via `ret`.
-/
def trStmts₁ : Λ' → Finset Λ'
  | Q@(Λ'.move _ _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.push _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.read q) => insert Q <| Finset.univ.biUnion fun s => trStmts₁ (q s)
  | Q@(Λ'.clear _ _ q) => insert Q <| trStmts₁ q
  | Q@(Λ'.copy q) => insert Q <| trStmts₁ q
  | Q@(Λ'.succ q) => insert Q <| insert (unrev q) <| trStmts₁ q
  | Q@(Λ'.pred q₁ q₂) => insert Q <| trStmts₁ q₁ ∪ insert (unrev q₂) (trStmts₁ q₂)
  | Q@(Λ'.ret _) => {Q}

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Turing.PartrecToTM2.trStmts** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trStmts₁_trans {q q'} : q' ∈ trStmts₁ q → trStmts₁ q' ⊆ trStmts₁ q := by
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
  all_goals
    simp +contextual only [trStmts₁, Finset.mem_insert, Finset.mem_union,
      or_imp, Finset.mem_singleton, Finset.Subset.refl, imp_true_iff, true_and]
    repeat exact fun h => Finset.Subset.trans (q_ih h) (Finset.subset_insert _ _)
  · simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, forall_exists_index]
    intro s h x h'
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_insert]
    exact Or.inr ⟨_, q_ih s h h'⟩
  · constructor
    · rintro rfl
      apply Finset.subset_insert
    · intro h x h'
      simp only [Finset.mem_insert]
      exact Or.inr (Or.inr <| q_ih h h')
  · refine ⟨fun h x h' => ?_, fun _ x h' => ?_, fun h x h' => ?_⟩ <;> simp
    · exact Or.inr (Or.inr <| Or.inl <| q₁_ih h h')
    · rcases Finset.mem_insert.1 h' with h' | h' <;> simp [h', unrev]
    · exact Or.inr (Or.inr <| Or.inr <| q₂_ih h h')
/-
**Turing.PartrecToTM2.trStmts** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trStmts₁_self (q) : q ∈ trStmts₁ q := by
  induction q <;> · first | apply Finset.mem_singleton_self | apply Finset.mem_insert_self

/-- The (finite!) set of machine states visited during the course of evaluation of `c`,
including the state `ret k` but not any states after that (that is, the states visited while
evaluating `k`). -/
/-
**Turing.PartrecToTM2.codeSupp'** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：codeSupp'_self (c k) : trStmts₁ (trNormal c k) subseteq codeSupp' c k
参数：c k。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (finite!) set of machine states visited during the course of evaluation of `
c`,
including the state `ret k` but not any states after that (that is, the states v
isited while
evaluating `k`).
-/
def codeSupp' : Code → Cont' → Finset Λ'
  | c@Code.zero', k => trStmts₁ (trNormal c k)
  | c@Code.succ, k => trStmts₁ (trNormal c k)
  | c@Code.tail, k => trStmts₁ (trNormal c k)
  | c@(Code.cons f fs), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' f (Cont'.cons₁ fs k) ∪
        (trStmts₁
            (move₂ (fun _ => false) main aux <|
              move₂ (fun s => s = Γ'.consₗ) stack main <|
                move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
          (codeSupp' fs (Cont'.cons₂ k) ∪ trStmts₁ (head stack <| Λ'.ret k))))
  | c@(Code.comp f g), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' g (Cont'.comp f k) ∪ (trStmts₁ (trNormal f k) ∪ codeSupp' f k))
  | c@(Code.case f g), k => trStmts₁ (trNormal c k) ∪ (codeSupp' f k ∪ codeSupp' g k)
  | c@(Code.fix f), k =>
    trStmts₁ (trNormal c k) ∪
      (codeSupp' f (Cont'.fix f k) ∪
        (trStmts₁ (Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) ∪ {Λ'.ret k}))

@[simp]
/-
**Turing.PartrecToTM2.codeSupp'_self** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecTo
TM2`。
形式化陈述：∀ (c : Turing.ToPartrec.Code) (k : Turing.PartrecToTM2.Cont'),   Turing.Pa
rtrecToTM2.trStmts₁ (Turing.PartrecToTM2.trNormal c k) ⊆ Turing.PartrecToTM2.cod
eSupp' c k
参数：c : Turing.ToPartrec.Code；k : Turing.PartrecToTM2.Cont'；Turing.PartrecToTM2.t
rNormal c k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `Turing.ToPartrec.Code.zero'`：zero'_eval : zero'.eval = fun v => pure (0 
:: v)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.union_subset_left`：union_subset_left (h : s union t subseteq u) :
 s subseteq u
-/
theorem codeSupp'_self (c k) : trStmts₁ (trNormal c k) ⊆ codeSupp' c k := by
  cases c <;> first | rfl | exact Finset.union_subset_left (fun _ a ↦ a)

/-- The (finite!) set of machine states visited during the course of evaluation of a continuation
`k`, not including the initial state `ret k`. -/
/-
**Turing.PartrecToTM2.contSupp** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Turing.PartrecToTM2.Cont' → Finset Turing.PartrecToTM2.Λ'
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (finite!) set of machine states visited during the course of evaluation of a
 continuation
`k`, not including the initial state `ret k`.
-/
def contSupp : Cont' → Finset Λ'
  | Cont'.cons₁ fs k =>
    trStmts₁
        (move₂ (fun _ => false) main aux <|
          move₂ (fun s => s = Γ'.consₗ) stack main <|
            move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
      (codeSupp' fs (Cont'.cons₂ k) ∪ (trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k))
  | Cont'.cons₂ k => trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k
  | Cont'.comp f k => codeSupp' f k ∪ contSupp k
  | Cont'.fix f k => codeSupp' (Code.fix f) k ∪ contSupp k
  | Cont'.halt => ∅

/-- The (finite!) set of machine states visited during the course of evaluation of `c` in
continuation `k`. This is actually closed under forward simulation (see `tr_supports`), and the
existence of this set means that the machine constructed in this section is in fact a proper
Turing machine, with a finite set of states. -/
/-
**Turing.PartrecToTM2.codeSupp** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：codeSupp (c : Code) (k : Cont') : Finset Λ'
参数：c : Code；k : Cont'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k

--- 原说明 ---
The (finite!) set of machine states visited during the course of evaluation of `
c` in
continuation `k`. This is actually closed under forward simulation (see `tr_supp
orts`), and the
existence of this set means that the machine constructed in this section is in f
act a proper
Turing machine, with a finite set of states.
-/
def codeSupp (c : Code) (k : Cont') : Finset Λ' :=
  codeSupp' c k ∪ contSupp k

@[simp]
/-
**Turing.PartrecToTM2.codeSupp_self** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：codeSupp_self (c k) : trStmts₁ (trNormal c k) subseteq codeSupp c k
参数：c k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `Turing.PartrecToTM2.codeSupp'_self`：∀ (c : Turing.ToPartrec.Code) (k : T
uring.PartrecToTM2.Cont'),   Turing.PartrecToTM2.trStmts₁ (Turing.PartrecToTM2.t
rNormal c k) ⊆ Turing.Pa…
· 使用定理 `Finset.union_subset_left`：union_subset_left (h : s union t subseteq u) :
 s subseteq u
-/
theorem codeSupp_self (c k) : trStmts₁ (trNormal c k) ⊆ codeSupp c k :=
  Finset.Subset.trans (codeSupp'_self _ _) (Finset.union_subset_left fun _ a ↦ a)

@[simp]
/-
**Turing.PartrecToTM2.codeSupp_zero** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：codeSupp_zero (k) : codeSupp Code.zero' k = trStmts₁ (trNormal Code.zero' 
k) union contSupp k
参数：k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.ToPartrec.Code.zero'`：zero'_eval : zero'.eval = fun v => pure (0 
:: v)
-/
theorem codeSupp_zero (k) : codeSupp Code.zero' k = trStmts₁ (trNormal Code.zero' k) ∪ contSupp k :=
  rfl

@[simp]
/-
**Turing.PartrecToTM2.codeSupp_succ** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：codeSupp_succ (k) : codeSupp Code.succ k = trStmts₁ (trNormal Code.succ k)
 union contSupp k
参数：k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codeSupp_succ (k) : codeSupp Code.succ k = trStmts₁ (trNormal Code.succ k) ∪ contSupp k :=
  rfl

@[simp]
/-
**Turing.PartrecToTM2.codeSupp_tail** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：codeSupp_tail (k) : codeSupp Code.tail k = trStmts₁ (trNormal Code.tail k)
 union contSupp k
参数：k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem codeSupp_tail (k) : codeSupp Code.tail k = trStmts₁ (trNormal Code.tail k) ∪ contSupp k :=
  rfl

@[simp]
/-
**Turing.PartrecToTM2.codeSupp_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：codeSupp_cons (f fs k) : codeSupp (Code.cons f fs) k = trStmts₁ (trNormal 
(Code.cons f fs) k) union codeSupp f (Cont'.cons₁ fs k)
参数：f fs k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_assoc`：union_assoc (s₁ s₂ s₃ : Finset α) : s₁ union s₂ unio
n s₃ = s₁ union (s₂ union s₃)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem codeSupp_cons (f fs k) :
    codeSupp (Code.cons f fs) k =
      trStmts₁ (trNormal (Code.cons f fs) k) ∪ codeSupp f (Cont'.cons₁ fs k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]

@[simp]
/-
**Turing.PartrecToTM2.codeSupp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：codeSupp_comp (f g k) : codeSupp (Code.comp f g) k = trStmts₁ (trNormal (C
ode.comp f g) k) union codeSupp g (Cont'.comp f k)
参数：f g k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.union_assoc`：union_assoc (s₁ s₂ s₃ : Finset α) : s₁ union s₂ unio
n s₃ = s₁ union (s₂ union s₃)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.union_eq_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s t : Fi
nset α}, s ∪ t = t ↔ s ⊆ t
· 使用定理 `Turing.PartrecToTM2.codeSupp'_self`：∀ (c : Turing.ToPartrec.Code) (k : T
uring.PartrecToTM2.Cont'),   Turing.PartrecToTM2.trStmts₁ (Turing.PartrecToTM2.t
rNormal c k) ⊆ Turing.Pa…
-/
theorem codeSupp_comp (f g k) :
    codeSupp (Code.comp f g) k =
      trStmts₁ (trNormal (Code.comp f g) k) ∪ codeSupp g (Cont'.comp f k) := by
  simp only [codeSupp, codeSupp', trNormal, Finset.union_assoc, contSupp]
  rw [← Finset.union_assoc _ _ (contSupp k),
    Finset.union_eq_right.2 (codeSupp'_self _ _)]

@[simp]
/-
**Turing.PartrecToTM2.codeSupp_case** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：codeSupp_case (f g k) : codeSupp (Code.case f g) k = trStmts₁ (trNormal (C
ode.case f g) k) union (codeSupp f k union codeSupp g k)
参数：f g k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.union_left_comm`：union_left_comm (s t u : Finset α) : s union (t 
union u) = t union (s union u)
· 使用定理 `Finset.union_assoc`：union_assoc (s₁ s₂ s₃ : Finset α) : s₁ union s₂ unio
n s₃ = s₁ union (s₂ union s₃)
· 使用定理 `Finset.union_idempotent`：union_idempotent (s : Finset α) : s union s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem codeSupp_case (f g k) :
    codeSupp (Code.case f g) k =
      trStmts₁ (trNormal (Code.case f g) k) ∪ (codeSupp f k ∪ codeSupp g k) := by
  simp [codeSupp, codeSupp', Finset.union_assoc, Finset.union_left_comm]

@[simp]
/-
**Turing.PartrecToTM2.codeSupp_fix** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM
2`。
形式化陈述：codeSupp_fix (f k) : codeSupp (Code.fix f) k = trStmts₁ (trNormal (Code.fi
x f) k) union codeSupp f (Cont'.fix f k)
参数：f k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.union_singleton`：union_singleton (x : α) (s : Finset α) : s union
 {x} = insert x s
· 使用定理 `Finset.union_insert`：union_insert (a : α) (s t : Finset α) : s union ins
ert a t = insert a (s union t)
· 使用定理 `Finset.union_left_comm`：union_left_comm (s t u : Finset α) : s union (t 
union u) = t union (s union u)
· 使用定理 `Finset.insert_union`：insert_union (a : α) (s t : Finset α) : insert a s 
union t = insert a (s union t)
· 使用定理 `Finset.union_assoc`：union_assoc (s₁ s₂ s₃ : Finset α) : s₁ union s₂ unio
n s₃ = s₁ union (s₂ union s₃)
· 使用定理 `Finset.union_left_idem`：union_left_idem (s t : Finset α) : s union (s un
ion t) = s union t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem codeSupp_fix (f k) :
    codeSupp (Code.fix f) k = trStmts₁ (trNormal (Code.fix f) k) ∪ codeSupp f (Cont'.fix f k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm,
    Finset.union_left_idem]

@[simp]
/-
**Turing.PartrecToTM2.contSupp_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem contSupp_cons₁ (fs k) :
    contSupp (Cont'.cons₁ fs k) =
      trStmts₁
          (move₂ (fun _ => false) main aux <|
            move₂ (fun s => s = Γ'.consₗ) stack main <|
              move₂ (fun _ => false) aux stack <| trNormal fs (Cont'.cons₂ k)) ∪
        codeSupp fs (Cont'.cons₂ k) := by
  simp [codeSupp, contSupp]

@[simp]
/-
**Turing.PartrecToTM2.contSupp_cons** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem contSupp_cons₂ (k) :
    contSupp (Cont'.cons₂ k) = trStmts₁ (head stack <| Λ'.ret k) ∪ contSupp k :=
  rfl

@[simp]
/-
**Turing.PartrecToTM2.contSupp_comp** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：contSupp_comp (f k) : contSupp (Cont'.comp f k) = codeSupp f k
参数：f k。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem contSupp_comp (f k) : contSupp (Cont'.comp f k) = codeSupp f k :=
  rfl
/-
**Turing.PartrecToTM2.contSupp_fix** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM
2`。
形式化陈述：contSupp_fix (f k) : contSupp (Cont'.fix f k) = codeSupp f (Cont'.fix f k)
参数：f k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_assoc`：union_assoc (s₁ s₂ s₃ : Finset α) : s₁ union s₂ unio
n s₃ = s₁ union (s₂ union s₃)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem contSupp_fix (f k) : contSupp (Cont'.fix f k) = codeSupp f (Cont'.fix f k) := by
  simp +contextual [codeSupp, codeSupp', contSupp, Finset.union_assoc,
    Finset.subset_iff, -Finset.singleton_union, -Finset.union_singleton]

@[simp]
/-
**Turing.PartrecToTM2.contSupp_halt** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：contSupp_halt : contSupp Cont'.halt = ∅
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem contSupp_halt : contSupp Cont'.halt = ∅ :=
  rfl

/-- The statement `Λ'.Supports S q` means that `contSupp k ⊆ S` for any `ret k`
reachable from `q`.
(This is a technical condition used in the proof that the machine is supported.) -/
/-
**Turing.PartrecToTM2.** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The statement `Λ'.Supports S q` means that `contSupp k ⊆ S` for any `ret k`
reachable from `q`.
(This is a technical condition used in the proof that the machine is supported.)
-/
def Λ'.Supports (S : Finset Λ') : Λ' → Prop
  | Λ'.move _ _ _ q => Λ'.Supports S q
  | Λ'.push _ _ q => Λ'.Supports S q
  | Λ'.read q => ∀ s, Λ'.Supports S (q s)
  | Λ'.clear _ _ q => Λ'.Supports S q
  | Λ'.copy q => Λ'.Supports S q
  | Λ'.succ q => Λ'.Supports S q
  | Λ'.pred q₁ q₂ => Λ'.Supports S q₁ ∧ Λ'.Supports S q₂
  | Λ'.ret k => contSupp k ⊆ S

/-- A shorthand for the predicate that we are proving in the main theorems `trStmts₁_supports`,
`codeSupp'_supports`, `contSupp_supports`, `codeSupp_supports`. The set `S` is fixed throughout
the proof, and denotes the full set of states in the machine, while `K` is a subset that we are
currently proving a property about. The predicate asserts that every state in `K` is closed in `S`
under forward simulation, i.e. stepping forward through evaluation starting from any state in `K`
stays entirely within `S`. -/
/-
**Turing.PartrecToTM2.Supports** 是 Mathlib 中的一个定义，位于命名空间 `Turing.PartrecToTM2`。
形式化陈述：Supports (K S : Finset Λ')
参数：K S : Finset Λ'。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a

--- 原说明 ---
A shorthand for the predicate that we are proving in the main theorems `trStmts₁
_supports`,
`codeSupp'_supports`, `contSupp_supports`, `codeSupp_supports`. The set `S` is f
ixed throughout
the proof, and denotes the full set of states in the machine, while `K` is a sub
set that we are
currently proving a property about. The predicate asserts that every state in `K
` is closed in `S`
under forward simulation, i.e. stepping forward through evaluation starting from
 any state in `K`
stays entirely within `S`.
-/
def Supports (K S : Finset Λ') :=
  ∀ q ∈ K, TM2.SupportsStmt S (tr q)
/-
**Turing.PartrecToTM2.supports_insert** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecT
oTM2`。
形式化陈述：supports_insert {K S q} : Supports (insert q K) S ↔ TM2.SupportsStmt S (tr
 q) ∧ Supports K S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem supports_insert {K S q} :
    Supports (insert q K) S ↔ TM2.SupportsStmt S (tr q) ∧ Supports K S := by simp [Supports]
/-
**Turing.PartrecToTM2.supports_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partr
ecToTM2`。
形式化陈述：supports_singleton {S q} : Supports {q} S ↔ TM2.SupportsStmt S (tr q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem supports_singleton {S q} : Supports {q} S ↔ TM2.SupportsStmt S (tr q) := by simp [Supports]
/-
**Turing.PartrecToTM2.supports_union** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecTo
TM2`。
形式化陈述：supports_union {K₁ K₂ S} : Supports (K₁ union K₂) S ↔ Supports K₁ S ∧ Supp
orts K₂ S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem supports_union {K₁ K₂ S} : Supports (K₁ ∪ K₂) S ↔ Supports K₁ S ∧ Supports K₂ S := by
  simp [Supports, or_imp, forall_and]
/-
**Turing.PartrecToTM2.supports_biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partrec
ToTM2`。
形式化陈述：supports_biUnion {K : Option Γ' -> Finset Λ'} {S} : Supports (Finset.univ.
biUnion K) S ↔ forall a, Supports (K a) S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem supports_biUnion {K : Option Γ' → Finset Λ'} {S} :
    Supports (Finset.univ.biUnion K) S ↔ ∀ a, Supports (K a) S := by
  simpa [Supports] using forall_comm
/-
**Turing.PartrecToTM2.head_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToT
M2`。
形式化陈述：head_supports {S k q} (H : (q : Λ').Supports S) : (head k q).Supports S
参数：H : (q : Λ').Supports S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem head_supports {S k q} (H : (q : Λ').Supports S) : (head k q).Supports S := fun _ => by
  dsimp only; split_ifs <;> exact H
/-
**Turing.PartrecToTM2.ret_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM
2`。
形式化陈述：ret_supports {S k} (H₁ : contSupp k subseteq S) : TM2.SupportsStmt S (tr (
Λ'.ret k))
参数：H₁ : contSupp k subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.trStmts₁_self`：trStmts₁_self (q) : q in trStmts₁ q
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_subset_iff`：union_subset_iff : s union t subseteq u ↔ s sub
seteq u ∧ t subseteq u
· 使用定理 `Turing.PartrecToTM2.contSupp_cons₁`：contSupp_cons₁ (fs k) : contSupp (Co
nt'.cons₁ fs k) = trStmts₁ (move₂ (fun _ => false) main aux <| move₂ (fun s => s
 = Γ'.consₗ) stack main …
· 使用定理 `Turing.PartrecToTM2.contSupp_cons₂`：contSupp_cons₂ (k) : contSupp (Cont'
.cons₂ k) = trStmts₁ (head stack <| Λ'.ret k) union contSupp k
· 使用定理 `Turing.PartrecToTM2.contSupp_comp`：contSupp_comp (f k) : contSupp (Cont'
.comp f k) = codeSupp f k
· 使用定理 `Turing.PartrecToTM2.codeSupp_self`：codeSupp_self (c k) : trStmts₁ (trNor
mal c k) subseteq codeSupp c k
· 使用定理 `Finset.mem_union_left`：mem_union_left (t : Finset α) (h : a in s) : a in
 s union t
· 使用定理 `Finset.mem_union_right`：mem_union_right (s : Finset α) (h : a in t) : a 
in s union t
· 使用定理 `Turing.PartrecToTM2.contSupp_fix`：contSupp_fix (f k) : contSupp (Cont'.f
ix f k) = codeSupp f (Cont'.fix f k)
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
-/
theorem ret_supports {S k} (H₁ : contSupp k ⊆ S) : TM2.SupportsStmt S (tr (Λ'.ret k)) := by
  have W := fun {q} => trStmts₁_self q
  cases k with
  | halt => trivial
  | cons₁ => rw [contSupp_cons₁, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | cons₂ => rw [contSupp_cons₂, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | comp => rw [contSupp_comp] at H₁; exact fun _ => H₁ (codeSupp_self _ _ W)
  | fix =>
    rw [contSupp_fix] at H₁
    have L := @Finset.mem_union_left; have R := @Finset.mem_union_right
    intro s; dsimp only; cases natEnd (s.getD default)
    · refine H₁ (R _ <| L _ <| R _ <| R _ <| L _ W)
    · exact H₁ (R _ <| L _ <| R _ <| R _ <| R _ <| Finset.mem_singleton_self _)

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
-- simp acts on multiple goals at the same time
/-
**Turing.PartrecToTM2.trStmts** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trStmts₁_supports {S q} (H₁ : (q : Λ').Supports S) (HS₁ : trStmts₁ q ⊆ S) :
    Supports (trStmts₁ q) S := by
  have W := fun {q} => trStmts₁_self q
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
    simp [trStmts₁, -Finset.singleton_subset_iff] at HS₁ ⊢
  any_goals
    obtain ⟨h₁, h₂⟩ := Finset.insert_subset_iff.1 HS₁
    first | have h₃ := h₂ W | try simp [Finset.subset_iff] at h₂
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₁⟩, q_ih H₁ h₂⟩ -- move
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₁⟩, q_ih H₁ h₂⟩ -- clear
  · exact supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₃⟩, q_ih H₁ h₂⟩ -- copy
  · exact supports_insert.2 ⟨⟨fun _ => h₃, fun _ => h₃⟩, q_ih H₁ h₂⟩ -- push
  · refine supports_insert.2 ⟨fun _ => h₂ _ W, ?_⟩ -- read
    exact supports_biUnion.2 fun _ => q_ih _ (H₁ _) fun _ h => h₂ _ h
  · refine supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₂.1, fun _ => h₂.1⟩, ?_⟩ -- succ
    exact supports_insert.2 ⟨⟨fun _ => h₂.2 _ W, fun _ => h₂.1⟩, q_ih H₁ h₂.2⟩
  · refine -- pred
      supports_insert.2 ⟨⟨fun _ => h₁, fun _ => h₂.2 _ (Or.inl W),
                          fun _ => h₂.1, fun _ => h₂.1⟩, ?_⟩
    refine supports_insert.2 ⟨⟨fun _ => h₂.2 _ (Or.inr W), fun _ => h₂.1⟩, ?_⟩
    refine supports_union.2 ⟨?_, ?_⟩
    · exact q₁_ih H₁.1 fun _ h => h₂.2 _ (Or.inl h)
    · exact q₂_ih H₁.2 fun _ h => h₂.2 _ (Or.inr h)
  · exact supports_singleton.2 (ret_supports H₁)  -- ret
/-
**Turing.PartrecToTM2.trStmts** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trStmts₁_supports' {S q K} (H₁ : (q : Λ').Supports S) (H₂ : trStmts₁ q ∪ K ⊆ S)
    (H₃ : K ⊆ S → Supports K S) : Supports (trStmts₁ q ∪ K) S := by
  simp only [Finset.union_subset_iff] at H₂
  exact supports_union.2 ⟨trStmts₁_supports H₁ H₂.1, H₃ H₂.2⟩

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/-
**Turing.PartrecToTM2.trNormal_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partre
cToTM2`。
形式化陈述：trNormal_supports {S c k} (Hk : codeSupp c k subseteq S) : (trNormal c k).
Supports S
参数：Hk : codeSupp c k subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.ToPartrec.Code.zero'`：zero'_eval : zero'.eval = fun v => pure (0 
:: v)
· 使用定理 `Turing.PartrecToTM2.Λ'.Supports.eq_2`：∀ (S : Finset Turing.PartrecToTM2.
Λ') (k : Turing.PartrecToTM2.K')   (s : Option Turing.PartrecToTM2.Γ' → Option T
uring.PartrecToTM2.Γ') (q …
· 使用定理 `Finset.union_subset_right`：union_subset_right {s t u : Finset α} (h : s 
union t subseteq u) : t subseteq u
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `Turing.PartrecToTM2.Λ'.Supports.eq_1`：∀ (S : Finset Turing.PartrecToTM2.
Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k₁ k₂ : Turing.PartrecToTM2.K')   (q : 
Turing.PartrecToTM2.Λ'),  …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Turing.PartrecToTM2.Λ'.Supports.eq_4`：∀ (S : Finset Turing.PartrecToTM2.
Λ') (p : Turing.PartrecToTM2.Γ' → Bool) (k : Turing.PartrecToTM2.K')   (q : Turi
ng.PartrecToTM2.Λ'),   Tur…
· 使用定理 `Turing.PartrecToTM2.codeSupp_cons`：codeSupp_cons (f fs k) : codeSupp (Co
de.cons f fs) k = trStmts₁ (trNormal (Code.cons f fs) k) union codeSupp f (Cont'
.cons₁ fs k)
· 使用定理 `Turing.PartrecToTM2.codeSupp_comp`：codeSupp_comp (f g k) : codeSupp (Cod
e.comp f g) k = trStmts₁ (trNormal (Code.comp f g) k) union codeSupp g (Cont'.co
mp f k)
· 使用定理 `Turing.PartrecToTM2.Λ'.Supports.eq_7`：∀ (S : Finset Turing.PartrecToTM2.
Λ') (q₁ q₂ : Turing.PartrecToTM2.Λ'),   Turing.PartrecToTM2.Λ'.Supports S (q₁.pr
ed q₂) =     (Turing.Partr…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Turing.PartrecToTM2.codeSupp_case`：codeSupp_case (f g k) : codeSupp (Cod
e.case f g) k = trStmts₁ (trNormal (Code.case f g) k) union (codeSupp f k union 
codeSupp g k)
· 使用定理 `Turing.PartrecToTM2.codeSupp_fix`：codeSupp_fix (f k) : codeSupp (Code.fi
x f) k = trStmts₁ (trNormal (Code.fix f) k) union codeSupp f (Cont'.fix f k)
-/
theorem trNormal_supports {S c k} (Hk : codeSupp c k ⊆ S) : (trNormal c k).Supports S := by
  induction c generalizing k with simp [Λ'.Supports, head]
  | zero' => exact Finset.union_subset_right Hk
  | succ => intro; split_ifs <;> exact Finset.union_subset_right Hk
  | tail => exact Finset.union_subset_right Hk
  | cons f fs IHf _ =>
    apply IHf
    rw [codeSupp_cons] at Hk
    exact Finset.union_subset_right Hk
  | comp f g _ IHg => apply IHg; rw [codeSupp_comp] at Hk; exact Finset.union_subset_right Hk
  | case f g IHf IHg =>
    simp only [codeSupp_case, Finset.union_subset_iff] at Hk
    exact ⟨IHf Hk.2.1, IHg Hk.2.2⟩
  | fix f IHf => apply IHf; rw [codeSupp_fix] at Hk; exact Finset.union_subset_right Hk
/-
**Turing.PartrecToTM2.codeSupp'_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partr
ecToTM2`。
形式化陈述：∀ {S : Finset Turing.PartrecToTM2.Λ'} {c : Turing.ToPartrec.Code} {k : Tur
ing.PartrecToTM2.Cont'},   Turing.PartrecToTM2.codeSupp c k ⊆ S → Turing.Partrec
ToTM2.Supports (Turing.PartrecToTM2.codeSupp' c k) S
参数：Turing.PartrecToTM2.codeSupp' c k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `Turing.ToPartrec.Code.zero'`：zero'_eval : zero'.eval = fun v => pure (0 
:: v)
· 使用定理 `Turing.PartrecToTM2.trStmts₁_supports`：trStmts₁_supports {S q} (H₁ : (q 
: Λ').Supports S) (HS₁ : trStmts₁ q subseteq S) : Supports (trStmts₁ q) S
· 使用定理 `Turing.PartrecToTM2.trNormal_supports`：trNormal_supports {S c k} (Hk : c
odeSupp c k subseteq S) : (trNormal c k).Supports S
· 使用定理 `Finset.Subset.trans`：∀ {α : Type u_1} {s₁ s₂ s₃ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₃ → s₁ ⊆ s₃
· 使用定理 `Turing.PartrecToTM2.codeSupp_self`：codeSupp_self (c k) : trStmts₁ (trNor
mal c k) subseteq codeSupp c k
· 使用定理 `Turing.PartrecToTM2.trStmts₁_supports'`：trStmts₁_supports' {S q K} (H₁ :
 (q : Λ').Supports S) (H₂ : trStmts₁ q union K subseteq S) (H₃ : K subseteq S ->
 Supports K S) : Supports (t…
· 使用定理 `Finset.union_subset_left`：union_subset_left (h : s union t subseteq u) :
 s subseteq u
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Turing.PartrecToTM2.supports_union`：supports_union {K₁ K₂ S} : Supports 
(K₁ union K₂) S ↔ Supports K₁ S ∧ Supports K₂ S
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.PartrecToTM2.codeSupp_cons`：codeSupp_cons (f fs k) : codeSupp (Co
de.cons f fs) k = trStmts₁ (trNormal (Code.cons f fs) k) union codeSupp f (Cont'
.cons₁ fs k)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.union_subset_right`：union_subset_right {s t u : Finset α} (h : s 
union t subseteq u) : t subseteq u
· 使用定理 `Turing.PartrecToTM2.contSupp_cons₁`：contSupp_cons₁ (fs k) : contSupp (Co
nt'.cons₁ fs k) = trStmts₁ (move₂ (fun _ => false) main aux <| move₂ (fun s => s
 = Γ'.consₗ) stack main …
· 使用定理 `Turing.PartrecToTM2.codeSupp.eq_1`：∀ (c : Turing.ToPartrec.Code) (k : Tu
ring.PartrecToTM2.Cont'),   Turing.PartrecToTM2.codeSupp c k = Turing.PartrecToT
M2.codeSupp' c k ∪ Turi…
· 使用定理 `Turing.PartrecToTM2.head_supports`：head_supports {S k q} (H : (q : Λ').S
upports S) : (head k q).Supports S
· 使用定理 `Turing.PartrecToTM2.codeSupp_comp`：codeSupp_comp (f g k) : codeSupp (Cod
e.comp f g) k = trStmts₁ (trNormal (Code.comp f g) k) union codeSupp g (Cont'.co
mp f k)
· 使用定理 `Turing.PartrecToTM2.codeSupp_case`：codeSupp_case (f g k) : codeSupp (Cod
e.case f g) k = trStmts₁ (trNormal (Code.case f g) k) union (codeSupp f k union 
codeSupp g k)
· 使用定理 `Turing.PartrecToTM2.codeSupp_fix`：codeSupp_fix (f k) : codeSupp (Code.fi
x f) k = trStmts₁ (trNormal (Code.fix f) k) union codeSupp f (Cont'.fix f k)
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Turing.PartrecToTM2.supports_singleton`：supports_singleton {S q} : Suppo
rts {q} S ↔ TM2.SupportsStmt S (tr q)
· 使用定理 `Turing.PartrecToTM2.ret_supports`：ret_supports {S k} (H₁ : contSupp k su
bseteq S) : TM2.SupportsStmt S (tr (Λ'.ret k))
-/
theorem codeSupp'_supports {S c k} (H : codeSupp c k ⊆ S) : Supports (codeSupp' c k) S := by
  induction c generalizing k with
  | cons f fs IHf IHfs =>
    have H' := H; simp only [codeSupp_cons, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHf H'.2, ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun h => ?_
    · simp only [codeSupp, Finset.union_subset_iff, contSupp] at h H ⊢
      exact ⟨h.2.2.1, h.2.2.2, H.2⟩
    refine supports_union.2 ⟨IHfs ?_, ?_⟩
    · rw [codeSupp, contSupp_cons₁] at H'
      exact Finset.union_subset_right (Finset.union_subset_right H'.2)
    exact
      trStmts₁_supports (head_supports <| Finset.union_subset_right H)
        (Finset.union_subset_right h)
  | comp f g IHf IHg =>
    have H' := H; rw [codeSupp_comp] at H'; have H' := Finset.union_subset_right H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHg H', ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun _ => ?_
    · simp only [codeSupp', codeSupp, Finset.union_subset_iff] at h H ⊢
      exact ⟨h.2.2, H.2⟩
    exact IHf (Finset.union_subset_right H')
  | case f g IHf IHg =>
    have H' := H; simp only [codeSupp_case, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun _ => ?_
    exact supports_union.2 ⟨IHf H'.2.1, IHg H'.2.2⟩
  | fix f IHf =>
    have H' := H; simp only [codeSupp_fix, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHf H'.2, ?_⟩
    refine trStmts₁_supports' (trNormal_supports ?_) (Finset.union_subset_right h) fun _ => ?_
    · simp only [codeSupp', codeSupp, Finset.union_subset_iff, contSupp, trStmts₁,
        Finset.insert_subset_iff] at h H ⊢
      exact ⟨h.1, ⟨H.1.1, h⟩, H.2⟩
    exact supports_singleton.2 (ret_supports <| Finset.union_subset_right H)
  | _ => exact trStmts₁_supports (trNormal_supports H) (Finset.Subset.trans (codeSupp_self _ _) H)
/-
**Turing.PartrecToTM2.contSupp_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partre
cToTM2`。
形式化陈述：contSupp_supports {S k} (H : contSupp k subseteq S) : Supports (contSupp k
) S
参数：H : contSupp k subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.union_subset_right`：union_subset_right {s t u : Finset α} (h : s 
union t subseteq u) : t subseteq u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Turing.PartrecToTM2.contSupp_cons₁`：contSupp_cons₁ (fs k) : contSupp (Co
nt'.cons₁ fs k) = trStmts₁ (move₂ (fun _ => false) main aux <| move₂ (fun s => s
 = Γ'.consₗ) stack main …
· 使用定理 `Turing.PartrecToTM2.trStmts₁_supports'`：trStmts₁_supports' {S q K} (H₁ :
 (q : Λ').Supports S) (H₂ : trStmts₁ q union K subseteq S) (H₃ : K subseteq S ->
 Supports K S) : Supports (t…
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `Turing.PartrecToTM2.trNormal_supports`：trNormal_supports {S c k} (Hk : c
odeSupp c k subseteq S) : (trNormal c k).Supports S
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Turing.PartrecToTM2.supports_union`：supports_union {K₁ K₂ S} : Supports 
(K₁ union K₂) S ↔ Supports K₁ S ∧ Supports K₂ S
· 使用定理 `Turing.PartrecToTM2.codeSupp'_supports`：∀ {S : Finset Turing.PartrecToTM
2.Λ'} {c : Turing.ToPartrec.Code} {k : Turing.PartrecToTM2.Cont'},   Turing.Part
recToTM2.codeSupp c k ⊆ S → …
· 使用定理 `Turing.PartrecToTM2.head_supports`：head_supports {S k q} (H : (q : Λ').S
upports S) : (head k q).Supports S
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Turing.PartrecToTM2.contSupp_cons₂`：contSupp_cons₂ (k) : contSupp (Cont'
.cons₂ k) = trStmts₁ (head stack <| Λ'.ret k) union contSupp k
· 使用定理 `Turing.PartrecToTM2.contSupp_comp`：contSupp_comp (f k) : contSupp (Cont'
.comp f k) = codeSupp f k
· 使用定理 `Turing.PartrecToTM2.contSupp.eq_4`：∀ (f : Turing.ToPartrec.Code) (k : Tu
ring.PartrecToTM2.Cont'),   Turing.PartrecToTM2.contSupp (Turing.PartrecToTM2.Co
nt'.fix f k) =     Turi…
-/
theorem contSupp_supports {S k} (H : contSupp k ⊆ S) : Supports (contSupp k) S := by
  induction k with
  | halt => simp [contSupp_halt, Supports]
  | cons₁ f k IH =>
    have H₁ := H; rw [contSupp_cons₁] at H₁; have H₂ := Finset.union_subset_right H₁
    refine trStmts₁_supports' (trNormal_supports H₂) H₁ fun h => ?_
    refine supports_union.2 ⟨codeSupp'_supports H₂, ?_⟩
    simp only [codeSupp, contSupp_cons₂, Finset.union_subset_iff] at H₂
    exact trStmts₁_supports' (head_supports H₂.2.2) (Finset.union_subset_right h) IH
  | cons₂ k IH =>
    have H' := H; rw [contSupp_cons₂] at H'
    exact trStmts₁_supports' (head_supports <| Finset.union_subset_right H') H' IH
  | comp f k IH =>
    have H' := H; rw [contSupp_comp] at H'; have H₂ := Finset.union_subset_right H'
    exact supports_union.2 ⟨codeSupp'_supports H', IH H₂⟩
  | fix f k IH =>
    rw [contSupp] at H
    exact supports_union.2 ⟨codeSupp'_supports H, IH (Finset.union_subset_right H)⟩
/-
**Turing.PartrecToTM2.codeSupp_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.Partre
cToTM2`。
形式化陈述：codeSupp_supports {S c k} (H : codeSupp c k subseteq S) : Supports (codeSu
pp c k) S
参数：H : codeSupp c k subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Turing.PartrecToTM2.codeSupp'`：codeSupp'_self (c k) : trStmts₁ (trNormal
 c k) subseteq codeSupp' c k
· 使用定理 `Turing.PartrecToTM2.supports_union`：supports_union {K₁ K₂ S} : Supports 
(K₁ union K₂) S ↔ Supports K₁ S ∧ Supports K₂ S
· 使用定理 `Turing.PartrecToTM2.codeSupp'_supports`：∀ {S : Finset Turing.PartrecToTM
2.Λ'} {c : Turing.ToPartrec.Code} {k : Turing.PartrecToTM2.Cont'},   Turing.Part
recToTM2.codeSupp c k ⊆ S → …
· 使用定理 `Turing.PartrecToTM2.contSupp_supports`：contSupp_supports {S k} (H : cont
Supp k subseteq S) : Supports (contSupp k) S
· 使用定理 `Finset.union_subset_right`：union_subset_right {s t u : Finset α} (h : s 
union t subseteq u) : t subseteq u
-/
theorem codeSupp_supports {S c k} (H : codeSupp c k ⊆ S) : Supports (codeSupp c k) S :=
  supports_union.2 ⟨codeSupp'_supports H, contSupp_supports (Finset.union_subset_right H)⟩

/-- The set `codeSupp c k` is a finite set that witnesses the effective finiteness of the `tr`
Turing machine. Starting from the initial state `trNormal c k`, forward simulation uses only
states in `codeSupp c k`, so this is a finite state machine. Even though the underlying type of
state labels `Λ'` is infinite, for a given partial recursive function `c` and continuation `k`,
only finitely many states are accessed, corresponding roughly to subterms of `c`. -/
/-
**Turing.PartrecToTM2.tr_supports** 是 Mathlib 中的一个定理，位于命名空间 `Turing.PartrecToTM2
`。
形式化陈述：tr_supports (c k) : @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (codeSupp c k)
参数：c k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Turing.PartrecToTM2.K'`：K'.elim_main (a b c d) : K'.elim a b c d K'.main
 = a
· 使用定理 `Turing.PartrecToTM2.codeSupp_self`：codeSupp_self (c k) : trStmts₁ (trNor
mal c k) subseteq codeSupp c k
· 使用定理 `Turing.PartrecToTM2.trStmts₁_self`：trStmts₁_self (q) : q in trStmts₁ q
· 使用定理 `Turing.PartrecToTM2.codeSupp_supports`：codeSupp_supports {S c k} (H : co
deSupp c k subseteq S) : Supports (codeSupp c k) S
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s

--- 原说明 ---
The set `codeSupp c k` is a finite set that witnesses the effective finiteness o
f the `tr`
Turing machine. Starting from the initial state `trNormal c k`, forward simulati
on uses only
states in `codeSupp c k`, so this is a finite state machine. Even though the und
erlying type of
state labels `Λ'` is infinite, for a given partial recursive function `c` and co
ntinuation `k`,
only finitely many states are accessed, corresponding roughly to subterms of `c`
.
-/
theorem tr_supports (c k) : @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (codeSupp c k) :=
  ⟨codeSupp_self _ _ (trStmts₁_self _), fun _ => codeSupp_supports (Finset.Subset.refl _) _⟩

end

end PartrecToTM2

end Turing

