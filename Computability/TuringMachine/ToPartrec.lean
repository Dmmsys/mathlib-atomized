/-
Copyright (c) 2020 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Computability.Halting
public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.Num.Lemmas
public import Mathlib.Tactic.DeriveFintype -- shake: keep (deriving handlers not tracked yet)
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
    inductive Γ' | consₗ | cons | bit0 | bit1
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
/--
Inductive type `Γ'` / 归纳类型 `Γ'`

English:
inductive Γ'
  constructors (4):
    - consₗ: 
    - cons: 
    - bit0: 
    - bit1: 

中文:
归纳类型 Γ'
  构造子 (4 个):
    - consₗ: 
    - cons: 
    - bit0: 
    - bit1: 
-/
inductive Γ'
  | consₗ
  | cons
  | bit0
  | bit1
  deriving DecidableEq, Inhabited, Fintype

-- A proof below relies on the value of that `deriving Inhabited` picks here.
/--
theorem `default_Γ'` / 定理 `default_Γ'`

English:
theorem default_Γ'
  statement: (default : Γ') = .consₗ
  proof: rfl

中文:
定理 default_Γ'
  结论: (default : Γ') = .consₗ
  证明: rfl
-/
@[simp] theorem default_Γ' : (default : Γ') = .consₗ := rfl

/--
Inductive type `K'` / 归纳类型 `K'`

English:
inductive K'
  constructors (4):
    - main: 
    - rev: 
    - aux: 
    - stack: 

中文:
归纳类型 K'
  构造子 (4 个):
    - main: 
    - rev: 
    - aux: 
    - stack: 
-/
inductive K'
  | main
  | rev
  | aux
  | stack
  deriving DecidableEq, Inhabited

open K'

/--
Inductive type `Cont'` / 归纳类型 `Cont'`

English:
inductive Cont'
  constructors (5):
    - halt: 
    - cons₁: Code -> Cont' -> Cont'
    - cons₂: Cont' -> Cont'
    - comp: Code -> Cont' -> Cont'
    - fix: Code -> Cont' -> Cont'

中文:
归纳类型 余nt'
  构造子 (5 个):
    - halt: 
    - cons₁: 余de -> 余nt' -> 余nt'
    - cons₂: 余nt' -> 余nt'
    - comp: 余de -> 余nt' -> 余nt'
    - fix: 余de -> 余nt' -> 余nt'
-/
inductive Cont'
  | halt
  | cons₁ : Code -> Cont' -> Cont'
  | cons₂ : Cont' -> Cont'
  | comp : Code -> Cont' -> Cont'
  | fix : Code -> Cont' -> Cont'
  deriving DecidableEq, Inhabited

/--
Inductive type `Λ'` / 归纳类型 `Λ'`

English:
inductive Λ'
  constructors (8):
    - move: (p : Γ' -> Bool) (k₁ k₂ : K') (q : Λ')
    - clear: (p : Γ' -> Bool) (k : K') (q : Λ')
    - copy: (q : Λ')
    - push: (k : K') (s : Option Γ' -> Option Γ') (q : Λ')
    - read: (f : Option Γ' -> Λ')
    - succ: (q : Λ')
    - pred: (q₁ q₂ : Λ')
    - ret: (k : Cont')

中文:
归纳类型 Λ'
  构造子 (8 个):
    - move: (p : Γ' -> 布尔值) (k₁ k₂ : K') (q : Λ')
    - clear: (p : Γ' -> 布尔值) (k : K') (q : Λ')
    - copy: (q : Λ')
    - push: (k : K') (s : 选项类型 Γ' -> 选项类型 Γ') (q : Λ')
    - read: (f : 选项类型 Γ' -> Λ')
    - succ: (q : Λ')
    - pred: (q₁ q₂ : Λ')
    - ret: (k : 余nt')
-/
inductive Λ'
  | move (p : Γ' -> Bool) (k₁ k₂ : K') (q : Λ')
  | clear (p : Γ' -> Bool) (k : K') (q : Λ')
  | copy (q : Λ')
  | push (k : K') (s : Option Γ' -> Option Γ') (q : Λ')
  | read (f : Option Γ' -> Λ')
  | succ (q : Λ')
  | pred (q₁ q₂ : Λ')
  | ret (k : Cont')

compile_inductive% Code
compile_inductive% Cont'
compile_inductive% K'
compile_inductive% Λ'

/--
Instance `Λ'.instInhabited` / 实例 `Λ'.instInhabited`

English:
instance Λ'.instInhabited
  signature: : Inhabited Λ'
  body: ⟨Λ'.ret Cont'.halt⟩

中文:
实例 Λ'.instInhabited
  签名: : 可居 Λ'
  定义体: ⟨Λ'.ret Cont'.halt⟩
-/
instance Λ'.instInhabited : Inhabited Λ' :=
  ⟨Λ'.ret Cont'.halt⟩

/--
Instance `Λ'.instDecidableEq` / 实例 `Λ'.instDecidableEq`

English:
instance Λ'.instDecidableEq
  signature: : DecidableEq Λ'
  body: fun a b => by
  induction a generalizing b <;> cases b
  case move.move p k₁ k₂ q _ p' k₁' k₂' q' =>
    exact decidable_of_iff' (p = p' ∧ k₁ = k₁' ∧ k₂ = k₂' ∧ q = q') (by simp)
  case clear.clear p k q _ p' k' q' => exact decidable_of_iff' (p = p' ∧ k = k' ∧ q = q') (by simp)
  case copy.copy q _ 

中文:
实例 Λ'.instDecidableEq
  签名: : DecidableEq Λ'
  定义体: fun a b => by
  induction a generalizing b <;> cases b
  case move.move p k₁ k₂ q _ p' k₁' k₂' q' =>
    exact decidable_of_iff' (p = p' ∧ k₁ = k₁' ∧ k₂ = k₂' ∧ q = q') (by simp)
  case clear.clear p k q _ p' k' q' => exact decidable_of_iff' (p = p' ∧ k = k' ∧ q = q') (by simp)
  case copy.copy q _ 
-/
instance Λ'.instDecidableEq : DecidableEq Λ' := fun a b => by
  induction a generalizing b <;> cases b
  case move.move p k₁ k₂ q _ p' k₁' k₂' q' =>
    exact decidable_of_iff' (p = p' ∧ k₁ = k₁' ∧ k₂ = k₂' ∧ q = q') (by simp)
  case clear.clear p k q _ p' k' q' => exact decidable_of_iff' (p = p' ∧ k = k' ∧ q = q') (by simp)
  case copy.copy q _ q' => exact decidable_of_iff' (q = q') (by simp)
  case push.push k s q _ k' s' q' => exact decidable_of_iff' (k = k' ∧ s = s' ∧ q = q') (by simp)
  case read.read f _ f' => exact decidable_of_iff' (forall a, f a = f' a) (by simp [funext_iff])
  case succ.succ q _ q' => exact decidable_of_iff' (q = q') (by simp)
  case pred.pred q₁ q₂ _ _ q₁' q₂' => exact decidable_of_iff' (q₁ = q₁' ∧ q₂ = q₂') (by simp)
  case ret.ret k k' => exact decidable_of_iff' (k = k') (by simp)
  all_goals exact .isFalse (by rintro ⟨⟨⟩⟩)

/--
Definition of `Stmt'` / `Stmt'` 的定义

English:
definition Stmt'
  body: TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

中文:
定义 Stmt'
  定义体: TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

Depends on / 依赖: Inhabited, TM2.Stmt, deriving
-/
def Stmt' :=
  TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

/--
Definition of `Cfg'` / `Cfg'` 的定义

English:
definition Cfg'
  body: TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

中文:
定义 Cfg'
  定义体: TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

Depends on / 依赖: Inhabited, TM2.Cfg, deriving
-/
def Cfg' :=
  TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ') deriving Inhabited

open TM2.Stmt

/-- A predicate that detects the end of a natural number, either `Γ'.cons` or `Γ'.consₗ` (or
implicitly the end of the list), for use in predicate-taking functions like `move` and `clear`. -/
@[simp]
/--
Definition of `natEnd` / `natEnd` 的定义

English:
definition natEnd
  signature: : Γ' -> Bool

中文:
定义 natEnd
  签名: : Γ' -> 布尔值
-/
def natEnd : Γ' -> Bool
  | Γ'.consₗ => true
  | Γ'.cons => true
  | _ => false
attribute [nolint simpNF] natEnd.eq_3

/-- Pop a value from the stack and place the result in local store. -/
@[simp]
/--
Definition of `pop'` / `pop'` 的定义

English:
definition pop'
  signature: (k : K')
  body: pop k fun _ v => v

中文:
定义 pop'
  签名: (k : K')
  定义体: pop k fun _ v => v
-/
def pop' (k : K') : Stmt' -> Stmt' :=
  pop k fun _ v => v

/-- Peek a value from the stack and place the result in local store. -/
@[simp]
/--
Definition of `peek'` / `peek'` 的定义

English:
definition peek'
  signature: (k : K')
  body: peek k fun _ v => v

中文:
定义 peek'
  签名: (k : K')
  定义体: peek k fun _ v => v
-/
def peek' (k : K') : Stmt' -> Stmt' :=
  peek k fun _ v => v

/-- Push the value in the local store to the given stack. -/
@[simp]
/--
Definition of `push'` / `push'` 的定义

English:
definition push'
  signature: (k : K')
  body: push k fun x => x.getD default

中文:
定义 push'
  签名: (k : K')
  定义体: push k fun x => x.getD default

Depends on / 依赖: x.getD
-/
def push' (k : K') : Stmt' -> Stmt' :=
  push k fun x => x.getD default

/--
Definition of `unrev` / `unrev` 的定义

English:
definition unrev
  body: Λ'.move (fun _ => false) rev main

中文:
定义 unrev
  定义体: Λ'.move (fun _ => false) rev main
-/
def unrev :=
  Λ'.move (fun _ => false) rev main

/--
Definition of `moveExcl` / `moveExcl` 的定义

English:
definition moveExcl
  signature: (p k₁ k₂ q)
  body: Λ'.move p k₁ k₂ Λ'.push k₁ id q

中文:
定义 moveExcl
  签名: (p k₁ k₂ q)
  定义体: Λ'.move p k₁ k₂ Λ'.push k₁ id q
-/
def moveExcl (p k₁ k₂ q) :=
Λ'.move p k₁ k₂ Λ'.push k₁ id q

/--
Definition of `move₂` / `move₂` 的定义

English:
definition move₂
  signature: (p k₁ k₂ q)
  body: moveExcl p k₁ rev Λ'.move (fun _ => false) rev k₂ q

中文:
定义 move₂
  签名: (p k₁ k₂ q)
  定义体: moveExcl p k₁ rev Λ'.move (fun _ => false) rev k₂ q

Depends on / 依赖: moveExcl
-/
def move₂ (p k₁ k₂ q) :=
moveExcl p k₁ rev Λ'.move (fun _ => false) rev k₂ q

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (k : K') (q : Λ')
  body: Λ'.move natEnd k rev
(Λ'.push rev fun _ => some Γ'.cons)
      Λ'.read fun s =>
(if s = some Γ'.consₗ then id else Λ'.clear (fun x => x = Γ'.consₗ) k) unrev q

中文:
定义 head
  签名: (k : K') (q : Λ')
  定义体: Λ'.move natEnd k rev
(Λ'.push rev fun _ => some Γ'.cons)
      Λ'.read fun s =>
(if s = some Γ'.consₗ then id else Λ'.clear (fun x => x = Γ'.consₗ) k) unrev q

Depends on / 依赖: natEnd
-/
def head (k : K') (q : Λ') : Λ' :=
Λ'.move natEnd k rev
(Λ'.push rev fun _ => some Γ'.cons)
      Λ'.read fun s =>
(if s = some Γ'.consₗ then id else Λ'.clear (fun x => x = Γ'.consₗ) k) unrev q

/-- The program that evaluates code `c` with continuation `k`. This expects an initial state where
`trList v` is on `main`, `trContStack k` is on `stack`, and `aux` and `rev` are empty.
See the section documentation for details. -/
@[simp]
/--
Definition of `trNormal` / `trNormal` 的定义

English:
definition trNormal
  signature: : Code -> Cont' -> Λ'

中文:
定义 trNormal
  签名: : 余de -> 余nt' -> Λ'
-/
def trNormal : Code -> Cont' -> Λ'
| Code.zero', k => (Λ'.push main fun _ => some Γ'.cons) Λ'.ret k
| Code.succ, k => head main Λ'.succ Λ'.ret k
| Code.tail, k => Λ'.clear natEnd main Λ'.ret k
  | Code.cons f fs, k =>
(Λ'.push stack fun _ => some Γ'.consₗ)
Λ'.move (fun _ => false) main rev Λ'.copy trNormal f (Cont'.cons₁ fs k)
  | Code.comp f g, k => trNormal g (Cont'.comp f k)
  | Code.case f g, k => Λ'.pred (trNormal f k) (trNormal g k)
  | Code.fix f, k => trNormal f (Cont'.fix f k)

/--
Definition of `tr` / `tr` 的定义

English:
definition tr
  signature: : Λ' -> Stmt'

中文:
定义 tr
  签名: : Λ' -> Stmt'
-/
def tr : Λ' -> Stmt'
  | Λ'.move p k₁ k₂ q =>
pop' k₁
      branch (fun s => s.elim true p) (goto fun _ => q)
        (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)
  | Λ'.push k f q =>
    branch (fun s => (f s).isSome) ((push k fun s => (f s).getD default) <| goto fun _ => q)
      (goto fun _ => q)
  | Λ'.read q => goto q
  | Λ'.clear p k q =>
pop' k branch (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)
  | Λ'.copy q =>
pop' rev
      branch Option.isSome (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)
  | Λ'.succ q =>
pop' main
branch (fun s => s = some Γ'.bit1) ((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q)
        branch (fun s => s = some Γ'.cons)
          ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
          ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
  | Λ'.pred q₁ q₂ =>
pop' main
      branch (fun s => s = some Γ'.bit0)
((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂)
        branch (fun s => natEnd (s.getD default)) (goto fun _ => q₁)
          (peek' main <|
            branch (fun s => natEnd (s.getD default)) (goto fun _ => unrev q₂)
              ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))
  | Λ'.ret (Cont'.cons₁ fs k) =>
    goto fun _ =>
move₂ (fun _ => false) main aux
move₂ (fun s => s = Γ'.consₗ) stack main
move₂ (fun _ => false) aux stack trNormal fs (Cont'.cons₂ k)
| Λ'.ret (Cont'.cons₂ k) => goto fun _ => head stack Λ'.ret k
  | Λ'.ret (Cont'.comp f k) => goto fun _ => trNormal f k
  | Λ'.ret (Cont'.fix f k) =>
pop' main
      goto fun s =>
cond (natEnd (s.getD default)) (Λ'.ret k)
Λ'.clear natEnd main trNormal f (Cont'.fix f k)
| Λ'.ret Cont'.halt => (load fun _ => none) halt

@[simp]
/--
theorem `tr_move` / 定理 `tr_move`

English:
theorem tr_move
  given: (p k₁ k₂ q)
  statement: tr (Λ'.move p k₁ k₂ q) =
  proof: rfl

@[simp]

中文:
定理 tr_move
  条件: (p k₁ k₂ q)
  结论: tr (Λ'.move p k₁ k₂ q) =
  证明: rfl

@[simp]
-/
theorem tr_move (p k₁ k₂ q) : tr (Λ'.move p k₁ k₂ q) =
    pop' k₁ (branch (fun s => s.elim true p) (goto fun _ => q)
      (push' k₂ <| goto fun _ => Λ'.move p k₁ k₂ q)) := rfl

@[simp]
/--
theorem `tr_push` / 定理 `tr_push`

English:
theorem tr_push
  given: (k f q)
  statement: tr (Λ'.push k f q) = branch (fun s => (f s).isSome)
  proof: rfl

@[simp]

中文:
定理 tr_push
  条件: (k f q)
  结论: tr (Λ'.push k f q) = branch (fun s => (f s).isSome)
  证明: rfl

@[simp]
-/
theorem tr_push (k f q) : tr (Λ'.push k f q) = branch (fun s => (f s).isSome)
    ((push k fun s => (f s).getD default) <| goto fun _ => q) (goto fun _ => q) := rfl

@[simp]
/--
theorem `tr_read` / 定理 `tr_read`

English:
theorem tr_read
  given: (q)
  statement: tr (Λ'.read q) = goto q
  proof: rfl

@[simp]

中文:
定理 tr_read
  条件: (q)
  结论: tr (Λ'.read q) = goto q
  证明: rfl

@[simp]
-/
theorem tr_read (q) : tr (Λ'.read q) = goto q := rfl

@[simp]
/--
theorem `tr_clear` / 定理 `tr_clear`

English:
theorem tr_clear
  given: (p k q)
  statement: tr (Λ'.clear p k q) = pop' k (branch
  proof: rfl

@[simp]

中文:
定理 tr_clear
  条件: (p k q)
  结论: tr (Λ'.clear p k q) = pop' k (branch
  证明: rfl

@[simp]
-/
theorem tr_clear (p k q) : tr (Λ'.clear p k q) = pop' k (branch
    (fun s => s.elim true p) (goto fun _ => q) (goto fun _ => Λ'.clear p k q)) := rfl

@[simp]
/--
theorem `tr_copy` / 定理 `tr_copy`

English:
theorem tr_copy
  given: (q)
  statement: tr (Λ'.copy q) = pop' rev (branch Option.isSome
  proof: rfl

@[simp]

中文:
定理 tr_copy
  条件: (q)
  结论: tr (Λ'.copy q) = pop' rev (branch 选项类型.isSome
  证明: rfl

@[simp]
-/
theorem tr_copy (q) : tr (Λ'.copy q) = pop' rev (branch Option.isSome
    (push' main <| push' stack <| goto fun _ => Λ'.copy q) (goto fun _ => q)) := rfl

@[simp]
/--
theorem `tr_succ` / 定理 `tr_succ`

English:
theorem tr_succ
  given: (q)
  statement: tr (Λ'.succ q) = pop' main (branch (fun s => s = some Γ'.bit1)
  proof: rfl

@[simp]

中文:
定理 tr_succ
  条件: (q)
  结论: tr (Λ'.succ q) = pop' main (branch (fun s => s = some Γ'.bit1)
  证明: rfl

@[simp]
-/
theorem tr_succ (q) : tr (Λ'.succ q) = pop' main (branch (fun s => s = some Γ'.bit1)
((push rev fun _ => Γ'.bit0) <| goto fun _ => Λ'.succ q)
      branch (fun s => s = some Γ'.cons)
        ((push main fun _ => Γ'.cons) <| (push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)
        ((push main fun _ => Γ'.bit1) <| goto fun _ => unrev q)) := rfl

@[simp]
/--
theorem `tr_pred` / 定理 `tr_pred`

English:
theorem tr_pred
  given: (q₁ q₂)
  statement: tr (Λ'.pred q₁ q₂) = pop' main (branch (fun s => s = some Γ'.bit0)
  proof: rfl

@[simp]

中文:
定理 tr_pred
  条件: (q₁ q₂)
  结论: tr (Λ'.pred q₁ q₂) = pop' main (branch (fun s => s = some Γ'.bit0)
  证明: rfl

@[simp]
-/
theorem tr_pred (q₁ q₂) : tr (Λ'.pred q₁ q₂) = pop' main (branch (fun s => s = some Γ'.bit0)
((push rev fun _ => Γ'.bit1) <| goto fun _ => Λ'.pred q₁ q₂)
    branch (fun s => natEnd (s.getD default)) (goto fun _ => q₁)
      (peek' main <|
        branch (fun s => natEnd (s.getD default)) (goto fun _ => unrev q₂)
          ((push rev fun _ => Γ'.bit0) <| goto fun _ => unrev q₂))) := rfl

@[simp]
/--
theorem `tr_ret_cons₁` / 定理 `tr_ret_cons₁`

English:
theorem tr_ret_cons₁
  given: (fs k)
  statement: tr (Λ'.ret (Cont'.cons₁ fs k)) = goto fun _ =>
  proof: rfl

@[simp]

中文:
定理 tr_ret_cons₁
  条件: (fs k)
  结论: tr (Λ'.ret (余nt'.cons₁ fs k)) = goto fun _ =>
  证明: rfl

@[simp]
-/
theorem tr_ret_cons₁ (fs k) : tr (Λ'.ret (Cont'.cons₁ fs k)) = goto fun _ =>
move₂ (fun _ => false) main aux
move₂ (fun s => s = Γ'.consₗ) stack main
move₂ (fun _ => false) aux stack trNormal fs (Cont'.cons₂ k) := rfl

@[simp]
/--
theorem `tr_ret_cons₂` / 定理 `tr_ret_cons₂`

English:
theorem tr_ret_cons₂
  given: (k)
  statement: tr (Λ'.ret (Cont'.cons₂ k)) =
  proof: rfl

@[simp]

中文:
定理 tr_ret_cons₂
  条件: (k)
  结论: tr (Λ'.ret (余nt'.cons₂ k)) =
  证明: rfl

@[simp]
-/
theorem tr_ret_cons₂ (k) : tr (Λ'.ret (Cont'.cons₂ k)) =
goto fun _ => head stack Λ'.ret k := rfl

@[simp]
/--
theorem `tr_ret_comp` / 定理 `tr_ret_comp`

English:
theorem tr_ret_comp
  given: (f k)
  statement: tr (Λ'.ret (Cont'.comp f k)) = goto fun _ => trNormal f k
  proof: rfl

@[simp]

中文:
定理 tr_ret_comp
  条件: (f k)
  结论: tr (Λ'.ret (余nt'.comp f k)) = goto fun _ => trNormal f k
  证明: rfl

@[simp]
-/
theorem tr_ret_comp (f k) : tr (Λ'.ret (Cont'.comp f k)) = goto fun _ => trNormal f k := rfl

@[simp]
/--
theorem `tr_ret_fix` / 定理 `tr_ret_fix`

English:
theorem tr_ret_fix
  given: (f k)
  statement: tr (Λ'.ret (Cont'.fix f k)) = pop' main (goto fun s =>
  proof: rfl

@[simp]

中文:
定理 tr_ret_fix
  条件: (f k)
  结论: tr (Λ'.ret (余nt'.fix f k)) = pop' main (goto fun s =>
  证明: rfl

@[simp]
-/
theorem tr_ret_fix (f k) : tr (Λ'.ret (Cont'.fix f k)) = pop' main (goto fun s =>
cond (natEnd (s.getD default)) (Λ'.ret k)
Λ'.clear natEnd main trNormal f (Cont'.fix f k)) := rfl

@[simp]
/--
theorem `tr_ret_halt` / 定理 `tr_ret_halt`

English:
theorem tr_ret_halt
  statement: tr (Λ'.ret Cont'.halt) = (load fun _ => none) halt
  proof: rfl

中文:
定理 tr_ret_halt
  结论: tr (Λ'.ret 余nt'.halt) = (load fun _ => none) halt
  证明: rfl
-/
theorem tr_ret_halt : tr (Λ'.ret Cont'.halt) = (load fun _ => none) halt := rfl

/--
Definition of `trCont` / `trCont` 的定义

English:
definition trCont
  signature: : Cont -> Cont'

中文:
定义 trCont
  签名: : 余nt -> 余nt'
-/
def trCont : Cont -> Cont'
  | Cont.halt => Cont'.halt
  | Cont.cons₁ c _ k => Cont'.cons₁ c (trCont k)
  | Cont.cons₂ _ k => Cont'.cons₂ (trCont k)
  | Cont.comp c k => Cont'.comp c (trCont k)
  | Cont.fix c k => Cont'.fix c (trCont k)

/--
Definition of `trPosNum` / `trPosNum` 的定义

English:
definition trPosNum
  signature: : PosNum -> List Γ'

中文:
定义 trPosNum
  签名: : PosNum -> 列表 Γ'
-/
def trPosNum : PosNum -> List Γ'
  | PosNum.one => [Γ'.bit1]
  | PosNum.bit0 n => Γ'.bit0 :: trPosNum n
  | PosNum.bit1 n => Γ'.bit1 :: trPosNum n

/--
Definition of `trNum` / `trNum` 的定义

English:
definition trNum
  signature: : Num -> List Γ'

中文:
定义 trNum
  签名: : Num -> 列表 Γ'
-/
def trNum : Num -> List Γ'
  | Num.zero => []
  | Num.pos n => trPosNum n

/--
Definition of `trNat` / `trNat` 的定义

English:
definition trNat
  signature: (n : Nat)
  body: trNum n

@[simp]

中文:
定义 tr自然数
  签名: (n : 自然数)
  定义体: trNum n

@[simp]
-/
def trNat (n : Nat) : List Γ' :=
  trNum n

@[simp]
/--
theorem `trNat_zero` / 定理 `trNat_zero`

English:
theorem trNat_zero
  statement: trNat 0 = []
  proof: by rw [trNat, Nat.cast_zero]; rfl

中文:
定理 tr自然数_zero
  结论: tr自然数 0 = []
  证明: by rw [trNat, Nat.cast_zero]; rfl

Depends on / 依赖: Nat.cast_zero, cast_zero
-/
theorem trNat_zero : trNat 0 = [] := by rw [trNat, Nat.cast_zero]; rfl

/--
theorem `trNat_default` / 定理 `trNat_default`

English:
theorem trNat_default
  statement: trNat default = []
  proof: trNat_zero

中文:
定理 tr自然数_default
  结论: tr自然数 default = []
  证明: trNat_zero

Depends on / 依赖: trNat_zero
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
/--
Definition of `trList` / `trList` 的定义

English:
definition trList
  signature: : List Nat -> List Γ'

中文:
定义 trList
  签名: : 列表 自然数 -> 列表 Γ'
-/
def trList : List Nat -> List Γ'
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
/--
Definition of `trLList` / `trLList` 的定义

English:
definition trLList
  signature: : List (List Nat) -> List Γ'

中文:
定义 trLList
  签名: : 列表 (列表 自然数) -> 列表 Γ'
-/
def trLList : List (List Nat) -> List Γ'
  | [] => []
  | l::ls => trList l ++ Γ'.consₗ :: trLList ls

/-- The data part of a continuation is a list of lists, which is encoded on the `stack` stack
using `trLList`. -/
@[simp]
/--
Definition of `contStack` / `contStack` 的定义

English:
definition contStack
  signature: : Cont -> List (List Nat)

中文:
定义 contStack
  签名: : 余nt -> 列表 (列表 自然数)
-/
def contStack : Cont -> List (List Nat)
  | Cont.halt => []
  | Cont.cons₁ _ ns k => ns :: contStack k
  | Cont.cons₂ ns k => ns :: contStack k
  | Cont.comp _ k => contStack k
  | Cont.fix _ k => contStack k

/--
Definition of `trContStack` / `trContStack` 的定义

English:
definition trContStack
  signature: (k : Cont)
  body: trLList (contStack k)

中文:
定义 trContStack
  签名: (k : 余nt)
  定义体: trLList (contStack k)

Depends on / 依赖: contStack, trLList
-/
def trContStack (k : Cont) :=
  trLList (contStack k)

/--
Definition of `K'.elim` / `K'.elim` 的定义

English:
definition K'.elim
  signature: (a b c d : List Γ')

中文:
定义 K'.elim
  签名: (a b c d : 列表 Γ')
-/
def K'.elim (a b c d : List Γ') : K' -> List Γ'
  | K'.main => a
  | K'.rev => b
  | K'.aux => c
  | K'.stack => d

-- The equation lemma of `elim` simplifies to `match` structures.

/--
theorem `K'.elim_main` / 定理 `K'.elim_main`

English:
theorem K'.elim_main
  given: (a b c d)
  statement: K'.elim a b c d K'.main = a
  proof: rfl

中文:
定理 K'.elim_main
  条件: (a b c d)
  结论: K'.elim a b c d K'.main = a
  证明: rfl
-/
theorem K'.elim_main (a b c d) : K'.elim a b c d K'.main = a := rfl

/--
theorem `K'.elim_rev` / 定理 `K'.elim_rev`

English:
theorem K'.elim_rev
  given: (a b c d)
  statement: K'.elim a b c d K'.rev = b
  proof: rfl

中文:
定理 K'.elim_rev
  条件: (a b c d)
  结论: K'.elim a b c d K'.rev = b
  证明: rfl
-/
theorem K'.elim_rev (a b c d) : K'.elim a b c d K'.rev = b := rfl

/--
theorem `K'.elim_aux` / 定理 `K'.elim_aux`

English:
theorem K'.elim_aux
  given: (a b c d)
  statement: K'.elim a b c d K'.aux = c
  proof: rfl

中文:
定理 K'.elim_aux
  条件: (a b c d)
  结论: K'.elim a b c d K'.aux = c
  证明: rfl
-/
theorem K'.elim_aux (a b c d) : K'.elim a b c d K'.aux = c := rfl

/--
theorem `K'.elim_stack` / 定理 `K'.elim_stack`

English:
theorem K'.elim_stack
  given: (a b c d)
  statement: K'.elim a b c d K'.stack = d
  proof: rfl

中文:
定理 K'.elim_stack
  条件: (a b c d)
  结论: K'.elim a b c d K'.stack = d
  证明: rfl
-/
theorem K'.elim_stack (a b c d) : K'.elim a b c d K'.stack = d := rfl

attribute [simp] K'.elim

@[simp]
/--
theorem `K'.elim_update_main` / 定理 `K'.elim_update_main`

English:
theorem K'.elim_update_main
  given: {a b c d a'}
  statement: update (K'.elim a b c d) main a' = K'.elim a' b c d
  proof: by
  funext x; cases x <;> rfl

@[simp]

中文:
定理 K'.elim_update_main
  条件: {a b c d a'}
  结论: update (K'.elim a b c d) main a' = K'.elim a' b c d
  证明: by
  funext x; cases x <;> rfl

@[simp]
-/
theorem K'.elim_update_main {a b c d a'} : update (K'.elim a b c d) main a' = K'.elim a' b c d := by
  funext x; cases x <;> rfl

@[simp]
/--
theorem `K'.elim_update_rev` / 定理 `K'.elim_update_rev`

English:
theorem K'.elim_update_rev
  given: {a b c d b'}
  statement: update (K'.elim a b c d) rev b' = K'.elim a b' c d
  proof: by
  funext x; cases x <;> rfl

@[simp]

中文:
定理 K'.elim_update_rev
  条件: {a b c d b'}
  结论: update (K'.elim a b c d) rev b' = K'.elim a b' c d
  证明: by
  funext x; cases x <;> rfl

@[simp]
-/
theorem K'.elim_update_rev {a b c d b'} : update (K'.elim a b c d) rev b' = K'.elim a b' c d := by
  funext x; cases x <;> rfl

@[simp]
/--
theorem `K'.elim_update_aux` / 定理 `K'.elim_update_aux`

English:
theorem K'.elim_update_aux
  given: {a b c d c'}
  statement: update (K'.elim a b c d) aux c' = K'.elim a b c' d
  proof: by
  funext x; cases x <;> rfl

@[simp]

中文:
定理 K'.elim_update_aux
  条件: {a b c d c'}
  结论: update (K'.elim a b c d) aux c' = K'.elim a b c' d
  证明: by
  funext x; cases x <;> rfl

@[simp]
-/
theorem K'.elim_update_aux {a b c d c'} : update (K'.elim a b c d) aux c' = K'.elim a b c' d := by
  funext x; cases x <;> rfl

@[simp]
/--
theorem `K'.elim_update_stack` / 定理 `K'.elim_update_stack`

English:
theorem K'.elim_update_stack
  given: {a b c d d'}
  proof: by funext x; cases x <;> rfl

中文:
定理 K'.elim_update_stack
  条件: {a b c d d'}
  证明: by funext x; cases x <;> rfl
-/
theorem K'.elim_update_stack {a b c d d'} :
    update (K'.elim a b c d) stack d' = K'.elim a b c d' := by funext x; cases x <;> rfl

/--
Definition of `halt` / `halt` 的定义

English:
definition halt
  signature: (v : List Nat)
  body: ⟨none, none, K'.elim (trList v) [] [] []⟩

中文:
定义 halt
  签名: (v : 列表 自然数)
  定义体: ⟨none, none, K'.elim (trList v) [] [] []⟩

Depends on / 依赖: trList
-/
def halt (v : List Nat) : Cfg' :=
  ⟨none, none, K'.elim (trList v) [] [] []⟩

/--
Definition of `TrCfg` / `TrCfg` 的定义

English:
definition TrCfg
  signature: : Cfg -> Cfg' -> Prop

中文:
定义 TrCfg
  签名: : Cfg -> Cfg' -> 命题
-/
def TrCfg : Cfg -> Cfg' -> Prop
  | Cfg.ret k v, c' =>
    exists s, c' = ⟨some (Λ'.ret (trCont k)), s, K'.elim (trList v) [] [] (trContStack k)⟩
  | Cfg.halt v, c' => c' = halt v

/--
Definition of `splitAtPred` / `splitAtPred` 的定义

English:
definition splitAtPred
  signature: {α} (p : α -> Bool)
  body: splitAtPred p as
      ⟨a::l₁, o, l₂⟩

中文:
定义 splitAtPred
  签名: {α} (p : α -> 布尔值)
  定义体: splitAtPred p as
      ⟨a::l₁, o, l₂⟩

Depends on / 依赖: splitAtPred
-/
def splitAtPred {α} (p : α -> Bool) : List α -> List α × Option α × List α
  | [] => ([], none, [])
  | a :: as =>
cond (p a) ([], some a, as)
      let ⟨l₁, o, l₂⟩ := splitAtPred p as
      ⟨a::l₁, o, l₂⟩

/--
theorem `splitAtPred_eq` / 定理 `splitAtPred_eq`

English:
theorem splitAtPred_eq
  given: {α} (p : α -> Bool)
  proof: splitAtPred_eq p L
    rcases o with - | o
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨⟨⟩, rfl⟩
      rw [h₁ a (List.Mem.head _)]; rw [cond]; rw [IH L none [] _ ⟨rfl, rfl⟩]
      exact fun x h => h₁ x (List.Mem.tail _ h)
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨h₂, ⟨⟩⟩
      ·

中文:
定理 splitAtPred_eq
  条件: {α} (p : α -> 布尔值)
  证明: splitAtPred_eq p L
    rcases o with - | o
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨⟨⟩, rfl⟩
      rw [h₁ a (List.Mem.head _)]; rw [cond]; rw [IH L none [] _ ⟨rfl, rfl⟩]
      exact fun x h => h₁ x (List.Mem.tail _ h)
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨h₂, ⟨⟩⟩
      ·

Depends on / 依赖: splitAtPred_eq
-/
theorem splitAtPred_eq {α} (p : α -> Bool) :
    forall L l₁ o l₂,
      (forall x in l₁, p x = false) ->
        Option.elim' (L = l₁ ∧ l₂ = []) (fun a => p a = true ∧ L = l₁ ++ a::l₂) o ->
          splitAtPred p L = (l₁, o, l₂)
  | [], _, none, _, _, ⟨rfl, rfl⟩ => rfl
  | [], l₁, some o, l₂, _, ⟨_, h₃⟩ => by simp at h₃
  | a :: L, l₁, o, l₂, h₁, h₂ => by
    rw [splitAtPred]
    have IH := splitAtPred_eq p L
    rcases o with - | o
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨⟨⟩, rfl⟩
      rw [h₁ a (List.Mem.head _)]; rw [cond]; rw [IH L none [] _ ⟨rfl, rfl⟩]
      exact fun x h => h₁ x (List.Mem.tail _ h)
    · rcases l₁ with - | ⟨a', l₁⟩ <;> rcases h₂ with ⟨h₂, ⟨⟩⟩
      · rw [h₂, cond]
      rw [h₁ a (List.Mem.head _)]; rw [cond]; rw [IH l₁ (some o) l₂ _ ⟨h₂]; rw [_⟩] <;> try rfl
      exact fun x h => h₁ x (List.Mem.tail _ h)

/--
theorem `splitAtPred_false` / 定理 `splitAtPred_false`

English:
theorem splitAtPred_false
  given: {α} (L : List α)
  statement: splitAtPred (fun _ => false) L = (L, none, [])
  proof: splitAtPred_eq _ _ _ _ _ (fun _ _ => rfl) ⟨rfl, rfl⟩

中文:
定理 splitAtPred_false
  条件: {α} (L : 列表 α)
  结论: splitAtPred (fun _ => false) L = (L, none, [])
  证明: splitAtPred_eq _ _ _ _ _ (fun _ _ => rfl) ⟨rfl, rfl⟩

Depends on / 依赖: splitAtPred_eq
-/
theorem splitAtPred_false {α} (L : List α) : splitAtPred (fun _ => false) L = (L, none, []) :=
  splitAtPred_eq _ _ _ _ _ (fun _ _ => rfl) ⟨rfl, rfl⟩

/--
theorem `move_ok` / 定理 `move_ok`

English:
theorem move_ok
  statement: {p k₁ k₂ q s L₁ o L₂} {S : K' -> List Γ'} (h₁ : k₁ != k₂)
  proof: by
  induction L₁ generalizing S s with
  | nil =>
    rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    swap
    · rw [Function.update_of_ne h₁.symm, List.reverseAux_nil]
    refine TransGen.head' rfl ?_
    simp only [tr_move, pop', TM2.stepAux]
    grind [splitAtPred.eq_def]
  | cons a 

中文:
定理 move_ok
  结论: {p k₁ k₂ q s L₁ o L₂} {S : K' -> 列表 Γ'} (h₁ : k₁ != k₂)
  证明: by
  induction L₁ generalizing S s with
  | nil =>
    rw [(_ : [].reverseAux _ = _), Function.update_eq_self]
    swap
    · rw [Function.update_of_ne h₁.symm, List.reverseAux_nil]
    refine TransGen.head' rfl ?_
    simp only [tr_move, pop', TM2.stepAux]
    grind [splitAtPred.eq_def]
  | cons a 

Depends on / 依赖: Function, Function.update_eq_self, Function.update_of_ne, List.reverseAux_nil, Option.elim, TM2.stepAux, TransGen, TransGen.head, eq_def, generalizing, reverseAux, reverseAux_nil, splitAtPred, splitAtPred.eq_def, stepAux, tr_move, update_eq_self, update_of_ne
-/
theorem move_ok {p k₁ k₂ q s L₁ o L₂} {S : K' -> List Γ'} (h₁ : k₁ != k₂)
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

/--
theorem `unrev_ok` / 定理 `unrev_ok`

English:
theorem unrev_ok
  given: {q s} {S : K' -> List Γ'}
  proof: move_ok (by decide) splitAtPred_false _

中文:
定理 unrev_ok
  条件: {q s} {S : K' -> 列表 Γ'}
  证明: move_ok (by decide) splitAtPred_false _

Depends on / 依赖: move_ok, splitAtPred_false
-/
theorem unrev_ok {q s} {S : K' -> List Γ'} :
    Reaches₁ (TM2.step tr) ⟨some (unrev q), s, S⟩
      ⟨some q, none, update (update S rev []) main (List.reverseAux (S rev) (S main))⟩ :=
move_ok (by decide) splitAtPred_false _

/--
theorem `move₂_ok` / 定理 `move₂_ok`

English:
theorem move₂_ok
  statement: {p k₁ k₂ q s L₁ o L₂} {S : K' -> List Γ'} (h₁ : k₁ != rev ∧ k₂ != rev ∧ k₁ != k₂)
  proof: by
  refine (move_ok h₁.1 e).trans (TransGen.head rfl ?_)
  simp only [TM2.step, Option.mem_def, Option.elim]
  cases o <;> simp only <;> rw [tr]
    <;> simp only [id, TM2.stepAux, Option.isSome, cond_true, cond_false]
  · convert! move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [Fu

中文:
定理 move₂_ok
  结论: {p k₁ k₂ q s L₁ o L₂} {S : K' -> 列表 Γ'} (h₁ : k₁ != rev ∧ k₂ != rev ∧ k₁ != k₂)
  证明: by
  refine (move_ok h₁.1 e).trans (TransGen.head rfl ?_)
  simp only [TM2.step, Option.mem_def, Option.elim]
  cases o <;> simp only <;> rw [tr]
    <;> simp only [id, TM2.stepAux, Option.isSome, cond_true, cond_false]
  · convert! move_ok h₁.2.1.symm (splitAtPred_false _) using 2
    simp only [Fu

Depends on / 依赖: Function, Function.update_comm, Function.update_eq_self, Function.update_idem, Function.update_of_ne, Option.elim, Option.isSome, Option.mem_def, TM2.step, TM2.stepAux, TransGen, TransGen.head, cond_false, cond_true, convert, isSome, mem_def, move_ok, splitAtPred_false, stepAux
-/
theorem move₂_ok {p k₁ k₂ q s L₁ o L₂} {S : K' -> List Γ'} (h₁ : k₁ != rev ∧ k₂ != rev ∧ k₁ != k₂)
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

/--
theorem `clear_ok` / 定理 `clear_ok`

English:
theorem clear_ok
  given: {p k q s L₁ o L₂} {S : K' -> List Γ'} (e : splitAtPred p (S k) = (L₁, o, L₂))
  proof: by
  induction L₁ generalizing S s with
  | nil =>
    refine TransGen.head' rfl ?_
    rw [tr]; simp only [pop', TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    revert e; rcases S k with - | ⟨a, Sk⟩ <;> intro e
    · cases e
      rfl
    simp only [splitAtPred, List.head?, List.tail_cons] 

中文:
定理 clear_ok
  条件: {p k q s L₁ o L₂} {S : K' -> 列表 Γ'} (e : splitAtPred p (S k) = (L₁, o, L₂))
  证明: by
  induction L₁ generalizing S s with
  | nil =>
    refine TransGen.head' rfl ?_
    rw [tr]; simp only [pop', TM2.step, Option.mem_def, TM2.stepAux, Option.elim]
    revert e; rcases S k with - | ⟨a, Sk⟩ <;> intro e
    · cases e
      rfl
    simp only [splitAtPred, List.head?, List.tail_cons] 

Depends on / 依赖: List.head, List.tail_cons, Option.elim, Option.mem_def, Prod.mk.injEq, TM2.step, TM2.stepAux, TransGen, TransGen.head, cond_false, cond_true, false_and, generalizing, mem_def, reduceCtorEq, revert, splitAtPred, stepAux, tail_cons, true_and
-/
theorem clear_ok {p k q s L₁ o L₂} {S : K' -> List Γ'} (e : splitAtPred p (S k) = (L₁, o, L₂)) :
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
    rw [e₁]; rw [e₂]
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
/--
theorem `copy_ok` / 定理 `copy_ok`

English:
theorem copy_ok
  given: (q s a b c d)
  proof: by
  induction b generalizing a d s with
  | nil =>
    refine TransGen.single ?_
    simp
  | cons x b IH =>
    refine TransGen.head rfl ?_
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_rev, List.head?_cons, Option.isSome_some,
      List.tail_cons, elim_update_rev, elim_m

中文:
定理 copy_ok
  条件: (q s a b c d)
  证明: by
  induction b generalizing a d s with
  | nil =>
    refine TransGen.single ?_
    simp
  | cons x b IH =>
    refine TransGen.head rfl ?_
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, elim_rev, List.head?_cons, Option.isSome_some,
      List.tail_cons, elim_update_rev, elim_m

Depends on / 依赖: List.head, List.reverseAux_cons, List.tail_cons, Option.isSome_some, Option.mem_def, TM2.step, TM2.stepAux, TransGen, TransGen.head, TransGen.single, _cons, cond_true, elim_main, elim_rev, elim_stack, elim_update_main, elim_update_rev, elim_update_stack, generalizing, isSome_some
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

/--
theorem `trPosNum_natEnd` / 定理 `trPosNum_natEnd`

English:
theorem trPosNum_natEnd
  statement: forall (n), forall x in trPosNum n, natEnd x = false

中文:
定理 trPosNum_natEnd
  结论: 对任意 (n), 对任意 x in trPosNum n, natEnd x = false
-/
theorem trPosNum_natEnd : forall (n), forall x in trPosNum n, natEnd x = false
  | PosNum.one, _, List.Mem.head _ => rfl
  | PosNum.bit0 _, _, List.Mem.head _ => rfl
  | PosNum.bit0 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h
  | PosNum.bit1 _, _, List.Mem.head _ => rfl
  | PosNum.bit1 n, _, List.Mem.tail _ h => trPosNum_natEnd n _ h

/--
theorem `trNum_natEnd` / 定理 `trNum_natEnd`

English:
theorem trNum_natEnd
  statement: forall (n), forall x in trNum n, natEnd x = false

中文:
定理 trNum_natEnd
  结论: 对任意 (n), 对任意 x in trNum n, natEnd x = false
-/
theorem trNum_natEnd : forall (n), forall x in trNum n, natEnd x = false
  | Num.pos n, x, h => trPosNum_natEnd n x h

/--
theorem `trNat_natEnd` / 定理 `trNat_natEnd`

English:
theorem trNat_natEnd
  given: (n)
  statement: forall x in trNat n, natEnd x = false
  proof: trNum_natEnd _

中文:
定理 tr自然数_natEnd
  条件: (n)
  结论: 对任意 x in tr自然数 n, natEnd x = false
  证明: trNum_natEnd _

Depends on / 依赖: trNum_natEnd
-/
theorem trNat_natEnd (n) : forall x in trNat n, natEnd x = false :=
  trNum_natEnd _

/--
theorem `trList_ne_consₗ` / 定理 `trList_ne_consₗ`

English:
theorem trList_ne_consₗ
  statement: forall (l), forall x in trList l, x != Γ'.consₗ
  proof: h
    · rintro rfl
      cases trNat_natEnd _ _ h
    · rintro ⟨⟩
    · exact trList_ne_consₗ l _ h

中文:
定理 trList_ne_consₗ
  结论: 对任意 (l), 对任意 x in trList l, x != Γ'.consₗ
  证明: h
    · rintro rfl
      cases trNat_natEnd _ _ h
    · rintro ⟨⟩
    · exact trList_ne_consₗ l _ h
-/
theorem trList_ne_consₗ : forall (l), forall x in trList l, x != Γ'.consₗ
  | a :: l, x, h => by
    simp only [trList, List.mem_append, List.mem_cons] at h
    obtain h | rfl | h := h
    · rintro rfl
      cases trNat_natEnd _ _ h
    · rintro ⟨⟩
    · exact trList_ne_consₗ l _ h

/--
theorem `head_main_ok` / 定理 `head_main_ok`

English:
theorem head_main_ok
  given: {q s L} {c d : List Γ'}
  proof: by
  let o : Option Γ' := List.casesOn L none fun _ _ => some Γ'.cons
  refine
    (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat L.headI) o (trList L.tail) (trNat_natEnd _) ?_)).trans
      (TransGen.head rfl (TransGen.head rfl ?_))
  · cases L <;> simp [o]
  rw [tr]
  simp only [TM2.ste

中文:
定理 head_main_ok
  条件: {q s L} {c d : 列表 Γ'}
  证明: by
  let o : Option Γ' := List.casesOn L none fun _ _ => some Γ'.cons
  refine
    (move_ok (by decide)
          (splitAtPred_eq _ _ (trNat L.headI) o (trList L.tail) (trNat_natEnd _) ?_)).trans
      (TransGen.head rfl (TransGen.head rfl ?_))
  · cases L <;> simp [o]
  rw [tr]
  simp only [TM2.ste

Depends on / 依赖: Function, Function.update_self, L.headI, L.tail, List.casesOn, Option.mem_def, TM2.step, TM2.stepAux, TransGen, TransGen.head, casesOn, clear_ok, elim_rev, elim_update_main, elim_update_rev, if_neg, mem_def, move_ok, splitAtPred_eq, stepAux
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
  rw [if_neg (show o != some Γ'.consₗ by cases L <;> simp [o])]
  refine (clear_ok (splitAtPred_eq _ _ _ none [] ?_ ⟨rfl, rfl⟩)).trans ?_
  · exact fun x h => Bool.decide_false (trList_ne_consₗ _ _ h)
  convert! unrev_ok using 2; simp [List.reverseAux_eq]

/--
theorem `head_stack_ok` / 定理 `head_stack_ok`

English:
theorem head_stack_ok
  given: {q s L₁ L₂ L₃}
  proof: by
  rcases L₂ with - | ⟨a, L₂⟩
  · refine
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ [] (some Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
        (TransGen.head rfl (TransGen.head rfl ?_))
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, ite_true

中文:
定理 head_stack_ok
  条件: {q s L₁ L₂ L₃}
  证明: by
  rcases L₂ with - | ⟨a, L₂⟩
  · refine
      TransGen.trans
        (move_ok (by decide)
          (splitAtPred_eq _ _ [] (some Γ'.consₗ) L₃ (by rintro _ ⟨⟩) ⟨rfl, rfl⟩))
        (TransGen.head rfl (TransGen.head rfl ?_))
    rw [tr]
    simp only [TM2.step, Option.mem_def, TM2.stepAux, ite_true

Depends on / 依赖: Function, Function.update_self, List.headI_nil, List.nil_append, List.reverseAux_nil, Option.mem_def, TM2.step, TM2.stepAux, TransGen, TransGen.head, TransGen.trans, convert, elim_rev, elim_update_rev, elim_update_stack, headI_nil, id_eq, ite_true, mem_def, move_ok
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
/--
theorem `succ_ok` / 定理 `succ_ok`

English:
theorem succ_ok
  given: {q s n} {c d : List Γ'}
  proof: by
  simp only [trList, trNat.eq_1, Nat.cast_succ, Num.add_one]
  rcases (n : Num) with - | a
  · refine TransGen.head rfl ?_
    simp only [Option.mem_def]
    convert! unrev_ok using 1
    simp only [elim_update_rev, elim_rev, elim_main, List.reverseAux_nil, elim_update_main]
    rfl
  simp only [

中文:
定理 succ_ok
  条件: {q s n} {c d : 列表 Γ'}
  证明: by
  simp only [trList, trNat.eq_1, Nat.cast_succ, Num.add_one]
  rcases (n : Num) with - | a
  · refine TransGen.head rfl ?_
    simp only [Option.mem_def]
    convert! unrev_ok using 1
    simp only [elim_update_rev, elim_rev, elim_main, List.reverseAux_nil, elim_update_main]
    rfl
  simp only [

Depends on / 依赖: List.reverseAux, List.reverseAux_nil, Nat.cast_succ, Num.add_one, Num.succ, Option.mem_def, TM2.step, TransGen, TransGen.head, a.succ, add_one, cast_succ, convert, elim_main, elim_rev, elim_update_main, elim_update_rev, eq_1, mem_def, q.succ
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
  suffices forall l₁, exists l₁' l₂' s',
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
/--
theorem `pred_ok` / 定理 `pred_ok`

English:
theorem pred_ok
  given: (q₁ q₂ s v) (c d : List Γ')
  statement: exists s',
  proof: by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine ⟨none, TransGen.single ?_⟩
    simp
  · refine ⟨some Γ'.cons, TransGen.single ?_⟩
    simp
  refine ⟨none, ?_⟩
  simp only [trList, trNat.eq_1, trNum, Nat.cast_succ, Num.add_one, Num.succ,
    List.tail_cons, List.headI_cons]
  rcases (n : Num) with - |

中文:
定理 pred_ok
  条件: (q₁ q₂ s v) (c d : 列表 Γ')
  结论: 存在 s',
  证明: by
  rcases v with (_ | ⟨_ | n, v⟩)
  · refine ⟨none, TransGen.single ?_⟩
    simp
  · refine ⟨some Γ'.cons, TransGen.single ?_⟩
    simp
  refine ⟨none, ?_⟩
  simp only [trList, trNat.eq_1, trNum, Nat.cast_succ, Num.add_one, Num.succ,
    List.tail_cons, List.headI_cons]
  rcases (n : Num) with - |

Depends on / 依赖: List.headI_cons, List.nil_append, List.singleton_append, List.tail_cons, Nat.cast_succ, Num.add_one, Num.succ, TM2.stepAux, TransGen, TransGen.head, TransGen.single, add_one, cast_succ, convert, eq_1, headI_cons, nil_append, single, singleton_append, stepAux
-/
theorem pred_ok (q₁ q₂ s v) (c d : List Γ') : exists s',
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
  suffices forall l₁, exists l₁' l₂' s',
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
    obtain ⟨a, l, e, h⟩ : exists a l, (trPosNum m = a::l) ∧ natEnd a = false := by
      cases m <;> refine ⟨_, _, rfl, rfl⟩
    refine ⟨Γ'.bit0 :: l₁, _, some a, rfl, TransGen.single ?_⟩
    simp [trPosNum, PosNum.succ, e, h, show some Γ'.bit1 != some Γ'.bit0 by decide,
      Option.getD, -natEnd]
    rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `trNormal_respects` / 定理 `trNormal_respects`

English:
theorem trNormal_respects
  given: (c k v s)
  proof: by
  induction c generalizing k v s with
  | zero' => refine ⟨_, ⟨s, rfl⟩, TransGen.single ?_⟩; simp
  | succ => refine ⟨_, ⟨none, rfl⟩, head_main_ok.trans succ_ok⟩
  | tail =>
    let o : Option Γ' := List.casesOn v none fun _ _ => some Γ'.cons
    refine ⟨_, ⟨o, rfl⟩, ?_⟩; convert! clear_ok _ usin

中文:
定理 trNormal_respects
  条件: (c k v s)
  证明: by
  induction c generalizing k v s with
  | zero' => refine ⟨_, ⟨s, rfl⟩, TransGen.single ?_⟩; simp
  | succ => refine ⟨_, ⟨none, rfl⟩, head_main_ok.trans succ_ok⟩
  | tail =>
    let o : Option Γ' := List.casesOn v none fun _ _ => some Γ'.cons
    refine ⟨_, ⟨o, rfl⟩, ?_⟩; convert! clear_ok _ usin

Depends on / 依赖: Cont.cons, List.casesOn, TransGen, TransGen.head, TransGen.single, casesOn, clear_ok, convert, generalizing, head_main_ok, head_main_ok.trans, single, splitAtPred_eq, succ_ok, trNat_natEnd, v.headI
-/
theorem trNormal_respects (c k v s) :
    exists b₂,
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
refine ⟨c, h₁, TransGen.head rfl (move_ok (by decide) (splitAtPred_false _)).trans ?_⟩
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
/--
theorem `tr_ret_respects` / 定理 `tr_ret_respects`

English:
theorem tr_ret_respects
  given: (k v s)
  statement: exists b₂,
  proof: by
  induction k generalizing v s with
  | halt => exact ⟨_, rfl, TransGen.single rfl⟩
  | cons₁ fs as k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects fs (Cont.cons₂ v k) as none
    refine ⟨s', h₁, TransGen.head rfl ?_⟩; simp
    refine (move₂_ok (by decide) ?_ (splitAtPred_false _)).trans ?_; 

中文:
定理 tr_ret_respects
  条件: (k v s)
  结论: 存在 b₂,
  证明: by
  induction k generalizing v s with
  | halt => exact ⟨_, rfl, TransGen.single rfl⟩
  | cons₁ fs as k _ =>
    obtain ⟨s', h₁, h₂⟩ := trNormal_respects fs (Cont.cons₂ v k) as none
    refine ⟨s', h₁, TransGen.head rfl ?_⟩; simp
    refine (move₂_ok (by decide) ?_ (splitAtPred_false _)).trans ?_; 

Depends on / 依赖: Cont.cons, List.append_nil, Option.elim, Option.mem_def, TM2.step, TransGen, TransGen.head, TransGen.single, append_nil, elim_aux, elim_main, elim_update_aux, elim_update_main, generalizing, id_eq, mem_def, single, splitAtPred_false, trNormal_respects
-/
theorem tr_ret_respects (k v s) : exists b₂,
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
exact ⟨c, h₁, TransGen.head rfl head_stack_ok.trans h₂⟩
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
      rw [trList]; rw [List.headI]; rw [trNat]; rw [Nat.cast_succ]; rw [Num.add_one]; rw [Num.succ]; rw [List.tail]
      cases (n : Num).succ' <;> exact ⟨rfl, rfl⟩
    by_cases h : v.headI = 0 <;> simp only [h, ite_true, ite_false] at this ⊢
    · obtain ⟨c, h₁, h₂⟩ := IH v.tail (trList v).head?
      refine ⟨c, h₁, TransGen.head rfl ?_⟩
      rw [trCont]; rw [tr]; simp only [pop', TM2.stepAux, elim_main, this, elim_update_main]
      exact h₂
    · obtain ⟨s', h₁, h₂⟩ := trNormal_respects f (Cont.fix f k) v.tail (some Γ'.cons)
refine ⟨_, h₁, TransGen.head rfl TransGen.trans ?_ h₂⟩
      rw [trCont]; rw [tr]; simp only [pop', TM2.stepAux, elim_main, this.1]
      convert! clear_ok (splitAtPred_eq _ _ (trNat v.headI).tail (some Γ'.cons) _ _ _) using 2
      · simp
        convert! rfl
      · exact fun x h => trNat_natEnd _ _ (List.tail_subset _ h)
      · exact ⟨rfl, this.2⟩

/--
theorem `tr_respects` / 定理 `tr_respects`

English:
theorem tr_respects
  statement: Respects step (TM2.step tr) TrCfg

中文:
定理 tr_respects
  结论: Respects step (TM2.step tr) TrCfg
-/
theorem tr_respects : Respects step (TM2.step tr) TrCfg
  | Cfg.ret _ _, _, ⟨_, rfl⟩ => tr_ret_respects _ _ _
  | Cfg.halt _, _, rfl => rfl

/--
Definition of `init` / `init` 的定义

English:
definition init
  signature: (c : Code) (v : List Nat)
  body: ⟨some (trNormal c Cont'.halt), none, K'.elim (trList v) [] [] []⟩

中文:
定义 init
  签名: (c : 余de) (v : 列表 自然数)
  定义体: ⟨some (trNormal c Cont'.halt), none, K'.elim (trList v) [] [] []⟩

Depends on / 依赖: trList, trNormal
-/
def init (c : Code) (v : List Nat) : Cfg' :=
  ⟨some (trNormal c Cont'.halt), none, K'.elim (trList v) [] [] []⟩

/--
theorem `tr_init` / 定理 `tr_init`

English:
theorem tr_init
  given: (c v)
  proof: trNormal_respects _ _ _ _

中文:
定理 tr_init
  条件: (c v)
  证明: trNormal_respects _ _ _ _

Depends on / 依赖: trNormal_respects
-/
theorem tr_init (c v) :
    exists b, TrCfg (stepNormal c Cont.halt v) b ∧ Reaches₁ (TM2.step tr) (init c v) b :=
  trNormal_respects _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `tr_eval` / 定理 `tr_eval`

English:
theorem tr_eval
  given: (c v)
  statement: eval (TM2.step tr) (init c v) = halt < > Code.eval c v
  proof: by
  obtain ⟨i, h₁, h₂⟩ := tr_init c v
  refine Part.ext fun x => ?_
  rw [reaches_eval h₂.to_reflTransGen]; simp only [Part.map_eq_map, Part.mem_map_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, hc₁, hc₂⟩ := tr_eval_rev tr_respects h₁ h
    simp only [stepNormal_eval, Part.map_eq_map, Part.mem_map

中文:
定理 tr_eval
  条件: (c v)
  结论: eval (TM2.step tr) (init c v) = halt < > 余de.eval c v
  证明: by
  obtain ⟨i, h₁, h₂⟩ := tr_init c v
  refine Part.ext fun x => ?_
  rw [reaches_eval h₂.to_reflTransGen]; simp only [Part.map_eq_map, Part.mem_map_iff]
  refine ⟨fun h => ?_, ?_⟩
  · obtain ⟨c, hc₁, hc₂⟩ := tr_eval_rev tr_respects h₁ h
    simp only [stepNormal_eval, Part.map_eq_map, Part.mem_map

Depends on / 依赖: Cfg.halt, Part.ext, Part.map_eq_map, Part.mem_map_i, Part.mem_map_iff, StateTransition, StateTransition.tr_eval, map_eq_map, mem_map_i, mem_map_iff, reaches_eval, stepNormal_eval, to_reflTransGen, tr_eval, tr_eval_rev, tr_init, tr_respects
-/
theorem tr_eval (c v) : eval (TM2.step tr) (init c v) = halt < > Code.eval c v := by
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

/--
Definition of `trStmts₁` / `trStmts₁` 的定义

English:
definition trStmts₁
  signature: : Λ' -> Finset Λ'

中文:
定义 trStmts₁
  签名: : Λ' -> 有限集 Λ'
-/
def trStmts₁ : Λ' -> Finset Λ'
| Q@(Λ'.move _ _ _ q) => insert Q trStmts₁ q
| Q@(Λ'.push _ _ q) => insert Q trStmts₁ q
| Q@(Λ'.read q) => insert Q Finset.univ.biUnion fun s => trStmts₁ (q s)
| Q@(Λ'.clear _ _ q) => insert Q trStmts₁ q
| Q@(Λ'.copy q) => insert Q trStmts₁ q
| Q@(Λ'.succ q) => insert Q insert (unrev q) trStmts₁ q
| Q@(Λ'.pred q₁ q₂) => insert Q trStmts₁ q₁ union insert (unrev q₂) (trStmts₁ q₂)
  | Q@(Λ'.ret _) => {Q}

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `trStmts₁_trans` / 定理 `trStmts₁_trans`

English:
theorem trStmts₁_trans
  given: {q q'}
  statement: q' in trStmts₁ q -> trStmts₁ q' subseteq trStmts₁ q
  proof: by
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
  all_goals
    simp +contextual only [trStmts₁, Finset.mem_insert, Finset.mem_union,
      or_imp, 

中文:
定理 trStmts₁_trans
  条件: {q q'}
  结论: q' in trStmts₁ q -> trStmts₁ q' subseteq trStmts₁ q
  证明: by
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
  all_goals
    simp +contextual only [trStmts₁, Finset.mem_insert, Finset.mem_union,
      or_imp, 

Depends on / 依赖: Finset, Finset.Subset.refl, Finset.Subset.trans, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton, Finset.mem_union, Finset.mem_univ, Finset.subset_insert, Subset, all_goals, contextual, forall_exists_, imp_true_iff, mem_biUnion, mem_insert, mem_singleton, mem_union, mem_univ, or_imp
-/
theorem trStmts₁_trans {q q'} : q' in trStmts₁ q -> trStmts₁ q' subseteq trStmts₁ q := by
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

/--
theorem `trStmts₁_self` / 定理 `trStmts₁_self`

English:
theorem trStmts₁_self
  given: (q)
  statement: q in trStmts₁ q
  proof: by
  induction q <;> · first | apply Finset.mem_singleton_self | apply Finset.mem_insert_self

中文:
定理 trStmts₁_self
  条件: (q)
  结论: q in trStmts₁ q
  证明: by
  induction q <;> · first | apply Finset.mem_singleton_self | apply Finset.mem_insert_self

Depends on / 依赖: Finset, Finset.mem_insert_self, Finset.mem_singleton_self, mem_insert_self, mem_singleton_self
-/
theorem trStmts₁_self (q) : q in trStmts₁ q := by
  induction q <;> · first | apply Finset.mem_singleton_self | apply Finset.mem_insert_self

/--
Definition of `codeSupp'` / `codeSupp'` 的定义

English:
definition codeSupp'
  signature: : Code -> Cont' -> Finset Λ'

中文:
定义 codeSupp'
  签名: : 余de -> 余nt' -> 有限集 Λ'
-/
def codeSupp' : Code -> Cont' -> Finset Λ'
  | c@Code.zero', k => trStmts₁ (trNormal c k)
  | c@Code.succ, k => trStmts₁ (trNormal c k)
  | c@Code.tail, k => trStmts₁ (trNormal c k)
  | c@(Code.cons f fs), k =>
    trStmts₁ (trNormal c k) union
      (codeSupp' f (Cont'.cons₁ fs k) union
        (trStmts₁
            (move₂ (fun _ => false) main aux <|
move₂ (fun s => s = Γ'.consₗ) stack main
move₂ (fun _ => false) aux stack trNormal fs (Cont'.cons₂ k)) union
          (codeSupp' fs (Cont'.cons₂ k) union trStmts₁ (head stack <| Λ'.ret k))))
  | c@(Code.comp f g), k =>
    trStmts₁ (trNormal c k) union
      (codeSupp' g (Cont'.comp f k) union (trStmts₁ (trNormal f k) union codeSupp' f k))
  | c@(Code.case f g), k => trStmts₁ (trNormal c k) union (codeSupp' f k union codeSupp' g k)
  | c@(Code.fix f), k =>
    trStmts₁ (trNormal c k) union
      (codeSupp' f (Cont'.fix f k) union
        (trStmts₁ (Λ'.clear natEnd main <| trNormal f (Cont'.fix f k)) union {Λ'.ret k}))

@[simp]
/--
theorem `codeSupp'_self` / 定理 `codeSupp'_self`

English:
theorem codeSupp'_self
  given: (c k)
  statement: trStmts₁ (trNormal c k) subseteq codeSupp' c k
  proof: by
  cases c <;> first | rfl | exact Finset.union_subset_left (fun _ a => a)

中文:
定理 codeSupp'_self
  条件: (c k)
  结论: trStmts₁ (trNormal c k) subseteq codeSupp' c k
  证明: by
  cases c <;> first | rfl | exact Finset.union_subset_left (fun _ a => a)

Depends on / 依赖: Finset, Finset.union_subset_left, union_subset_left
-/
theorem codeSupp'_self (c k) : trStmts₁ (trNormal c k) subseteq codeSupp' c k := by
  cases c <;> first | rfl | exact Finset.union_subset_left (fun _ a => a)

/--
Definition of `contSupp` / `contSupp` 的定义

English:
definition contSupp
  signature: : Cont' -> Finset Λ'

中文:
定义 contSupp
  签名: : 余nt' -> 有限集 Λ'
-/
def contSupp : Cont' -> Finset Λ'
  | Cont'.cons₁ fs k =>
    trStmts₁
        (move₂ (fun _ => false) main aux <|
move₂ (fun s => s = Γ'.consₗ) stack main
move₂ (fun _ => false) aux stack trNormal fs (Cont'.cons₂ k)) union
      (codeSupp' fs (Cont'.cons₂ k) union (trStmts₁ (head stack <| Λ'.ret k) union contSupp k))
  | Cont'.cons₂ k => trStmts₁ (head stack <| Λ'.ret k) union contSupp k
  | Cont'.comp f k => codeSupp' f k union contSupp k
  | Cont'.fix f k => codeSupp' (Code.fix f) k union contSupp k
  | Cont'.halt => ∅

/--
Definition of `codeSupp` / `codeSupp` 的定义

English:
definition codeSupp
  signature: (c : Code) (k : Cont')
  body: codeSupp' c k union contSupp k

@[simp]

中文:
定义 codeSupp
  签名: (c : 余de) (k : 余nt')
  定义体: codeSupp' c k union contSupp k

@[simp]

Depends on / 依赖: codeSupp, contSupp
-/
def codeSupp (c : Code) (k : Cont') : Finset Λ' :=
  codeSupp' c k union contSupp k

@[simp]
/--
theorem `codeSupp_self` / 定理 `codeSupp_self`

English:
theorem codeSupp_self
  given: (c k)
  statement: trStmts₁ (trNormal c k) subseteq codeSupp c k
  proof: Finset.Subset.trans (codeSupp'_self _ _) (Finset.union_subset_left fun _ a => a)

@[simp]

中文:
定理 codeSupp_self
  条件: (c k)
  结论: trStmts₁ (trNormal c k) subseteq codeSupp c k
  证明: Finset.Subset.trans (codeSupp'_self _ _) (Finset.union_subset_left fun _ a => a)

@[simp]

Depends on / 依赖: Finset, Finset.Subset.trans, Finset.union_subset_left, Subset, _self, codeSupp, union_subset_left
-/
theorem codeSupp_self (c k) : trStmts₁ (trNormal c k) subseteq codeSupp c k :=
  Finset.Subset.trans (codeSupp'_self _ _) (Finset.union_subset_left fun _ a => a)

@[simp]
/--
theorem `codeSupp_zero` / 定理 `codeSupp_zero`

English:
theorem codeSupp_zero
  given: (k)
  statement: codeSupp Code.zero' k = trStmts₁ (trNormal Code.zero' k) union contSupp k
  proof: rfl

@[simp]

中文:
定理 codeSupp_zero
  条件: (k)
  结论: codeSupp 余de.zero' k = trStmts₁ (trNormal 余de.zero' k) union contSupp k
  证明: rfl

@[simp]
-/
theorem codeSupp_zero (k) : codeSupp Code.zero' k = trStmts₁ (trNormal Code.zero' k) union contSupp k :=
  rfl

@[simp]
/--
theorem `codeSupp_succ` / 定理 `codeSupp_succ`

English:
theorem codeSupp_succ
  given: (k)
  statement: codeSupp Code.succ k = trStmts₁ (trNormal Code.succ k) union contSupp k
  proof: rfl

@[simp]

中文:
定理 codeSupp_succ
  条件: (k)
  结论: codeSupp 余de.succ k = trStmts₁ (trNormal 余de.succ k) union contSupp k
  证明: rfl

@[simp]
-/
theorem codeSupp_succ (k) : codeSupp Code.succ k = trStmts₁ (trNormal Code.succ k) union contSupp k :=
  rfl

@[simp]
/--
theorem `codeSupp_tail` / 定理 `codeSupp_tail`

English:
theorem codeSupp_tail
  given: (k)
  statement: codeSupp Code.tail k = trStmts₁ (trNormal Code.tail k) union contSupp k
  proof: rfl

@[simp]

中文:
定理 codeSupp_tail
  条件: (k)
  结论: codeSupp 余de.tail k = trStmts₁ (trNormal 余de.tail k) union contSupp k
  证明: rfl

@[simp]
-/
theorem codeSupp_tail (k) : codeSupp Code.tail k = trStmts₁ (trNormal Code.tail k) union contSupp k :=
  rfl

@[simp]
/--
theorem `codeSupp_cons` / 定理 `codeSupp_cons`

English:
theorem codeSupp_cons
  given: (f fs k)
  proof: by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]

@[simp]

中文:
定理 codeSupp_cons
  条件: (f fs k)
  证明: by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]

@[simp]

Depends on / 依赖: Finset, Finset.union_assoc, codeSupp, contSupp, union_assoc
-/
theorem codeSupp_cons (f fs k) :
    codeSupp (Code.cons f fs) k =
      trStmts₁ (trNormal (Code.cons f fs) k) union codeSupp f (Cont'.cons₁ fs k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc]

@[simp]
/--
theorem `codeSupp_comp` / 定理 `codeSupp_comp`

English:
theorem codeSupp_comp
  given: (f g k)
  proof: by
  simp only [codeSupp, codeSupp', trNormal, Finset.union_assoc, contSupp]
  rw [← Finset.union_assoc _ _ (contSupp k)]; rw [Finset.union_eq_right.2 (codeSupp'_self _ _)]

@[simp]

中文:
定理 codeSupp_comp
  条件: (f g k)
  证明: by
  simp only [codeSupp, codeSupp', trNormal, Finset.union_assoc, contSupp]
  rw [← Finset.union_assoc _ _ (contSupp k)]; rw [Finset.union_eq_right.2 (codeSupp'_self _ _)]

@[simp]

Depends on / 依赖: Finset, Finset.union_assoc, Finset.union_eq_right, _self, codeSupp, contSupp, trNormal, union_assoc, union_eq_right
-/
theorem codeSupp_comp (f g k) :
    codeSupp (Code.comp f g) k =
      trStmts₁ (trNormal (Code.comp f g) k) union codeSupp g (Cont'.comp f k) := by
  simp only [codeSupp, codeSupp', trNormal, Finset.union_assoc, contSupp]
  rw [← Finset.union_assoc _ _ (contSupp k)]; rw [Finset.union_eq_right.2 (codeSupp'_self _ _)]

@[simp]
/--
theorem `codeSupp_case` / 定理 `codeSupp_case`

English:
theorem codeSupp_case
  given: (f g k)
  proof: by
  simp [codeSupp, codeSupp', Finset.union_assoc, Finset.union_left_comm]

@[simp]

中文:
定理 codeSupp_case
  条件: (f g k)
  证明: by
  simp [codeSupp, codeSupp', Finset.union_assoc, Finset.union_left_comm]

@[simp]

Depends on / 依赖: Finset, Finset.union_assoc, Finset.union_left_comm, codeSupp, union_assoc, union_left_comm
-/
theorem codeSupp_case (f g k) :
    codeSupp (Code.case f g) k =
      trStmts₁ (trNormal (Code.case f g) k) union (codeSupp f k union codeSupp g k) := by
  simp [codeSupp, codeSupp', Finset.union_assoc, Finset.union_left_comm]

@[simp]
/--
theorem `codeSupp_fix` / 定理 `codeSupp_fix`

English:
theorem codeSupp_fix
  given: (f k)
  proof: by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm,
    Finset.union_left_idem]

@[simp]

中文:
定理 codeSupp_fix
  条件: (f k)
  证明: by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm,
    Finset.union_left_idem]

@[simp]

Depends on / 依赖: Finset, Finset.union_assoc, Finset.union_left_comm, Finset.union_left_idem, codeSupp, contSupp, union_assoc, union_left_comm, union_left_idem
-/
theorem codeSupp_fix (f k) :
    codeSupp (Code.fix f) k = trStmts₁ (trNormal (Code.fix f) k) union codeSupp f (Cont'.fix f k) := by
  simp [codeSupp, codeSupp', contSupp, Finset.union_assoc, Finset.union_left_comm,
    Finset.union_left_idem]

@[simp]
/--
theorem `contSupp_cons₁` / 定理 `contSupp_cons₁`

English:
theorem contSupp_cons₁
  given: (fs k)
  proof: by
  simp [codeSupp, contSupp]

@[simp]

中文:
定理 contSupp_cons₁
  条件: (fs k)
  证明: by
  simp [codeSupp, contSupp]

@[simp]

Depends on / 依赖: codeSupp, contSupp
-/
theorem contSupp_cons₁ (fs k) :
    contSupp (Cont'.cons₁ fs k) =
      trStmts₁
          (move₂ (fun _ => false) main aux <|
move₂ (fun s => s = Γ'.consₗ) stack main
move₂ (fun _ => false) aux stack trNormal fs (Cont'.cons₂ k)) union
        codeSupp fs (Cont'.cons₂ k) := by
  simp [codeSupp, contSupp]

@[simp]
/--
theorem `contSupp_cons₂` / 定理 `contSupp_cons₂`

English:
theorem contSupp_cons₂
  given: (k)
  proof: rfl

@[simp]

中文:
定理 contSupp_cons₂
  条件: (k)
  证明: rfl

@[simp]
-/
theorem contSupp_cons₂ (k) :
    contSupp (Cont'.cons₂ k) = trStmts₁ (head stack <| Λ'.ret k) union contSupp k :=
  rfl

@[simp]
/--
theorem `contSupp_comp` / 定理 `contSupp_comp`

English:
theorem contSupp_comp
  given: (f k)
  statement: contSupp (Cont'.comp f k) = codeSupp f k
  proof: rfl

中文:
定理 contSupp_comp
  条件: (f k)
  结论: contSupp (余nt'.comp f k) = codeSupp f k
  证明: rfl
-/
theorem contSupp_comp (f k) : contSupp (Cont'.comp f k) = codeSupp f k :=
  rfl

/--
theorem `contSupp_fix` / 定理 `contSupp_fix`

English:
theorem contSupp_fix
  given: (f k)
  statement: contSupp (Cont'.fix f k) = codeSupp f (Cont'.fix f k)
  proof: by
  simp +contextual [codeSupp, codeSupp', contSupp, Finset.union_assoc,
    Finset.subset_iff, -Finset.singleton_union, -Finset.union_singleton]

@[simp]

中文:
定理 contSupp_fix
  条件: (f k)
  结论: contSupp (余nt'.fix f k) = codeSupp f (余nt'.fix f k)
  证明: by
  simp +contextual [codeSupp, codeSupp', contSupp, Finset.union_assoc,
    Finset.subset_iff, -Finset.singleton_union, -Finset.union_singleton]

@[simp]

Depends on / 依赖: Finset, Finset.singleton_union, Finset.subset_iff, Finset.union_assoc, Finset.union_singleton, codeSupp, contSupp, contextual, singleton_union, subset_iff, union_assoc, union_singleton
-/
theorem contSupp_fix (f k) : contSupp (Cont'.fix f k) = codeSupp f (Cont'.fix f k) := by
  simp +contextual [codeSupp, codeSupp', contSupp, Finset.union_assoc,
    Finset.subset_iff, -Finset.singleton_union, -Finset.union_singleton]

@[simp]
/--
theorem `contSupp_halt` / 定理 `contSupp_halt`

English:
theorem contSupp_halt
  statement: contSupp Cont'.halt = ∅
  proof: rfl

中文:
定理 contSupp_halt
  结论: contSupp 余nt'.halt = ∅
  证明: rfl
-/
theorem contSupp_halt : contSupp Cont'.halt = ∅ :=
  rfl

/--
Definition of `Λ'.Supports` / `Λ'.Supports` 的定义

English:
definition Λ'.Supports
  signature: (S : Finset Λ')

中文:
定义 Λ'.Supports
  签名: (S : 有限集 Λ')
-/
def Λ'.Supports (S : Finset Λ') : Λ' -> Prop
  | Λ'.move _ _ _ q => Λ'.Supports S q
  | Λ'.push _ _ q => Λ'.Supports S q
  | Λ'.read q => forall s, Λ'.Supports S (q s)
  | Λ'.clear _ _ q => Λ'.Supports S q
  | Λ'.copy q => Λ'.Supports S q
  | Λ'.succ q => Λ'.Supports S q
  | Λ'.pred q₁ q₂ => Λ'.Supports S q₁ ∧ Λ'.Supports S q₂
  | Λ'.ret k => contSupp k subseteq S

/--
Definition of `Supports` / `Supports` 的定义

English:
definition Supports
  signature: (K S : Finset Λ')
  body: forall q in K, TM2.SupportsStmt S (tr q)

中文:
定义 Supports
  签名: (K S : 有限集 Λ')
  定义体: forall q in K, TM2.SupportsStmt S (tr q)

Depends on / 依赖: SupportsStmt, TM2.SupportsStmt
-/
def Supports (K S : Finset Λ') :=
  forall q in K, TM2.SupportsStmt S (tr q)

/--
theorem `supports_insert` / 定理 `supports_insert`

English:
theorem supports_insert
  given: {K S q}
  proof: by simp [Supports]

中文:
定理 supports_insert
  条件: {K S q}
  证明: by simp [Supports]

Depends on / 依赖: Supports
-/
theorem supports_insert {K S q} :
    Supports (insert q K) S ↔ TM2.SupportsStmt S (tr q) ∧ Supports K S := by simp [Supports]

/--
theorem `supports_singleton` / 定理 `supports_singleton`

English:
theorem supports_singleton
  given: {S q}
  statement: Supports {q} S ↔ TM2.SupportsStmt S (tr q)
  proof: by simp [Supports]

中文:
定理 supports_singleton
  条件: {S q}
  结论: Supports {q} S ↔ TM2.SupportsStmt S (tr q)
  证明: by simp [Supports]

Depends on / 依赖: Supports
-/
theorem supports_singleton {S q} : Supports {q} S ↔ TM2.SupportsStmt S (tr q) := by simp [Supports]

/--
theorem `supports_union` / 定理 `supports_union`

English:
theorem supports_union
  given: {K₁ K₂ S}
  statement: Supports (K₁ union K₂) S ↔ Supports K₁ S ∧ Supports K₂ S
  proof: by
  simp [Supports, or_imp, forall_and]

中文:
定理 supports_union
  条件: {K₁ K₂ S}
  结论: Supports (K₁ union K₂) S ↔ Supports K₁ S ∧ Supports K₂ S
  证明: by
  simp [Supports, or_imp, forall_and]

Depends on / 依赖: Supports, forall_and, or_imp
-/
theorem supports_union {K₁ K₂ S} : Supports (K₁ union K₂) S ↔ Supports K₁ S ∧ Supports K₂ S := by
  simp [Supports, or_imp, forall_and]

/--
theorem `supports_biUnion` / 定理 `supports_biUnion`

English:
theorem supports_biUnion
  given: {K : Option Γ' -> Finset Λ'} {S}
  proof: by
  simpa [Supports] using forall_comm

中文:
定理 supports_biUnion
  条件: {K : 选项类型 Γ' -> 有限集 Λ'} {S}
  证明: by
  simpa [Supports] using forall_comm

Depends on / 依赖: Supports, forall_comm
-/
theorem supports_biUnion {K : Option Γ' -> Finset Λ'} {S} :
    Supports (Finset.univ.biUnion K) S ↔ forall a, Supports (K a) S := by
  simpa [Supports] using forall_comm

/--
theorem `head_supports` / 定理 `head_supports`

English:
theorem head_supports
  given: {S k q} (H : (q : Λ').Supports S)
  statement: (head k q).Supports S
  proof: fun _ => by
  dsimp only; split_ifs <;> exact H

中文:
定理 head_supports
  条件: {S k q} (H : (q : Λ').Supports S)
  结论: (head k q).Supports S
  证明: fun _ => by
  dsimp only; split_ifs <;> exact H

Depends on / 依赖: split_ifs
-/
theorem head_supports {S k q} (H : (q : Λ').Supports S) : (head k q).Supports S := fun _ => by
  dsimp only; split_ifs <;> exact H

/--
theorem `ret_supports` / 定理 `ret_supports`

English:
theorem ret_supports
  given: {S k} (H₁ : contSupp k subseteq S)
  statement: TM2.SupportsStmt S (tr (Λ'.ret k))
  proof: by
  have W := fun {q} => trStmts₁_self q
  cases k with
  | halt => trivial
  | cons₁ => rw [contSupp_cons₁, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | cons₂ => rw [contSupp_cons₂, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | comp => rw [contSupp_comp] at H₁; exact fun _

中文:
定理 ret_supports
  条件: {S k} (H₁ : contSupp k subseteq S)
  结论: TM2.SupportsStmt S (tr (Λ'.ret k))
  证明: by
  have W := fun {q} => trStmts₁_self q
  cases k with
  | halt => trivial
  | cons₁ => rw [contSupp_cons₁, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | cons₂ => rw [contSupp_cons₂, Finset.union_subset_iff] at H₁; exact fun _ => H₁.1 W
  | comp => rw [contSupp_comp] at H₁; exact fun _

Depends on / 依赖: Finset, Finset.mem_union_left, Finset.mem_union_right, Finset.union_subset_iff, codeSupp_self, contSupp_comp, contSupp_fix, mem_union_left, mem_union_right, natEnd, s.getD, union_subset_iff
-/
theorem ret_supports {S k} (H₁ : contSupp k subseteq S) : TM2.SupportsStmt S (tr (Λ'.ret k)) := by
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
/--
theorem `trStmts₁_supports` / 定理 `trStmts₁_supports`

English:
theorem trStmts₁_supports
  given: {S q} (H₁ : (q : Λ').Supports S) (HS₁ : trStmts₁ q subseteq S)
  proof: by
  have W := fun {q} => trStmts₁_self q
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
    simp [trStmts₁, -Finset.singleton_subset_iff] at HS₁ ⊢
  

中文:
定理 trStmts₁_supports
  条件: {S q} (H₁ : (q : Λ').Supports S) (HS₁ : trStmts₁ q subseteq S)
  证明: by
  have W := fun {q} => trStmts₁_self q
  induction q with
  | move _ _ _ q q_ih => _ | clear _ _ q q_ih => _ | copy q q_ih => _ | push _ _ q q_ih => _
  | read q q_ih => _ | succ q q_ih => _ | pred q₁ q₂ q₁_ih q₂_ih => _ | ret => _ <;>
    simp [trStmts₁, -Finset.singleton_subset_iff] at HS₁ ⊢
  

Depends on / 依赖: Finset, Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.subset_iff, any_goals, insert_subset_iff, q_ih, singleton_subset_iff, subset_iff, supports_i, supports_insert
-/
theorem trStmts₁_supports {S q} (H₁ : (q : Λ').Supports S) (HS₁ : trStmts₁ q subseteq S) :
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
  · exact supports_singleton.2 (ret_supports H₁) -- ret

/--
theorem `trStmts₁_supports'` / 定理 `trStmts₁_supports'`

English:
theorem trStmts₁_supports'
  statement: {S q K} (H₁ : (q : Λ').Supports S) (H₂ : trStmts₁ q union K subseteq S)
  proof: by
  simp only [Finset.union_subset_iff] at H₂
  exact supports_union.2 ⟨trStmts₁_supports H₁ H₂.1, H₃ H₂.2⟩

中文:
定理 trStmts₁_supports'
  结论: {S q K} (H₁ : (q : Λ').Supports S) (H₂ : trStmts₁ q union K subseteq S)
  证明: by
  simp only [Finset.union_subset_iff] at H₂
  exact supports_union.2 ⟨trStmts₁_supports H₁ H₂.1, H₃ H₂.2⟩

Depends on / 依赖: Finset, Finset.union_subset_iff, supports_union, union_subset_iff
-/
theorem trStmts₁_supports' {S q K} (H₁ : (q : Λ').Supports S) (H₂ : trStmts₁ q union K subseteq S)
    (H₃ : K subseteq S -> Supports K S) : Supports (trStmts₁ q union K) S := by
  simp only [Finset.union_subset_iff] at H₂
  exact supports_union.2 ⟨trStmts₁_supports H₁ H₂.1, H₃ H₂.2⟩

set_option linter.flexible false in -- TODO: revisit this after #13791 is merged
/--
theorem `trNormal_supports` / 定理 `trNormal_supports`

English:
theorem trNormal_supports
  given: {S c k} (Hk : codeSupp c k subseteq S)
  statement: (trNormal c k).Supports S
  proof: by
  induction c generalizing k with simp [Λ'.Supports, head]
  | zero' => exact Finset.union_subset_right Hk
  | succ => intro; split_ifs <;> exact Finset.union_subset_right Hk
  | tail => exact Finset.union_subset_right Hk
  | cons f fs IHf _ =>
    apply IHf
    rw [codeSupp_cons] at Hk
    exact

中文:
定理 trNormal_supports
  条件: {S c k} (Hk : codeSupp c k subseteq S)
  结论: (trNormal c k).Supports S
  证明: by
  induction c generalizing k with simp [Λ'.Supports, head]
  | zero' => exact Finset.union_subset_right Hk
  | succ => intro; split_ifs <;> exact Finset.union_subset_right Hk
  | tail => exact Finset.union_subset_right Hk
  | cons f fs IHf _ =>
    apply IHf
    rw [codeSupp_cons] at Hk
    exact

Depends on / 依赖: Finset, Finset.union_subset_iff, Finset.union_subset_right, Supports, codeSupp_case, codeSupp_comp, codeSupp_cons, generalizing, split_ifs, union_subset_iff, union_subset_right
-/
theorem trNormal_supports {S c k} (Hk : codeSupp c k subseteq S) : (trNormal c k).Supports S := by
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

/--
theorem `codeSupp'_supports` / 定理 `codeSupp'_supports`

English:
theorem codeSupp'_supports
  given: {S c k} (H : codeSupp c k subseteq S)
  statement: Supports (codeSupp' c k) S
  proof: by
  induction c generalizing k with
  | cons f fs IHf IHfs =>
    have H' := H; simp only [codeSupp_cons, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHf H'.2, ?_⟩
    refine trStmts₁_suppor

中文:
定理 codeSupp'_supports
  条件: {S c k} (H : codeSupp c k subseteq S)
  结论: Supports (codeSupp' c k) S
  证明: by
  induction c generalizing k with
  | cons f fs IHf IHfs =>
    have H' := H; simp only [codeSupp_cons, Finset.union_subset_iff] at H'
    refine trStmts₁_supports' (trNormal_supports H) (Finset.union_subset_left H) fun h => ?_
    refine supports_union.2 ⟨IHf H'.2, ?_⟩
    refine trStmts₁_suppor
-/
theorem codeSupp'_supports {S c k} (H : codeSupp c k subseteq S) : Supports (codeSupp' c k) S := by
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

/--
theorem `contSupp_supports` / 定理 `contSupp_supports`

English:
theorem contSupp_supports
  given: {S k} (H : contSupp k subseteq S)
  statement: Supports (contSupp k) S
  proof: by
  induction k with
  | halt => simp [contSupp_halt, Supports]
  | cons₁ f k IH =>
    have H₁ := H; rw [contSupp_cons₁] at H₁; have H₂ := Finset.union_subset_right H₁
    refine trStmts₁_supports' (trNormal_supports H₂) H₁ fun h => ?_
    refine supports_union.2 ⟨codeSupp'_supports H₂, ?_⟩
    si

中文:
定理 contSupp_supports
  条件: {S k} (H : contSupp k subseteq S)
  结论: Supports (contSupp k) S
  证明: by
  induction k with
  | halt => simp [contSupp_halt, Supports]
  | cons₁ f k IH =>
    have H₁ := H; rw [contSupp_cons₁] at H₁; have H₂ := Finset.union_subset_right H₁
    refine trStmts₁_supports' (trNormal_supports H₂) H₁ fun h => ?_
    refine supports_union.2 ⟨codeSupp'_supports H₂, ?_⟩
    si

Depends on / 依赖: Finset, Finset.union_subset_iff, Finset.union_subset_right, Supports, _supports, codeSupp, contSupp_halt, head_supports, supports_union, trNormal_supports, union_subset_iff, union_subset_right
-/
theorem contSupp_supports {S k} (H : contSupp k subseteq S) : Supports (contSupp k) S := by
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

/--
theorem `codeSupp_supports` / 定理 `codeSupp_supports`

English:
theorem codeSupp_supports
  given: {S c k} (H : codeSupp c k subseteq S)
  statement: Supports (codeSupp c k) S
  proof: supports_union.2 ⟨codeSupp'_supports H, contSupp_supports (Finset.union_subset_right H)⟩

中文:
定理 codeSupp_supports
  条件: {S c k} (H : codeSupp c k subseteq S)
  结论: Supports (codeSupp c k) S
  证明: supports_union.2 ⟨codeSupp'_supports H, contSupp_supports (Finset.union_subset_right H)⟩

Depends on / 依赖: Finset, Finset.union_subset_right, _supports, codeSupp, contSupp_supports, supports_union, union_subset_right
-/
theorem codeSupp_supports {S c k} (H : codeSupp c k subseteq S) : Supports (codeSupp c k) S :=
  supports_union.2 ⟨codeSupp'_supports H, contSupp_supports (Finset.union_subset_right H)⟩

/--
theorem `tr_supports` / 定理 `tr_supports`

English:
theorem tr_supports
  given: (c k)
  statement: @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (codeSupp c k)
  proof: ⟨codeSupp_self _ _ (trStmts₁_self _), fun _ => codeSupp_supports (Finset.Subset.refl _) _⟩

中文:
定理 tr_supports
  条件: (c k)
  结论: @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (codeSupp c k)
  证明: ⟨codeSupp_self _ _ (trStmts₁_self _), fun _ => codeSupp_supports (Finset.Subset.refl _) _⟩

Depends on / 依赖: Finset, Finset.Subset.refl, Subset, codeSupp_self, codeSupp_supports
-/
theorem tr_supports (c k) : @TM2.Supports _ _ _ _ ⟨trNormal c k⟩ tr (codeSupp c k) :=
  ⟨codeSupp_self _ _ (trStmts₁_self _), fun _ => codeSupp_supports (Finset.Subset.refl _) _⟩

end

end PartrecToTM2

end Turing
