/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Control.Functor
public import Mathlib.Data.SProd
public import Mathlib.Util.CompileInductive
public import Batteries.Tactic.Lint.Basic
public import Batteries.Data.List.Basic
public import Batteries.Logic

/-!
## Definitions on lists

This file contains various definitions on lists. It does not contain
proofs about these definitions, those are contained in other files in `Data.List`
-/

@[expose] public section

namespace List

open Function Nat

universe u v w x

variable {α β γ δ ε ζ : Type*}

/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq α] : SDiff (List α) :=
  ⟨List.diff⟩

/-- "Inhabited" `get` function: returns `default` instead of `none` in the case
  that the index is out of bounds. -/
/-
**List.getI** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：getI [Inhabited α] (l : List α) (n : Nat) : α
参数：l : List α；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Inhabited" `get` function: returns `default` instead of `none` in the case
  that the index is out of bounds.
-/
def getI [Inhabited α] (l : List α) (n : Nat) : α :=
  getD l n default

/-- The head of a list, or the default element of the type is the list is `nil`. -/
/-
**List.headI** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → [Inhabited α] → List α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The head of a list, or the default element of the type is the list is `nil`.
-/
def headI [Inhabited α] : List α → α
  | [] => default
  | (a :: _) => a
/-
**List.headI_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Inhabited α], [].headI = default
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem headI_nil [Inhabited α] : ([] : List α).headI = default := rfl
/-
**List.headI_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Inhabited α] {h : α} {t : List α}, (h :: t).headI
 = h
参数：h :: t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem headI_cons [Inhabited α] {h : α} {t : List α} : (h :: t).headI = h := rfl

/-- The last element of a list, with the default if list empty -/
/-
**List.getLastI** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → [Inhabited α] → List α → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The last element of a list, with the default if list empty
-/
def getLastI [Inhabited α] : List α → α
  | [] => default
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => getLastI l

/-- "Inhabited" `take` function: Take `n` elements from a list `l`. If `l` has less than `n`
  elements, append `n - length l` elements `default`. -/
/-
**List.takeI** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：takeI [Inhabited α] (n : Nat) (l : List α) : List α
参数：n : Nat；l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Inhabited" `take` function: Take `n` elements from a list `l`. If `l` has less 
than `n`
  elements, append `n - length l` elements `default`.
-/
def takeI [Inhabited α] (n : Nat) (l : List α) : List α :=
  takeD n l default

/-- `findM tac l` returns the first element of `l` on which `tac` succeeds, and
fails otherwise. -/
/-
**List.findM** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：findM {α} {m : Type u -> Type v} [Alternative m] (tac : α -> m PUnit) : Li
st α -> m α
参数：tac : α -> m PUnit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`findM tac l` returns the first element of `l` on which `tac` succeeds, and
fails otherwise.
-/
def findM {α} {m : Type u → Type v} [Alternative m] (tac : α → m PUnit) : List α → m α :=
  List.firstM fun a => (tac a) $> a

/-- `findM? p l` returns the first element `a` of `l` for which `p a` returns
true. `findM?` short-circuits, so `p` is not necessarily run on every `a` in
`l`. This is a monadic version of `List.find`. -/
/-
**List.findM** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：findM {α} {m : Type u -> Type v} [Alternative m] (tac : α -> m PUnit) : Li
st α -> m α
参数：tac : α -> m PUnit。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`findM? p l` returns the first element `a` of `l` for which `p a` returns
true. `findM?` short-circuits, so `p` is not necessarily run on every `a` in
`l`. This is a monadic version of `List.find`.
-/
def findM?'
    {m : Type u → Type v}
    [Monad m] {α : Type u}
    (p : α → m (ULift Bool)) : List α → m (Option α)
  | [] => pure none
  | x :: xs => do
    let ⟨px⟩ ← p x
    if px then pure (some x) else findM?' p xs

section

variable {m : Type → Type v} [Monad m]

/-- `orM xs` runs the actions in `xs`, returning true if any of them returns
true. `orM` short-circuits, so if an action returns true, later actions are
not run. -/
/-
**List.orM** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：orM : List (m Bool) -> m Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`orM xs` runs the actions in `xs`, returning true if any of them returns
true. `orM` short-circuits, so if an action returns true, later actions are
not run.
-/
def orM : List (m Bool) → m Bool :=
  anyM id

/-- `andM xs` runs the actions in `xs`, returning true if all of them return
true. `andM` short-circuits, so if an action returns false, later actions are
not run. -/
/-
**List.andM** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：andM : List (m Bool) -> m Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`andM xs` runs the actions in `xs`, returning true if all of them return
true. `andM` short-circuits, so if an action returns false, later actions are
not run.
-/
def andM : List (m Bool) → m Bool :=
  allM id

end

section foldIdxM

variable {m : Type v → Type w} [Monad m]

/-- Monadic variant of `foldlIdx`. -/
/-
**List.foldlIdxM** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：foldlIdxM {α β} (f : Nat -> β -> α -> m β) (b : β) (as : List α) : m β
参数：f : Nat -> β -> α -> m β；b : β；as : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monadic variant of `foldlIdx`.
-/
def foldlIdxM {α β} (f : ℕ → β → α → m β) (b : β) (as : List α) : m β :=
  as.foldlIdx
    (fun i ma b => do
      let a ← ma
      f i a b)
    (pure b)

/-- Monadic variant of `foldrIdx`. -/
/-
**List.foldrIdxM** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：foldrIdxM {α β} (f : Nat -> α -> β -> m β) (b : β) (as : List α) : m β
参数：f : Nat -> α -> β -> m β；b : β；as : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Monadic variant of `foldrIdx`.
-/
def foldrIdxM {α β} (f : ℕ → α → β → m β) (b : β) (as : List α) : m β :=
  as.foldrIdx
    (fun i a mb => do
      let b ← mb
      f i a b)
    (pure b)

end foldIdxM


section mapIdxM

-- This could be relaxed to `Applicative` but is `Monad` to match `List.mapIdxM`.
variable {m : Type v → Type w} [Monad m]

/-- Auxiliary definition for `mapIdxM'`. -/
/-
**List.mapIdxMAux'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mapIdxMAux'_eq_mapIdxMGo {α} (f : Nat -> α -> m PUnit) (as : List α) (arr 
: Array PUnit) : mapIdxMAux' f arr.size as = mapIdxM.go f as arr *> pure PUnit.u
nit
参数：f : Nat -> α -> m PUnit；as : List α；arr : Array PUnit。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `mapIdxM'`.
-/
def mapIdxMAux' {α} (f : ℕ → α → m PUnit) : ℕ → List α → m PUnit
  | _, [] => pure ⟨⟩
  | i, a :: as => f i a *> mapIdxMAux' f (i + 1) as

/-- A variant of `mapIdxM` specialised to applicative actions which
return `Unit`. -/
/-
**List.mapIdxM'** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：mapIdxM' {α} (f : Nat -> α -> m PUnit) (as : List α) : m PUnit
参数：f : Nat -> α -> m PUnit；as : List α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.mapIdxMAux'`：mapIdxMAux'_eq_mapIdxMGo {α} (f : Nat -> α -> m PUnit)
 (as : List α) (arr : Array PUnit) : mapIdxMAux' f arr.size as = mapIdxM.go f as
 arr *…

--- 原说明 ---
A variant of `mapIdxM` specialised to applicative actions which
return `Unit`.
-/
def mapIdxM' {α} (f : ℕ → α → m PUnit) (as : List α) : m PUnit :=
  mapIdxMAux' f 0 as

end mapIdxM

/-- `l.Forall p` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction, i.e.
`List.Forall p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp]
/-
**List.Forall** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → Prop) → List α → Prop
参数：α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`l.Forall p` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunct
ion, i.e.
`List.Forall p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`.
-/
def Forall (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l

section Permutations

/-- An auxiliary function for defining `permutations`. `permutationsAux2 t ts r ys f` is equal to
`(ys ++ ts, (insert_left ys t ts).map f ++ r)`, where `insert_left ys t ts` (not explicitly
defined) is the list of lists of the form `insert_nth n t (ys ++ ts)` for `0 ≤ n < length ys`.

```
    permutations_aux2 10 [4, 5, 6] [] [1, 2, 3] id =
      ([1, 2, 3, 4, 5, 6],
       [[10, 1, 2, 3, 4, 5, 6],
        [1, 10, 2, 3, 4, 5, 6],
        [1, 2, 10, 3, 4, 5, 6]])
```
-/
/-
**List.permutationsAux2** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：permutationsAux2 (t : α) (ts : List α) (r : List β) : List α -> (List α ->
 β) -> List α × List β | [], _ => (ts, r) | y :: ys, f => let (us, zs)
参数：t : α；ts : List α；r : List β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary function for defining `permutations`. `permutationsAux2 t ts r ys f
` is equal to
`(ys ++ ts, (insert_left ys t ts).map f ++ r)`, where `insert_left ys t ts` (not
 explicitly
defined) is the list of lists of the form `insert_nth n t (ys ++ ts)` for `0 ≤ n
 < length ys`.

```
    permutations_aux2 10 [4, 5, 6] [] [1, 2, 3] id =
      ([1, 2, 3, 4, 5, 6],
       [[10, 1, 2, 3, 4, 5, 6],
        [1, 10, 2, 3, 4, 5, 6],
        [1, 2, 10, 3, 4, 5, 6]])
```
-/
def permutationsAux2 (t : α) (ts : List α) (r : List β) : List α → (List α → β) → List α × List β
  | [], _ => (ts, r)
  | y :: ys, f =>
    let (us, zs) := permutationsAux2 t ts r ys (fun x : List α => f (y :: x))
    (y :: us, f (t :: y :: us) :: zs)

/-- A recursor for pairs of lists. To have `C l₁ l₂` for all `l₁`, `l₂`, it suffices to have it for
`l₂ = []` and to be able to pour the elements of `l₁` into `l₂`. -/
@[elab_as_elim]
/-
**List.permutationsAux.rec** 是 Mathlib 中的一个定义，位于命名空间 `List.permutationsAux`。
形式化陈述：{α : Type u_1} →   {C : List α → List α → Sort v} →     ((is : List α) → C
 [] is) →       ((t : α) → (ts is : List α) → C ts (t :: is) → C is [] → C (t ::
 ts) is) → (l₁ l₂ : List α) → C l₁ l₂
参数：(is : List α) → C [] is；(t : α) → (ts is : List α) → C ts (t :: is) → C is []
 → C (t :: ts) is；l₁ l₂ : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for pairs of lists. To have `C l₁ l₂` for all `l₁`, `l₂`, it suffices
 to have it for
`l₂ = []` and to be able to pour the elements of `l₁` into `l₂`.
-/
def permutationsAux.rec {C : List α → List α → Sort v} (H0 : ∀ is, C [] is)
    (H1 : ∀ t ts is, C ts (t :: is) → C is [] → C (t :: ts) is) : ∀ l₁ l₂, C l₁ l₂
  | [], is => H0 is
  | t :: ts, is =>
      H1 t ts is (permutationsAux.rec H0 H1 ts (t :: is)) (permutationsAux.rec H0 H1 is [])
  termination_by ts is => (length ts + length is, length ts)
  decreasing_by all_goals (simp_wf; grind)

/-- An auxiliary function for defining `permutations`. `permutationsAux ts is` is the set of all
permutations of `is ++ ts` that do not fix `ts`. -/
/-
**List.permutationsAux** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：permutationsAux : List α -> List α -> List (List α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary function for defining `permutations`. `permutationsAux ts is` is th
e set of all
permutations of `is ++ ts` that do not fix `ts`.
-/
def permutationsAux : List α → List α → List (List α) :=
  permutationsAux.rec (fun _ => []) fun t ts is IH1 IH2 =>
    foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)

/-- List of all permutations of `l`.

```
     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]]
```
-/
/-
**List.permutations** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：permutations (l : List α) : List (List α)
参数：l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
List of all permutations of `l`.

```
     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [3, 2, 1],
        [2, 3, 1], [3, 1, 2], [1, 3, 2]]
```
-/
def permutations (l : List α) : List (List α) :=
  l :: permutationsAux l []

/-- `permutations'Aux t ts` inserts `t` into every position in `ts`, including the last.
This function is intended for use in specifications, so it is simpler than `permutationsAux2`,
which plays roughly the same role in `permutations`.

Note that `(permutationsAux2 t [] [] ts id).2` is similar to this function, but skips the last
position:

```
    permutations'Aux 10 [1, 2, 3] =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3], [1, 2, 3, 10]]
    (permutationsAux2 10 [] [] [1, 2, 3] id).2 =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3]]
```
-/
@[simp]
/-
**List.permutations'Aux** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → α → List α → List (List α)
参数：List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`permutations'Aux t ts` inserts `t` into every position in `ts`, including the l
ast.
This function is intended for use in specifications, so it is simpler than `perm
utationsAux2`,
which plays roughly the same role in `permutations`.

Note that `(permutationsAux2 t [] [] ts id).2` is similar to this function, but 
skips the last
position:

```
    permutations'Aux 10 [1, 2, 3] =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3], [1, 2, 3, 10]]
    (permutationsAux2 10 [] [] [1, 2, 3] id).2 =
      [[10, 1, 2, 3], [1, 10, 2, 3], [1, 2, 10, 3]]
```
-/
def permutations'Aux (t : α) : List α → List (List α)
  | [] => [[t]]
  | y :: ys => (t :: y :: ys) :: (permutations'Aux t ys).map (cons y)

/-- List of all permutations of `l`. This version of `permutations` is less efficient but has
simpler definitional equations. The permutations are in a different order,
but are equal up to permutation, as shown by `List.permutations_perm_permutations'`.

```
     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 3, 2], [3, 1, 2], [3, 2, 1]]
```
-/
@[simp]
/-
**List.permutations'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：permutations'Aux_eq_permutationsAux2 (t : α) (ts : List α) : permutations'
Aux t ts = (permutationsAux2 t [] [ts ++ [t]] ts id).2
参数：t : α；ts : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
List of all permutations of `l`. This version of `permutations` is less efficien
t but has
simpler definitional equations. The permutations are in a different order,
but are equal up to permutation, as shown by `List.permutations_perm_permutation
s'`.

```
     permutations [1, 2, 3] =
       [[1, 2, 3], [2, 1, 3], [2, 3, 1],
        [1, 3, 2], [3, 1, 2], [3, 2, 1]]
```
-/
def permutations' : List α → List (List α)
  | [] => [[]]
  | t :: ts => (permutations' ts).flatMap <| permutations'Aux t

end Permutations

/-- `extractp p l` returns a pair of an element `a` of `l` satisfying the predicate
  `p`, and `l`, with `a` removed. If there is no such element `a` it returns `(none, l)`. -/
/-
**List.extractp** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：extractp (p : α -> Prop) [DecidablePred p] : List α -> Option α × List α |
 [] => (none, []) | a :: l => if p a then (some a, l) else let (a', l')
参数：p : α -> Prop。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`extractp p l` returns a pair of an element `a` of `l` satisfying the predicate
  `p`, and `l`, with `a` removed. If there is no such element `a` it returns `(n
one, l)`.
-/
def extractp (p : α → Prop) [DecidablePred p] : List α → Option α × List α
  | [] => (none, [])
  | a :: l =>
    if p a then (some a, l)
    else
      let (a', l') := extractp p l
      (a', a :: l')

/-- Notation for calculating the product of a `List` -/
/-
**List.instSProd** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：instSProd : SProd (List α) (List β) (List (α × β)) where sprod
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Notation for calculating the product of a `List`
-/
instance instSProd : SProd (List α) (List β) (List (α × β)) where
  sprod := List.product

/-- `dedup l` removes duplicates from `l` (taking only the last occurrence).
Defined as `pwFilter (≠)`.

See also `eraseDups` which keeps the first occurrence instead:
```
dedup [2, 0, 1, 0, 2, 0] = [1, 2, 0]
eraseDups [2, 0, 1, 0, 2, 0] = [2, 0, 1]
``` -/
/-
**List.dedup** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：dedup [DecidableEq α] : List α -> List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`dedup l` removes duplicates from `l` (taking only the last occurrence).
Defined as `pwFilter (≠)`.

See also `eraseDups` which keeps the first occurrence instead:
```
dedup [2, 0, 1, 0, 2, 0] = [1, 2, 0]
eraseDups [2, 0, 1, 0, 2, 0] = [2, 0, 1]
```
-/
def dedup [DecidableEq α] : List α → List α :=
  pwFilter (· ≠ ·)

/-- Greedily create a sublist of `a :: l` such that, for every two adjacent elements `a, b`,
`R a b` holds. Mostly used with ≠; for example, `destutter' (≠) 1 [2, 2, 1, 1] = [1, 2, 1]`,
`destutter' (≠) 1, [2, 3, 3] = [1, 2, 3]`, `destutter' (<) 1 [2, 5, 2, 3, 4, 9] = [1, 2, 5, 9]`. -/
/-
**List.destutter'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：destutter'_nil : destutter' R a [] = [a]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Greedily create a sublist of `a :: l` such that, for every two adjacent elements
 `a, b`,
`R a b` holds. Mostly used with ≠; for example, `destutter' (≠) 1 [2, 2, 1, 1] =
 [1, 2, 1]`,
`destutter' (≠) 1, [2, 3, 3] = [1, 2, 3]`, `destutter' (<) 1 [2, 5, 2, 3, 4, 9] 
= [1, 2, 5, 9]`.
-/
def destutter' (R : α → α → Prop) [DecidableRel R] : α → List α → List α
  | a, [] => [a]
  | a, h :: l => if R a h then a :: destutter' R h l else destutter' R a l

-- TODO: should below be "lazily"?
-- TODO: Remove destutter' as we have removed chain'
/-- Greedily create a sublist of `l` such that, for every two adjacent elements `a, b ∈ l`,
`R a b` holds. Mostly used with ≠; for example, `destutter (≠) [1, 2, 2, 1, 1] = [1, 2, 1]`,
`destutter (≠) [1, 2, 3, 3] = [1, 2, 3]`, `destutter (<) [1, 2, 5, 2, 3, 4, 9] = [1, 2, 5, 9]`. -/
/-
**List.destutter** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (R : α → α → Prop) → [DecidableRel R] → List α → List α
参数：R : α → α → Prop。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.destutter'`：destutter'_nil : destutter' R a [] = [a]

--- 原说明 ---
Greedily create a sublist of `l` such that, for every two adjacent elements `a, 
b ∈ l`,
`R a b` holds. Mostly used with ≠; for example, `destutter (≠) [1, 2, 2, 1, 1] =
 [1, 2, 1]`,
`destutter (≠) [1, 2, 3, 3] = [1, 2, 3]`, `destutter (<) [1, 2, 5, 2, 3, 4, 9] =
 [1, 2, 5, 9]`.
-/
def destutter (R : α → α → Prop) [DecidableRel R] : List α → List α
  | h :: l => destutter' R h l
  | [] => []

section Choose

variable (p : α → Prop) [DecidablePred p] (l : List α)

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns both `a` and proofs
of `a ∈ l` and `p a`. -/
/-
**List.chooseX** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：chooseX : forall l : List α, forall _ : exists a, a in l ∧ p a, { a // a i
n l ∧ p a } | [], hp => False.elim (Exists.elim hp fun _ h => not_mem_nil h.left
) | l :: ls, hp => if pl : p l then ⟨l, ⟨mem_cons.mpr Or.inl rfl, pl⟩⟩ else -- p
attern matching on `hx` too makes this not reducible! let ⟨a, ha⟩
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p
 a`,
choose the first element with this property. This version returns both `a` and p
roofs
of `a ∈ l` and `p a`.
-/
def chooseX : ∀ l : List α, ∀ _ : ∃ a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a }
  | [], hp => False.elim (Exists.elim hp fun _ h => not_mem_nil h.left)
  | l :: ls, hp =>
    if pl : p l then ⟨l, ⟨mem_cons.mpr <| Or.inl rfl, pl⟩⟩
    else
      -- pattern matching on `hx` too makes this not reducible!
      let ⟨a, ha⟩ :=
        chooseX ls
          (hp.imp fun _ ⟨o, h₂⟩ => ⟨(mem_cons.mp o).resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
      ⟨a, mem_cons.mpr <| Or.inr ha.1, ha.2⟩

/-- Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p a`,
choose the first element with this property. This version returns `a : α`, and properties
are given by `choose_mem` and `choose_property`. -/
/-
**List.choose** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：choose (hp : exists a, a in l ∧ p a) : α
参数：hp : exists a, a in l ∧ p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a decidable predicate `p` and a proof of existence of `a ∈ l` such that `p
 a`,
choose the first element with this property. This version returns `a : α`, and p
roperties
are given by `choose_mem` and `choose_property`.
-/
def choose (hp : ∃ a, a ∈ l ∧ p a) : α :=
  chooseX p l hp

end Choose

/-- `mapDiagM' f l` calls `f` on all elements in the upper triangular part of `l × l`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mapDiagM' f l` will evaluate, in this order,
`f 1 1`, `f 1 2`, `f 1 3`, `f 2 2`, `f 2 3`, `f 3 3`.
-/
/-
**List.mapDiagM'** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{m : Type → Type u_7} → [Monad m] → {α : Type u_8} → (α → α → m Unit) → Li
st α → m Unit
参数：α → α → m Unit。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mapDiagM' f l` calls `f` on all elements in the upper triangular part of `l × l
`.
That is, for each `e ∈ l`, it will run `f e e` and then `f e e'`
for each `e'` that appears after `e` in `l`.

Example: suppose `l = [1, 2, 3]`. `mapDiagM' f l` will evaluate, in this order,
`f 1 1`, `f 1 2`, `f 1 3`, `f 2 2`, `f 2 3`, `f 3 3`.
-/
def mapDiagM' {m} [Monad m] {α} (f : α → α → m Unit) : List α → m Unit
  | [] => return ()
  | h :: t => do
    _ ← f h h
    _ ← t.mapM' (f h)
    t.mapDiagM' f
-- as ported:
--   | [] => return ()
--   | h :: t => (f h h >> t.mapM' (f h)) >> t.mapDiagM'

/-- Left-biased version of `List.map₂`. `map₂Left' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.

```
map₂Left' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

map₂Left' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left-biased version of `List.map₂`. `map₂Left' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is
applied to `none` for the remaining `aᵢ`. Returns the results of the `f`
applications and the remaining `bs`.

```
map₂Left' prod.mk [1, 2] ['a'] = ([(1, some 'a'), (2, none)], [])

map₂Left' prod.mk [1] ['a', 'b'] = ([(1, some 'a')], ['b'])
```
-/
def map₂Left' (f : α → Option β → γ) : List α → List β → List γ × List β
  | [], bs => ([], bs)
  | a :: as, [] => ((a :: as).map fun a => f a none, [])
  | a :: as, b :: bs =>
    let rec' := map₂Left' f as bs
    (f a (some b) :: rec'.fst, rec'.snd)

/-- Right-biased version of `List.map₂`. `map₂Right' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.

```
map₂Right' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

map₂Right' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right-biased version of `List.map₂`. `map₂Right' f as bs` applies `f` to each
pair of elements `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is
applied to `none` for the remaining `bᵢ`. Returns the results of the `f`
applications and the remaining `as`.

```
map₂Right' prod.mk [1] ['a', 'b'] = ([(some 1, 'a'), (none, 'b')], [])

map₂Right' prod.mk [1, 2] ['a'] = ([(some 1, 'a')], [2])
```
-/
def map₂Right' (f : Option α → β → γ) (as : List α) (bs : List β) : List γ × List α :=
  map₂Left' (flip f) bs as


/-- Left-biased version of `List.map₂`. `map₂Left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.

```
map₂Left Prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]

map₂Left Prod.mk [1] ['a', 'b'] = [(1, some 'a')]

map₂Left f as bs = (map₂Left' f as bs).fst
```
-/
@[simp]
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left-biased version of `List.map₂`. `map₂Left f as bs` applies `f` to each pair
`aᵢ ∈ as` and `bᵢ ∈ bs`. If `bs` is shorter than `as`, `f` is applied to `none`
for the remaining `aᵢ`.

```
map₂Left Prod.mk [1, 2] ['a'] = [(1, some 'a'), (2, none)]

map₂Left Prod.mk [1] ['a', 'b'] = [(1, some 'a')]

map₂Left f as bs = (map₂Left' f as bs).fst
```
-/
def map₂Left (f : α → Option β → γ) : List α → List β → List γ
  | [], _ => []
  | a :: as, [] => (a :: as).map fun a => f a none
  | a :: as, b :: bs => f a (some b) :: map₂Left f as bs

/-- Right-biased version of `List.map₂`. `map₂Right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.

```
map₂Right Prod.mk [1, 2] ['a'] = [(some 1, 'a')]

map₂Right Prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

map₂Right f as bs = (map₂Right' f as bs).fst
```
-/
/-
**List.map** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (α → β) → List α → List β
参数：α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right-biased version of `List.map₂`. `map₂Right f as bs` applies `f` to each
pair `aᵢ ∈ as` and `bᵢ ∈ bs`. If `as` is shorter than `bs`, `f` is applied to
`none` for the remaining `bᵢ`.

```
map₂Right Prod.mk [1, 2] ['a'] = [(some 1, 'a')]

map₂Right Prod.mk [1] ['a', 'b'] = [(some 1, 'a'), (none, 'b')]

map₂Right f as bs = (map₂Right' f as bs).fst
```
-/
def map₂Right (f : Option α → β → γ) (as : List α) (bs : List β) : List γ :=
  map₂Left (flip f) bs as

-- TODO: naming is awkward...
/-- Asynchronous version of `List.map`.
-/
/-
**List.mapAsyncChunked** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：mapAsyncChunked {α β} (f : α -> β) (xs : List α) (chunk_size
参数：f : α -> β；xs : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Asynchronous version of `List.map`.
-/
def mapAsyncChunked {α β} (f : α → β) (xs : List α) (chunk_size := 1024) : List β :=
  ((xs.toChunks chunk_size).map fun xs => Task.spawn fun _ => List.map f xs).flatMap Task.get


/-!
We add some n-ary versions of `List.zipWith` for functions with more than two arguments.
These can also be written in terms of `List.zip` or `List.zipWith`.
For example, `zipWith3 f xs ys zs` could also be written as
`zipWith id (zipWith f xs ys) zs`
or as
`(zip xs <| zip ys zs).map <| fun ⟨x, y, z⟩ ↦ f x y z`.
-/

/-- Ternary version of `List.zipWith`. -/
/-
**List.zipWith3** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → {δ : Type u_4} → (α → β
 → γ → δ) → List α → List β → List γ → List δ
参数：α → β → γ → δ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Ternary version of `List.zipWith`.
-/
def zipWith3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: zipWith3 f xs ys zs
  | _, _, _ => []

/-- Quaternary version of `list.zipWith`. -/
/-
**List.zipWith4** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} → {δ : Type u_4} → 
{ε : Type u_5} → (α → β → γ → δ → ε) → List α → List β → List γ → List δ → List 
ε
参数：α → β → γ → δ → ε。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quaternary version of `list.zipWith`.
-/
def zipWith4 (f : α → β → γ → δ → ε) : List α → List β → List γ → List δ → List ε
  | x :: xs, y :: ys, z :: zs, u :: us => f x y z u :: zipWith4 f xs ys zs us
  | _, _, _, _ => []

/-- Quinary version of `list.zipWith`. -/
/-
**List.zipWith5** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} →       {δ : Type u
_4} →         {ε : Type u_5} → {ζ : Type u_6} → (α → β → γ → δ → ε → ζ) → List α
 → List β → List γ → List δ → List ε → List ζ
参数：α → β → γ → δ → ε → ζ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quinary version of `list.zipWith`.
-/
def zipWith5 (f : α → β → γ → δ → ε → ζ) : List α → List β → List γ → List δ → List ε → List ζ
  | x :: xs, y :: ys, z :: zs, u :: us, v :: vs => f x y z u v :: zipWith5 f xs ys zs us vs
  | _, _, _, _, _ => []

/-- Given a starting list `old`, a list of Booleans and a replacement list `new`,
read the items in `old` in succession and either replace them with the next element of `new` or
not, according as to whether the corresponding Boolean is `true` or `false`. -/
/-
**List.replaceIf** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → List α → List Bool → List α → List α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a starting list `old`, a list of Booleans and a replacement list `new`,
read the items in `old` in succession and either replace them with the next elem
ent of `new` or
not, according as to whether the corresponding Boolean is `true` or `false`.
-/
def replaceIf : List α → List Bool → List α → List α
  | l, _, [] => l
  | [], _, _ => []
  | l, [], _ => l
  | n :: ns, tf :: bs, e@(c :: cs) => if tf then c :: ns.replaceIf bs cs else n :: ns.replaceIf bs e

/-- `iterate f a n` is `[a, f a, ..., f^[n - 1] a]`. -/
@[simp]
/-
**List.iterate** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (α → α) → α → ℕ → List α
参数：α → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`iterate f a n` is `[a, f a, ..., f^[n - 1] a]`.
-/
def iterate (f : α → α) (a : α) : (n : ℕ) → List α
  | 0 => []
  | n + 1 => a :: iterate f (f a) n

/-- Tail-recursive version of `List.iterate`. -/
@[inline]
/-
**List.iterateTR** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：iterateTR (f : α -> α) (a : α) (n : Nat) : List α
参数：f : α -> α；a : α；n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tail-recursive version of `List.iterate`.
-/
def iterateTR (f : α → α) (a : α) (n : ℕ) : List α :=
  loop a n []
where
  /-- `iterateTR.loop f a n l := iterate f a n ++ reverse l`. -/
  @[simp, specialize]
  loop (a : α) (n : ℕ) (l : List α) : List α :=
    match n with
    | 0 => reverse l
    | n + 1 => loop (f a) n (a :: l)
/-
**List.iterateTR_loop_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：iterateTR_loop_eq (f : α -> α) (a : α) (n : Nat) (l : List α) : iterateTR.
loop f a n l = reverse l ++ iterate f a n
参数：f : α -> α；a : α；n : Nat；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
-/
theorem iterateTR_loop_eq (f : α → α) (a : α) (n : ℕ) (l : List α) :
    iterateTR.loop f a n l = reverse l ++ iterate f a n := by
  induction n generalizing a l <;> simp [*]

@[csimp]
/-
**List.iterate_eq_iterateTR** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：iterate_eq_iterateTR : @iterate = @iterateTR
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.iterateTR_loop_eq`：iterateTR_loop_eq (f : α -> α) (a : α) (n : Nat)
 (l : List α) : iterateTR.loop f a n l = reverse l ++ iterate f a n
-/
theorem iterate_eq_iterateTR : @iterate = @iterateTR := by
  funext α f a n
  exact Eq.symm <| iterateTR_loop_eq f a n []

section MapAccumr

/-- Runs a function over a list returning the intermediate results and a final result. -/
/-
**List.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：mapAccumr (f : α -> γ -> γ × β) : List α -> γ -> γ × List β | [], c => (c,
 []) | y :: yr, c => let r
参数：f : α -> γ -> γ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Runs a function over a list returning the intermediate results and a final resul
t.
-/
def mapAccumr (f : α → γ → γ × β) : List α → γ → γ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)

/-- Length of the list obtained by `mapAccumr`. -/
@[simp]
/-
**List.length_mapAccumr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → γ → γ × β) (x : Li
st α) (s : γ),   (List.mapAccumr f x s).2.length = x.length
参数：f : α → γ → γ × β；x : List α；s : γ；List.mapAccumr f x s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Length of the list obtained by `mapAccumr`.
-/
theorem length_mapAccumr :
    ∀ (f : α → γ → γ × β) (x : List α) (s : γ), length (mapAccumr f x s).2 = length x
  | f, _ :: x, s => congr_arg succ (length_mapAccumr f x s)
  | _, [], _ => rfl

/-- Runs a function over two lists returning the intermediate results and a final result. -/
/-
**List.mapAccumr** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：mapAccumr (f : α -> γ -> γ × β) : List α -> γ -> γ × List β | [], c => (c,
 []) | y :: yr, c => let r
参数：f : α -> γ -> γ × β。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Runs a function over two lists returning the intermediate results and a final re
sult.
-/
def mapAccumr₂ (f : α → β → γ → γ × δ) : List α → List β → γ → γ × List δ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)

/-- Length of a list obtained using `mapAccumr₂`. -/
@[simp]
/-
**List.length_mapAccumr** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α → γ → γ × β) (x : Li
st α) (s : γ),   (List.mapAccumr f x s).2.length = x.length
参数：f : α → γ → γ × β；x : List α；s : γ；List.mapAccumr f x s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Length of a list obtained using `mapAccumr₂`.
-/
theorem length_mapAccumr₂ :
    ∀ (f : α → β → γ → γ × δ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, _ :: x, _ :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congr_arg succ (length_mapAccumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (succ_min_succ (length x) (length y))
  | _, _ :: _, [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, [], [], _ => rfl

end MapAccumr

section consecutivePairs

/-- `consecutivePairs [a, b, c, d]` is `[(a, b), (b, c), (c, d)]`. -/
/-
**List.consecutivePairs** 是 Mathlib 中的一个缩写定义，位于命名空间 `List`。
形式化陈述：consecutivePairs (l : List α) : List (α × α)
参数：l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`consecutivePairs [a, b, c, d]` is `[(a, b), (b, c), (c, d)]`.
-/
abbrev consecutivePairs (l : List α) : List (α × α) := l.zip l.tail

end consecutivePairs

end List

