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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : SDiff (List α)
  body: ⟨List.diff⟩

中文:
实例 [DecidableEq
  签名: α] : 对称差 (列表 α)
  定义体: ⟨List.diff⟩

Depends on / 依赖: List.diff
-/
instance [DecidableEq α] : SDiff (List α) :=
  ⟨List.diff⟩

/--
Definition of `getI` / `getI` 的定义

English:
definition getI
  signature: [Inhabited α] (l : List α) (n : Nat)
  body: getD l n default

中文:
定义 getI
  签名: [可居 α] (l : 列表 α) (n : 自然数)
  定义体: getD l n default
-/
def getI [Inhabited α] (l : List α) (n : Nat) : α :=
  getD l n default

/--
Definition of `headI` / `headI` 的定义

English:
definition headI
  signature: [Inhabited α]

中文:
定义 headI
  签名: [可居 α]
-/
def headI [Inhabited α] : List α -> α
  | [] => default
  | (a :: _) => a

/--
theorem `headI_nil` / 定理 `headI_nil`

English:
theorem headI_nil
  given: [Inhabited α]
  statement: ([] : List α).headI = default
  proof: rfl

中文:
定理 headI_nil
  条件: [可居 α]
  结论: ([] : 列表 α).headI = default
  证明: rfl
-/
@[simp] theorem headI_nil [Inhabited α] : ([] : List α).headI = default := rfl
/--
theorem `headI_cons` / 定理 `headI_cons`

English:
theorem headI_cons
  given: [Inhabited α] {h : α} {t : List α}
  statement: (h :: t).headI = h
  proof: rfl

中文:
定理 headI_cons
  条件: [可居 α] {h : α} {t : 列表 α}
  结论: (h :: t).headI = h
  证明: rfl
-/
@[simp] theorem headI_cons [Inhabited α] {h : α} {t : List α} : (h :: t).headI = h := rfl

/--
Definition of `getLastI` / `getLastI` 的定义

English:
definition getLastI
  signature: [Inhabited α]

中文:
定义 getLastI
  签名: [可居 α]
-/
def getLastI [Inhabited α] : List α -> α
  | [] => default
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => getLastI l

/--
Definition of `takeI` / `takeI` 的定义

English:
definition takeI
  signature: [Inhabited α] (n : Nat) (l : List α)
  body: takeD n l default

中文:
定义 takeI
  签名: [可居 α] (n : 自然数) (l : 列表 α)
  定义体: takeD n l default
-/
def takeI [Inhabited α] (n : Nat) (l : List α) : List α :=
  takeD n l default

/--
Definition of `findM` / `findM` 的定义

English:
definition findM
  signature: {α} {m : Type u -> Type v} [Alternative m] (tac : α -> m PUnit)
  body: List.firstM fun a => (tac a) > a

中文:
定义 findM
  签名: {α} {m : 类型u -> 类型v} [Alternative m] (tac : α -> m 命题单元)
  定义体: List.firstM fun a => (tac a) > a

Depends on / 依赖: List.firstM, firstM
-/
def findM {α} {m : Type u -> Type v} [Alternative m] (tac : α -> m PUnit) : List α -> m α :=
List.firstM fun a => (tac a) > a

/--
Definition of `findM?'` / `findM?'` 的定义

English:
definition findM?'

中文:
定义 findM?'
-/
def findM?'
    {m : Type u -> Type v}
    [Monad m] {α : Type u}
    (p : α -> m (ULift Bool)) : List α -> m (Option α)
  | [] => pure none
  | x :: xs => do
    let ⟨px⟩ ← p x
    if px then pure (some x) else findM?' p xs

section

variable {m : Type -> Type v} [Monad m]

/--
Definition of `orM` / `orM` 的定义

English:
definition orM
  signature: : List (m Bool) -> m Bool
  body: anyM id

中文:
定义 orM
  签名: : 列表 (m 布尔值) -> m 布尔值
  定义体: anyM id
-/
def orM : List (m Bool) -> m Bool :=
  anyM id

/--
Definition of `andM` / `andM` 的定义

English:
definition andM
  signature: : List (m Bool) -> m Bool
  body: allM id

中文:
定义 andM
  签名: : 列表 (m 布尔值) -> m 布尔值
  定义体: allM id
-/
def andM : List (m Bool) -> m Bool :=
  allM id

end

section foldIdxM

variable {m : Type v -> Type w} [Monad m]

/--
Definition of `foldlIdxM` / `foldlIdxM` 的定义

English:
definition foldlIdxM
  signature: {α β} (f : Nat -> β -> α -> m β) (b : β) (as : List α)
  body: as.foldlIdx
    (fun i ma b => do
      let a ← ma
      f i a b)
    (pure b)

中文:
定义 foldlIdxM
  签名: {α β} (f : 自然数 -> β -> α -> m β) (b : β) (as : 列表 α)
  定义体: as.foldlIdx
    (fun i ma b => do
      let a ← ma
      f i a b)
    (pure b)

Depends on / 依赖: as.foldlIdx, foldlIdx
-/
def foldlIdxM {α β} (f : Nat -> β -> α -> m β) (b : β) (as : List α) : m β :=
  as.foldlIdx
    (fun i ma b => do
      let a ← ma
      f i a b)
    (pure b)

/--
Definition of `foldrIdxM` / `foldrIdxM` 的定义

English:
definition foldrIdxM
  signature: {α β} (f : Nat -> α -> β -> m β) (b : β) (as : List α)
  body: as.foldrIdx
    (fun i a mb => do
      let b ← mb
      f i a b)
    (pure b)

中文:
定义 foldrIdxM
  签名: {α β} (f : 自然数 -> α -> β -> m β) (b : β) (as : 列表 α)
  定义体: as.foldrIdx
    (fun i a mb => do
      let b ← mb
      f i a b)
    (pure b)

Depends on / 依赖: as.foldrIdx, foldrIdx
-/
def foldrIdxM {α β} (f : Nat -> α -> β -> m β) (b : β) (as : List α) : m β :=
  as.foldrIdx
    (fun i a mb => do
      let b ← mb
      f i a b)
    (pure b)

end foldIdxM


section mapIdxM

-- This could be relaxed to `Applicative` but is `Monad` to match `List.mapIdxM`.
variable {m : Type v -> Type w} [Monad m]

/--
Definition of `mapIdxMAux'` / `mapIdxMAux'` 的定义

English:
definition mapIdxMAux'
  signature: {α} (f : Nat -> α -> m PUnit)

中文:
定义 mapIdxMAux'
  签名: {α} (f : 自然数 -> α -> m 命题单元)
-/
def mapIdxMAux' {α} (f : Nat -> α -> m PUnit) : Nat -> List α -> m PUnit
  | _, [] => pure ⟨⟩
  | i, a :: as => f i a *> mapIdxMAux' f (i + 1) as

/--
Definition of `mapIdxM'` / `mapIdxM'` 的定义

English:
definition mapIdxM'
  signature: {α} (f : Nat -> α -> m PUnit) (as : List α)
  body: mapIdxMAux' f 0 as

中文:
定义 mapIdxM'
  签名: {α} (f : 自然数 -> α -> m 命题单元) (as : 列表 α)
  定义体: mapIdxMAux' f 0 as

Depends on / 依赖: mapIdxMAux
-/
def mapIdxM' {α} (f : Nat -> α -> m PUnit) (as : List α) : m PUnit :=
  mapIdxMAux' f 0 as

end mapIdxM

/-- `l.Forall p` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction, i.e.
`List.Forall p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
@[simp]
/--
Definition of `Forall` / `Forall` 的定义

English:
definition Forall
  signature: (p : α -> Prop)

中文:
定义 任意
  签名: (p : α -> 命题)
-/
def Forall (p : α -> Prop) : List α -> Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l

section Permutations

/--
Definition of `permutationsAux2` / `permutationsAux2` 的定义

English:
definition permutationsAux2
  signature: (t : α) (ts : List α) (r : List β)
  body: permutationsAux2 t ts r ys (fun x : List α => f (y :: x))
    (y :: us, f (t :: y :: us) :: zs)

中文:
定义 permutationsAux2
  签名: (t : α) (ts : 列表 α) (r : 列表 β)
  定义体: permutationsAux2 t ts r ys (fun x : List α => f (y :: x))
    (y :: us, f (t :: y :: us) :: zs)

Depends on / 依赖: permutationsAux2
-/
def permutationsAux2 (t : α) (ts : List α) (r : List β) : List α -> (List α -> β) -> List α × List β
  | [], _ => (ts, r)
  | y :: ys, f =>
    let (us, zs) := permutationsAux2 t ts r ys (fun x : List α => f (y :: x))
    (y :: us, f (t :: y :: us) :: zs)

/-- A recursor for pairs of lists. To have `C l₁ l₂` for all `l₁`, `l₂`, it suffices to have it for
`l₂ = []` and to be able to pour the elements of `l₁` into `l₂`. -/
@[elab_as_elim]
/--
Definition of `permutationsAux.rec` / `permutationsAux.rec` 的定义

English:
definition permutationsAux.rec
  signature: {C : List α -> List α -> Sort v} (H0 : forall is, C [] is)

中文:
定义 permutationsAux.rec
  签名: {C : 列表 α -> 列表 α -> 类型层 v} (H0 : 对任意 is, C [] is)
-/
def permutationsAux.rec {C : List α -> List α -> Sort v} (H0 : forall is, C [] is)
    (H1 : forall t ts is, C ts (t :: is) -> C is [] -> C (t :: ts) is) : forall l₁ l₂, C l₁ l₂
  | [], is => H0 is
  | t :: ts, is =>
      H1 t ts is (permutationsAux.rec H0 H1 ts (t :: is)) (permutationsAux.rec H0 H1 is [])
  termination_by ts is => (length ts + length is, length ts)
  decreasing_by all_goals (simp_wf; grind)

/--
Definition of `permutationsAux` / `permutationsAux` 的定义

English:
definition permutationsAux
  signature: : List α -> List α -> List (List α)
  body: permutationsAux.rec (fun _ => []) fun t ts is IH1 IH2 =>
    foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)

中文:
定义 permutationsAux
  签名: : 列表 α -> 列表 α -> 列表 (列表 α)
  定义体: permutationsAux.rec (fun _ => []) fun t ts is IH1 IH2 =>
    foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)

Depends on / 依赖: permutationsAux, permutationsAux.rec, permutationsAux2
-/
def permutationsAux : List α -> List α -> List (List α) :=
  permutationsAux.rec (fun _ => []) fun t ts is IH1 IH2 =>
    foldr (fun y r => (permutationsAux2 t ts r y id).2) IH1 (is :: IH2)

/--
Definition of `permutations` / `permutations` 的定义

English:
definition permutations
  signature: (l : List α)
  body: l :: permutationsAux l []

中文:
定义 permutations
  签名: (l : 列表 α)
  定义体: l :: permutationsAux l []

Depends on / 依赖: permutationsAux
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
/--
Definition of `permutations'Aux` / `permutations'Aux` 的定义

English:
definition permutations'Aux
  signature: (t : α)

中文:
定义 permutations'Aux
  签名: (t : α)
-/
def permutations'Aux (t : α) : List α -> List (List α)
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
/--
Definition of `permutations'` / `permutations'` 的定义

English:
definition permutations'
  signature: : List α -> List (List α)

中文:
定义 permutations'
  签名: : 列表 α -> 列表 (列表 α)
-/
def permutations' : List α -> List (List α)
  | [] => [[]]
| t :: ts => (permutations' ts).flatMap permutations'Aux t

end Permutations

/--
Definition of `extractp` / `extractp` 的定义

English:
definition extractp
  signature: (p : α -> Prop) [DecidablePred p]
  body: extractp p l
      (a', a :: l')

中文:
定义 extractp
  签名: (p : α -> 命题) [DecidablePred p]
  定义体: extractp p l
      (a', a :: l')

Depends on / 依赖: extractp
-/
def extractp (p : α -> Prop) [DecidablePred p] : List α -> Option α × List α
  | [] => (none, [])
  | a :: l =>
    if p a then (some a, l)
    else
      let (a', l') := extractp p l
      (a', a :: l')

/--
Instance `instSProd` / 实例 `instSProd`

English:
instance instSProd
  signature: : SProd (List α) (List β) (List (α × β)) where
  body: List.product

中文:
实例 instSProd
  签名: : SProd (列表 α) (列表 β) (列表 (α × β)) where
  定义体: List.product

Depends on / 依赖: List.product, product
-/
instance instSProd : SProd (List α) (List β) (List (α × β)) where
  sprod := List.product

/--
Definition of `dedup` / `dedup` 的定义

English:
definition dedup
  signature: [DecidableEq α]
  body: pwFilter (· != ·)

中文:
定义 dedup
  签名: [DecidableEq α]
  定义体: pwFilter (· != ·)

Depends on / 依赖: pwFilter
-/
def dedup [DecidableEq α] : List α -> List α :=
  pwFilter (· != ·)

/--
Definition of `destutter'` / `destutter'` 的定义

English:
definition destutter'
  signature: (R : α -> α -> Prop) [DecidableRel R]

中文:
定义 destutter'
  签名: (R : α -> α -> 命题) [DecidableRel R]
-/
def destutter' (R : α -> α -> Prop) [DecidableRel R] : α -> List α -> List α
  | a, [] => [a]
  | a, h :: l => if R a h then a :: destutter' R h l else destutter' R a l

-- TODO: should below be "lazily"?
-- TODO: Remove destutter' as we have removed chain'
/--
Definition of `destutter` / `destutter` 的定义

English:
definition destutter
  signature: (R : α -> α -> Prop) [DecidableRel R]

中文:
定义 destutter
  签名: (R : α -> α -> 命题) [DecidableRel R]
-/
def destutter (R : α -> α -> Prop) [DecidableRel R] : List α -> List α
  | h :: l => destutter' R h l
  | [] => []

section Choose

variable (p : α -> Prop) [DecidablePred p] (l : List α)

/--
Definition of `chooseX` / `chooseX` 的定义

English:
definition chooseX
  signature: : forall l : List α, forall _ : exists a, a in l ∧ p a, { a // a in l ∧ p a }
  body: chooseX ls
          (hp.imp fun _ ⟨o, h₂⟩ => ⟨(mem_cons.mp o).resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
⟨a, mem_cons.mpr Or.inr ha.1, ha.2⟩

中文:
定义 chooseX
  签名: : 对任意 l : 列表 α, 对任意 _ : 存在 a, a in l ∧ p a, { a // a in l ∧ p a }
  定义体: chooseX ls
          (hp.imp fun _ ⟨o, h₂⟩ => ⟨(mem_cons.mp o).resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
⟨a, mem_cons.mpr Or.inr ha.1, ha.2⟩

Depends on / 依赖: Or.inr, chooseX, hp.imp, mem_cons, mem_cons.mp, mem_cons.mpr, resolve_left
-/
def chooseX : forall l : List α, forall _ : exists a, a in l ∧ p a, { a // a in l ∧ p a }
  | [], hp => False.elim (Exists.elim hp fun _ h => not_mem_nil h.left)
  | l :: ls, hp =>
if pl : p l then ⟨l, ⟨mem_cons.mpr Or.inl rfl, pl⟩⟩
    else
      -- pattern matching on `hx` too makes this not reducible!
      let ⟨a, ha⟩ :=
        chooseX ls
          (hp.imp fun _ ⟨o, h₂⟩ => ⟨(mem_cons.mp o).resolve_left fun e => pl <| e ▸ h₂, h₂⟩)
⟨a, mem_cons.mpr Or.inr ha.1, ha.2⟩

/--
Definition of `choose` / `choose` 的定义

English:
definition choose
  signature: (hp : exists a, a in l ∧ p a)
  body: chooseX p l hp

中文:
定义 choose
  签名: (hp : 存在 a, a in l ∧ p a)
  定义体: chooseX p l hp

Depends on / 依赖: chooseX
-/
def choose (hp : exists a, a in l ∧ p a) : α :=
  chooseX p l hp

end Choose

/--
Definition of `mapDiagM'` / `mapDiagM'` 的定义

English:
definition mapDiagM'
  signature: {m} [Monad m] {α} (f : α -> α -> m Unit)

中文:
定义 mapDiagM'
  签名: {m} [单子 m] {α} (f : α -> α -> m 单元)
-/
def mapDiagM' {m} [Monad m] {α} (f : α -> α -> m Unit) : List α -> m Unit
  | [] => return ()
  | h :: t => do
    _ ← f h h
    _ ← t.mapM' (f h)
    t.mapDiagM' f
-- as ported:
-- | [] => return ()
-- | h :: t => (f h h >> t.mapM' (f h)) >> t.mapDiagM'

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
/--
Definition of `map₂Left'` / `map₂Left'` 的定义

English:
definition map₂Left'
  signature: (f : α -> Option β -> γ)
  body: map₂Left' f as bs
    (f a (some b) :: rec'.fst, rec'.snd)

中文:
定义 map₂Left'
  签名: (f : α -> 选项类型 β -> γ)
  定义体: map₂Left' f as bs
    (f a (some b) :: rec'.fst, rec'.snd)
-/
def map₂Left' (f : α -> Option β -> γ) : List α -> List β -> List γ × List β
  | [], bs => ([], bs)
  | a :: as, [] => ((a :: as).map fun a => f a none, [])
  | a :: as, b :: bs =>
    let rec' := map₂Left' f as bs
    (f a (some b) :: rec'.fst, rec'.snd)

/--
Definition of `map₂Right'` / `map₂Right'` 的定义

English:
definition map₂Right'
  signature: (f : Option α -> β -> γ) (as : List α) (bs : List β)
  body: map₂Left' (flip f) bs as

中文:
定义 map₂Right'
  签名: (f : 选项类型 α -> β -> γ) (as : 列表 α) (bs : 列表 β)
  定义体: map₂Left' (flip f) bs as
-/
def map₂Right' (f : Option α -> β -> γ) (as : List α) (bs : List β) : List γ × List α :=
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
/--
Definition of `map₂Left` / `map₂Left` 的定义

English:
definition map₂Left
  signature: (f : α -> Option β -> γ)

中文:
定义 map₂Left
  签名: (f : α -> 选项类型 β -> γ)
-/
def map₂Left (f : α -> Option β -> γ) : List α -> List β -> List γ
  | [], _ => []
  | a :: as, [] => (a :: as).map fun a => f a none
  | a :: as, b :: bs => f a (some b) :: map₂Left f as bs

/--
Definition of `map₂Right` / `map₂Right` 的定义

English:
definition map₂Right
  signature: (f : Option α -> β -> γ) (as : List α) (bs : List β)
  body: map₂Left (flip f) bs as

中文:
定义 map₂Right
  签名: (f : 选项类型 α -> β -> γ) (as : 列表 α) (bs : 列表 β)
  定义体: map₂Left (flip f) bs as
-/
def map₂Right (f : Option α -> β -> γ) (as : List α) (bs : List β) : List γ :=
  map₂Left (flip f) bs as

-- TODO: naming is awkward...
/--
Definition of `mapAsyncChunked` / `mapAsyncChunked` 的定义

English:
definition mapAsyncChunked
  signature: {α β} (f : α -> β) (xs : List α) (chunk_size := 1024)
  body: ((xs.toChunks chunk_size).map fun xs => Task.spawn fun _ => List.map f xs).flatMap Task.get

中文:
定义 mapAsyncChunked
  签名: {α β} (f : α -> β) (xs : 列表 α) (chunk_size := 1024)
  定义体: ((xs.toChunks chunk_size).map fun xs => Task.spawn fun _ => List.map f xs).flatMap Task.get
-/
def mapAsyncChunked {α β} (f : α -> β) (xs : List α) (chunk_size := 1024) : List β :=
  ((xs.toChunks chunk_size).map fun xs => Task.spawn fun _ => List.map f xs).flatMap Task.get


/-!
We add some n-ary versions of `List.zipWith` for functions with more than two arguments.
These can also be written in terms of `List.zip` or `List.zipWith`.
For example, `zipWith3 f xs ys zs` could also be written as
`zipWith id (zipWith f xs ys) zs`
or as
`(zip xs <| zip ys zs).map <| fun ⟨x, y, z⟩ ↦ f x y z`.
-/

/--
Definition of `zipWith3` / `zipWith3` 的定义

English:
definition zipWith3
  signature: (f : α -> β -> γ -> δ)

中文:
定义 zipWith3
  签名: (f : α -> β -> γ -> δ)
-/
def zipWith3 (f : α -> β -> γ -> δ) : List α -> List β -> List γ -> List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: zipWith3 f xs ys zs
  | _, _, _ => []

/--
Definition of `zipWith4` / `zipWith4` 的定义

English:
definition zipWith4
  signature: (f : α -> β -> γ -> δ -> ε)

中文:
定义 zipWith4
  签名: (f : α -> β -> γ -> δ -> ε)
-/
def zipWith4 (f : α -> β -> γ -> δ -> ε) : List α -> List β -> List γ -> List δ -> List ε
  | x :: xs, y :: ys, z :: zs, u :: us => f x y z u :: zipWith4 f xs ys zs us
  | _, _, _, _ => []

/--
Definition of `zipWith5` / `zipWith5` 的定义

English:
definition zipWith5
  signature: (f : α -> β -> γ -> δ -> ε -> ζ)

中文:
定义 zipWith5
  签名: (f : α -> β -> γ -> δ -> ε -> ζ)
-/
def zipWith5 (f : α -> β -> γ -> δ -> ε -> ζ) : List α -> List β -> List γ -> List δ -> List ε -> List ζ
  | x :: xs, y :: ys, z :: zs, u :: us, v :: vs => f x y z u v :: zipWith5 f xs ys zs us vs
  | _, _, _, _, _ => []

/--
Definition of `replaceIf` / `replaceIf` 的定义

English:
definition replaceIf
  signature: : List α -> List Bool -> List α -> List α

中文:
定义 replaceIf
  签名: : 列表 α -> 列表 布尔值 -> 列表 α -> 列表 α
-/
def replaceIf : List α -> List Bool -> List α -> List α
  | l, _, [] => l
  | [], _, _ => []
  | l, [], _ => l
  | n :: ns, tf :: bs, e@(c :: cs) => if tf then c :: ns.replaceIf bs cs else n :: ns.replaceIf bs e

/-- `iterate f a n` is `[a, f a, ..., f^[n - 1] a]`. -/
@[simp]
/--
Definition of `iterate` / `iterate` 的定义

English:
definition iterate
  signature: (f : α -> α) (a : α)

中文:
定义 iterate
  签名: (f : α -> α) (a : α)
-/
def iterate (f : α -> α) (a : α) : (n : Nat) -> List α
  | 0 => []
  | n + 1 => a :: iterate f (f a) n

/-- Tail-recursive version of `List.iterate`. -/
@[inline]
/--
Definition of `iterateTR` / `iterateTR` 的定义

English:
definition iterateTR
  signature: (f : α -> α) (a : α) (n : Nat)
  body: loop a n []

中文:
定义 iterateTR
  签名: (f : α -> α) (a : α) (n : 自然数)
  定义体: loop a n []
-/
def iterateTR (f : α -> α) (a : α) (n : Nat) : List α :=
  loop a n []
where
  /-- `iterateTR.loop f a n l := iterate f a n ++ reverse l`. -/
  @[simp, specialize]
  loop (a : α) (n : Nat) (l : List α) : List α :=
    match n with
    | 0 => reverse l
    | n + 1 => loop (f a) n (a :: l)

/--
theorem `iterateTR_loop_eq` / 定理 `iterateTR_loop_eq`

English:
theorem iterateTR_loop_eq
  given: (f : α -> α) (a : α) (n : Nat) (l : List α)
  proof: by
  induction n generalizing a l <;> simp [*]

@[csimp]

中文:
定理 iterateTR_loop_eq
  条件: (f : α -> α) (a : α) (n : 自然数) (l : 列表 α)
  证明: by
  induction n generalizing a l <;> simp [*]

@[csimp]

Depends on / 依赖: generalizing
-/
theorem iterateTR_loop_eq (f : α -> α) (a : α) (n : Nat) (l : List α) :
    iterateTR.loop f a n l = reverse l ++ iterate f a n := by
  induction n generalizing a l <;> simp [*]

@[csimp]
/--
theorem `iterate_eq_iterateTR` / 定理 `iterate_eq_iterateTR`

English:
theorem iterate_eq_iterateTR
  statement: @iterate = @iterateTR
  proof: by
  funext α f a n
exact Eq.symm iterateTR_loop_eq f a n []

中文:
定理 iterate_eq_iterateTR
  结论: @iterate = @iterateTR
  证明: by
  funext α f a n
exact Eq.symm iterateTR_loop_eq f a n []

Depends on / 依赖: Eq.symm, iterateTR_loop_eq
-/
theorem iterate_eq_iterateTR : @iterate = @iterateTR := by
  funext α f a n
exact Eq.symm iterateTR_loop_eq f a n []

section MapAccumr

/--
Definition of `mapAccumr` / `mapAccumr` 的定义

English:
definition mapAccumr
  signature: (f : α -> γ -> γ × β)
  body: mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)

中文:
定义 mapAccumr
  签名: (f : α -> γ -> γ × β)
  定义体: mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)

Depends on / 依赖: mapAccumr
-/
def mapAccumr (f : α -> γ -> γ × β) : List α -> γ -> γ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)

/-- Length of the list obtained by `mapAccumr`. -/
@[simp]
/--
theorem `length_mapAccumr` / 定理 `length_mapAccumr`

English:
theorem length_mapAccumr

中文:
定理 length_mapAccumr
-/
theorem length_mapAccumr :
    forall (f : α -> γ -> γ × β) (x : List α) (s : γ), length (mapAccumr f x s).2 = length x
  | f, _ :: x, s => congr_arg succ (length_mapAccumr f x s)
  | _, [], _ => rfl

/--
Definition of `mapAccumr₂` / `mapAccumr₂` 的定义

English:
definition mapAccumr₂
  signature: (f : α -> β -> γ -> γ × δ)
  body: mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)

中文:
定义 mapAccumr₂
  签名: (f : α -> β -> γ -> γ × δ)
  定义体: mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)
-/
def mapAccumr₂ (f : α -> β -> γ -> γ × δ) : List α -> List β -> γ -> γ × List δ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)

/-- Length of a list obtained using `mapAccumr₂`. -/
@[simp]
/--
theorem `length_mapAccumr₂` / 定理 `length_mapAccumr₂`

English:
theorem length_mapAccumr₂
  proof: congr_arg succ (length_mapAccumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (succ_min_succ (length x) (length y))
  | _, _ :: _, [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, [], [], _ => rfl

中文:
定理 length_mapAccumr₂
  证明: congr_arg succ (length_mapAccumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (succ_min_succ (length x) (length y))
  | _, _ :: _, [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, [], [], _ => rfl

Depends on / 依赖: Eq.symm, congr_arg, length, succ_min_succ
-/
theorem length_mapAccumr₂ :
    forall (f : α -> β -> γ -> γ × δ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
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

/--
Definition of `consecutivePairs` / `consecutivePairs` 的定义

English:
abbreviation consecutivePairs
  signature: (l : List α)
  body: l.zip l.tail

中文:
缩写 consecutivePairs
  签名: (l : 列表 α)
  定义体: l.zip l.tail

Depends on / 依赖: l.tail, l.zip
-/
abbrev consecutivePairs (l : List α) : List (α × α) := l.zip l.tail

end consecutivePairs

end List
