/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

public import Mathlib.Data.List.Defs
public import Mathlib.Tactic.Common

/-!
The type `List.Vector` represents lists with fixed length.

TODO: The API of `List.Vector` is quite incomplete relative to `Vector`,
and in particular does not use `x[i]` (that is `GetElem` notation) as the preferred accessor.
Any combination of reducing the use of `List.Vector` in Mathlib, or modernising its API,
would be welcome.
-/

@[expose] public section

assert_not_exists Monoid

universe u v w
/--
Definition of `List.Vector` / `List.Vector` 的定义

English:
definition List.Vector
  signature: (α : Type u) (n : Nat)
  body: { l : List α // l.length = n }

中文:
定义 列表.Vector
  签名: (α : 类型u) (n : 自然数)
  定义体: { l : List α // l.length = n }

Depends on / 依赖: l.length, length
-/
def List.Vector (α : Type u) (n : Nat) :=
  { l : List α // l.length = n }

namespace List.Vector

variable {α β σ φ : Type*} {n : Nat} {p : α -> Prop}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DecidableEq
  signature: α] : DecidableEq (Vector α n)
  body: inferInstanceAs (DecidableEq {l : List α // l.length = n})

中文:
实例 [DecidableEq
  签名: α] : DecidableEq (Vector α n)
  定义体: inferInstanceAs (DecidableEq {l : List α // l.length = n})

Depends on / 依赖: DecidableEq, l.length, length
-/
instance [DecidableEq α] : DecidableEq (Vector α n) :=
  inferInstanceAs (DecidableEq {l : List α // l.length = n})

/-- The empty vector with elements of type `α` -/
@[match_pattern]
/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: : Vector α 0
  body: ⟨[], rfl⟩

中文:
定义 nil
  签名: : Vector α 0
  定义体: ⟨[], rfl⟩
-/
def nil : Vector α 0 :=
  ⟨[], rfl⟩

/-- If `a : α` and `l : Vector α n`, then `cons a l`, is the vector of length `n + 1`
whose first element is a and with l as the rest of the list. -/
@[match_pattern]
/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: : α -> Vector α n -> Vector α (Nat.succ n)

中文:
定义 cons
  签名: : α -> Vector α n -> Vector α (自然数.succ n)
-/
def cons : α -> Vector α n -> Vector α (Nat.succ n)
  | a, ⟨v, h⟩ => ⟨a :: v, congrArg Nat.succ h⟩


/-- The length of a vector. -/
@[reducible, nolint unusedArguments]
/--
Definition of `length` / `length` 的定义

English:
definition length
  signature: (_ : Vector α n)
  body: n

中文:
定义 length
  签名: (_ : Vector α n)
  定义体: n
-/
def length (_ : Vector α n) : Nat :=
  n

open Nat

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: : Vector α (Nat.succ n) -> α

中文:
定义 head
  签名: : Vector α (自然数.succ n) -> α
-/
def head : Vector α (Nat.succ n) -> α
  | ⟨a :: _, _⟩ => a

/-- The head of a vector obtained by prepending is the element prepended. -/
@[simp, grind =]
/--
theorem `head_cons` / 定理 `head_cons`

English:
theorem head_cons
  given: (a : α)
  statement: forall v : Vector α n, head (cons a v) = a

中文:
定理 head_cons
  条件: (a : α)
  结论: 对任意 v : Vector α n, head (cons a v) = a
-/
theorem head_cons (a : α) : forall v : Vector α n, head (cons a v) = a
  | ⟨_, _⟩ => rfl

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: : Vector α n -> Vector α (n - 1)

中文:
定义 tail
  签名: : Vector α n -> Vector α (n - 1)
-/
def tail : Vector α n -> Vector α (n - 1)
  | ⟨[], h⟩ => ⟨[], congrArg pred h⟩
  | ⟨_ :: v, h⟩ => ⟨v, congrArg pred h⟩

/-- The tail of a vector obtained by prepending is the vector prepended. to -/
@[simp, grind =]
/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  given: (a : α)
  statement: forall v : Vector α n, tail (cons a v) = v

中文:
定理 tail_cons
  条件: (a : α)
  结论: 对任意 v : Vector α n, tail (cons a v) = v
-/
theorem tail_cons (a : α) : forall v : Vector α n, tail (cons a v) = v
  | ⟨_, _⟩ => rfl

/-- Prepending the head of a vector to its tail gives the vector. -/
@[simp]
/--
theorem `cons_head_tail` / 定理 `cons_head_tail`

English:
theorem cons_head_tail
  statement: forall v : Vector α (succ n), cons (head v) (tail v) = v

中文:
定理 cons_head_tail
  结论: 对任意 v : Vector α (succ n), cons (head v) (tail v) = v
-/
theorem cons_head_tail : forall v : Vector α (succ n), cons (head v) (tail v) = v
  | ⟨[], h⟩ => by contradiction
  | ⟨_ :: _, _⟩ => rfl

/--
Definition of `toList` / `toList` 的定义

English:
definition toList
  signature: (v : Vector α n)
  body: v.1

中文:
定义 toList
  签名: (v : Vector α n)
  定义体: v.1
-/
def toList (v : Vector α n) : List α :=
  v.1

/--
Definition of `get` / `get` 的定义

English:
definition get
  signature: (l : Vector α n) (i : Fin n)
  body: l.1.get i.cast l.2.symm

中文:
定义 get
  签名: (l : Vector α n) (i : 有限集 n)
  定义体: l.1.get i.cast l.2.symm

Depends on / 依赖: i.cast
-/
def get (l : Vector α n) (i : Fin n) : α :=
l.1.get i.cast l.2.symm

instance {n m : Nat} : HAppend (Vector α n) (Vector α m) (Vector α (n + m)) where
  hAppend | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩

/--
lemma `append_def` / 引理 `append_def`

English:
lemma append_def
  given: {n m : Nat}
  proof: rfl

中文:
引理 append_def
  条件: {n m : 自然数}
  证明: rfl
-/
lemma append_def {n m : Nat} :
    (HAppend.hAppend : Vector α n -> Vector α m -> Vector α (n + m)) =
      fun | ⟨l₁, h₁⟩, ⟨l₂, h₂⟩ => ⟨l₁ ++ l₂, by simp [*]⟩ :=
  rfl

/-- Elimination rule for `Vector`. -/
@[elab_as_elim]
/--
Definition of `elim` / `elim` 的定义

English:
definition elim
  signature: {α} {C : forall {n}, Vector α n -> Sort u}

中文:
定义 elim
  签名: {α} {C : 对任意 {n}, Vector α n -> 类型层 u}
-/
def elim {α} {C : forall {n}, Vector α n -> Sort u}
    (H : forall l : List α, C ⟨l, rfl⟩) {n : Nat} : forall v : Vector α n, C v
  | ⟨l, h⟩ =>
    match n, h with
    | _, rfl => H l

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β)

中文:
定义 map
  签名: (f : α -> β)
-/
def map (f : α -> β) : Vector α n -> Vector β n
  | ⟨l, h⟩ => ⟨List.map f l, by simp [*]⟩

/-- A `nil` vector maps to a `nil` vector. -/
@[simp]
/--
theorem `map_nil` / 定理 `map_nil`

English:
theorem map_nil
  given: (f : α -> β)
  statement: map f nil = nil
  proof: rfl

中文:
定理 map_nil
  条件: (f : α -> β)
  结论: map f nil = nil
  证明: rfl
-/
theorem map_nil (f : α -> β) : map f nil = nil :=
  rfl

/-- `map` is natural with respect to `cons`. -/
@[simp]
/--
theorem `map_cons` / 定理 `map_cons`

English:
theorem map_cons
  given: (f : α -> β) (a : α)
  statement: forall v : Vector α n, map f (cons a v) = cons (f a) (map f v)

中文:
定理 map_cons
  条件: (f : α -> β) (a : α)
  结论: 对任意 v : Vector α n, map f (cons a v) = cons (f a) (map f v)
-/
theorem map_cons (f : α -> β) (a : α) : forall v : Vector α n, map f (cons a v) = cons (f a) (map f v)
  | ⟨_, _⟩ => rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pmap` / `pmap` 的定义

English:
definition pmap
  signature: (f : (a : α) -> p a -> β)

中文:
定义 pmap
  签名: (f : (a : α) -> p a -> β)
-/
def pmap (f : (a : α) -> p a -> β) :
    (v : Vector α n) -> (forall x in v.toList, p x) -> Vector β n
  | ⟨l, h⟩, hp => ⟨List.pmap f l hp, by simp [h]⟩

@[simp]
/--
theorem `pmap_nil` / 定理 `pmap_nil`

English:
theorem pmap_nil
  given: (f : (a : α) -> p a -> β) (hp : forall x in nil.toList, p x)
  proof: rfl

中文:
定理 pmap_nil
  条件: (f : (a : α) -> p a -> β) (hp : 对任意 x in nil.toList, p x)
  证明: rfl
-/
theorem pmap_nil (f : (a : α) -> p a -> β) (hp : forall x in nil.toList, p x) :
    nil.pmap f hp = nil := rfl

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : α -> β -> φ)

中文:
定义 map₂
  签名: (f : α -> β -> φ)
-/
def map₂ (f : α -> β -> φ) : Vector α n -> Vector β n -> Vector φ n
  | ⟨x, _⟩, ⟨y, _⟩ => ⟨List.zipWith f x y, by simp [*]⟩

/--
Definition of `replicate` / `replicate` 的定义

English:
definition replicate
  signature: (n : Nat) (a : α)
  body: ⟨List.replicate n a, List.length_replicate⟩

中文:
定义 replicate
  签名: (n : 自然数) (a : α)
  定义体: ⟨List.replicate n a, List.length_replicate⟩

Depends on / 依赖: List.length_replicate, List.replicate, length_replicate, replicate
-/
def replicate (n : Nat) (a : α) : Vector α n :=
  ⟨List.replicate n a, List.length_replicate⟩

/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: (i : Nat)

中文:
定义 drop
  签名: (i : 自然数)
-/
def drop (i : Nat) : Vector α n -> Vector α (n - i)
  | ⟨l, p⟩ => ⟨List.drop i l, by simp [*]⟩

/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: (i : Nat)

中文:
定义 take
  签名: (i : 自然数)
-/
def take (i : Nat) : Vector α n -> Vector α (min i n)
  | ⟨l, p⟩ => ⟨List.take i l, by simp [*]⟩

/--
Definition of `eraseIdx` / `eraseIdx` 的定义

English:
definition eraseIdx
  signature: (i : Fin n)

中文:
定义 eraseIdx
  签名: (i : 有限集 n)
-/
def eraseIdx (i : Fin n) : Vector α n -> Vector α (n - 1)
  | ⟨l, p⟩ => ⟨List.eraseIdx l i.1, by rw [l.length_eraseIdx_of_lt] <;> rw [p]; exact i.2⟩

/--
Definition of `ofFn` / `ofFn` 的定义

English:
definition ofFn
  signature: : forall {n}, (Fin n -> α) -> Vector α n

中文:
定义 ofFn
  签名: : 对任意 {n}, (有限集 n -> α) -> Vector α n
-/
def ofFn : forall {n}, (Fin n -> α) -> Vector α n
  | 0, _ => nil
  | _ + 1, f => cons (f 0) (ofFn fun i => f i.succ)

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: {n m : Nat} (h : n = m)

中文:
定义 congr
  签名: {n m : 自然数} (h : n = m)
-/
protected def congr {n m : Nat} (h : n = m) : Vector α n -> Vector α m
  | ⟨x, p⟩ => ⟨x, h ▸ p⟩

section Accum

open Prod

/--
Definition of `mapAccumr` / `mapAccumr` 的定义

English:
definition mapAccumr
  signature: (f : α -> σ -> σ × β)
  body: List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*, res]⟩

中文:
定义 mapAccumr
  签名: (f : α -> σ -> σ × β)
  定义体: List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*, res]⟩

Depends on / 依赖: List.mapAccumr, mapAccumr
-/
def mapAccumr (f : α -> σ -> σ × β) : Vector α n -> σ -> σ × Vector β n
  | ⟨x, px⟩, c =>
    let res := List.mapAccumr f x c
    ⟨res.1, res.2, by simp [*, res]⟩

/--
Definition of `mapAccumr₂` / `mapAccumr₂` 的定义

English:
definition mapAccumr₂
  signature: (f : α -> β -> σ -> σ × φ)
  body: List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*, res]⟩

中文:
定义 mapAccumr₂
  签名: (f : α -> β -> σ -> σ × φ)
  定义体: List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*, res]⟩

Depends on / 依赖: List.mapAccumr
-/
def mapAccumr₂ (f : α -> β -> σ -> σ × φ) : Vector α n -> Vector β n -> σ -> σ × Vector φ n
  | ⟨x, px⟩, ⟨y, py⟩, c =>
    let res := List.mapAccumr₂ f x y c
    ⟨res.1, res.2, by simp [*, res]⟩

end Accum

/-! ### Shift Primitives -/
section Shift

/--
Definition of `shiftLeftFill` / `shiftLeftFill` 的定义

English:
definition shiftLeftFill
  signature: (v : Vector α n) (i : Nat) (fill : α)
  body: Vector.congr (by simp) (drop i v ++ replicate (min n i) fill)

中文:
定义 shiftLeftFill
  签名: (v : Vector α n) (i : 自然数) (fill : α)
  定义体: Vector.congr (by simp) (drop i v ++ replicate (min n i) fill)

Depends on / 依赖: Vector, Vector.congr, replicate
-/
def shiftLeftFill (v : Vector α n) (i : Nat) (fill : α) : Vector α n :=
  Vector.congr (by simp) (drop i v ++ replicate (min n i) fill)

/--
Definition of `shiftRightFill` / `shiftRightFill` 的定义

English:
definition shiftRightFill
  signature: (v : Vector α n) (i : Nat) (fill : α)
  body: Vector.congr (by omega) (replicate (min n i) fill ++ take (n - i) v)

中文:
定义 shiftRightFill
  签名: (v : Vector α n) (i : 自然数) (fill : α)
  定义体: Vector.congr (by omega) (replicate (min n i) fill ++ take (n - i) v)

Depends on / 依赖: Vector, Vector.congr, replicate
-/
def shiftRightFill (v : Vector α n) (i : Nat) (fill : α) : Vector α n :=
  Vector.congr (by omega) (replicate (min n i) fill ++ take (n - i) v)

end Shift


/-! ### Basic Theorems -/
/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {n : Nat}
  statement: forall a1 a2 : Vector α n, toList a1 = toList a2 -> a1 = a2

中文:
定理 eq
  条件: {n : 自然数}
  结论: 对任意 a1 a2 : Vector α n, toList a1 = toList a2 -> a1 = a2
-/
protected theorem eq {n : Nat} : forall a1 a2 : Vector α n, toList a1 = toList a2 -> a1 = a2
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/--
theorem `eq_nil` / 定理 `eq_nil`

English:
theorem eq_nil
  given: (v : Vector α 0)
  statement: v = nil
  proof: v.eq nil (List.eq_nil_of_length_eq_zero v.2)

中文:
定理 eq_nil
  条件: (v : Vector α 0)
  结论: v = nil
  证明: v.eq nil (List.eq_nil_of_length_eq_zero v.2)
-/
protected theorem eq_nil (v : Vector α 0) : v = nil :=
  v.eq nil (List.eq_nil_of_length_eq_zero v.2)

/-- Vector of length from a list `v`
with witness that `v` has length `n` maps to `v` under `toList`. -/
@[simp]
/--
theorem `toList_mk` / 定理 `toList_mk`

English:
theorem toList_mk
  given: (v : List α) (P : List.length v = n)
  statement: toList (Subtype.mk v P) = v
  proof: rfl

中文:
定理 toList_mk
  条件: (v : 列表 α) (P : 列表.length v = n)
  结论: toList (子类型.mk v P) = v
  证明: rfl
-/
theorem toList_mk (v : List α) (P : List.length v = n) : toList (Subtype.mk v P) = v :=
  rfl

/-- A nil vector maps to a nil list. -/
@[simp]
/--
theorem `toList_nil` / 定理 `toList_nil`

English:
theorem toList_nil
  statement: toList nil = @List.nil α
  proof: rfl

中文:
定理 toList_nil
  结论: toList nil = @列表.nil α
  证明: rfl
-/
theorem toList_nil : toList nil = @List.nil α :=
  rfl

/-- The length of the list to which a vector of length `n` maps is `n`. -/
@[simp]
/--
theorem `toList_length` / 定理 `toList_length`

English:
theorem toList_length
  given: (v : Vector α n)
  statement: (toList v).length = n
  proof: v.2

中文:
定理 toList_length
  条件: (v : Vector α n)
  结论: (toList v).length = n
  证明: v.2
-/
theorem toList_length (v : Vector α n) : (toList v).length = n :=
  v.2

/-- `toList` of `cons` of a vector and an element is
the `cons` of the list obtained by `toList` and the element -/
@[simp]
/--
theorem `toList_cons` / 定理 `toList_cons`

English:
theorem toList_cons
  given: (a : α) (v : Vector α n)
  statement: toList (cons a v) = a :: toList v
  proof: by
  cases v; rfl

中文:
定理 toList_cons
  条件: (a : α) (v : Vector α n)
  结论: toList (cons a v) = a :: toList v
  证明: by
  cases v; rfl
-/
theorem toList_cons (a : α) (v : Vector α n) : toList (cons a v) = a :: toList v := by
  cases v; rfl

/-- Appending of vectors corresponds under `toList` to appending of lists. -/
@[simp]
/--
theorem `toList_append` / 定理 `toList_append`

English:
theorem toList_append
  given: {n m : Nat} (v : Vector α n) (w : Vector α m)
  proof: rfl

中文:
定理 toList_append
  条件: {n m : 自然数} (v : Vector α n) (w : Vector α m)
  证明: rfl
-/
theorem toList_append {n m : Nat} (v : Vector α n) (w : Vector α m) :
    toList (v ++ w) = toList v ++ toList w := rfl

/-- `drop` of vectors corresponds under `toList` to `drop` of lists. -/
@[simp]
/--
theorem `toList_drop` / 定理 `toList_drop`

English:
theorem toList_drop
  given: {n m : Nat} (v : Vector α m)
  statement: toList (drop n v) = List.drop n (toList v)
  proof: by
  cases v
  rfl

中文:
定理 toList_drop
  条件: {n m : 自然数} (v : Vector α m)
  结论: toList (drop n v) = 列表.drop n (toList v)
  证明: by
  cases v
  rfl
-/
theorem toList_drop {n m : Nat} (v : Vector α m) : toList (drop n v) = List.drop n (toList v) := by
  cases v
  rfl

/-- `take` of vectors corresponds under `toList` to `take` of lists. -/
@[simp]
/--
theorem `toList_take` / 定理 `toList_take`

English:
theorem toList_take
  given: {n m : Nat} (v : Vector α m)
  statement: toList (take n v) = List.take n (toList v)
  proof: by
  cases v
  rfl

中文:
定理 toList_take
  条件: {n m : 自然数} (v : Vector α m)
  结论: toList (take n v) = 列表.take n (toList v)
  证明: by
  cases v
  rfl
-/
theorem toList_take {n m : Nat} (v : Vector α m) : toList (take n v) = List.take n (toList v) := by
  cases v
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: GetElem (Vector α n) Nat α fun _ i => i < n
  body: fun x i h => get x ⟨i, h⟩

中文:
实例 :
  签名: GetElem (Vector α n) 自然数 α fun _ i => i < n
  定义体: fun x i h => get x ⟨i, h⟩
-/
instance : GetElem (Vector α n) Nat α fun _ i => i < n where
  getElem := fun x i h => get x ⟨i, h⟩

/--
lemma `getElem_def` / 引理 `getElem_def`

English:
lemma getElem_def
  given: (v : Vector α n) (i : Nat) {hi : i < n}
  proof: rfl

中文:
引理 getElem_def
  条件: (v : Vector α n) (i : 自然数) {hi : i < n}
  证明: rfl
-/
lemma getElem_def (v : Vector α n) (i : Nat) {hi : i < n} :
    v[i] = v.toList[i]'(by simpa) := rfl

/--
lemma `toList_getElem` / 引理 `toList_getElem`

English:
lemma toList_getElem
  given: (v : Vector α n) (i : Nat) {hi : i < v.toList.length}
  proof: rfl

中文:
引理 toList_getElem
  条件: (v : Vector α n) (i : 自然数) {hi : i < v.toList.length}
  证明: rfl
-/
lemma toList_getElem (v : Vector α n) (i : Nat) {hi : i < v.toList.length} :
    v.toList[i] = v[i]'(by simp_all) := rfl

end List.Vector
