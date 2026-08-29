/-
Copyright (c) 2024 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Take operations on tuples

We define the `take` operation on `n`-tuples, which restricts a tuple to its first `m` elements.

* `Fin.take`: Given `h : m ≤ n`, `Fin.take m h v` for an `n`-tuple `v = (v 0, ..., v (n - 1))` is
  the `m`-tuple `(v 0, ..., v (m - 1))`.
-/

@[expose] public section

namespace Fin

open Function

variable {n : Nat} {α : Fin n -> Sort*}

section Take

/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i)
  body: fun i => v (castLE h i)

@[simp]

中文:
定义 take
  签名: (m : 自然数) (h : m <= n) (v : (i : Fin n) -> α i)
  定义体: fun i => v (castLE h i)

@[simp]

Depends on / 依赖: castLE
-/
def take (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) : (i : Fin m) -> α (castLE h i) :=
  fun i => v (castLE h i)

@[simp]
/--
theorem `take_apply` / 定理 `take_apply`

English:
theorem take_apply
  given: (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin m)
  proof: rfl

@[simp]

中文:
定理 take_apply
  条件: (m : 自然数) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin m)
  证明: rfl

@[simp]
-/
theorem take_apply (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin m) :
    (take m h v) i = v (castLE h i) := rfl

@[simp]
/--
theorem `take_zero` / 定理 `take_zero`

English:
theorem take_zero
  given: (v : (i : Fin n) -> α i)
  statement: take 0 n.zero_le v = fun i => elim0 i
  proof: by
  ext i; exact elim0 i

@[simp]

中文:
定理 take_zero
  条件: (v : (i : Fin n) -> α i)
  结论: take 0 n.zero_le v = fun i => elim0 i
  证明: by
  ext i; exact elim0 i

@[simp]
-/
theorem take_zero (v : (i : Fin n) -> α i) : take 0 n.zero_le v = fun i => elim0 i := by
  ext i; exact elim0 i

@[simp]
/--
theorem `take_one` / 定理 `take_one`

English:
theorem take_one
  given: {α : Fin (n + 1) -> Sort*} (v : (i : Fin (n + 1)) -> α i)
  proof: by
  ext i
  simp only [take]

@[simp]

中文:
定理 take_one
  条件: {α : Fin (n + 1) -> Sort*} (v : (i : Fin (n + 1)) -> α i)
  证明: by
  ext i
  simp only [take]

@[simp]
-/
theorem take_one {α : Fin (n + 1) -> Sort*} (v : (i : Fin (n + 1)) -> α i) :
    take 1 (Nat.le_add_left 1 n) v = (fun i => v (castLE (Nat.le_add_left 1 n) i)) := by
  ext i
  simp only [take]

@[simp]
/--
theorem `take_eq_init` / 定理 `take_eq_init`

English:
theorem take_eq_init
  given: {α : Fin (n + 1) -> Sort*} (v : (i : Fin (n + 1)) -> α i)
  proof: rfl

@[simp]

中文:
定理 take_eq_init
  条件: {α : Fin (n + 1) -> Sort*} (v : (i : Fin (n + 1)) -> α i)
  证明: rfl

@[simp]
-/
theorem take_eq_init {α : Fin (n + 1) -> Sort*} (v : (i : Fin (n + 1)) -> α i) :
    take n n.le_succ v = init v := rfl

@[simp]
/--
theorem `take_eq_self` / 定理 `take_eq_self`

English:
theorem take_eq_self
  given: (v : (i : Fin n) -> α i)
  statement: take n (le_refl n) v = v
  proof: by
  ext i
  simp [take]

@[simp]

中文:
定理 take_eq_self
  条件: (v : (i : Fin n) -> α i)
  结论: take n (le_refl n) v = v
  证明: by
  ext i
  simp [take]

@[simp]
-/
theorem take_eq_self (v : (i : Fin n) -> α i) : take n (le_refl n) v = v := by
  ext i
  simp [take]

@[simp]
/--
theorem `take_take` / 定理 `take_take`

English:
theorem take_take
  given: {m n' : Nat} (h : m <= n') (h' : n' <= n) (v : (i : Fin n) -> α i)
  proof: rfl

@[simp]

中文:
定理 take_take
  条件: {m n' : 自然数} (h : m <= n') (h' : n' <= n) (v : (i : Fin n) -> α i)
  证明: rfl

@[simp]
-/
theorem take_take {m n' : Nat} (h : m <= n') (h' : n' <= n) (v : (i : Fin n) -> α i) :
    take m h (take n' h' v) = take m (Nat.le_trans h h') v := rfl

@[simp]
/--
theorem `take_init` / 定理 `take_init`

English:
theorem take_init
  given: {α : Fin (n + 1) -> Sort*} (m : Nat) (h : m <= n) (v : (i : Fin (n + 1)) -> α i)
  proof: rfl

中文:
定理 take_init
  条件: {α : Fin (n + 1) -> Sort*} (m : 自然数) (h : m <= n) (v : (i : Fin (n + 1)) -> α i)
  证明: rfl
-/
theorem take_init {α : Fin (n + 1) -> Sort*} (m : Nat) (h : m <= n) (v : (i : Fin (n + 1)) -> α i) :
    take m h (init v) = take m (Nat.le_succ_of_le h) v := rfl

/--
theorem `take_repeat` / 定理 `take_repeat`

English:
theorem take_repeat
  given: {α : Type*} {n' : Nat} (m : Nat) (h : m <= n) (a : Fin n' -> α)
  proof: by
  ext i
  simp only [take, repeat_apply, modNat, val_castLE]

中文:
定理 take_repeat
  条件: {α : 类型} {n' : 自然数} (m : 自然数) (h : m <= n) (a : Fin n' -> α)
  证明: by
  ext i
  simp only [take, repeat_apply, modNat, val_castLE]

Depends on / 依赖: modNat, repeat_apply, val_castLE
-/
theorem take_repeat {α : Type*} {n' : Nat} (m : Nat) (h : m <= n) (a : Fin n' -> α) :
    take (m * n') (Nat.mul_le_mul_right n' h) (Fin.repeat n a) = Fin.repeat m a := by
  ext i
  simp only [take, repeat_apply, modNat, val_castLE]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `take_succ_eq_snoc` / 定理 `take_succ_eq_snoc`

English:
theorem take_succ_eq_snoc
  given: (m : Nat) (h : m < n) (v : (i : Fin n) -> α i)
  proof: by
  ext i
  induction m with
  | zero =>
    have h' : i = 0 := by ext; simp
    subst h'
    simp [take, snoc, castLE]
  | succ m _ =>
    induction i using reverseInduction with
    | last => simp [take, snoc]; congr
    | cast i _ => simp

中文:
定理 take_succ_eq_snoc
  条件: (m : 自然数) (h : m < n) (v : (i : Fin n) -> α i)
  证明: by
  ext i
  induction m with
  | zero =>
    have h' : i = 0 := by ext; simp
    subst h'
    simp [take, snoc, castLE]
  | succ m _ =>
    induction i using reverseInduction with
    | last => simp [take, snoc]; congr
    | cast i _ => simp

Depends on / 依赖: castLE, reverseInduction
-/
theorem take_succ_eq_snoc (m : Nat) (h : m < n) (v : (i : Fin n) -> α i) :
    take m.succ h v = snoc (take m h.le v) (v ⟨m, h⟩) := by
  ext i
  induction m with
  | zero =>
    have h' : i = 0 := by ext; simp
    subst h'
    simp [take, snoc, castLE]
  | succ m _ =>
    induction i using reverseInduction with
    | last => simp [take, snoc]; congr
    | cast i _ => simp

/-- `take` commutes with `update` for indices in the range of `take`. -/
@[simp]
/--
theorem `take_update_of_lt` / 定理 `take_update_of_lt`

English:
theorem take_update_of_lt
  statement: (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin m)
  proof: by
  ext j
  by_cases h' : j = i
  · rw [h']
    simp only [take, update_self]
  · have : castLE h j != castLE h i := by simp [h']
    simp only [take, update_of_ne h', update_of_ne this]

中文:
定理 take_update_of_lt
  结论: (m : 自然数) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin m)
  证明: by
  ext j
  by_cases h' : j = i
  · rw [h']
    simp only [take, update_self]
  · have : castLE h j != castLE h i := by simp [h']
    simp only [take, update_of_ne h', update_of_ne this]

Depends on / 依赖: castLE, update_of_ne, update_self
-/
theorem take_update_of_lt (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin m)
    (x : α (castLE h i)) : take m h (update v (castLE h i) x) = update (take m h v) i x := by
  ext j
  by_cases h' : j = i
  · rw [h']
    simp only [take, update_self]
  · have : castLE h j != castLE h i := by simp [h']
    simp only [take, update_of_ne h', update_of_ne this]

/-- `take` is the same after `update` for indices outside the range of `take`. -/
@[simp]
/--
theorem `take_update_of_ge` / 定理 `take_update_of_ge`

English:
theorem take_update_of_ge
  statement: (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin n) (hi : i >= m)
  proof: by
  ext j
  have : castLE h j != i := by
    refine ne_of_val_ne ?_
    simp only [val_castLE]
    exact Nat.ne_of_lt (lt_of_lt_of_le j.isLt hi)
  simp only [take, update_of_ne this]

中文:
定理 take_update_of_ge
  结论: (m : 自然数) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin n) (hi : i >= m)
  证明: by
  ext j
  have : castLE h j != i := by
    refine ne_of_val_ne ?_
    simp only [val_castLE]
    exact Nat.ne_of_lt (lt_of_lt_of_le j.isLt hi)
  simp only [take, update_of_ne this]

Depends on / 依赖: Nat.ne_of_lt, castLE, j.isLt, lt_of_lt_of_le, ne_of_lt, ne_of_val_ne, update_of_ne, val_castLE
-/
theorem take_update_of_ge (m : Nat) (h : m <= n) (v : (i : Fin n) -> α i) (i : Fin n) (hi : i >= m)
    (x : α i) : take m h (update v i x) = take m h v := by
  ext j
  have : castLE h j != i := by
    refine ne_of_val_ne ?_
    simp only [val_castLE]
    exact Nat.ne_of_lt (lt_of_lt_of_le j.isLt hi)
  simp only [take, update_of_ne this]

/--
theorem `take_addCases_left` / 定理 `take_addCases_left`

English:
theorem take_addCases_left
  statement: {n' : Nat} {motive : Fin (n + n') -> Sort*} (m : Nat) (h : m <= n)
  proof: by
  ext i
  have : i < n := Nat.lt_of_lt_of_le i.isLt h
  simp only [take, addCases, this, val_castLE, ↓reduceDIte]
  congr

中文:
定理 take_addCases_left
  结论: {n' : 自然数} {motive : Fin (n + n') -> Sort*} (m : 自然数) (h : m <= n)
  证明: by
  ext i
  have : i < n := Nat.lt_of_lt_of_le i.isLt h
  simp only [take, addCases, this, val_castLE, ↓reduceDIte]
  congr

Depends on / 依赖: Nat.lt_of_lt_of_le, addCases, i.isLt, lt_of_lt_of_le, reduceDIte, val_castLE
-/
theorem take_addCases_left {n' : Nat} {motive : Fin (n + n') -> Sort*} (m : Nat) (h : m <= n)
    (u : (i : Fin n) -> motive (castAdd n' i)) (v : (i : Fin n') -> motive (natAdd n i)) :
      take m (Nat.le_add_right_of_le h) (addCases u v) = take m h u := by
  ext i
  have : i < n := Nat.lt_of_lt_of_le i.isLt h
  simp only [take, addCases, this, val_castLE, ↓reduceDIte]
  congr

/--
theorem `take_append_left` / 定理 `take_append_left`

English:
theorem take_append_left
  statement: {n' : Nat} {α : Sort*} (m : Nat) (h : m <= n) (u : (i : Fin n) -> α)
  proof: take_addCases_left m h _ _

中文:
定理 take_append_left
  结论: {n' : 自然数} {α : Sort*} (m : 自然数) (h : m <= n) (u : (i : Fin n) -> α)
  证明: take_addCases_left m h _ _

Depends on / 依赖: take_addCases_left
-/
theorem take_append_left {n' : Nat} {α : Sort*} (m : Nat) (h : m <= n) (u : (i : Fin n) -> α)
    (v : (i : Fin n') -> α) : take m (Nat.le_add_right_of_le h) (append u v) = take m h u :=
  take_addCases_left m h _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `take_addCases_right` / 定理 `take_addCases_right`

English:
theorem take_addCases_right
  statement: {n' : Nat} {motive : Fin (n + n') -> Sort*} (m : Nat) (h : m <= n')
  proof: by
  ext i
  simp only [take, addCases, val_castLE]
  by_cases h' : i < n
  · simp only [h', ↓reduceDIte]
    congr
  · simp only [h', ↓reduceDIte, subNat, castLE, Fin.cast, eqRec_eq_cast]

中文:
定理 take_addCases_right
  结论: {n' : 自然数} {motive : Fin (n + n') -> Sort*} (m : 自然数) (h : m <= n')
  证明: by
  ext i
  simp only [take, addCases, val_castLE]
  by_cases h' : i < n
  · simp only [h', ↓reduceDIte]
    congr
  · simp only [h', ↓reduceDIte, subNat, castLE, Fin.cast, eqRec_eq_cast]

Depends on / 依赖: Fin.cast, addCases, castLE, eqRec_eq_cast, reduceDIte, subNat, val_castLE
-/
theorem take_addCases_right {n' : Nat} {motive : Fin (n + n') -> Sort*} (m : Nat) (h : m <= n')
    (u : (i : Fin n) -> motive (castAdd n' i)) (v : (i : Fin n') -> motive (natAdd n i)) :
      take (n + m) (Nat.add_le_add_left h n) (addCases u v) = addCases u (take m h v) := by
  ext i
  simp only [take, addCases, val_castLE]
  by_cases h' : i < n
  · simp only [h', ↓reduceDIte]
    congr
  · simp only [h', ↓reduceDIte, subNat, castLE, Fin.cast, eqRec_eq_cast]

/--
theorem `take_append_right` / 定理 `take_append_right`

English:
theorem take_append_right
  statement: {n' : Nat} {α : Sort*} (m : Nat) (h : m <= n') (u : (i : Fin n) -> α)
  proof: take_addCases_right m h _ _

中文:
定理 take_append_right
  结论: {n' : 自然数} {α : Sort*} (m : 自然数) (h : m <= n') (u : (i : Fin n) -> α)
  证明: take_addCases_right m h _ _

Depends on / 依赖: take_addCases_right
-/
theorem take_append_right {n' : Nat} {α : Sort*} (m : Nat) (h : m <= n') (u : (i : Fin n) -> α)
    (v : (i : Fin n') -> α) : take (n + m) (Nat.add_le_add_left h n) (append u v)
        = append u (take m h v) :=
  take_addCases_right m h _ _

/--
theorem `ofFn_take_eq_take_ofFn` / 定理 `ofFn_take_eq_take_ofFn`

English:
theorem ofFn_take_eq_take_ofFn
  given: {α : Type*} {m : Nat} (h : m <= n) (v : Fin n -> α)
  proof: List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

中文:
定理 ofFn_take_eq_take_ofFn
  条件: {α : 类型} {m : 自然数} (h : m <= n) (v : Fin n -> α)
  证明: List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

Depends on / 依赖: List.ext_get, ext_get
-/
theorem ofFn_take_eq_take_ofFn {α : Type*} {m : Nat} (h : m <= n) (v : Fin n -> α) :
    List.ofFn (take m h v) = (List.ofFn v).take m :=
  List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

/--
theorem `ofFn_take_get` / 定理 `ofFn_take_get`

English:
theorem ofFn_take_get
  given: {α : Type*} {m : Nat} (l : List α) (h : m <= l.length)
  proof: List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

中文:
定理 ofFn_take_get
  条件: {α : 类型} {m : 自然数} (l : List α) (h : m <= l.length)
  证明: List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

Depends on / 依赖: List.ext_get, ext_get
-/
theorem ofFn_take_get {α : Type*} {m : Nat} (l : List α) (h : m <= l.length) :
    List.ofFn (take m h l.get) = l.take m :=
  List.ext_get (by simp [h]) (fun n h1 h2 => by simp)

/--
theorem `get_take_eq_take_get_comp_cast` / 定理 `get_take_eq_take_get_comp_cast`

English:
theorem get_take_eq_take_get_comp_cast
  given: {α : Type*} {m : Nat} (l : List α) (h : m <= l.length)
  proof: by
  ext i
  simp only [List.get_eq_getElem, List.getElem_take, comp_apply, take_apply, val_castLE, val_cast]

中文:
定理 get_take_eq_take_get_comp_cast
  条件: {α : 类型} {m : 自然数} (l : List α) (h : m <= l.length)
  证明: by
  ext i
  simp only [List.get_eq_getElem, List.getElem_take, comp_apply, take_apply, val_castLE, val_cast]

Depends on / 依赖: List.getElem_take, List.get_eq_getElem, comp_apply, getElem_take, get_eq_getElem, take_apply, val_cast, val_castLE
-/
theorem get_take_eq_take_get_comp_cast {α : Type*} {m : Nat} (l : List α) (h : m <= l.length) :
    (l.take m).get = take m h l.get ∘ Fin.cast (List.length_take_of_le h) := by
  ext i
  simp only [List.get_eq_getElem, List.getElem_take, comp_apply, take_apply, val_castLE, val_cast]

/--
theorem `get_take_ofFn_eq_take_comp_cast` / 定理 `get_take_ofFn_eq_take_comp_cast`

English:
theorem get_take_ofFn_eq_take_comp_cast
  given: {α : Type*} {m : Nat} (v : Fin n -> α) (h : m <= n)
  proof: by
  ext i
  simp [castLE]

中文:
定理 get_take_ofFn_eq_take_comp_cast
  条件: {α : 类型} {m : 自然数} (v : Fin n -> α) (h : m <= n)
  证明: by
  ext i
  simp [castLE]

Depends on / 依赖: castLE
-/
theorem get_take_ofFn_eq_take_comp_cast {α : Type*} {m : Nat} (v : Fin n -> α) (h : m <= n) :
    ((List.ofFn v).take m).get = take m h v ∘ Fin.cast (by simp [h]) := by
  ext i
  simp [castLE]

end Take

end Fin
