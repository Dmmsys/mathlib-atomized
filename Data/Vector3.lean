/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fin.Fin2
public import Mathlib.Util.Notation3

/-!
# Alternate definition of `Vector` in terms of `Fin2`

This file provides a scope `Vector3` which overrides the `[a, b, c]` notation to create a `Vector3`
instead of a `List`.

The `::` notation is also overloaded by this file to mean `Vector3.cons`.
-/

@[expose] public section

open Fin2 Nat

universe u

variable {α : Type*} {m n : Nat}

/--
Definition of `Vector3` / `Vector3` 的定义

English:
definition Vector3
  signature: (α : Type u) (n : Nat)
  body: Fin2 n -> α

中文:
定义 Vector3
  签名: (α : 类型u) (n : 自然数)
  定义体: Fin2 n -> α
-/
def Vector3 (α : Type u) (n : Nat) : Type u :=
  Fin2 n -> α

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Vector3 α n) where
  body: fun _ => default

中文:
实例 [Inhabited
  签名: α] : Inhabited (Vector3 α n) where
  定义体: fun _ => default
-/
instance [Inhabited α] : Inhabited (Vector3 α n) where
  default := fun _ => default

namespace Vector3

/-- The empty vector -/
@[match_pattern]
/--
Definition of `nil` / `nil` 的定义

English:
definition nil
  signature: : Vector3 α 0
  body: nofun

中文:
定义 nil
  签名: : Vector3 α 0
  定义体: nofun
-/
def nil : Vector3 α 0 :=
  nofun

/-- The vector cons operation -/
@[match_pattern]
/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (a : α) (v : Vector3 α n)
  body: fun i => by
  refine i.cases' ?_ ?_
  · exact a
  · exact v

中文:
定义 cons
  签名: (a : α) (v : Vector3 α n)
  定义体: fun i => by
  refine i.cases' ?_ ?_
  · exact a
  · exact v

Depends on / 依赖: i.cases
-/
def cons (a : α) (v : Vector3 α n) : Vector3 α (n + 1) := fun i => by
  refine i.cases' ?_ ?_
  · exact a
  · exact v

section
open Lean

scoped macro_rules | `([$l,*]) => `(expand_foldr% (h t => cons h t) nil [$(.ofElems l),*])

-- this is copied from `Init/NotationExtra.lean` (Lean core)
/-- Unexpander for `Vector3.nil` -/
@[app_unexpander Vector3.nil] meta def unexpandNil : Lean.PrettyPrinter.Unexpander
  | `($(_)) => `([])

-- this is copied from `Init/NotationExtra.lean` (Lean core)
/-- Unexpander for `Vector3.cons` -/
@[app_unexpander Vector3.cons] meta def unexpandCons : Lean.PrettyPrinter.Unexpander
  | `($(_) $x []) => `([$x])
  | `($(_) $x [$xs,*]) => `([$x, $xs,*])
  | _ => throw ()

end

-- Overloading the usual `::` notation for `List.cons` with `Vector3.cons`.
@[inherit_doc]
scoped notation a " :: " b => cons a b

@[simp]
/--
theorem `cons_fz` / 定理 `cons_fz`

English:
theorem cons_fz
  given: (a : α) (v : Vector3 α n)
  statement: (a :: v) fz = a
  proof: rfl

@[simp]

中文:
定理 cons_fz
  条件: (a : α) (v : Vector3 α n)
  结论: (a :: v) fz = a
  证明: rfl

@[simp]
-/
theorem cons_fz (a : α) (v : Vector3 α n) : (a :: v) fz = a :=
  rfl

@[simp]
/--
theorem `cons_fs` / 定理 `cons_fs`

English:
theorem cons_fs
  given: (a : α) (v : Vector3 α n) (i)
  statement: (a :: v) (fs i) = v i
  proof: rfl

中文:
定理 cons_fs
  条件: (a : α) (v : Vector3 α n) (i)
  结论: (a :: v) (fs i) = v i
  证明: rfl
-/
theorem cons_fs (a : α) (v : Vector3 α n) (i) : (a :: v) (fs i) = v i :=
  rfl

/--
Definition of `nth` / `nth` 的定义

English:
abbreviation nth
  signature: (i : Fin2 n) (v : Vector3 α n)
  body: v i

中文:
缩写 nth
  签名: (i : Fin2 n) (v : Vector3 α n)
  定义体: v i
-/
abbrev nth (i : Fin2 n) (v : Vector3 α n) : α :=
  v i

/--
Definition of `ofFn` / `ofFn` 的定义

English:
abbreviation ofFn
  signature: (f : Fin2 n -> α)
  body: f

中文:
缩写 ofFn
  签名: (f : Fin2 n -> α)
  定义体: f
-/
abbrev ofFn (f : Fin2 n -> α) : Vector3 α n :=
  f

/--
Definition of `head` / `head` 的定义

English:
definition head
  signature: (v : Vector3 α (n + 1))
  body: v fz

中文:
定义 head
  签名: (v : Vector3 α (n + 1))
  定义体: v fz
-/
def head (v : Vector3 α (n + 1)) : α :=
  v fz

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (v : Vector3 α (n + 1))
  body: fun i => v (fs i)

中文:
定义 tail
  签名: (v : Vector3 α (n + 1))
  定义体: fun i => v (fs i)
-/
def tail (v : Vector3 α (n + 1)) : Vector3 α n := fun i => v (fs i)

/--
theorem `eq_nil` / 定理 `eq_nil`

English:
theorem eq_nil
  given: (v : Vector3 α 0)
  statement: v = []
  proof: funext fun i => nomatch i

中文:
定理 eq_nil
  条件: (v : Vector3 α 0)
  结论: v = []
  证明: funext fun i => nomatch i

Depends on / 依赖: nomatch
-/
theorem eq_nil (v : Vector3 α 0) : v = [] :=
  funext fun i => nomatch i

/--
theorem `cons_head_tail` / 定理 `cons_head_tail`

English:
theorem cons_head_tail
  given: (v : Vector3 α (n + 1))
  statement: (head v :: tail v) = v
  proof: funext fun i => Fin2.cases' rfl (fun _ => rfl) i

中文:
定理 cons_head_tail
  条件: (v : Vector3 α (n + 1))
  结论: (head v :: tail v) = v
  证明: funext fun i => Fin2.cases' rfl (fun _ => rfl) i

Depends on / 依赖: Fin2.cases
-/
theorem cons_head_tail (v : Vector3 α (n + 1)) : (head v :: tail v) = v :=
  funext fun i => Fin2.cases' rfl (fun _ => rfl) i

/-- Eliminator for an empty vector. -/
@[elab_as_elim]
/--
Definition of `nilElim` / `nilElim` 的定义

English:
definition nilElim
  signature: {C : Vector3 α 0 -> Sort u} (H : C []) (v : Vector3 α 0)
  body: by
  rw [eq_nil v]; apply H

中文:
定义 nilElim
  签名: {C : Vector3 α 0 -> Sort u} (H : C []) (v : Vector3 α 0)
  定义体: by
  rw [eq_nil v]; apply H

Depends on / 依赖: eq_nil
-/
def nilElim {C : Vector3 α 0 -> Sort u} (H : C []) (v : Vector3 α 0) : C v := by
  rw [eq_nil v]; apply H

/-- Recursion principle for a nonempty vector. -/
@[elab_as_elim]
/--
Definition of `consElim` / `consElim` 的定义

English:
definition consElim
  signature: {C : Vector3 α (n + 1) -> Sort u} (H : forall (a : α) (t : Vector3 α n), C (a :: t))
  body: by rw [← cons_head_tail v]; apply H

@[simp]

中文:
定义 consElim
  签名: {C : Vector3 α (n + 1) -> Sort u} (H : 对任意 (a : α) (t : Vector3 α n), C (a :: t))
  定义体: by rw [← cons_head_tail v]; apply H

@[simp]

Depends on / 依赖: cons_head_tail
-/
def consElim {C : Vector3 α (n + 1) -> Sort u} (H : forall (a : α) (t : Vector3 α n), C (a :: t))
    (v : Vector3 α (n + 1)) : C v := by rw [← cons_head_tail v]; apply H

@[simp]
/--
theorem `consElim_cons` / 定理 `consElim_cons`

English:
theorem consElim_cons
  given: {C H a t}
  statement: @consElim α n C H (a :: t) = H a t
  proof: rfl

中文:
定理 consElim_cons
  条件: {C H a t}
  结论: @consElim α n C H (a :: t) = H a t
  证明: rfl
-/
theorem consElim_cons {C H a t} : @consElim α n C H (a :: t) = H a t :=
  rfl

/-- Recursion principle with the vector as first argument. -/
@[elab_as_elim]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: {C : forall {n}, Vector3 α n -> Sort u} {n} (v : Vector3 α n) (H0 : C [])
  body: match n with
  | 0 => v.nilElim H0
  | _ + 1 => v.consElim fun a t => Hs a t (Vector3.recOn t H0 Hs)

@[simp]

中文:
定义 recOn
  签名: {C : 对任意 {n}, Vector3 α n -> Sort u} {n} (v : Vector3 α n) (H0 : C [])
  定义体: match n with
  | 0 => v.nilElim H0
  | _ + 1 => v.consElim fun a t => Hs a t (Vector3.recOn t H0 Hs)

@[simp]
-/
protected def recOn {C : forall {n}, Vector3 α n -> Sort u} {n} (v : Vector3 α n) (H0 : C [])
    (Hs : forall {n} (a) (w : Vector3 α n), C w -> C (a :: w)) : C v :=
  match n with
  | 0 => v.nilElim H0
  | _ + 1 => v.consElim fun a t => Hs a t (Vector3.recOn t H0 Hs)

@[simp]
/--
theorem `recOn_nil` / 定理 `recOn_nil`

English:
theorem recOn_nil
  given: {C H0 Hs}
  statement: @Vector3.recOn α (@C) 0 [] H0 @Hs = H0
  proof: rfl

@[simp]

中文:
定理 recOn_nil
  条件: {C H0 Hs}
  结论: @Vector3.recOn α (@C) 0 [] H0 @Hs = H0
  证明: rfl

@[simp]
-/
theorem recOn_nil {C H0 Hs} : @Vector3.recOn α (@C) 0 [] H0 @Hs = H0 :=
  rfl

@[simp]
/--
theorem `recOn_cons` / 定理 `recOn_cons`

English:
theorem recOn_cons
  given: {C H0 Hs n a v}
  proof: rfl

中文:
定理 recOn_cons
  条件: {C H0 Hs n a v}
  证明: rfl
-/
theorem recOn_cons {C H0 Hs n a v} :
    @Vector3.recOn α (@C) (n + 1) (a :: v) H0 @Hs = Hs a v (@Vector3.recOn α (@C) n v H0 @Hs) :=
  rfl

/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: (v : Vector3 α m) (w : Vector3 α n)
  body: v.recOn w (fun a _ IH => a :: IH)

中文:
定义 append
  签名: (v : Vector3 α m) (w : Vector3 α n)
  定义体: v.recOn w (fun a _ IH => a :: IH)

Depends on / 依赖: v.recOn
-/
def append (v : Vector3 α m) (w : Vector3 α n) : Vector3 α (n + m) :=
  v.recOn w (fun a _ IH => a :: IH)

/--
A local infix notation for `Vector3.append`
-/
local infixl:65 " +-+ " => Vector3.append

@[simp]
/--
theorem `append_nil` / 定理 `append_nil`

English:
theorem append_nil
  given: (w : Vector3 α n)
  statement: [] +-+ w = w
  proof: rfl

@[simp]

中文:
定理 append_nil
  条件: (w : Vector3 α n)
  结论: [] +-+ w = w
  证明: rfl

@[simp]
-/
theorem append_nil (w : Vector3 α n) : [] +-+ w = w :=
  rfl

@[simp]
/--
theorem `append_cons` / 定理 `append_cons`

English:
theorem append_cons
  given: (a : α) (v : Vector3 α m) (w : Vector3 α n)
  statement: (a :: v) +-+ w = a :: v +-+ w
  proof: rfl

@[simp]

中文:
定理 append_cons
  条件: (a : α) (v : Vector3 α m) (w : Vector3 α n)
  结论: (a :: v) +-+ w = a :: v +-+ w
  证明: rfl

@[simp]
-/
theorem append_cons (a : α) (v : Vector3 α m) (w : Vector3 α n) : (a :: v) +-+ w = a :: v +-+ w :=
  rfl

@[simp]
/--
theorem `append_left` / 定理 `append_left`

English:
theorem append_left

中文:
定理 append_left
-/
theorem append_left :
    forall {m} (i : Fin2 m) (v : Vector3 α m) {n} (w : Vector3 α n), (v +-+ w) (left n i) = v i
  | _, @fz m, v, _, _ => v.consElim fun a _t => by simp [*, left]
  | _, @fs m i, v, n, w => v.consElim fun _a t => by simp [append_left, left]

@[simp]
/--
theorem `append_add` / 定理 `append_add`

English:
theorem append_add

中文:
定理 append_add
-/
theorem append_add :
    forall {m} (v : Vector3 α m) {n} (w : Vector3 α n) (i : Fin2 n), (v +-+ w) (add i m) = w i
  | 0, _, _, _, _ => rfl
  | m + 1, v, n, w, i => v.consElim fun _a t => by simp [append_add, add]

/--
Definition of `insert` / `insert` 的定义

English:
definition insert
  signature: (a : α) (v : Vector3 α n) (i : Fin2 (n + 1))
  body: fun j =>
  (a :: v) (insertPerm i j)

@[simp]

中文:
定义 insert
  签名: (a : α) (v : Vector3 α n) (i : Fin2 (n + 1))
  定义体: fun j =>
  (a :: v) (insertPerm i j)

@[simp]
-/
def insert (a : α) (v : Vector3 α n) (i : Fin2 (n + 1)) : Vector3 α (n + 1) := fun j =>
  (a :: v) (insertPerm i j)

@[simp]
/--
theorem `insert_fz` / 定理 `insert_fz`

English:
theorem insert_fz
  given: (a : α) (v : Vector3 α n)
  statement: insert a v fz = a :: v
  proof: by
  refine funext fun j => j.cases' ?_ ?_ <;> intros <;> rfl

@[simp]

中文:
定理 insert_fz
  条件: (a : α) (v : Vector3 α n)
  结论: insert a v fz = a :: v
  证明: by
  refine funext fun j => j.cases' ?_ ?_ <;> intros <;> rfl

@[simp]

Depends on / 依赖: intros, j.cases
-/
theorem insert_fz (a : α) (v : Vector3 α n) : insert a v fz = a :: v := by
  refine funext fun j => j.cases' ?_ ?_ <;> intros <;> rfl

@[simp]
/--
theorem `insert_fs` / 定理 `insert_fs`

English:
theorem insert_fs
  given: (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (n + 1))
  proof: funext fun j => by
    refine j.cases' (by simp [insert, insertPerm]) fun j => ?_
    simp only [insert, insertPerm, succ_eq_add_one, cons_fs]
    refine Fin2.cases' ?_ ?_ (insertPerm i j) <;> simp

中文:
定理 insert_fs
  条件: (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (n + 1))
  证明: funext fun j => by
    refine j.cases' (by simp [insert, insertPerm]) fun j => ?_
    simp only [insert, insertPerm, succ_eq_add_one, cons_fs]
    refine Fin2.cases' ?_ ?_ (insertPerm i j) <;> simp

Depends on / 依赖: Fin2.cases, cons_fs, insert, insertPerm, j.cases, succ_eq_add_one
-/
theorem insert_fs (a : α) (b : α) (v : Vector3 α n) (i : Fin2 (n + 1)) :
    insert a (b :: v) (fs i) = b :: insert a v i :=
  funext fun j => by
    refine j.cases' (by simp [insert, insertPerm]) fun j => ?_
    simp only [insert, insertPerm, succ_eq_add_one, cons_fs]
    refine Fin2.cases' ?_ ?_ (insertPerm i j) <;> simp

/--
theorem `append_insert` / 定理 `append_insert`

English:
theorem append_insert
  statement: (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1))
  proof: by
  refine Vector3.recOn t (fun e => ?_) (@fun k b t IH _ => ?_) e
  · rfl
  have e' : (n + 1) + k = (n + k) + 1 := by lia
  change
    insert a (b :: t +-+ v)
      (Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (add i k))) =
      Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (b :: t +-+ insert a

中文:
定理 append_insert
  结论: (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1))
  证明: by
  refine Vector3.recOn t (fun e => ?_) (@fun k b t IH _ => ?_) e
  · rfl
  have e' : (n + 1) + k = (n + k) + 1 := by lia
  change
    insert a (b :: t +-+ v)
      (Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (add i k))) =
      Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (b :: t +-+ insert a

Depends on / 依赖: Eq.recOn, Vector3, Vector3.recOn, congr_arg, i.add, insert
-/
theorem append_insert (a : α) (t : Vector3 α m) (v : Vector3 α n) (i : Fin2 (n + 1))
    (e : (n + 1) + m = (n + m) + 1) :
    insert a (t +-+ v) (Eq.recOn e (i.add m)) = Eq.recOn e (t +-+ insert a v i) := by
  refine Vector3.recOn t (fun e => ?_) (@fun k b t IH _ => ?_) e
  · rfl
  have e' : (n + 1) + k = (n + k) + 1 := by lia
  change
    insert a (b :: t +-+ v)
      (Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (add i k))) =
      Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (b :: t +-+ insert a v i)
  rw [← (Eq.recOn e' rfl :
      fs (Eq.recOn e' (i.add k) : Fin2 ((n + k) + 1)) =
        Eq.recOn (congr_arg (· + 1) e' : _ + 1 = _) (fs (i.add k)))]
  simpa [IH] using Eq.recOn e' rfl

end Vector3

section Vector3

open Vector3

/--
Definition of `VectorEx` / `VectorEx` 的定义

English:
definition VectorEx
  signature: : forall k, (Vector3 α k -> Prop) -> Prop

中文:
定义 VectorEx
  签名: : 对任意 k, (Vector3 α k -> 命题) -> 命题
-/
def VectorEx : forall k, (Vector3 α k -> Prop) -> Prop
  | 0, f => f []
  | succ k, f => exists x : α, VectorEx k fun v => f (x :: v)

/--
Definition of `VectorAll` / `VectorAll` 的定义

English:
definition VectorAll
  signature: : forall k, (Vector3 α k -> Prop) -> Prop

中文:
定义 VectorAll
  签名: : 对任意 k, (Vector3 α k -> 命题) -> 命题
-/
def VectorAll : forall k, (Vector3 α k -> Prop) -> Prop
  | 0, f => f []
  | succ k, f => forall x : α, VectorAll k fun v => f (x :: v)

/--
theorem `exists_vector_zero` / 定理 `exists_vector_zero`

English:
theorem exists_vector_zero
  given: (f : Vector3 α 0 -> Prop)
  statement: Exists f ↔ f []
  proof: ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v]; exact fv, fun f0 => ⟨[], f0⟩⟩

中文:
定理 exists_vector_zero
  条件: (f : Vector3 α 0 -> 命题)
  结论: Exists f ↔ f []
  证明: ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v]; exact fv, fun f0 => ⟨[], f0⟩⟩

Depends on / 依赖: eq_nil
-/
theorem exists_vector_zero (f : Vector3 α 0 -> Prop) : Exists f ↔ f [] :=
  ⟨fun ⟨v, fv⟩ => by rw [← eq_nil v]; exact fv, fun f0 => ⟨[], f0⟩⟩

/--
theorem `exists_vector_succ` / 定理 `exists_vector_succ`

English:
theorem exists_vector_succ
  given: (f : Vector3 α (succ n) -> Prop)
  statement: Exists f ↔ exists x v, f (x :: v)
  proof: ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v]; exact fv⟩, fun ⟨_, _, fxv⟩ => ⟨_, fxv⟩⟩

中文:
定理 exists_vector_succ
  条件: (f : Vector3 α (succ n) -> 命题)
  结论: Exists f ↔ 存在 x v, f (x :: v)
  证明: ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v]; exact fv⟩, fun ⟨_, _, fxv⟩ => ⟨_, fxv⟩⟩

Depends on / 依赖: cons_head_tail
-/
theorem exists_vector_succ (f : Vector3 α (succ n) -> Prop) : Exists f ↔ exists x v, f (x :: v) :=
  ⟨fun ⟨v, fv⟩ => ⟨_, _, by rw [cons_head_tail v]; exact fv⟩, fun ⟨_, _, fxv⟩ => ⟨_, fxv⟩⟩

/--
theorem `vectorEx_iff_exists` / 定理 `vectorEx_iff_exists`

English:
theorem vectorEx_iff_exists
  statement: forall {n} (f : Vector3 α n -> Prop), VectorEx n f ↔ Exists f

中文:
定理 vectorEx_iff_exists
  结论: 对任意 {n} (f : Vector3 α n -> 命题), VectorEx n f ↔ Exists f
-/
theorem vectorEx_iff_exists : forall {n} (f : Vector3 α n -> Prop), VectorEx n f ↔ Exists f
  | 0, f => (exists_vector_zero f).symm
  | succ _, f =>
    Iff.trans (exists_congr fun _ => vectorEx_iff_exists _) (exists_vector_succ f).symm

/--
theorem `vectorAll_iff_forall` / 定理 `vectorAll_iff_forall`

English:
theorem vectorAll_iff_forall
  statement: forall {n} (f : Vector3 α n -> Prop), VectorAll n f ↔ forall v, f v

中文:
定理 vectorAll_iff_forall
  结论: 对任意 {n} (f : Vector3 α n -> 命题), VectorAll n f ↔ 对任意 v, f v
-/
theorem vectorAll_iff_forall : forall {n} (f : Vector3 α n -> Prop), VectorAll n f ↔ forall v, f v
  | 0, _ => ⟨fun f0 v => v.nilElim f0, fun al => al []⟩
  | succ _, f =>
    (forall_congr' fun x => vectorAll_iff_forall fun v => f (x :: v)).trans
      ⟨fun al v => v.consElim al, fun al x v => al (x :: v)⟩

/--
Definition of `VectorAllP` / `VectorAllP` 的定义

English:
definition VectorAllP
  signature: (p : α -> Prop) (v : Vector3 α n)
  body: Vector3.recOn v True fun a v IH =>
    @Vector3.recOn _ (fun _ => Prop) _ v (p a) fun _ _ _ => p a ∧ IH

@[simp]

中文:
定义 VectorAllP
  签名: (p : α -> 命题) (v : Vector3 α n)
  定义体: Vector3.recOn v True fun a v IH =>
    @Vector3.recOn _ (fun _ => Prop) _ v (p a) fun _ _ _ => p a ∧ IH

@[simp]

Depends on / 依赖: Vector3, Vector3.recOn
-/
def VectorAllP (p : α -> Prop) (v : Vector3 α n) : Prop :=
  Vector3.recOn v True fun a v IH =>
    @Vector3.recOn _ (fun _ => Prop) _ v (p a) fun _ _ _ => p a ∧ IH

@[simp]
/--
theorem `vectorAllP_nil` / 定理 `vectorAllP_nil`

English:
theorem vectorAllP_nil
  given: (p : α -> Prop)
  statement: VectorAllP p [] = True
  proof: rfl

@[simp]

中文:
定理 vectorAllP_nil
  条件: (p : α -> 命题)
  结论: VectorAllP p [] = True
  证明: rfl

@[simp]
-/
theorem vectorAllP_nil (p : α -> Prop) : VectorAllP p [] = True :=
  rfl

@[simp]
/--
theorem `vectorAllP_singleton` / 定理 `vectorAllP_singleton`

English:
theorem vectorAllP_singleton
  given: (p : α -> Prop) (x : α)
  statement: VectorAllP p (cons x []) = p x
  proof: rfl

@[simp]

中文:
定理 vectorAllP_singleton
  条件: (p : α -> 命题) (x : α)
  结论: VectorAllP p (cons x []) = p x
  证明: rfl

@[simp]
-/
theorem vectorAllP_singleton (p : α -> Prop) (x : α) : VectorAllP p (cons x []) = p x :=
  rfl

@[simp]
/--
theorem `vectorAllP_cons` / 定理 `vectorAllP_cons`

English:
theorem vectorAllP_cons
  given: (p : α -> Prop) (x : α) (v : Vector3 α n)
  proof: Vector3.recOn v (iff_of_eq (and_true _)).symm fun _ _ _ => Iff.rfl

中文:
定理 vectorAllP_cons
  条件: (p : α -> 命题) (x : α) (v : Vector3 α n)
  证明: Vector3.recOn v (iff_of_eq (and_true _)).symm fun _ _ _ => Iff.rfl

Depends on / 依赖: Iff.rfl, Vector3, Vector3.recOn, and_true, iff_of_eq
-/
theorem vectorAllP_cons (p : α -> Prop) (x : α) (v : Vector3 α n) :
    VectorAllP p (x :: v) ↔ p x ∧ VectorAllP p v :=
  Vector3.recOn v (iff_of_eq (and_true _)).symm fun _ _ _ => Iff.rfl

/--
theorem `vectorAllP_iff_forall` / 定理 `vectorAllP_iff_forall`

English:
theorem vectorAllP_iff_forall
  given: (p : α -> Prop) (v : Vector3 α n)
  proof: by
  refine v.recOn ?_ ?_
  · exact ⟨fun _ => Fin2.elim0, fun _ => trivial⟩
  · simp only [vectorAllP_cons]
    refine fun {n} a v IH =>
      (and_congr_right fun _ => IH).trans
        ⟨fun ⟨pa, h⟩ i => by
          refine i.cases' ?_ ?_
          exacts [pa, h], fun h => ⟨?_, fun i => ?_⟩⟩
    · 

中文:
定理 vectorAllP_iff_forall
  条件: (p : α -> 命题) (v : Vector3 α n)
  证明: by
  refine v.recOn ?_ ?_
  · exact ⟨fun _ => Fin2.elim0, fun _ => trivial⟩
  · simp only [vectorAllP_cons]
    refine fun {n} a v IH =>
      (and_congr_right fun _ => IH).trans
        ⟨fun ⟨pa, h⟩ i => by
          refine i.cases' ?_ ?_
          exacts [pa, h], fun h => ⟨?_, fun i => ?_⟩⟩
    · 

Depends on / 依赖: Fin2.elim0, and_congr_right, exacts, i.cases, v.recOn, vectorAllP_cons
-/
theorem vectorAllP_iff_forall (p : α -> Prop) (v : Vector3 α n) :
    VectorAllP p v ↔ forall i, p (v i) := by
  refine v.recOn ?_ ?_
  · exact ⟨fun _ => Fin2.elim0, fun _ => trivial⟩
  · simp only [vectorAllP_cons]
    refine fun {n} a v IH =>
      (and_congr_right fun _ => IH).trans
        ⟨fun ⟨pa, h⟩ i => by
          refine i.cases' ?_ ?_
          exacts [pa, h], fun h => ⟨?_, fun i => ?_⟩⟩
    · simpa using h fz
    · simpa using h (fs i)

/--
theorem `VectorAllP.imp` / 定理 `VectorAllP.imp`

English:
theorem VectorAllP.imp
  statement: {p q : α -> Prop} (h : forall x, p x -> q x) {v : Vector3 α n}
  proof: (vectorAllP_iff_forall _ _).2 fun _ => h _ (vectorAllP_iff_forall _ _).1 al _

中文:
定理 VectorAllP.imp
  结论: {p q : α -> 命题} (h : 对任意 x, p x -> q x) {v : Vector3 α n}
  证明: (vectorAllP_iff_forall _ _).2 fun _ => h _ (vectorAllP_iff_forall _ _).1 al _

Depends on / 依赖: vectorAllP_iff_forall
-/
theorem VectorAllP.imp {p q : α -> Prop} (h : forall x, p x -> q x) {v : Vector3 α n}
    (al : VectorAllP p v) : VectorAllP q v :=
(vectorAllP_iff_forall _ _).2 fun _ => h _ (vectorAllP_iff_forall _ _).1 al _

end Vector3
