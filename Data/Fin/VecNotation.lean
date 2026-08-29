/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Eric Wieser
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Matrix and vector notation

This file defines notation for vectors and matrices. Given `a b c d : α`,
the notation allows us to write `![a, b, c, d] : Fin 4 → α`.
Nesting vectors gives coefficients of a matrix, so `![![a, b], ![c, d]] : Fin 2 → Fin 2 → α`.
In later files we introduce `!![a, b; c, d]` as notation for `Matrix.of ![![a, b], ![c, d]]`.

## Main definitions

* `vecEmpty` is the empty vector (or `0` by `n` matrix) `![]`
* `vecCons` prepends an entry to a vector, so `![a, b]` is `vecCons a (vecCons b vecEmpty)`

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vecCons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notation

The main new notation is `![a, b]`, which gets expanded to `vecCons a (vecCons b vecEmpty)`.

## Examples

Examples of usage can be found in the `MathlibTest/matrix.lean` file.
-/

@[expose] public section


namespace Matrix

universe u

variable {α : Type u}

section MatrixNotation

/--
Definition of `vecEmpty` / `vecEmpty` 的定义

English:
definition vecEmpty
  signature: : Fin 0 -> α
  body: Fin.elim0

中文:
定义 vecEmpty
  签名: : 有限集 0 -> α
  定义体: Fin.elim0

Depends on / 依赖: Fin.elim0
-/
def vecEmpty : Fin 0 -> α :=
  Fin.elim0

/--
Definition of `vecCons` / `vecCons` 的定义

English:
definition vecCons
  signature: {n : Nat} (h : α) (t : Fin n -> α)
  body: Fin.cons h t

中文:
定义 vecCons
  签名: {n : 自然数} (h : α) (t : 有限集 n -> α)
  定义体: Fin.cons h t

Depends on / 依赖: Fin.cons
-/
def vecCons {n : Nat} (h : α) (t : Fin n -> α) : Fin n.succ -> α :=
  Fin.cons h t

/-- `![...]` notation is used to construct a vector `Fin n → α` using `Matrix.vecEmpty` and
`Matrix.vecCons`.

For instance, `![a, b, c] : Fin 3` is syntax for `vecCons a (vecCons b (vecCons c vecEmpty))`.

Note that this should not be used as syntax for `Matrix` as it generates a term with the wrong type.
The `!![a, b; c, d]` syntax (provided by `Matrix.matrixNotation`) should be used instead.
-/
syntax (name := vecNotation) "![" term,* "]" : term

macro_rules
  | `(![$term:term, $terms:term,*]) => `(vecCons $term ![$terms,*])
  | `(![$term:term]) => `(vecCons $term ![])
  | `(![]) => `(vecEmpty)

/-- Unexpander for the `![x, y, ...]` notation. -/
@[app_unexpander vecCons]
meta def vecConsUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term ![$term2, $terms,*]) => `(![$term, $term2, $terms,*])
  | `($_ $term ![$term2]) => `(![$term, $term2])
  | `($_ $term ![]) => `(![$term])
  | _ => throw ()

/-- Unexpander for the `![]` notation. -/
@[app_unexpander vecEmpty]
meta def vecEmptyUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(![])
  | _ => throw ()

/--
Definition of `vecHead` / `vecHead` 的定义

English:
definition vecHead
  signature: {n : Nat} (v : Fin n.succ -> α)
  body: v 0

中文:
定义 vecHead
  签名: {n : 自然数} (v : 有限集 n.succ -> α)
  定义体: v 0
-/
def vecHead {n : Nat} (v : Fin n.succ -> α) : α :=
  v 0

/--
Definition of `vecTail` / `vecTail` 的定义

English:
definition vecTail
  signature: {n : Nat} (v : Fin n.succ -> α)
  body: v ∘ Fin.succ

中文:
定义 vecTail
  签名: {n : 自然数} (v : 有限集 n.succ -> α)
  定义体: v ∘ Fin.succ

Depends on / 依赖: Fin.succ
-/
def vecTail {n : Nat} (v : Fin n.succ -> α) : Fin n -> α :=
  v ∘ Fin.succ

variable {m n : Nat}

/--
Instance `_root_.PiFin.hasRepr` / 实例 `_root_.PiFin.hasRepr`

English:
instance _root_.PiFin.hasRepr
  signature: [Repr α]
  body: Std.Format.bracket "![" (Std.Format.joinSep
      ((List.finRange n).map fun n => repr (f n)) ("," ++ Std.Format.line)) "]"

中文:
实例 _root_.PiFin.hasRepr
  签名: [Repr α]
  定义体: Std.Format.bracket "![" (Std.Format.joinSep
      ((List.finRange n).map fun n => repr (f n)) ("," ++ Std.Format.line)) "]"

Depends on / 依赖: Format, List.finRange, Std.Format.bracket, Std.Format.joinSep, Std.Format.line, bracket, finRange, joinSep
-/
instance _root_.PiFin.hasRepr [Repr α] : Repr (Fin n -> α) where
  reprPrec f _ :=
    Std.Format.bracket "![" (Std.Format.joinSep
      ((List.finRange n).map fun n => repr (f n)) ("," ++ Std.Format.line)) "]"

end MatrixNotation

variable {m n o : Nat}

/--
theorem `empty_eq` / 定理 `empty_eq`

English:
theorem empty_eq
  given: (v : Fin 0 -> α)
  statement: v = ![]
  proof: Subsingleton.elim _ _

中文:
定理 empty_eq
  条件: (v : 有限集 0 -> α)
  结论: v = ![]
  证明: Subsingleton.elim _ _

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem empty_eq (v : Fin 0 -> α) : v = ![] :=
  Subsingleton.elim _ _

section Val

@[simp]
/--
theorem `head_fin_const` / 定理 `head_fin_const`

English:
theorem head_fin_const
  given: (a : α)
  statement: (vecHead fun _ : Fin (n + 1) => a) = a
  proof: rfl

@[simp]

中文:
定理 head_fin_const
  条件: (a : α)
  结论: (vecHead fun _ : 有限集 (n + 1) => a) = a
  证明: rfl

@[simp]
-/
theorem head_fin_const (a : α) : (vecHead fun _ : Fin (n + 1) => a) = a :=
  rfl

@[simp]
/--
theorem `cons_val_zero` / 定理 `cons_val_zero`

English:
theorem cons_val_zero
  given: (x : α) (u : Fin m -> α)
  statement: vecCons x u 0 = x
  proof: rfl

中文:
定理 cons_val_zero
  条件: (x : α) (u : 有限集 m -> α)
  结论: vecCons x u 0 = x
  证明: rfl
-/
theorem cons_val_zero (x : α) (u : Fin m -> α) : vecCons x u 0 = x :=
  rfl

/--
theorem `cons_val_zero'` / 定理 `cons_val_zero'`

English:
theorem cons_val_zero'
  given: (h : 0 < m.succ) (x : α) (u : Fin m -> α)
  statement: vecCons x u ⟨0, h⟩ = x
  proof: rfl

@[simp]

中文:
定理 cons_val_zero'
  条件: (h : 0 < m.succ) (x : α) (u : 有限集 m -> α)
  结论: vecCons x u ⟨0, h⟩ = x
  证明: rfl

@[simp]
-/
theorem cons_val_zero' (h : 0 < m.succ) (x : α) (u : Fin m -> α) : vecCons x u ⟨0, h⟩ = x :=
  rfl

@[simp]
/--
theorem `cons_val_succ` / 定理 `cons_val_succ`

English:
theorem cons_val_succ
  given: (x : α) (u : Fin m -> α) (i : Fin m)
  statement: vecCons x u i.succ = u i
  proof: by
  simp [vecCons]

@[simp]

中文:
定理 cons_val_succ
  条件: (x : α) (u : 有限集 m -> α) (i : 有限集 m)
  结论: vecCons x u i.succ = u i
  证明: by
  simp [vecCons]

@[simp]

Depends on / 依赖: vecCons
-/
theorem cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m) : vecCons x u i.succ = u i := by
  simp [vecCons]

@[simp]
/--
theorem `cons_val_succ'` / 定理 `cons_val_succ'`

English:
theorem cons_val_succ'
  given: {i : Nat} (h : i.succ < m.succ) (x : α) (u : Fin m -> α)
  proof: by
  simp only [vecCons, Fin.cons, Fin.cases_succ']

中文:
定理 cons_val_succ'
  条件: {i : 自然数} (h : i.succ < m.succ) (x : α) (u : 有限集 m -> α)
  证明: by
  simp only [vecCons, Fin.cons, Fin.cases_succ']

Depends on / 依赖: Fin.cases_succ, Fin.cons, cases_succ, vecCons
-/
theorem cons_val_succ' {i : Nat} (h : i.succ < m.succ) (x : α) (u : Fin m -> α) :
    vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ h⟩ := by
  simp only [vecCons, Fin.cons, Fin.cases_succ']

/-- We don't want to always simplify `Fin.cons` to `vecCons`.
But in cases that we are already mixing the declarations for dependent tuples and non-dependent
tuples, we can simplify to the non-dependent tuples. -/
@[simp]
/--
lemma `Fin.cons_vecEmpty` / 引理 `Fin.cons_vecEmpty`

English:
lemma Fin.cons_vecEmpty
  given: {α : Type*} (x : α)
  statement: Fin.cons x ![] = ![x]
  proof: by rfl

中文:
引理 有限集.cons_vecEmpty
  条件: {α : 类型} (x : α)
  结论: 有限集.cons x ![] = ![x]
  证明: by rfl
-/
lemma Fin.cons_vecEmpty {α : Type*} (x : α) : Fin.cons x ![] = ![x] := by rfl

/-- Simplify `Fin.snoc` to `vecCons` in this case. -/
@[simp]
/--
lemma `Fin.snoc_vecEmpty` / 引理 `Fin.snoc_vecEmpty`

English:
lemma Fin.snoc_vecEmpty
  given: {α : Type*} (x : α)
  statement: Fin.snoc ![] x = ![x]
  proof: by
  ext i
  cases Fin.fin_one_eq_zero i
  rfl

中文:
引理 有限集.snoc_vecEmpty
  条件: {α : 类型} (x : α)
  结论: 有限集.snoc ![] x = ![x]
  证明: by
  ext i
  cases Fin.fin_one_eq_zero i
  rfl

Depends on / 依赖: Fin.fin_one_eq_zero, fin_one_eq_zero
-/
lemma Fin.snoc_vecEmpty {α : Type*} (x : α) : Fin.snoc ![] x = ![x] := by
  ext i
  cases Fin.fin_one_eq_zero i
  rfl

/-- We don't want to always simplify `Fin.cons` to `vecCons`.
But in cases that we are already mixing the declarations for dependent tuples and non-dependent
tuples, we can simplify to the non-dependent tuples.
This allows us to simplify `Fin.cons 5 ![1, 3, 7]` to `![5, 1, 3, 7]`. -/
@[simp]
/--
lemma `Fin.cons_vecCons` / 引理 `Fin.cons_vecCons`

English:
lemma Fin.cons_vecCons
  given: {α : Type*} (x y : α) (p : Fin n -> α)
  proof: by rfl

中文:
引理 有限集.cons_vecCons
  条件: {α : 类型} (x y : α) (p : 有限集 n -> α)
  证明: by rfl
-/
lemma Fin.cons_vecCons {α : Type*} (x y : α) (p : Fin n -> α) :
  Fin.cons x (vecCons y p) = vecCons x (vecCons y p) := by rfl

/-- We push `Fin.snoc` inside `vecCons`. This allows us to simplify e.g.
`Fin.snoc ![1, 3, 7] 5` to `![1, 3, 7, 5]`. -/
@[simp]
/--
lemma `Fin.snoc_vecCons` / 引理 `Fin.snoc_vecCons`

English:
lemma Fin.snoc_vecCons
  given: {α : Type*} (x y : α) (p : Fin n -> α)
  proof: .symm Fin.cons_snoc_eq_snoc_cons ..

中文:
引理 有限集.snoc_vecCons
  条件: {α : 类型} (x y : α) (p : 有限集 n -> α)
  证明: .symm Fin.cons_snoc_eq_snoc_cons ..

Depends on / 依赖: Fin.cons_snoc_eq_snoc_cons, cons_snoc_eq_snoc_cons
-/
lemma Fin.snoc_vecCons {α : Type*} (x y : α) (p : Fin n -> α) :
    Fin.snoc (vecCons y p) x = vecCons y (Fin.snoc p x) :=
.symm Fin.cons_snoc_eq_snoc_cons ..

section simprocs
open Lean Qq

/-- Parses a chain of `Matrix.vecCons` calls into elements, leaving everything else in the tail.

`let ⟨xs, tailn, tail⟩ ← matchVecConsPrefix n e` decomposes `e : Fin n → _` in the form
`vecCons x₀ <| ... <| vecCons xₙ <| tail` where `tail : Fin tailn → _`. -/
meta partial def matchVecConsPrefix (n : Q(Nat)) (e : Expr) :
MetaM List Expr × Q(Nat) × Expr := do
  match_expr ← Meta.whnfR e with
  | Matrix.vecCons _ n x xs => do
    let (elems, n', tail) ← matchVecConsPrefix n xs
    return (x :: elems, n', tail)
  | _ =>
    return ([], n, e)

open Qq in
/-- A simproc that handles terms of the form `Matrix.vecCons a f i` where `i` is a numeric literal.

In practice, this is most effective at handling `![a, b, c] i`-style terms. -/
dsimproc cons_val (Matrix.vecCons _ _ _) := fun e => do
  let_expr Matrix.vecCons α en x xs' ei := ← Meta.whnfR e | return .continue
  let some i := ei.int? | return .continue
  let (xs, etailn, tail) ← matchVecConsPrefix en xs'
  let xs := x :: xs
  -- Determine if the tail is a numeral or only an offset.
  let (tailn, variadic, etailn) ← do
    let etailn_whnf : Q(Nat) ← Meta.whnfD etailn
    if let Expr.lit (.natVal length) := etailn_whnf then
      pure (length, false, q(OfNat.ofNat $etailn_whnf))
    else if let some ((base : Q(Nat)), offset) ← (Meta.isOffset? etailn_whnf).run then
      pure (offset, true, q($base + $offset))
    else
      pure (0, true, etailn)
  -- Wrap the index if possible, and abort if not
  let wrapped_i ←
    if variadic then
      -- can't wrap as we don't know the length
      unless 0 <= i ∧ i < xs.length + tailn do return .continue
      pure i.toNat
    else
      pure (i % (xs.length + tailn)).toNat
  if h : wrapped_i < xs.length then
    return .continue xs[wrapped_i]
  else
    -- Within the `tail`
    let _ ← synthInstanceQ q(NeZero $etailn)
    have i_lit : Q(Nat) := mkRawNatLit (wrapped_i - xs.length)
    return .continue (.some <| .app tail q(OfNat.ofNat $i_lit : Fin $etailn))

end simprocs

@[simp]
/--
theorem `head_cons` / 定理 `head_cons`

English:
theorem head_cons
  given: (x : α) (u : Fin m -> α)
  statement: vecHead (vecCons x u) = x
  proof: rfl

@[simp]

中文:
定理 head_cons
  条件: (x : α) (u : 有限集 m -> α)
  结论: vecHead (vecCons x u) = x
  证明: rfl

@[simp]
-/
theorem head_cons (x : α) (u : Fin m -> α) : vecHead (vecCons x u) = x :=
  rfl

@[simp]
/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  given: (x : α) (u : Fin m -> α)
  statement: vecTail (vecCons x u) = u
  proof: by
  ext
  simp [vecTail]

@[simp]

中文:
定理 tail_cons
  条件: (x : α) (u : 有限集 m -> α)
  结论: vecTail (vecCons x u) = u
  证明: by
  ext
  simp [vecTail]

@[simp]

Depends on / 依赖: vecTail
-/
theorem tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons x u) = u := by
  ext
  simp [vecTail]

@[simp]
/--
theorem `_root_.Fin.tail_vecCons` / 定理 `_root_.Fin.tail_vecCons`

English:
theorem _root_.Fin.tail_vecCons
  given: (x : α) (t : Fin n -> α)
  statement: Fin.tail (Matrix.vecCons x t) = t
  proof: rfl

中文:
定理 _root_.有限集.tail_vecCons
  条件: (x : α) (t : 有限集 n -> α)
  结论: 有限集.tail (矩阵.vecCons x t) = t
  证明: rfl
-/
theorem _root_.Fin.tail_vecCons (x : α) (t : Fin n -> α) : Fin.tail (Matrix.vecCons x t) = t :=
  rfl

/--
theorem `empty_val'` / 定理 `empty_val'`

English:
theorem empty_val'
  given: {n' : Type*} (j : n')
  statement: (fun i => (![] : Fin 0 -> n' -> α) i j) = ![]
  proof: empty_eq _

@[simp]

中文:
定理 empty_val'
  条件: {n' : 类型} (j : n')
  结论: (fun i => (![] : 有限集 0 -> n' -> α) i j) = ![]
  证明: empty_eq _

@[simp]

Depends on / 依赖: empty_eq
-/
theorem empty_val' {n' : Type*} (j : n') : (fun i => (![] : Fin 0 -> n' -> α) i j) = ![] :=
  empty_eq _

@[simp]
/--
theorem `cons_head_tail` / 定理 `cons_head_tail`

English:
theorem cons_head_tail
  given: (u : Fin m.succ -> α)
  statement: vecCons (vecHead u) (vecTail u) = u
  proof: Fin.cons_self_tail _

@[simp]

中文:
定理 cons_head_tail
  条件: (u : 有限集 m.succ -> α)
  结论: vecCons (vecHead u) (vecTail u) = u
  证明: Fin.cons_self_tail _

@[simp]

Depends on / 依赖: Fin.cons_self_tail, cons_self_tail
-/
theorem cons_head_tail (u : Fin m.succ -> α) : vecCons (vecHead u) (vecTail u) = u :=
  Fin.cons_self_tail _

@[simp]
/--
theorem `range_cons` / 定理 `range_cons`

English:
theorem range_cons
  given: (x : α) (u : Fin n -> α)
  statement: Set.range (vecCons x u) = {x} union Set.range u
  proof: Set.ext fun y => by simp [Fin.exists_fin_succ, eq_comm]

@[simp]

中文:
定理 range_cons
  条件: (x : α) (u : 有限集 n -> α)
  结论: 集合.range (vecCons x u) = {x} union 集合.range u
  证明: Set.ext fun y => by simp [Fin.exists_fin_succ, eq_comm]

@[simp]

Depends on / 依赖: Fin.exists_fin_succ, Set.ext, eq_comm, exists_fin_succ
-/
theorem range_cons (x : α) (u : Fin n -> α) : Set.range (vecCons x u) = {x} union Set.range u :=
  Set.ext fun y => by simp [Fin.exists_fin_succ, eq_comm]

@[simp]
/--
theorem `range_empty` / 定理 `range_empty`

English:
theorem range_empty
  given: (u : Fin 0 -> α)
  statement: Set.range u = ∅
  proof: Set.range_eq_empty _

中文:
定理 range_empty
  条件: (u : 有限集 0 -> α)
  结论: 集合.range u = ∅
  证明: Set.range_eq_empty _

Depends on / 依赖: Set.range_eq_empty, range_eq_empty
-/
theorem range_empty (u : Fin 0 -> α) : Set.range u = ∅ :=
  Set.range_eq_empty _

/--
theorem `range_cons_empty` / 定理 `range_cons_empty`

English:
theorem range_cons_empty
  given: (x : α) (u : Fin 0 -> α)
  statement: Set.range (Matrix.vecCons x u) = {x}
  proof: by
  rw [range_cons]; rw [range_empty]; rw [Set.union_empty]

中文:
定理 range_cons_empty
  条件: (x : α) (u : 有限集 0 -> α)
  结论: 集合.range (矩阵.vecCons x u) = {x}
  证明: by
  rw [range_cons]; rw [range_empty]; rw [Set.union_empty]

Depends on / 依赖: Set.union_empty, range_cons, range_empty, union_empty
-/
theorem range_cons_empty (x : α) (u : Fin 0 -> α) : Set.range (Matrix.vecCons x u) = {x} := by
  rw [range_cons]; rw [range_empty]; rw [Set.union_empty]

-- simp can prove this (up to commutativity)
/--
theorem `range_cons_cons_empty` / 定理 `range_cons_cons_empty`

English:
theorem range_cons_cons_empty
  given: (x y : α) (u : Fin 0 -> α)
  proof: by
  rw [range_cons]; rw [range_cons_empty]; rw [Set.singleton_union]

中文:
定理 range_cons_cons_empty
  条件: (x y : α) (u : 有限集 0 -> α)
  证明: by
  rw [range_cons]; rw [range_cons_empty]; rw [Set.singleton_union]

Depends on / 依赖: Set.singleton_union, range_cons, range_cons_empty, singleton_union
-/
theorem range_cons_cons_empty (x y : α) (u : Fin 0 -> α) :
    Set.range (vecCons x <| vecCons y u) = {x, y} := by
  rw [range_cons]; rw [range_cons_empty]; rw [Set.singleton_union]

/--
theorem `vecCons_const` / 定理 `vecCons_const`

English:
theorem vecCons_const
  given: (a : α)
  statement: (vecCons a fun _ : Fin n => a) = fun _ => a
  proof: funext Fin.forall_iff_succ.2 ⟨rfl, cons_val_succ _ _⟩

中文:
定理 vecCons_const
  条件: (a : α)
  结论: (vecCons a fun _ : 有限集 n => a) = fun _ => a
  证明: funext Fin.forall_iff_succ.2 ⟨rfl, cons_val_succ _ _⟩

Depends on / 依赖: Fin.forall_iff_succ, cons_val_succ, forall_iff_succ
-/
theorem vecCons_const (a : α) : (vecCons a fun _ : Fin n => a) = fun _ => a :=
funext Fin.forall_iff_succ.2 ⟨rfl, cons_val_succ _ _⟩

/--
theorem `vec_single_eq_const` / 定理 `vec_single_eq_const`

English:
theorem vec_single_eq_const
  given: (a : α)
  statement: ![a] = fun _ => a
  proof: funext Unique.forall_iff.2 rfl

中文:
定理 vec_single_eq_const
  条件: (a : α)
  结论: ![a] = fun _ => a
  证明: funext Unique.forall_iff.2 rfl

Depends on / 依赖: Unique, Unique.forall_iff, forall_iff
-/
theorem vec_single_eq_const (a : α) : ![a] = fun _ => a :=
funext Unique.forall_iff.2 rfl

/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : Fin 1 = 0 : Fin 1`.
-/
@[simp]
/--
theorem `cons_val_one` / 定理 `cons_val_one`

English:
theorem cons_val_one
  given: (x : α) (u : Fin m.succ -> α)
  statement: vecCons x u 1 = u 0
  proof: rfl

中文:
定理 cons_val_one
  条件: (x : α) (u : 有限集 m.succ -> α)
  结论: vecCons x u 1 = u 0
  证明: rfl
-/
theorem cons_val_one (x : α) (u : Fin m.succ -> α) : vecCons x u 1 = u 0 :=
  rfl

/--
theorem `cons_val_two` / 定理 `cons_val_two`

English:
theorem cons_val_two
  given: (x : α) (u : Fin m.succ.succ -> α)
  statement: vecCons x u 2 = vecHead (vecTail u)
  proof: rfl

中文:
定理 cons_val_two
  条件: (x : α) (u : 有限集 m.succ.succ -> α)
  结论: vecCons x u 2 = vecHead (vecTail u)
  证明: rfl
-/
theorem cons_val_two (x : α) (u : Fin m.succ.succ -> α) : vecCons x u 2 = vecHead (vecTail u) := rfl

/--
lemma `cons_val_three` / 引理 `cons_val_three`

English:
lemma cons_val_three
  given: (x : α) (u : Fin m.succ.succ.succ -> α)
  proof: rfl

中文:
引理 cons_val_three
  条件: (x : α) (u : 有限集 m.succ.succ.succ -> α)
  证明: rfl
-/
lemma cons_val_three (x : α) (u : Fin m.succ.succ.succ -> α) :
    vecCons x u 3 = vecHead (vecTail (vecTail u)) :=
  rfl

/--
lemma `cons_val_four` / 引理 `cons_val_four`

English:
lemma cons_val_four
  given: (x : α) (u : Fin m.succ.succ.succ.succ -> α)
  proof: rfl

@[simp]

中文:
引理 cons_val_four
  条件: (x : α) (u : 有限集 m.succ.succ.succ.succ -> α)
  证明: rfl

@[simp]
-/
lemma cons_val_four (x : α) (u : Fin m.succ.succ.succ.succ -> α) :
    vecCons x u 4 = vecHead (vecTail (vecTail (vecTail u))) :=
  rfl

@[simp]
/--
theorem `cons_val_fin_one` / 定理 `cons_val_fin_one`

English:
theorem cons_val_fin_one
  given: (x : α) (u : Fin 0 -> α)
  statement: forall (i : Fin 1), vecCons x u i = x
  proof: by
  rw [Fin.forall_fin_one]
  rfl

中文:
定理 cons_val_fin_one
  条件: (x : α) (u : 有限集 0 -> α)
  结论: 对任意 (i : 有限集 1), vecCons x u i = x
  证明: by
  rw [Fin.forall_fin_one]
  rfl

Depends on / 依赖: Fin.forall_fin_one, forall_fin_one
-/
theorem cons_val_fin_one (x : α) (u : Fin 0 -> α) : forall (i : Fin 1), vecCons x u i = x := by
  rw [Fin.forall_fin_one]
  rfl

/--
theorem `cons_fin_one` / 定理 `cons_fin_one`

English:
theorem cons_fin_one
  given: (x : α) (u : Fin 0 -> α)
  statement: vecCons x u = fun _ => x
  proof: funext (cons_val_fin_one x u)

@[simp]

中文:
定理 cons_fin_one
  条件: (x : α) (u : 有限集 0 -> α)
  结论: vecCons x u = fun _ => x
  证明: funext (cons_val_fin_one x u)

@[simp]

Depends on / 依赖: cons_val_fin_one
-/
theorem cons_fin_one (x : α) (u : Fin 0 -> α) : vecCons x u = fun _ => x :=
  funext (cons_val_fin_one x u)

@[simp]
/--
theorem `vecCons_inj` / 定理 `vecCons_inj`

English:
theorem vecCons_inj
  given: {x y : α} {u v : Fin n -> α}
  statement: vecCons x u = vecCons y v ↔ x = y ∧ u = v
  proof: Fin.cons_inj

中文:
定理 vecCons_inj
  条件: {x y : α} {u v : 有限集 n -> α}
  结论: vecCons x u = vecCons y v ↔ x = y ∧ u = v
  证明: Fin.cons_inj

Depends on / 依赖: Fin.cons_inj, cons_inj
-/
theorem vecCons_inj {x y : α} {u v : Fin n -> α} : vecCons x u = vecCons y v ↔ x = y ∧ u = v :=
  Fin.cons_inj

open Lean Qq in
/-- `mkVecLiteralQ ![x, y, z]` produces the term `q(![$x, $y, $z])`. -/
meta def _root_.PiFin.mkLiteralQ {u : Level} {α : Q(Type u)} {n : Nat} (elems : Fin n -> Q($α)) :
    Q(Fin $n -> $α) :=
  loop 0 q(vecEmpty)
where
  /-- The core logic of `loop` is that `loop 0 ![] = ![a 0, a 1, a 2] = loop 1 ![a 2]`, where
  recursion starts from the end. In this example, on the right-hand side, the variable `rest := 1`
  tracks the length of the current generated notation `![a 2]`, and the last used index is
  `n - rest` (`= 3 - 1 = 2`). -/
  loop (i : Nat) (rest : Q(Fin $i -> $α)) : Q(Fin $n -> $α) :=
    if h : i < n then
      loop (i + 1) q(vecCons $(elems (Fin.rev ⟨i, h⟩)) $rest)
    else
      rest

open Lean Qq in
protected meta instance _root_.PiFin.toExpr [ToLevel.{u}] [ToExpr α] (n : Nat) : ToExpr (Fin n -> α) :=
  have lu := toLevel.{u}
  have eα : Q(Type $lu) := toTypeExpr α
  let toTypeExpr := q(Fin $n -> $eα)
  { toTypeExpr, toExpr v := PiFin.mkLiteralQ fun i => show Q($eα) from toExpr (v i) }

/-! ### `bit0` and `bit1` indices
The following definitions and `simp` lemmas are used to allow
numeral-indexed element of a vector given with matrix notation to
be extracted by `simp` in Lean 3 (even when the numeral is larger than the
number of elements in the vector, which is taken modulo that number
of elements by virtue of the semantics of `bit0` and `bit1` and of
addition on `Fin n`).
-/


/--
Definition of `vecAppend` / `vecAppend` 的定义

English:
definition vecAppend
  signature: {α : Type*} {o : Nat} (ho : o = m + n) (u : Fin m -> α) (v : Fin n -> α)
  body: Fin.append u v ∘ Fin.cast ho

中文:
定义 vecAppend
  签名: {α : 类型} {o : 自然数} (ho : o = m + n) (u : 有限集 m -> α) (v : 有限集 n -> α)
  定义体: Fin.append u v ∘ Fin.cast ho

Depends on / 依赖: Fin.append, Fin.cast, append
-/
def vecAppend {α : Type*} {o : Nat} (ho : o = m + n) (u : Fin m -> α) (v : Fin n -> α) : Fin o -> α :=
  Fin.append u v ∘ Fin.cast ho

/--
theorem `vecAppend_eq_ite` / 定理 `vecAppend_eq_ite`

English:
theorem vecAppend_eq_ite
  given: {α : Type*} {o : Nat} (ho : o = m + n) (u : Fin m -> α) (v : Fin n -> α)
  proof: by
  ext i
  rw [vecAppend]; rw [Fin.append]; rw [Function.comp_apply]; rw [Fin.addCases]
  congr with hi
  simp only [eq_rec_constant]
  rfl

@[simp]

中文:
定理 vecAppend_eq_ite
  条件: {α : 类型} {o : 自然数} (ho : o = m + n) (u : 有限集 m -> α) (v : 有限集 n -> α)
  证明: by
  ext i
  rw [vecAppend]; rw [Fin.append]; rw [Function.comp_apply]; rw [Fin.addCases]
  congr with hi
  simp only [eq_rec_constant]
  rfl

@[simp]

Depends on / 依赖: Fin.addCases, Fin.append, Function, Function.comp_apply, addCases, append, comp_apply, eq_rec_constant, vecAppend
-/
theorem vecAppend_eq_ite {α : Type*} {o : Nat} (ho : o = m + n) (u : Fin m -> α) (v : Fin n -> α) :
    vecAppend ho u v = fun i : Fin o =>
      if h : (i : Nat) < m then u ⟨i, h⟩ else v ⟨(i : Nat) - m, by lia⟩ := by
  ext i
  rw [vecAppend]; rw [Fin.append]; rw [Function.comp_apply]; rw [Fin.addCases]
  congr with hi
  simp only [eq_rec_constant]
  rfl

@[simp]
/--
theorem `vecAppend_apply_zero` / 定理 `vecAppend_apply_zero`

English:
theorem vecAppend_apply_zero
  statement: {α : Type*} {o : Nat} (ho : o + 1 = m + 1 + n) (u : Fin (m + 1) -> α)
  proof: rfl

@[simp]

中文:
定理 vecAppend_apply_zero
  结论: {α : 类型} {o : 自然数} (ho : o + 1 = m + 1 + n) (u : 有限集 (m + 1) -> α)
  证明: rfl

@[simp]
-/
theorem vecAppend_apply_zero {α : Type*} {o : Nat} (ho : o + 1 = m + 1 + n) (u : Fin (m + 1) -> α)
    (v : Fin n -> α) : vecAppend ho u v 0 = u 0 :=
  rfl

@[simp]
/--
theorem `empty_vecAppend` / 定理 `empty_vecAppend`

English:
theorem empty_vecAppend
  given: (v : Fin n -> α)
  statement: vecAppend n.zero_add.symm ![] v = v
  proof: by
  ext
  simp [vecAppend_eq_ite]

@[simp]

中文:
定理 empty_vecAppend
  条件: (v : 有限集 n -> α)
  结论: vecAppend n.zero_add.symm ![] v = v
  证明: by
  ext
  simp [vecAppend_eq_ite]

@[simp]

Depends on / 依赖: vecAppend_eq_ite
-/
theorem empty_vecAppend (v : Fin n -> α) : vecAppend n.zero_add.symm ![] v = v := by
  ext
  simp [vecAppend_eq_ite]

@[simp]
/--
theorem `vecAppend_empty` / 定理 `vecAppend_empty`

English:
theorem vecAppend_empty
  given: (v : Fin n -> α)
  statement: vecAppend rfl v ![] = v
  proof: by
  ext
  simp [vecAppend_eq_ite]

@[simp]

中文:
定理 vecAppend_empty
  条件: (v : 有限集 n -> α)
  结论: vecAppend rfl v ![] = v
  证明: by
  ext
  simp [vecAppend_eq_ite]

@[simp]

Depends on / 依赖: vecAppend_eq_ite
-/
theorem vecAppend_empty (v : Fin n -> α) : vecAppend rfl v ![] = v := by
  ext
  simp [vecAppend_eq_ite]

@[simp]
/--
theorem `cons_vecAppend` / 定理 `cons_vecAppend`

English:
theorem cons_vecAppend
  given: (ho : o + 1 = m + 1 + n) (x : α) (u : Fin m -> α) (v : Fin n -> α)
  proof: by
  ext i
  simp_rw [vecAppend_eq_ite]
  split_ifs with h
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp
    · simp only [Nat.add_lt_add_iff_right] at h
      simp [h]
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp at h
    · rw [not_lt, Fin.val_mk, Nat.add_le_add_iff_right] at h
      simp [not_lt.2 h]

中文:
定理 cons_vecAppend
  条件: (ho : o + 1 = m + 1 + n) (x : α) (u : 有限集 m -> α) (v : 有限集 n -> α)
  证明: by
  ext i
  simp_rw [vecAppend_eq_ite]
  split_ifs with h
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp
    · simp only [Nat.add_lt_add_iff_right] at h
      simp [h]
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp at h
    · rw [not_lt, Fin.val_mk, Nat.add_le_add_iff_right] at h
      simp [not_lt.2 h]

Depends on / 依赖: Fin.val_mk, Nat.add_le_add_iff_right, Nat.add_lt_add_iff_right, add_le_add_iff_right, add_lt_add_iff_right, nodup_cons, not_lt, simp_rw, split_ifs, val_mk, vecAppend_eq_ite
-/
theorem cons_vecAppend (ho : o + 1 = m + 1 + n) (x : α) (u : Fin m -> α) (v : Fin n -> α) :
    vecAppend ho (vecCons x u) v = vecCons x (vecAppend (by lia) u v) := by
  ext i
  simp_rw [vecAppend_eq_ite]
  split_ifs with h
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp
    · simp only [Nat.add_lt_add_iff_right] at h
      simp [h]
  · rcases i with ⟨⟨⟩ | i, hi⟩
    · simp at h
    · rw [not_lt, Fin.val_mk, Nat.add_le_add_iff_right] at h
      simp [not_lt.2 h]

/--
Definition of `vecAlt0` / `vecAlt0` 的定义

English:
definition vecAlt0
  signature: (hm : m = n + n) (v : Fin m -> α) (k : Fin n)
  body: v ⟨(k : Nat) + k, by lia⟩

中文:
定义 vecAlt0
  签名: (hm : m = n + n) (v : 有限集 m -> α) (k : 有限集 n)
  定义体: v ⟨(k : Nat) + k, by lia⟩

Depends on / 依赖: nodup_cons
-/
def vecAlt0 (hm : m = n + n) (v : Fin m -> α) (k : Fin n) : α := v ⟨(k : Nat) + k, by lia⟩

/--
Definition of `vecAlt1` / `vecAlt1` 的定义

English:
definition vecAlt1
  signature: (hm : m = n + n) (v : Fin m -> α) (k : Fin n)
  body: v ⟨(k : Nat) + k + 1, hm.symm ▸ Nat.add_succ_lt_add k.2 k.2⟩

中文:
定义 vecAlt1
  签名: (hm : m = n + n) (v : 有限集 m -> α) (k : 有限集 n)
  定义体: v ⟨(k : Nat) + k + 1, hm.symm ▸ Nat.add_succ_lt_add k.2 k.2⟩

Depends on / 依赖: Nat.add_succ_lt_add, add_succ_lt_add, hm.symm
-/
def vecAlt1 (hm : m = n + n) (v : Fin m -> α) (k : Fin n) : α :=
  v ⟨(k : Nat) + k + 1, hm.symm ▸ Nat.add_succ_lt_add k.2 k.2⟩

section bits

/--
theorem `vecAlt0_vecAppend` / 定理 `vecAlt0_vecAppend`

English:
theorem vecAlt0_vecAppend
  given: (v : Fin n -> α)
  proof: by
  ext i
  simp_rw [Function.comp, vecAlt0, vecAppend_eq_ite]
  split_ifs with h <;> congr
  · rw [Fin.val_mk] at h
    exact (Nat.mod_eq_of_lt h).symm
  · rw [Fin.val_mk, not_lt] at h
    simp only [Nat.mod_eq_sub_mod h]
    refine (Nat.mod_eq_of_lt ?_).symm
    lia

中文:
定理 vecAlt0_vecAppend
  条件: (v : 有限集 n -> α)
  证明: by
  ext i
  simp_rw [Function.comp, vecAlt0, vecAppend_eq_ite]
  split_ifs with h <;> congr
  · rw [Fin.val_mk] at h
    exact (Nat.mod_eq_of_lt h).symm
  · rw [Fin.val_mk, not_lt] at h
    simp only [Nat.mod_eq_sub_mod h]
    refine (Nat.mod_eq_of_lt ?_).symm
    lia

Depends on / 依赖: Fin.val_mk, Function, Function.comp, Nat.mod_eq_of_lt, Nat.mod_eq_sub_mod, mod_eq_of_lt, mod_eq_sub_mod, not_lt, simp_rw, split_ifs, val_mk, vecAlt0, vecAppend_eq_ite
-/
theorem vecAlt0_vecAppend (v : Fin n -> α) :
    vecAlt0 rfl (vecAppend rfl v v) = v ∘ (fun n => n + n) := by
  ext i
  simp_rw [Function.comp, vecAlt0, vecAppend_eq_ite]
  split_ifs with h <;> congr
  · rw [Fin.val_mk] at h
    exact (Nat.mod_eq_of_lt h).symm
  · rw [Fin.val_mk, not_lt] at h
    simp only [Nat.mod_eq_sub_mod h]
    refine (Nat.mod_eq_of_lt ?_).symm
    lia

/--
theorem `vecAlt1_vecAppend` / 定理 `vecAlt1_vecAppend`

English:
theorem vecAlt1_vecAppend
  given: (v : Fin (n + 1) -> α)
  proof: by
  ext i
  simp_rw [Function.comp, vecAlt1, vecAppend_eq_ite]
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := i
    simp only [Nat.zero_add, Nat.lt_one_iff] at hi; subst i; rfl
  | succ n =>
    split_ifs with h <;> congr
    · simp [Nat.mod_eq_of_lt, h]
    · rw [Fin.val_mk, not_lt] at h
      simp only [Nat.mod_add_mod,
        Nat.mod_eq_sub_mod h, show 1 % (n + 2) = 1 from Nat.mod_eq_of_lt (by lia)]
      refine (Nat.mod_eq_of_lt ?_).symm
      lia

@[simp]

中文:
定理 vecAlt1_vecAppend
  条件: (v : 有限集 (n + 1) -> α)
  证明: by
  ext i
  simp_rw [Function.comp, vecAlt1, vecAppend_eq_ite]
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := i
    simp only [Nat.zero_add, Nat.lt_one_iff] at hi; subst i; rfl
  | succ n =>
    split_ifs with h <;> congr
    · simp [Nat.mod_eq_of_lt, h]
    · rw [Fin.val_mk, not_lt] at h
      simp only [Nat.mod_add_mod,
        Nat.mod_eq_sub_mod h, show 1 % (n + 2) = 1 from Nat.mod_eq_of_lt (by lia)]
      refine (Nat.mod_eq_of_lt ?_).symm
      lia

@[simp]

Depends on / 依赖: Fin.val_mk, Function, Function.comp, Nat.lt_one_iff, Nat.mod_add_mod, Nat.mod_eq_of_lt, Nat.mod_eq_sub_mod, Nat.zero_add, lt_one_iff, mod_add_mod, mod_eq_of_lt, mod_eq_sub_mod, not_lt, simp_rw, split_ifs, val_mk, vecAlt1, vecAppend_eq_ite, zero_add
-/
theorem vecAlt1_vecAppend (v : Fin (n + 1) -> α) :
    vecAlt1 rfl (vecAppend rfl v v) = v ∘ (fun n => (n + n) + 1) := by
  ext i
  simp_rw [Function.comp, vecAlt1, vecAppend_eq_ite]
  cases n with
  | zero =>
    obtain ⟨i, hi⟩ := i
    simp only [Nat.zero_add, Nat.lt_one_iff] at hi; subst i; rfl
  | succ n =>
    split_ifs with h <;> congr
    · simp [Nat.mod_eq_of_lt, h]
    · rw [Fin.val_mk, not_lt] at h
      simp only [Nat.mod_add_mod,
        Nat.mod_eq_sub_mod h, show 1 % (n + 2) = 1 from Nat.mod_eq_of_lt (by lia)]
      refine (Nat.mod_eq_of_lt ?_).symm
      lia

@[simp]
/--
theorem `vecHead_vecAlt0` / 定理 `vecHead_vecAlt0`

English:
theorem vecHead_vecAlt0
  given: (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) -> α)
  proof: rfl

@[simp]

中文:
定理 vecHead_vecAlt0
  条件: (hm : m + 2 = n + 1 + (n + 1)) (v : 有限集 (m + 2) -> α)
  证明: rfl

@[simp]
-/
theorem vecHead_vecAlt0 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) -> α) :
    vecHead (vecAlt0 hm v) = v 0 :=
  rfl

@[simp]
/--
theorem `vecHead_vecAlt1` / 定理 `vecHead_vecAlt1`

English:
theorem vecHead_vecAlt1
  given: (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) -> α)
  proof: by simp [vecHead, vecAlt1]

中文:
定理 vecHead_vecAlt1
  条件: (hm : m + 2 = n + 1 + (n + 1)) (v : 有限集 (m + 2) -> α)
  证明: by simp [vecHead, vecAlt1]

Depends on / 依赖: vecAlt1, vecHead
-/
theorem vecHead_vecAlt1 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) -> α) :
    vecHead (vecAlt1 hm v) = v 1 := by simp [vecHead, vecAlt1]

/--
theorem `cons_vec_bit0_eq_alt0` / 定理 `cons_vec_bit0_eq_alt0`

English:
theorem cons_vec_bit0_eq_alt0
  given: (x : α) (u : Fin n -> α) (i : Fin (n + 1))
  proof: by
  rw [vecAlt0_vecAppend]; rfl

中文:
定理 cons_vec_bit0_eq_alt0
  条件: (x : α) (u : 有限集 n -> α) (i : 有限集 (n + 1))
  证明: by
  rw [vecAlt0_vecAppend]; rfl

Depends on / 依赖: vecAlt0_vecAppend
-/
theorem cons_vec_bit0_eq_alt0 (x : α) (u : Fin n -> α) (i : Fin (n + 1)) :
    vecCons x u (i + i) = vecAlt0 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i := by
  rw [vecAlt0_vecAppend]; rfl

/--
theorem `cons_vec_bit1_eq_alt1` / 定理 `cons_vec_bit1_eq_alt1`

English:
theorem cons_vec_bit1_eq_alt1
  given: (x : α) (u : Fin n -> α) (i : Fin (n + 1))
  proof: by
  rw [vecAlt1_vecAppend]; rfl

中文:
定理 cons_vec_bit1_eq_alt1
  条件: (x : α) (u : 有限集 n -> α) (i : 有限集 (n + 1))
  证明: by
  rw [vecAlt1_vecAppend]; rfl

Depends on / 依赖: vecAlt1_vecAppend
-/
theorem cons_vec_bit1_eq_alt1 (x : α) (u : Fin n -> α) (i : Fin (n + 1)) :
    vecCons x u ((i + i) + 1) = vecAlt1 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i := by
  rw [vecAlt1_vecAppend]; rfl

end bits

@[simp]
/--
theorem `cons_vecAlt0` / 定理 `cons_vecAlt0`

English:
theorem cons_vecAlt0
  given: (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m -> α)
  proof: by
  ext i
  simp_rw [vecAlt0]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp only [← Nat.add_assoc, Nat.add_right_comm, cons_val_succ',
      vecAlt0]

@[simp]

中文:
定理 cons_vecAlt0
  条件: (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : 有限集 m -> α)
  证明: by
  ext i
  simp_rw [vecAlt0]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp only [← Nat.add_assoc, Nat.add_right_comm, cons_val_succ',
      vecAlt0]

@[simp]

Depends on / 依赖: Nat.add_assoc, Nat.add_right_comm, add_assoc, add_right_comm, cons_val_succ, simp_rw, vecAlt0
-/
theorem cons_vecAlt0 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m -> α) :
    vecAlt0 h (vecCons x (vecCons y u)) = vecCons x (vecAlt0 (by lia) u) := by
  ext i
  simp_rw [vecAlt0]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp only [← Nat.add_assoc, Nat.add_right_comm, cons_val_succ',
      vecAlt0]

@[simp]
/--
theorem `empty_vecAlt0` / 定理 `empty_vecAlt0`

English:
theorem empty_vecAlt0
  given: (α) {h}
  statement: vecAlt0 h (![] : Fin 0 -> α) = ![]
  proof: by
  simp [eq_iff_true_of_subsingleton]

@[simp]

中文:
定理 empty_vecAlt0
  条件: (α) {h}
  结论: vecAlt0 h (![] : 有限集 0 -> α) = ![]
  证明: by
  simp [eq_iff_true_of_subsingleton]

@[simp]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem empty_vecAlt0 (α) {h} : vecAlt0 h (![] : Fin 0 -> α) = ![] := by
  simp [eq_iff_true_of_subsingleton]

@[simp]
/--
theorem `cons_vecAlt1` / 定理 `cons_vecAlt1`

English:
theorem cons_vecAlt1
  given: (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m -> α)
  proof: by
  ext i
  simp_rw [vecAlt1]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp [vecAlt1, Nat.add_right_comm, ← Nat.add_assoc]

@[simp]

中文:
定理 cons_vecAlt1
  条件: (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : 有限集 m -> α)
  证明: by
  ext i
  simp_rw [vecAlt1]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp [vecAlt1, Nat.add_right_comm, ← Nat.add_assoc]

@[simp]

Depends on / 依赖: Nat.add_assoc, Nat.add_right_comm, add_assoc, add_right_comm, simp_rw, vecAlt1
-/
theorem cons_vecAlt1 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m -> α) :
    vecAlt1 h (vecCons x (vecCons y u)) = vecCons y (vecAlt1 (by lia) u) := by
  ext i
  simp_rw [vecAlt1]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp [vecAlt1, Nat.add_right_comm, ← Nat.add_assoc]

@[simp]
/--
theorem `empty_vecAlt1` / 定理 `empty_vecAlt1`

English:
theorem empty_vecAlt1
  given: (α) {h}
  statement: vecAlt1 h (![] : Fin 0 -> α) = ![]
  proof: by
  simp [eq_iff_true_of_subsingleton]

中文:
定理 empty_vecAlt1
  条件: (α) {h}
  结论: vecAlt1 h (![] : 有限集 0 -> α) = ![]
  证明: by
  simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem empty_vecAlt1 (α) {h} : vecAlt1 h (![] : Fin 0 -> α) = ![] := by
  simp [eq_iff_true_of_subsingleton]

end Val

/--
lemma `const_fin1_eq` / 引理 `const_fin1_eq`

English:
lemma const_fin1_eq
  given: (x : α)
  statement: (fun _ : Fin 1 => x) = ![x]
  proof: (cons_fin_one x _).symm

中文:
引理 const_fin1_eq
  条件: (x : α)
  结论: (fun _ : 有限集 1 => x) = ![x]
  证明: (cons_fin_one x _).symm

Depends on / 依赖: cons_fin_one
-/
lemma const_fin1_eq (x : α) : (fun _ : Fin 1 => x) = ![x] :=
  (cons_fin_one x _).symm

/-!
### Interaction between cons and Equiv.swap
-/

section swap

@[simp]
/--
lemma `cons_cons_comp_swap_zero_one` / 引理 `cons_cons_comp_swap_zero_one`

English:
lemma cons_cons_comp_swap_zero_one
  given: (a b : α) (x : Fin n -> α)
  proof: by
  ext j : 1
  match j with
  | 0 => simp
  | 1 => simp
  | ⟨i + 2, h⟩ =>
    have h' : (⟨i + 2, h⟩ : Fin n.succ.succ) = Fin.succ (Fin.succ ⟨i, by lia⟩) := by grind
    simp only [Nat.succ_eq_add_one, h', Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _), cons_val_succ]

中文:
引理 cons_cons_comp_swap_zero_one
  条件: (a b : α) (x : 有限集 n -> α)
  证明: by
  ext j : 1
  match j with
  | 0 => simp
  | 1 => simp
  | ⟨i + 2, h⟩ =>
    have h' : (⟨i + 2, h⟩ : Fin n.succ.succ) = Fin.succ (Fin.succ ⟨i, by lia⟩) := by grind
    simp only [Nat.succ_eq_add_one, h', Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _), cons_val_succ]

Depends on / 依赖: Equiv.swap_apply_of_ne_of_ne, Fin.succ, Fin.succ_ne_zero, Fin.succ_succ_ne_one, Function, Function.comp_apply, Nat.succ_eq_add_one, comp_apply, cons_val_succ, n.succ.succ, succ_eq_add_one, succ_ne_zero, succ_succ_ne_one, swap_apply_of_ne_of_ne
-/
lemma cons_cons_comp_swap_zero_one (a b : α) (x : Fin n -> α) :
    vecCons a (vecCons b x) ∘ (Equiv.swap 0 1) = vecCons b (vecCons a x) := by
  ext j : 1
  match j with
  | 0 => simp
  | 1 => simp
  | ⟨i + 2, h⟩ =>
    have h' : (⟨i + 2, h⟩ : Fin n.succ.succ) = Fin.succ (Fin.succ ⟨i, by lia⟩) := by grind
    simp only [Nat.succ_eq_add_one, h', Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _), cons_val_succ]

/--
lemma `cons_swap` / 引理 `cons_swap`

English:
lemma cons_swap
  given: (a : α) (x : Fin n -> α) (i j : Fin n)
  proof: by
  ext k : 1
  rcases eq_or_ne k 0 with rfl | hk₀
  · simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
  rcases eq_or_ne k i.succ with rfl | hki
  · simp
  rcases eq_or_ne k j.succ with rfl | hkj
  · simp
  have hk : k = Fin.succ ⟨k - 1, by lia⟩ := by grind
  rw [Function.comp_apply]; rw [Equiv.swap_apply_of_ne_of_ne hki hkj]; rw [hk]; rw [cons_val_succ]; rw [Function.comp_apply]; rw [cons_val_succ]; rw [Equiv.swap_apply_of_ne_of_ne (by grind) (by grind)]

中文:
引理 cons_swap
  条件: (a : α) (x : 有限集 n -> α) (i j : 有限集 n)
  证明: by
  ext k : 1
  rcases eq_or_ne k 0 with rfl | hk₀
  · simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
  rcases eq_or_ne k i.succ with rfl | hki
  · simp
  rcases eq_or_ne k j.succ with rfl | hkj
  · simp
  have hk : k = Fin.succ ⟨k - 1, by lia⟩ := by grind
  rw [Function.comp_apply]; rw [Equiv.swap_apply_of_ne_of_ne hki hkj]; rw [hk]; rw [cons_val_succ]; rw [Function.comp_apply]; rw [cons_val_succ]; rw [Equiv.swap_apply_of_ne_of_ne (by grind) (by grind)]

Depends on / 依赖: Equiv.swap_apply_of_ne_of_ne, Fin.succ, Fin.succ_ne_zero, Function, Function.comp_apply, comp_apply, cons_val_succ, eq_or_ne, i.succ, j.succ, succ_ne_zero, swap_apply_of_ne_of_ne
-/
lemma cons_swap (a : α) (x : Fin n -> α) (i j : Fin n) :
    vecCons a (x ∘ (Equiv.swap i j)) = vecCons a x ∘ (Equiv.swap i.succ j.succ) := by
  ext k : 1
  rcases eq_or_ne k 0 with rfl | hk₀
  · simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
  rcases eq_or_ne k i.succ with rfl | hki
  · simp
  rcases eq_or_ne k j.succ with rfl | hkj
  · simp
  have hk : k = Fin.succ ⟨k - 1, by lia⟩ := by grind
  rw [Function.comp_apply]; rw [Equiv.swap_apply_of_ne_of_ne hki hkj]; rw [hk]; rw [cons_val_succ]; rw [Function.comp_apply]; rw [cons_val_succ]; rw [Equiv.swap_apply_of_ne_of_ne (by grind) (by grind)]

end swap

end Matrix
