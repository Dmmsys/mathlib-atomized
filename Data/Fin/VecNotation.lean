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

/-- `![]` is the vector with no entries. -/
/-
**Matrix.vecEmpty** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vecEmpty : Fin 0 -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`![]` is the vector with no entries.
-/
def vecEmpty : Fin 0 → α :=
  Fin.elim0

/-- `vecCons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vecHead` and `vecTail`.
The notation `![a, b, ...]` expands to `vecCons a (vecCons b ...)`.
-/
/-
**Matrix.vecCons** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vecCons {n : Nat} (h : α) (t : Fin n -> α) : Fin n.succ -> α
参数：h : α；t : Fin n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vecCons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vecHead` and `vecTail`.
The notation `![a, b, ...]` expands to `vecCons a (vecCons b ...)`.
-/
def vecCons {n : ℕ} (h : α) (t : Fin n → α) : Fin n.succ → α :=
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

/-- `vecHead v` gives the first entry of the vector `v` -/
/-
**Matrix.vecHead** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vecHead {n : Nat} (v : Fin n.succ -> α) : α
参数：v : Fin n.succ -> α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
`vecHead v` gives the first entry of the vector `v`
-/
def vecHead {n : ℕ} (v : Fin n.succ → α) : α :=
  v 0

/-- `vecTail v` gives a vector consisting of all entries of `v` except the first -/
/-
**Matrix.vecTail** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vecTail {n : Nat} (v : Fin n.succ -> α) : Fin n -> α
参数：v : Fin n.succ -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vecTail v` gives a vector consisting of all entries of `v` except the first
-/
def vecTail {n : ℕ} (v : Fin n.succ → α) : Fin n → α :=
  v ∘ Fin.succ

variable {m n : ℕ}

/-- Use `![...]` notation for displaying a vector `Fin n → α`, for example:

```
#eval ![1, 2] + ![3, 4] -- ![4, 6]
```
-/
/-
**Matrix._root_.PiFin.hasRepr** 是 Mathlib 中的一个实例，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `![...]` notation for displaying a vector `Fin n → α`, for example:

```
#eval ![1, 2] + ![3, 4] -- ![4, 6]
```
-/
instance _root_.PiFin.hasRepr [Repr α] : Repr (Fin n → α) where
  reprPrec f _ :=
    Std.Format.bracket "![" (Std.Format.joinSep
      ((List.finRange n).map fun n => repr (f n)) ("," ++ Std.Format.line)) "]"

end MatrixNotation

variable {m n o : ℕ}

/-
**Matrix.empty_eq** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_eq (v : Fin 0 -> α) : v = ![]
参数：v : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem empty_eq (v : Fin 0 → α) : v = ![] :=
  Subsingleton.elim _ _

section Val

@[simp]
/-
**Matrix.head_fin_const** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：head_fin_const (a : α) : (vecHead fun _ : Fin (n + 1) => a) = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_fin_const (a : α) : (vecHead fun _ : Fin (n + 1) => a) = a :=
  rfl

@[simp]
/-
**Matrix.cons_val_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_val_zero (x : α) (u : Fin m -> α) : vecCons x u 0 = x
参数：x : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cons_val_zero (x : α) (u : Fin m → α) : vecCons x u 0 = x :=
  rfl
/-
**Matrix.cons_val_zero'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_val_zero' (h : 0 < m.succ) (x : α) (u : Fin m -> α) : vecCons x u ⟨0,
 h⟩ = x
参数：h : 0 < m.succ；x : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_val_zero' (h : 0 < m.succ) (x : α) (u : Fin m → α) : vecCons x u ⟨0, h⟩ = x :=
  rfl

@[simp]
/-
**Matrix.cons_val_succ** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m) : vecCons x u i.succ = 
u i
参数：x : α；u : Fin m -> α；i : Fin m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_val_succ (x : α) (u : Fin m → α) (i : Fin m) : vecCons x u i.succ = u i := by
  simp [vecCons]

@[simp]
/-
**Matrix.cons_val_succ'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_val_succ' {i : Nat} (h : i.succ < m.succ) (x : α) (u : Fin m -> α) : 
vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ h⟩
参数：h : i.succ < m.succ；x : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_val_succ' {i : ℕ} (h : i.succ < m.succ) (x : α) (u : Fin m → α) :
    vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ h⟩ := by
  simp only [vecCons, Fin.cons, Fin.cases_succ']

/-- We don't want to always simplify `Fin.cons` to `vecCons`.
But in cases that we are already mixing the declarations for dependent tuples and non-dependent
tuples, we can simplify to the non-dependent tuples. -/
@[simp]
/-
**Matrix.Fin.cons_vecEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Fin`。
形式化陈述：∀ {α : Type u_1} (x : α), Fin.cons x ![] = ![x]
参数：x : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We don't want to always simplify `Fin.cons` to `vecCons`.
But in cases that we are already mixing the declarations for dependent tuples an
d non-dependent
tuples, we can simplify to the non-dependent tuples.
-/
lemma Fin.cons_vecEmpty {α : Type*} (x : α) : Fin.cons x ![] = ![x] := by rfl

/-- Simplify `Fin.snoc` to `vecCons` in this case. -/
@[simp]
/-
**Matrix.Fin.snoc_vecEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Fin`。
形式化陈述：∀ {α : Type u_1} (x : α), Fin.snoc ![] x = ![x]
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.fin_one_eq_zero`：∀ (a : Fin 1), a = 0

--- 原说明 ---
Simplify `Fin.snoc` to `vecCons` in this case.
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
/-
**Matrix.Fin.cons_vecCons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Fin`。
形式化陈述：∀ {n : ℕ} {α : Type u_1} (x y : α) (p : Fin n → α),   Fin.cons x (Matrix.v
ecCons y p) = Matrix.vecCons x (Matrix.vecCons y p)
参数：x y : α；p : Fin n → α；Matrix.vecCons y p；Matrix.vecCons y p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We don't want to always simplify `Fin.cons` to `vecCons`.
But in cases that we are already mixing the declarations for dependent tuples an
d non-dependent
tuples, we can simplify to the non-dependent tuples.
This allows us to simplify `Fin.cons 5 ![1, 3, 7]` to `![5, 1, 3, 7]`.
-/
lemma Fin.cons_vecCons {α : Type*} (x y : α) (p : Fin n → α) :
  Fin.cons x (vecCons y p) = vecCons x (vecCons y p) := by rfl

/-- We push `Fin.snoc` inside `vecCons`. This allows us to simplify e.g.
`Fin.snoc ![1, 3, 7] 5` to `![1, 3, 7, 5]`. -/
@[simp]
/-
**Matrix.Fin.snoc_vecCons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix.Fin`。
形式化陈述：∀ {n : ℕ} {α : Type u_1} (x y : α) (p : Fin n → α), Fin.snoc (Matrix.vecCo
ns y p) x = Matrix.vecCons y (Fin.snoc p x)
参数：x y : α；p : Fin n → α；Matrix.vecCons y p；Fin.snoc p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_snoc_eq_snoc_cons`：cons_snoc_eq_snoc_cons {β : Sort*} (a : β) (
q : Fin n -> β) (b : β) : @cons n.succ (fun _ => β) a (snoc q b) = snoc (cons a 
q) b

--- 原说明 ---
We push `Fin.snoc` inside `vecCons`. This allows us to simplify e.g.
`Fin.snoc ![1, 3, 7] 5` to `![1, 3, 7, 5]`.
-/
lemma Fin.snoc_vecCons {α : Type*} (x y : α) (p : Fin n → α) :
    Fin.snoc (vecCons y p) x = vecCons y (Fin.snoc p x) :=
  Fin.cons_snoc_eq_snoc_cons .. |>.symm

section simprocs
open Lean Qq

/-- Parses a chain of `Matrix.vecCons` calls into elements, leaving everything else in the tail.

`let ⟨xs, tailn, tail⟩ ← matchVecConsPrefix n e` decomposes `e : Fin n → _` in the form
`vecCons x₀ <| ... <| vecCons xₙ <| tail` where `tail : Fin tailn → _`. -/
meta partial def matchVecConsPrefix (n : Q(Nat)) (e : Expr) :
    MetaM <| List Expr × Q(Nat) × Expr := do
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
    let etailn_whnf : Q(ℕ) ← Meta.whnfD etailn
    if let Expr.lit (.natVal length) := etailn_whnf then
      pure (length, false, q(OfNat.ofNat $etailn_whnf))
    else if let some ((base : Q(ℕ)), offset) ← (Meta.isOffset? etailn_whnf).run then
      pure (offset, true, q($base + $offset))
    else
      pure (0, true, etailn)
  -- Wrap the index if possible, and abort if not
  let wrapped_i ←
    if variadic then
      -- can't wrap as we don't know the length
      unless 0 ≤ i ∧ i < xs.length + tailn do return .continue
      pure i.toNat
    else
      pure (i % (xs.length + tailn)).toNat
  if h : wrapped_i < xs.length then
    return .continue xs[wrapped_i]
  else
    -- Within the `tail`
    let _ ← synthInstanceQ q(NeZero $etailn)
    have i_lit : Q(ℕ) := mkRawNatLit (wrapped_i - xs.length)
    return .continue (.some <| .app tail q(OfNat.ofNat $i_lit : Fin $etailn))

end simprocs

@[simp]
/-
**Matrix.head_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：head_cons (x : α) (u : Fin m -> α) : vecHead (vecCons x u) = x
参数：x : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head_cons (x : α) (u : Fin m → α) : vecHead (vecCons x u) = x :=
  rfl

@[simp]
/-
**Matrix.tail_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：tail_cons (x : α) (u : Fin m -> α) : vecTail (vecCons x u) = u
参数：x : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem tail_cons (x : α) (u : Fin m → α) : vecTail (vecCons x u) = u := by
  ext
  simp [vecTail]

@[simp]
/-
**Matrix._root_.Fin.tail_vecCons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Fin.tail_vecCons (x : α) (t : Fin n → α) : Fin.tail (Matrix.vecCons x t) = t :=
  rfl
/-
**Matrix.empty_val'** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_val' {n' : Type*} (j : n') : (fun i => (![] : Fin 0 -> n' -> α) i j)
 = ![]
参数：j : n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.empty_eq`：empty_eq (v : Fin 0 -> α) : v = ![]
-/
theorem empty_val' {n' : Type*} (j : n') : (fun i => (![] : Fin 0 → n' → α) i j) = ![] :=
  empty_eq _

@[simp]
/-
**Matrix.cons_head_tail** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_head_tail (u : Fin m.succ -> α) : vecCons (vecHead u) (vecTail u) = u
参数：u : Fin m.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.cons_self_tail`：cons_self_tail : cons (q 0) (tail q) = q
-/
theorem cons_head_tail (u : Fin m.succ → α) : vecCons (vecHead u) (vecTail u) = u :=
  Fin.cons_self_tail _

@[simp]
/-
**Matrix.range_cons** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：range_cons (x : α) (u : Fin n -> α) : Set.range (vecCons x u) = {x} union 
Set.range u
参数：x : α；u : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem range_cons (x : α) (u : Fin n → α) : Set.range (vecCons x u) = {x} ∪ Set.range u :=
  Set.ext fun y => by simp [Fin.exists_fin_succ, eq_comm]

@[simp]
/-
**Matrix.range_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：range_empty (u : Fin 0 -> α) : Set.range u = ∅
参数：u : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
-/
theorem range_empty (u : Fin 0 → α) : Set.range u = ∅ :=
  Set.range_eq_empty _
/-
**Matrix.range_cons_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：range_cons_empty (x : α) (u : Fin 0 -> α) : Set.range (Matrix.vecCons x u)
 = {x}
参数：x : α；u : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
-/
theorem range_cons_empty (x : α) (u : Fin 0 → α) : Set.range (Matrix.vecCons x u) = {x} := by
  rw [range_cons, range_empty, Set.union_empty]

-- simp can prove this (up to commutativity)
/-
**Matrix.range_cons_cons_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：range_cons_cons_empty (x y : α) (u : Fin 0 -> α) : Set.range (vecCons x <|
 vecCons y u) = {x, y}
参数：x y : α；u : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_cons_empty`：range_cons_empty (x : α) (u : Fin 0 -> α) : Set
.range (Matrix.vecCons x u) = {x}
· 使用定理 `Set.singleton_union`：singleton_union : {a} union s = insert a s
-/
theorem range_cons_cons_empty (x y : α) (u : Fin 0 → α) :
    Set.range (vecCons x <| vecCons y u) = {x, y} := by
  rw [range_cons, range_cons_empty, Set.singleton_union]
/-
**Matrix.vecCons_const** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecCons_const (a : α) : (vecCons a fun _ : Fin n => a) = fun _ => a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.forall_iff_succ`：∀ {n : ℕ} {P : Fin (n + 1) → Prop}, (∀ (i : Fin (n 
+ 1)), P i) ↔ P 0 ∧ ∀ (i : Fin n), P i.succ
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
-/
theorem vecCons_const (a : α) : (vecCons a fun _ : Fin n => a) = fun _ => a :=
  funext <| Fin.forall_iff_succ.2 ⟨rfl, cons_val_succ _ _⟩
/-
**Matrix.vec_single_eq_const** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vec_single_eq_const (a : α) : ![a] = fun _ => a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Unique.forall_iff`：forall_iff {p : α -> Prop} : (forall a, p a) ↔ p defa
ult
-/
theorem vec_single_eq_const (a : α) : ![a] = fun _ => a :=
  funext <| Unique.forall_iff.2 rfl

/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : Fin 1 = 0 : Fin 1`.
-/
@[simp]
/-
**Matrix.cons_val_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_val_one (x : α) (u : Fin m.succ -> α) : vecCons x u 1 = u 0
参数：x : α；u : Fin m.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
`![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : Fin 1 = 0 : Fin 1`.
-/
theorem cons_val_one (x : α) (u : Fin m.succ → α) : vecCons x u 1 = u 0 :=
  rfl
/-
**Matrix.cons_val_two** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_val_two (x : α) (u : Fin m.succ.succ -> α) : vecCons x u 2 = vecHead 
(vecTail u)
参数：x : α；u : Fin m.succ.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem cons_val_two (x : α) (u : Fin m.succ.succ → α) : vecCons x u 2 = vecHead (vecTail u) := rfl
/-
**Matrix.cons_val_three** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cons_val_three (x : α) (u : Fin m.succ.succ.succ -> α) : vecCons x u 3 = v
ecHead (vecTail (vecTail u))
参数：x : α；u : Fin m.succ.succ.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma cons_val_three (x : α) (u : Fin m.succ.succ.succ → α) :
    vecCons x u 3 = vecHead (vecTail (vecTail u)) :=
  rfl
/-
**Matrix.cons_val_four** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cons_val_four (x : α) (u : Fin m.succ.succ.succ.succ -> α) : vecCons x u 4
 = vecHead (vecTail (vecTail (vecTail u)))
参数：x : α；u : Fin m.succ.succ.succ.succ -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma cons_val_four (x : α) (u : Fin m.succ.succ.succ.succ → α) :
    vecCons x u 4 = vecHead (vecTail (vecTail (vecTail u))) :=
  rfl

@[simp]
/-
**Matrix.cons_val_fin_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_val_fin_one (x : α) (u : Fin 0 -> α) : forall (i : Fin 1), vecCons x 
u i = x
参数：x : α；u : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.forall_fin_one`：∀ {p : Fin 1 → Prop}, (∀ (i : Fin 1), p i) ↔ p 0
-/
theorem cons_val_fin_one (x : α) (u : Fin 0 → α) : ∀ (i : Fin 1), vecCons x u i = x := by
  rw [Fin.forall_fin_one]
  rfl
/-
**Matrix.cons_fin_one** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_fin_one (x : α) (u : Fin 0 -> α) : vecCons x u = fun _ => x
参数：x : α；u : Fin 0 -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
-/
theorem cons_fin_one (x : α) (u : Fin 0 → α) : vecCons x u = fun _ => x :=
  funext (cons_val_fin_one x u)

@[simp]
/-
**Matrix.vecCons_inj** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecCons_inj {x y : α} {u v : Fin n -> α} : vecCons x u = vecCons y v ↔ x =
 y ∧ u = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fin.cons_inj`：cons_inj {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ} 
: cons x₀ x = cons y₀ y ↔ x₀ = y₀ ∧ x = y
-/
theorem vecCons_inj {x y : α} {u v : Fin n → α} : vecCons x u = vecCons y v ↔ x = y ∧ u = v :=
  Fin.cons_inj

open Lean Qq in
/-- `mkVecLiteralQ ![x, y, z]` produces the term `q(![$x, $y, $z])`. -/
meta def _root_.PiFin.mkLiteralQ {u : Level} {α : Q(Type u)} {n : ℕ} (elems : Fin n → Q($α)) :
    Q(Fin $n → $α) :=
  loop 0 q(vecEmpty)
where
  /-- The core logic of `loop` is that `loop 0 ![] = ![a 0, a 1, a 2] = loop 1 ![a 2]`, where
  recursion starts from the end. In this example, on the right-hand side, the variable `rest := 1`
  tracks the length of the current generated notation `![a 2]`, and the last used index is
  `n - rest` (`= 3 - 1 = 2`). -/
  loop (i : ℕ) (rest : Q(Fin $i → $α)) : Q(Fin $n → $α) :=
    if h : i < n then
      loop (i + 1) q(vecCons $(elems (Fin.rev ⟨i, h⟩)) $rest)
    else
      rest

open Lean Qq in
protected meta instance _root_.PiFin.toExpr [ToLevel.{u}] [ToExpr α] (n : ℕ) : ToExpr (Fin n → α) :=
  have lu := toLevel.{u}
  have eα : Q(Type $lu) := toTypeExpr α
  let toTypeExpr := q(Fin $n → $eα)
  { toTypeExpr, toExpr v := PiFin.mkLiteralQ fun i => show Q($eα) from toExpr (v i) }

/-! ### `bit0` and `bit1` indices
The following definitions and `simp` lemmas are used to allow
numeral-indexed element of a vector given with matrix notation to
be extracted by `simp` in Lean 3 (even when the numeral is larger than the
number of elements in the vector, which is taken modulo that number
of elements by virtue of the semantics of `bit0` and `bit1` and of
addition on `Fin n`).
-/


/-- `vecAppend ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`. This is a variant of `Fin.append` with an additional `ho` argument,
which provides control of definitional equality for the vector length.

This turns out to be helpful when providing simp lemmas to reduce `![a, b, c] n`, and also means
that `vecAppend ho u v 0` is valid. `Fin.append u v 0` is not valid in this case because there is
no `Zero (Fin (m + n))` instance. -/
/-
**Matrix.vecAppend** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vecAppend {α : Type*} {o : Nat} (ho : o = m + n) (u : Fin m -> α) (v : Fin
 n -> α) : Fin o -> α
参数：ho : o = m + n；u : Fin m -> α；v : Fin n -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vecAppend ho u v` appends two vectors of lengths `m` and `n` to produce
one of length `o = m + n`. This is a variant of `Fin.append` with an additional 
`ho` argument,
which provides control of definitional equality for the vector length.

This turns out to be helpful when providing simp lemmas to reduce `![a, b, c] n`
, and also means
that `vecAppend ho u v 0` is valid. `Fin.append u v 0` is not valid in this case
 because there is
no `Zero (Fin (m + n))` instance.
-/
def vecAppend {α : Type*} {o : ℕ} (ho : o = m + n) (u : Fin m → α) (v : Fin n → α) : Fin o → α :=
  Fin.append u v ∘ Fin.cast ho
/-
**Matrix.vecAppend_eq_ite** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecAppend_eq_ite {α : Type*} {o : Nat} (ho : o = m + n) (u : Fin m -> α) (
v : Fin n -> α) : vecAppend ho u v = fun i : Fin o => if h : (i : Nat) < m then 
u ⟨i, h⟩ else v ⟨(i : Nat) - m, by lia⟩
参数：ho : o = m + n；u : Fin m -> α；v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecAppend.eq_1`：∀ {m n : ℕ} {α : Type u_1} {o : ℕ} (ho : o = m + 
n) (u : Fin m → α) (v : Fin n → α),   Matrix.vecAppend ho u v = Fin.append u v ∘
 Fin.cast h…
· 使用定理 `Fin.append.eq_1`：∀ {m n : ℕ} {α : Sort u_1} (a : Fin m → α) (b : Fin n →
 α), Fin.append a b = Fin.addCases a b
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Fin.castAdd_castLT`：∀ {n : ℕ} (m : ℕ) (i : Fin (n + m)) (hi : ↑i < n), F
in.castAdd m (i.castLT hi) = i
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Fin.addCases.eq_1`：∀ {m n : ℕ} {motive : Fin (m + n) → Sort u} (left : (
i : Fin m) → motive (Fin.castAdd n i))   (right : (i : Fin n) → motive (Fin.natA
dd m i)…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_rec_constant`：∀ {α : Sort u_1} {a a' : α} {β : Sort u_2} (y : β) (h :
 a = a'), h ▸ y = y
-/
theorem vecAppend_eq_ite {α : Type*} {o : ℕ} (ho : o = m + n) (u : Fin m → α) (v : Fin n → α) :
    vecAppend ho u v = fun i : Fin o =>
      if h : (i : ℕ) < m then u ⟨i, h⟩ else v ⟨(i : ℕ) - m, by lia⟩ := by
  ext i
  rw [vecAppend, Fin.append, Function.comp_apply, Fin.addCases]
  congr with hi
  simp only [eq_rec_constant]
  rfl

@[simp]
/-
**Matrix.vecAppend_apply_zero** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecAppend_apply_zero {α : Type*} {o : Nat} (ho : o + 1 = m + 1 + n) (u : F
in (m + 1) -> α) (v : Fin n -> α) : vecAppend ho u v 0 = u 0
参数：ho : o + 1 = m + 1 + n；u : Fin (m + 1) -> α；v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem vecAppend_apply_zero {α : Type*} {o : ℕ} (ho : o + 1 = m + 1 + n) (u : Fin (m + 1) → α)
    (v : Fin n → α) : vecAppend ho u v 0 = u 0 :=
  rfl

@[simp]
/-
**Matrix.empty_vecAppend** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_vecAppend (v : Fin n -> α) : vecAppend n.zero_add.symm ![] v = v
参数：v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecAppend_eq_ite`：vecAppend_eq_ite {α : Type*} {o : Nat} (ho : o 
= m + n) (u : Fin m -> α) (v : Fin n -> α) : vecAppend ho u v = fun i : Fin o =>
 if h : (i : …
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem empty_vecAppend (v : Fin n → α) : vecAppend n.zero_add.symm ![] v = v := by
  ext
  simp [vecAppend_eq_ite]

@[simp]
/-
**Matrix.vecAppend_empty** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecAppend_empty (v : Fin n -> α) : vecAppend rfl v ![] = v
参数：v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecAppend_eq_ite`：vecAppend_eq_ite {α : Type*} {o : Nat} (ho : o 
= m + n) (u : Fin m -> α) (v : Fin n -> α) : vecAppend ho u v = fun i : Fin o =>
 if h : (i : …
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecAppend_empty (v : Fin n → α) : vecAppend rfl v ![] = v := by
  ext
  simp [vecAppend_eq_ite]

@[simp]
/-
**Matrix.cons_vecAppend** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_vecAppend (ho : o + 1 = m + 1 + n) (x : α) (u : Fin m -> α) (v : Fin 
n -> α) : vecAppend ho (vecCons x u) v = vecCons x (vecAppend (by lia) u v)
参数：ho : o + 1 = m + 1 + n；x : α；u : Fin m -> α；v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecAppend_eq_ite`：vecAppend_eq_ite {α : Type*} {o : Nat} (ho : o 
= m + n) (u : Fin m -> α) (v : Fin n -> α) : vecAppend ho u v = fun i : Fin o =>
 if h : (i : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Matrix.cons_val_succ'`：cons_val_succ' {i : Nat} (h : i.succ < m.succ) (x
 : α) (u : Fin m -> α) : vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ 
h⟩
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.Simproc.add_sub_add_le`：∀ (a c : ℕ) {b d : ℕ}, b ≤ d → a + b - (c + 
d) = a - (c + (d - b))
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.add_le_add_iff_right`：∀ {m k n : ℕ}, m + n ≤ k + n ↔ m ≤ k
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
theorem cons_vecAppend (ho : o + 1 = m + 1 + n) (x : α) (u : Fin m → α) (v : Fin n → α) :
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

/-- `vecAlt0 v` gives a vector with half the length of `v`, with
only alternate elements (even-numbered). -/
/-
**Matrix.vecAlt0** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vecAlt0 (hm : m = n + n) (v : Fin m -> α) (k : Fin n) : α
参数：hm : m = n + n；v : Fin m -> α；k : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vecAlt0 v` gives a vector with half the length of `v`, with
only alternate elements (even-numbered).
-/
def vecAlt0 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α := v ⟨(k : ℕ) + k, by lia⟩

/-- `vecAlt1 v` gives a vector with half the length of `v`, with
only alternate elements (odd-numbered). -/
/-
**Matrix.vecAlt1** 是 Mathlib 中的一个定义，位于命名空间 `Matrix`。
形式化陈述：vecAlt1 (hm : m = n + n) (v : Fin m -> α) (k : Fin n) : α
参数：hm : m = n + n；v : Fin m -> α；k : Fin n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`vecAlt1 v` gives a vector with half the length of `v`, with
only alternate elements (odd-numbered).
-/
def vecAlt1 (hm : m = n + n) (v : Fin m → α) (k : Fin n) : α :=
  v ⟨(k : ℕ) + k + 1, hm.symm ▸ Nat.add_succ_lt_add k.2 k.2⟩

section bits

/-
**Matrix.vecAlt0_vecAppend** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecAlt0_vecAppend (v : Fin n -> α) : vecAlt0 rfl (vecAppend rfl v v) = v ∘
 (fun n => n + n)
参数：v : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecAppend_eq_ite`：vecAppend_eq_ite {α : Type*} {o : Nat} (ho : o 
= m + n) (u : Fin m -> α) (v : Fin n -> α) : vecAppend ho u v = fun i : Fin o =>
 if h : (i : …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.mod_eq_sub_mod`：∀ {a b : ℕ}, a ≥ b → a % b = (a - b) % b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
-/
theorem vecAlt0_vecAppend (v : Fin n → α) :
    vecAlt0 rfl (vecAppend rfl v v) = v ∘ (fun n ↦ n + n) := by
  ext i
  simp_rw [Function.comp, vecAlt0, vecAppend_eq_ite]
  split_ifs with h <;> congr
  · rw [Fin.val_mk] at h
    exact (Nat.mod_eq_of_lt h).symm
  · rw [Fin.val_mk, not_lt] at h
    simp only [Nat.mod_eq_sub_mod h]
    refine (Nat.mod_eq_of_lt ?_).symm
    lia
/-
**Matrix.vecAlt1_vecAppend** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecAlt1_vecAppend (v : Fin (n + 1) -> α) : vecAlt1 rfl (vecAppend rfl v v)
 = v ∘ (fun n => (n + n) + 1)
参数：v : Fin (n + 1) -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Matrix.vecAppend_eq_ite`：vecAppend_eq_ite {α : Type*} {o : Nat} (ho : o 
= m + n) (u : Fin m -> α) (v : Fin n -> α) : vecAppend ho u v = fun i : Fin o =>
 if h : (i : …
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.mod_eq_of_lt`：∀ {a b : ℕ}, a < b → a % b = a
· 使用定理 `Nat.mod_add_mod`：∀ (m n k : ℕ), (m % n + k) % n = (m + k) % n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Nat.mod_eq_sub_mod`：∀ {a b : ℕ}, a ≥ b → a % b = (a - b) % b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
-/
theorem vecAlt1_vecAppend (v : Fin (n + 1) → α) :
    vecAlt1 rfl (vecAppend rfl v v) = v ∘ (fun n ↦ (n + n) + 1) := by
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
/-
**Matrix.vecHead_vecAlt0** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecHead_vecAlt0 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) -> α) : ve
cHead (vecAlt0 hm v) = v 0
参数：hm : m + 2 = n + 1 + (n + 1)；v : Fin (m + 2) -> α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem vecHead_vecAlt0 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) → α) :
    vecHead (vecAlt0 hm v) = v 0 :=
  rfl

@[simp]
/-
**Matrix.vecHead_vecAlt1** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：vecHead_vecAlt1 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) -> α) : ve
cHead (vecAlt1 hm v) = v 1
参数：hm : m + 2 = n + 1 + (n + 1)；v : Fin (m + 2) -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem vecHead_vecAlt1 (hm : m + 2 = n + 1 + (n + 1)) (v : Fin (m + 2) → α) :
    vecHead (vecAlt1 hm v) = v 1 := by simp [vecHead, vecAlt1]
/-
**Matrix.cons_vec_bit0_eq_alt0** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_vec_bit0_eq_alt0 (x : α) (u : Fin n -> α) (i : Fin (n + 1)) : vecCons
 x u (i + i) = vecAlt0 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i
参数：x : α；u : Fin n -> α；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecAlt0_vecAppend`：vecAlt0_vecAppend (v : Fin n -> α) : vecAlt0 r
fl (vecAppend rfl v v) = v ∘ (fun n => n + n)
-/
theorem cons_vec_bit0_eq_alt0 (x : α) (u : Fin n → α) (i : Fin (n + 1)) :
    vecCons x u (i + i) = vecAlt0 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i := by
  rw [vecAlt0_vecAppend]; rfl
/-
**Matrix.cons_vec_bit1_eq_alt1** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_vec_bit1_eq_alt1 (x : α) (u : Fin n -> α) (i : Fin (n + 1)) : vecCons
 x u ((i + i) + 1) = vecAlt1 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i
参数：x : α；u : Fin n -> α；i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.vecAlt1_vecAppend`：vecAlt1_vecAppend (v : Fin (n + 1) -> α) : vec
Alt1 rfl (vecAppend rfl v v) = v ∘ (fun n => (n + n) + 1)
-/
theorem cons_vec_bit1_eq_alt1 (x : α) (u : Fin n → α) (i : Fin (n + 1)) :
    vecCons x u ((i + i) + 1) = vecAlt1 rfl (vecAppend rfl (vecCons x u) (vecCons x u)) i := by
  rw [vecAlt1_vecAppend]; rfl

end bits

@[simp]
/-
**Matrix.cons_vecAlt0** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_vecAlt0 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m -> α) 
: vecAlt0 h (vecCons x (vecCons y u)) = vecCons x (vecAlt0 (by lia) u)
参数：h : m + 1 + 1 = n + 1 + (n + 1)；x y : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Matrix.cons_val_succ'`：cons_val_succ' {i : Nat} (h : i.succ < m.succ) (x
 : α) (u : Fin m -> α) : vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ 
h⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_vecAlt0 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m → α) :
    vecAlt0 h (vecCons x (vecCons y u)) = vecCons x (vecAlt0 (by lia) u) := by
  ext i
  simp_rw [vecAlt0]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp only [← Nat.add_assoc, Nat.add_right_comm, cons_val_succ',
      vecAlt0]

@[simp]
/-
**Matrix.empty_vecAlt0** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_vecAlt0 (α) {h} : vecAlt0 h (![] : Fin 0 -> α) = ![]
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem empty_vecAlt0 (α) {h} : vecAlt0 h (![] : Fin 0 → α) = ![] := by
  simp [eq_iff_true_of_subsingleton]

@[simp]
/-
**Matrix.cons_vecAlt1** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：cons_vecAlt1 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m -> α) 
: vecAlt1 h (vecCons x (vecCons y u)) = vecCons y (vecAlt1 (by lia) u)
参数：h : m + 1 + 1 = n + 1 + (n + 1)；x y : α；u : Fin m -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_right_comm`：∀ (n m k : ℕ), n + m + k = n + k + m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Matrix.cons_val_succ'`：cons_val_succ' {i : Nat} (h : i.succ < m.succ) (x
 : α) (u : Fin m -> α) : vecCons x u ⟨i.succ, h⟩ = u ⟨i, Nat.lt_of_succ_lt_succ 
h⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_vecAlt1 (h : m + 1 + 1 = n + 1 + (n + 1)) (x y : α) (u : Fin m → α) :
    vecAlt1 h (vecCons x (vecCons y u)) = vecCons y (vecAlt1 (by lia) u) := by
  ext i
  simp_rw [vecAlt1]
  rcases i with ⟨⟨⟩ | i, hi⟩
  · rfl
  · simp [vecAlt1, Nat.add_right_comm, ← Nat.add_assoc]

@[simp]
/-
**Matrix.empty_vecAlt1** 是 Mathlib 中的一个定理，位于命名空间 `Matrix`。
形式化陈述：empty_vecAlt1 (α) {h} : vecAlt1 h (![] : Fin 0 -> α) = ![]
参数：α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem empty_vecAlt1 (α) {h} : vecAlt1 h (![] : Fin 0 → α) = ![] := by
  simp [eq_iff_true_of_subsingleton]

end Val

/-
**Matrix.const_fin1_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：const_fin1_eq (x : α) : (fun _ : Fin 1 => x) = ![x]
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.cons_fin_one`：cons_fin_one (x : α) (u : Fin 0 -> α) : vecCons x u
 = fun _ => x
-/
lemma const_fin1_eq (x : α) : (fun _ : Fin 1 => x) = ![x] :=
  (cons_fin_one x _).symm

/-!
### Interaction between cons and Equiv.swap
-/

section swap

@[simp]
/-
**Matrix.cons_cons_comp_swap_zero_one** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cons_cons_comp_swap_zero_one (a b : α) (x : Fin n -> α) : vecCons a (vecCo
ns b x) ∘ (Equiv.swap 0 1) = vecCons b (vecCons a x)
参数：a b : α；x : Fin n -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Fin.succ_ne_zero`：∀ {n : ℕ} (k : Fin n), k.succ ≠ 0
· 使用定理 `Fin.succ_succ_ne_one`：∀ {n : ℕ} (a : Fin n), a.succ.succ ≠ 1
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
-/
lemma cons_cons_comp_swap_zero_one (a b : α) (x : Fin n → α) :
    vecCons a (vecCons b x) ∘ (Equiv.swap 0 1) = vecCons b (vecCons a x) := by
  ext j : 1
  match j with
  | 0 => simp
  | 1 => simp
  | ⟨i + 2, h⟩ =>
    have h' : (⟨i + 2, h⟩ : Fin n.succ.succ) = Fin.succ (Fin.succ ⟨i, by lia⟩) := by grind
    simp only [Nat.succ_eq_add_one, h', Function.comp_apply,
      Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _) (Fin.succ_succ_ne_one _), cons_val_succ]
/-
**Matrix.cons_swap** 是 Mathlib 中的一个引理，位于命名空间 `Matrix`。
形式化陈述：cons_swap (a : α) (x : Fin n -> α) (i j : Fin n) : vecCons a (x ∘ (Equiv.s
wap i j)) = vecCons a x ∘ (Equiv.swap i.succ j.succ)
参数：a : α；x : Fin n -> α；i j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Fin.succ_ne_zero`：∀ {n : ℕ} (k : Fin n), k.succ ≠ 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.cons_val_succ`：cons_val_succ (x : α) (u : Fin m -> α) (i : Fin m)
 : vecCons x u i.succ = u i
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `Equiv.swap_apply_right`：swap_apply_right (a b : α) : swap a b b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma cons_swap (a : α) (x : Fin n → α) (i j : Fin n) :
    vecCons a (x ∘ (Equiv.swap i j)) = vecCons a x ∘ (Equiv.swap i.succ j.succ) := by
  ext k : 1
  rcases eq_or_ne k 0 with rfl | hk₀
  · simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
  rcases eq_or_ne k i.succ with rfl | hki
  · simp
  rcases eq_or_ne k j.succ with rfl | hkj
  · simp
  have hk : k = Fin.succ ⟨k - 1, by lia⟩ := by grind
  rw [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj, hk, cons_val_succ,
    Function.comp_apply, cons_val_succ, Equiv.swap_apply_of_ne_of_ne (by grind) (by grind)]

end swap

end Matrix

