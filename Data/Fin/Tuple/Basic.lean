/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yury Kudryashov, Sébastien Gouëzel, Chris Hughes, Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Fin.Rev
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Fin.Basic
public import Batteries.Data.Fin.Lemmas

/-!
# Operation on tuples

We interpret maps `∀ i : Fin n, α i` as `n`-tuples of elements of possibly varying type `α i`,
`(α 0, …, α (n-1))`. A particular case is `Fin n → α` of elements with all the same type.
In this case when `α i` is a constant map, then tuples are isomorphic (but not definitionally equal)
to `Vector`s.

## Main declarations

There are three (main) ways to consider `Fin n` as a subtype of `Fin (n + 1)`, hence three (main)
ways to move between tuples of length `n` and of length `n + 1` by adding/removing an entry.

### Adding at the start

* `Fin.succ`: Send `i : Fin n` to `i + 1 : Fin (n + 1)`. This is defined in Core.
* `Fin.cases`: Induction/recursion principle for `Fin`: To prove a property/define a function for
  all `Fin (n + 1)`, it is enough to prove/define it for `0` and for `i.succ` for all `i : Fin n`.
  This is defined in Core.
* `Fin.cons`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.cons a f : Fin (n + 1) → α` by adding `a` at the start. In general, tuples can be dependent
  functions, in which case `f : ∀ i : Fin n, α i.succ` and `a : α 0`. This is a special case of
  `Fin.cases`.
* `Fin.tail`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.tail f : Fin n → α` by forgetting
  the start. In general, tuples can be dependent functions,
  in which case `Fin.tail f : ∀ i : Fin n, α i.succ`.

### Adding at the end

* `Fin.castSucc`: Send `i : Fin n` to `i : Fin (n + 1)`. This is defined in Core.
* `Fin.lastCases`: Induction/recursion principle for `Fin`: To prove a property/define a function
  for all `Fin (n + 1)`, it is enough to prove/define it for `last n` and for `i.castSucc` for all
  `i : Fin n`. This is defined in Core.
* `Fin.snoc`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.snoc f a : Fin (n + 1) → α` by adding `a` at the end. In general, tuples can be dependent
  functions, in which case `f : ∀ i : Fin n, α i.castSucc` and `a : α (last n)`. This is a
  special case of `Fin.lastCases`.
* `Fin.init`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.init f : Fin n → α` by forgetting
  the end. In general, tuples can be dependent functions,
  in which case `Fin.init f : ∀ i : Fin n, α i.castSucc`.

### Adding in the middle

For a **pivot** `p : Fin (n + 1)`,
* `Fin.succAbove`: Send `i : Fin n` to
  * `i : Fin (n + 1)` if `i < p`,
  * `i + 1 : Fin (n + 1)` if `p ≤ i`.
* `Fin.succAboveCases`: Induction/recursion principle for `Fin`: To prove a property/define a
  function for all `Fin (n + 1)`, it is enough to prove/define it for `p` and for `p.succAbove i`
  for all `i : Fin n`.
* `Fin.insertNth`: Turn a tuple `f : Fin n → α` and an entry `a : α` into a tuple
  `Fin.insertNth f a : Fin (n + 1) → α` by adding `a` in position `p`. In general, tuples can be
  dependent functions, in which case `f : ∀ i : Fin n, α (p.succAbove i)` and `a : α p`. This is a
  special case of `Fin.succAboveCases`.
* `Fin.removeNth`: Turn a tuple `f : Fin (n + 1) → α` into a tuple `Fin.removeNth p f : Fin n → α`
  by forgetting the `p`-th value. In general, tuples can be dependent functions,
  in which case `Fin.removeNth f : ∀ i : Fin n, α (succAbove p i)`.

`p = 0` means we add at the start. `p = last n` means we add at the end.

### Miscellaneous

* `Fin.find p h` : returns the first index `i : Fin n` where `p i` is satisfied given the
  hypothesis that `h : ∃ i, p i`.
* `Fin.append a b` : append two tuples.
* `Fin.repeat n a` : repeat a tuple `n` times.

-/

@[expose] public section

assert_not_exists Monoid

universe u v

namespace Fin

variable {m n : Nat}

open Function

section Tuple

/-- There is exactly one tuple of size zero. -/
example (α : Fin 0 -> Sort u) : Unique (forall i : Fin 0, α i) := by infer_instance

/--
theorem `tuple0_le` / 定理 `tuple0_le`

English:
theorem tuple0_le
  given: {α : Fin 0 -> Type*} [forall i, Preorder (α i)] (f g : forall i, α i)
  statement: f <= g
  proof: finZeroElim

中文:
定理 tuple0_le
  条件: {α : 有限集 0 -> 类型} [对任意 i, 预序 (α i)] (f g : 对任意 i, α i)
  结论: f <= g
  证明: finZeroElim

Depends on / 依赖: finZeroElim
-/
theorem tuple0_le {α : Fin 0 -> Type*} [forall i, Preorder (α i)] (f g : forall i, α i) : f <= g :=
  finZeroElim

variable {α : Fin (n + 1) -> Sort u} (x : α 0) (q : forall i, α i) (p : forall i : Fin n, α i.succ) (i : Fin n)
  (y : α i.succ) (z : α 0)

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (q : forall i, α i)
  body: fun i => q i.succ

中文:
定义 tail
  签名: (q : 对任意 i, α i)
  定义体: fun i => q i.succ

Depends on / 依赖: i.succ
-/
def tail (q : forall i, α i) : forall i : Fin n, α i.succ := fun i => q i.succ

/--
theorem `tail_def` / 定理 `tail_def`

English:
theorem tail_def
  given: {n : Nat} {α : Fin (n + 1) -> Sort*} {q : forall i, α i}
  proof: rfl

中文:
定理 tail_def
  条件: {n : 自然数} {α : 有限集 (n + 1) -> 类型层*} {q : 对任意 i, α i}
  证明: rfl
-/
theorem tail_def {n : Nat} {α : Fin (n + 1) -> Sort*} {q : forall i, α i} :
    (tail fun k : Fin (n + 1) => q k) = fun k : Fin n => q k.succ :=
  rfl

/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (x : α 0) (p : forall i : Fin n, α i.succ)
  body: fun j => Fin.cases x p j

@[simp]

中文:
定义 cons
  签名: (x : α 0) (p : 对任意 i : 有限集 n, α i.succ)
  定义体: fun j => Fin.cases x p j

@[simp]

Depends on / 依赖: Fin.cases
-/
def cons (x : α 0) (p : forall i : Fin n, α i.succ) : forall i, α i := fun j => Fin.cases x p j

@[simp]
/--
theorem `tail_cons` / 定理 `tail_cons`

English:
theorem tail_cons
  statement: tail (cons x p) = p
  proof: by
  simp +unfoldPartialApp [tail, cons]

@[simp]

中文:
定理 tail_cons
  结论: tail (cons x p) = p
  证明: by
  simp +unfoldPartialApp [tail, cons]

@[simp]

Depends on / 依赖: unfoldPartialApp
-/
theorem tail_cons : tail (cons x p) = p := by
  simp +unfoldPartialApp [tail, cons]

@[simp]
/--
theorem `cons_succ` / 定理 `cons_succ`

English:
theorem cons_succ
  statement: cons x p i.succ = p i
  proof: by simp [cons]

@[simp]

中文:
定理 cons_succ
  结论: cons x p i.succ = p i
  证明: by simp [cons]

@[simp]
-/
theorem cons_succ : cons x p i.succ = p i := by simp [cons]

@[simp]
/--
theorem `cons_comp_succ` / 定理 `cons_comp_succ`

English:
theorem cons_comp_succ
  given: {α : Sort*} (x : α) (p : Fin n -> α)
  proof: funext fun _ => Fin.cons_succ ..

@[simp]

中文:
定理 cons_comp_succ
  条件: {α : 类型层*} (x : α) (p : 有限集 n -> α)
  证明: funext fun _ => Fin.cons_succ ..

@[simp]

Depends on / 依赖: Fin.cons_succ, cons_succ
-/
theorem cons_comp_succ {α : Sort*} (x : α) (p : Fin n -> α) :
    cons x p ∘ Fin.succ = p :=
  funext fun _ => Fin.cons_succ ..

@[simp]
/--
theorem `cons_zero` / 定理 `cons_zero`

English:
theorem cons_zero
  statement: cons x p 0 = x
  proof: by simp [cons]

@[simp]

中文:
定理 cons_zero
  结论: cons x p 0 = x
  证明: by simp [cons]

@[simp]
-/
theorem cons_zero : cons x p 0 = x := by simp [cons]

@[simp]
/--
theorem `cons_one` / 定理 `cons_one`

English:
theorem cons_one
  given: {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall i : Fin n.succ, α i.succ)
  proof: by
  rw [← cons_succ x p]; rfl

@[simp]

中文:
定理 cons_one
  条件: {α : 有限集 (n + 2) -> 类型层*} (x : α 0) (p : 对任意 i : 有限集 n.succ, α i.succ)
  证明: by
  rw [← cons_succ x p]; rfl

@[simp]

Depends on / 依赖: cons_succ
-/
theorem cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall i : Fin n.succ, α i.succ) :
    cons x p 1 = p 0 := by
  rw [← cons_succ x p]; rfl

@[simp]
/--
theorem `cons_last` / 定理 `cons_last`

English:
theorem cons_last
  given: {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall i : Fin n.succ, α i.succ)
  proof: by
  rw [← cons_succ x p]; rfl

中文:
定理 cons_last
  条件: {α : 有限集 (n + 2) -> 类型层*} (x : α 0) (p : 对任意 i : 有限集 n.succ, α i.succ)
  证明: by
  rw [← cons_succ x p]; rfl

Depends on / 依赖: cons_succ
-/
theorem cons_last {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall i : Fin n.succ, α i.succ) :
    cons x p (.last _) = p (.last _) := by
  rw [← cons_succ x p]; rfl

/-- Updating a tuple and adding an element at the beginning commute. -/
@[simp]
/--
theorem `cons_update` / 定理 `cons_update`

English:
theorem cons_update
  statement: cons x (update p i y) = update (cons x p) i.succ y
  proof: by
  ext j
  cases j using Fin.cases <;> simp [Ne.symm, update_apply_of_injective _ (succ_injective _)]

中文:
定理 cons_update
  结论: cons x (update p i y) = update (cons x p) i.succ y
  证明: by
  ext j
  cases j using Fin.cases <;> simp [Ne.symm, update_apply_of_injective _ (succ_injective _)]

Depends on / 依赖: Fin.cases, Ne.symm, succ_injective, update_apply_of_injective
-/
theorem cons_update : cons x (update p i y) = update (cons x p) i.succ y := by
  ext j
  cases j using Fin.cases <;> simp [Ne.symm, update_apply_of_injective _ (succ_injective _)]

/--
theorem `cons_injective2` / 定理 `cons_injective2`

English:
theorem cons_injective2
  statement: Function.Injective2 (@cons n α)
  proof: fun x₀ y₀ x y h =>
  ⟨congr_fun h 0, funext fun i => by simpa using congr_fun h (Fin.succ i)⟩

@[simp]

中文:
定理 cons_injective2
  结论: 函数.Injective2 (@cons n α)
  证明: fun x₀ y₀ x y h =>
  ⟨congr_fun h 0, funext fun i => by simpa using congr_fun h (Fin.succ i)⟩

@[simp]
-/
theorem cons_injective2 : Function.Injective2 (@cons n α) := fun x₀ y₀ x y h =>
  ⟨congr_fun h 0, funext fun i => by simpa using congr_fun h (Fin.succ i)⟩

@[simp]
/--
theorem `cons_inj` / 定理 `cons_inj`

English:
theorem cons_inj
  given: {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ}
  proof: cons_injective2.eq_iff

中文:
定理 cons_inj
  条件: {x₀ y₀ : α 0} {x y : 对任意 i : 有限集 n, α i.succ}
  证明: cons_injective2.eq_iff

Depends on / 依赖: cons_injective2, cons_injective2.eq_iff, eq_iff
-/
theorem cons_inj {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ} :
    cons x₀ x = cons y₀ y ↔ x₀ = y₀ ∧ x = y :=
  cons_injective2.eq_iff

/--
theorem `cons_left_injective` / 定理 `cons_left_injective`

English:
theorem cons_left_injective
  given: (x : forall i : Fin n, α i.succ)
  statement: Function.Injective fun x₀ => cons x₀ x
  proof: cons_injective2.left _

中文:
定理 cons_left_injective
  条件: (x : 对任意 i : 有限集 n, α i.succ)
  结论: 函数.单射 fun x₀ => cons x₀ x
  证明: cons_injective2.left _

Depends on / 依赖: cons_injective2, cons_injective2.left
-/
theorem cons_left_injective (x : forall i : Fin n, α i.succ) : Function.Injective fun x₀ => cons x₀ x :=
  cons_injective2.left _

/--
theorem `cons_right_injective` / 定理 `cons_right_injective`

English:
theorem cons_right_injective
  given: (x₀ : α 0)
  statement: Function.Injective (cons x₀)
  proof: cons_injective2.right _

中文:
定理 cons_right_injective
  条件: (x₀ : α 0)
  结论: 函数.单射 (cons x₀)
  证明: cons_injective2.right _

Depends on / 依赖: cons_injective2, cons_injective2.right
-/
theorem cons_right_injective (x₀ : α 0) : Function.Injective (cons x₀) :=
  cons_injective2.right _

/-- Adding an element at the beginning of a tuple and then updating it amounts to adding it
directly. -/
@[simp]
/--
theorem `update_cons_zero` / 定理 `update_cons_zero`

English:
theorem update_cons_zero
  statement: update (cons x p) 0 z = cons z p
  proof: by
  ext j
  cases j using Fin.cases <;> simp

中文:
定理 update_cons_zero
  结论: update (cons x p) 0 z = cons z p
  证明: by
  ext j
  cases j using Fin.cases <;> simp

Depends on / 依赖: Fin.cases
-/
theorem update_cons_zero : update (cons x p) 0 z = cons z p := by
  ext j
  cases j using Fin.cases <;> simp

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
/--
theorem `cons_self_tail` / 定理 `cons_self_tail`

English:
theorem cons_self_tail
  statement: cons (q 0) (tail q) = q
  proof: by
  ext j
  cases j using Fin.cases <;> simp [tail]

@[simp]

中文:
定理 cons_self_tail
  结论: cons (q 0) (tail q) = q
  证明: by
  ext j
  cases j using Fin.cases <;> simp [tail]

@[simp]

Depends on / 依赖: Fin.cases
-/
theorem cons_self_tail : cons (q 0) (tail q) = q := by
  ext j
  cases j using Fin.cases <;> simp [tail]

@[simp]
/--
theorem `cons_zero_succ` / 定理 `cons_zero_succ`

English:
theorem cons_zero_succ
  statement: (cons 0 Fin.succ : Fin (n + 1) -> Fin (n + 1)) = id
  proof: cons_self_tail id

中文:
定理 cons_zero_succ
  结论: (cons 0 有限集.succ : 有限集 (n + 1) -> 有限集 (n + 1)) = id
  证明: cons_self_tail id

Depends on / 依赖: cons_self_tail
-/
theorem cons_zero_succ : (cons 0 Fin.succ : Fin (n + 1) -> Fin (n + 1)) = id :=
  cons_self_tail id

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the first element of the tuple.

This is `Fin.cons` as an `Equiv`. -/
@[simps]
/--
Definition of `consEquiv` / `consEquiv` 的定义

English:
definition consEquiv
  signature: (α : Fin (n + 1) -> Type*)
  body: cons f.1 f.2
  invFun f := (f 0, tail f)
  left_inv f := by simp
  right_inv f := by simp

中文:
定义 consEquiv
  签名: (α : 有限集 (n + 1) -> 类型)
  定义体: cons f.1 f.2
  invFun f := (f 0, tail f)
  left_inv f := by simp
  right_inv f := by simp
-/
def consEquiv (α : Fin (n + 1) -> Type*) : α 0 × (forall i, α (succ i)) ≃ forall i, α i where
  toFun f := cons f.1 f.2
  invFun f := (f 0, tail f)
  left_inv f := by simp
  right_inv f := by simp

/-- Recurse on an `n+1`-tuple by splitting it into a single element and an `n`-tuple. -/
@[elab_as_elim]
/--
Definition of `consCases` / `consCases` 的定义

English:
definition consCases
  signature: {motive : (forall i : Fin n.succ, α i) -> Sort v} (cons : forall x₀ x, motive (Fin.cons x₀ x))
  body: _root_.cast (by rw [cons_self_tail]) cons (x 0) (tail x)

中文:
定义 consCases
  签名: {motive : (对任意 i : 有限集 n.succ, α i) -> 类型层 v} (cons : 对任意 x₀ x, motive (有限集.cons x₀ x))
  定义体: _root_.cast (by rw [cons_self_tail]) cons (x 0) (tail x)

Depends on / 依赖: _root_, _root_.cast, cons_self_tail
-/
def consCases {motive : (forall i : Fin n.succ, α i) -> Sort v} (cons : forall x₀ x, motive (Fin.cons x₀ x))
    (x : forall i : Fin n.succ, α i) : motive x :=
_root_.cast (by rw [cons_self_tail]) cons (x 0) (tail x)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `consCases_cons` / 定理 `consCases_cons`

English:
theorem consCases_cons
  statement: {motive : (forall i : Fin n.succ, α i) -> Sort v}
  proof: by
  rw [consCases]; rw [cast_eq]
  congr

中文:
定理 consCases_cons
  结论: {motive : (对任意 i : 有限集 n.succ, α i) -> 类型层 v}
  证明: by
  rw [consCases]; rw [cast_eq]
  congr

Depends on / 依赖: cast_eq, consCases
-/
theorem consCases_cons {motive : (forall i : Fin n.succ, α i) -> Sort v}
    (cons : forall x₀ x, motive (Fin.cons x₀ x))
    (x₀ : α 0) (x : forall i : Fin n, α i.succ) : consCases cons (Fin.cons x₀ x) = cons x₀ x := by
  rw [consCases]; rw [cast_eq]
  congr

/-- Recurse on a tuple by splitting into `Fin.elim0` and `Fin.cons`. -/
@[elab_as_elim]
/--
Definition of `consInduction` / `consInduction` 的定义

English:
definition consInduction
  signature: {α : Sort*} {motive : forall {n : Nat}, (Fin n -> α) -> Sort v} (elim0 : motive Fin.elim0)

中文:
定义 consInduction
  签名: {α : 类型层*} {motive : 对任意 {n : 自然数}, (有限集 n -> α) -> 类型层 v} (elim0 : motive 有限集.elim0)
-/
def consInduction {α : Sort*} {motive : forall {n : Nat}, (Fin n -> α) -> Sort v} (elim0 : motive Fin.elim0)
    (cons : forall {n} (x₀) (x : Fin n -> α), motive x -> motive (Fin.cons x₀ x)) :
    forall {n : Nat} (x : Fin n -> α), motive x
  | 0, x => by convert! elim0
  | _ + 1, x => consCases (fun _ _ => cons _ _ <| consInduction elim0 cons _) x

/--
theorem `cons_injective_of_injective` / 定理 `cons_injective_of_injective`

English:
theorem cons_injective_of_injective
  statement: {α} {x₀ : α} {x : Fin n -> α} (hx₀ : x₀ ∉ Set.range x)
  proof: by
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> aesop (add simp [hx.eq_iff])

中文:
定理 cons_injective_of_injective
  结论: {α} {x₀ : α} {x : 有限集 n -> α} (hx₀ : x₀ ∉ 集合.range x)
  证明: by
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> aesop (add simp [hx.eq_iff])

Depends on / 依赖: Fin.cases, eq_iff, hx.eq_iff
-/
theorem cons_injective_of_injective {α} {x₀ : α} {x : Fin n -> α} (hx₀ : x₀ ∉ Set.range x)
    (hx : Function.Injective x) : Function.Injective (cons x₀ x : Fin n.succ -> α) := by
  intro i j
  cases i using Fin.cases <;> cases j using Fin.cases <;> aesop (add simp [hx.eq_iff])

/--
theorem `cons_injective_iff` / 定理 `cons_injective_iff`

English:
theorem cons_injective_iff
  given: {α} {x₀ : α} {x : Fin n -> α}
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => cons_injective_of_injective h.1 h.2⟩
  · rintro ⟨i, hi⟩
    replace h := @h i.succ 0
    simp [hi] at h
  · simpa [Function.comp] using! h.comp (Fin.succ_injective _)

中文:
定理 cons_injective_iff
  条件: {α} {x₀ : α} {x : 有限集 n -> α}
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => cons_injective_of_injective h.1 h.2⟩
  · rintro ⟨i, hi⟩
    replace h := @h i.succ 0
    simp [hi] at h
  · simpa [Function.comp] using! h.comp (Fin.succ_injective _)

Depends on / 依赖: Fin.succ_injective, Function, Function.comp, cons_injective_of_injective, h.comp, i.succ, replace, succ_injective
-/
theorem cons_injective_iff {α} {x₀ : α} {x : Fin n -> α} :
    Function.Injective (cons x₀ x : Fin n.succ -> α) ↔ x₀ ∉ Set.range x ∧ Function.Injective x := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => cons_injective_of_injective h.1 h.2⟩
  · rintro ⟨i, hi⟩
    replace h := @h i.succ 0
    simp [hi] at h
  · simpa [Function.comp] using! h.comp (Fin.succ_injective _)

/--
theorem `exists_cons` / 定理 `exists_cons`

English:
theorem exists_cons
  given: {α : Fin (n + 1) -> Type*} (q : forall i, α i)
  proof: ⟨q 0, tail q, (cons_self_tail q).symm⟩

@[simp]

中文:
定理 存在_cons
  条件: {α : 有限集 (n + 1) -> 类型} (q : 对任意 i, α i)
  证明: ⟨q 0, tail q, (cons_self_tail q).symm⟩

@[simp]

Depends on / 依赖: cons_self_tail
-/
theorem exists_cons {α : Fin (n + 1) -> Type*} (q : forall i, α i) :
    exists (x₀ : α 0) (x : forall i : Fin n, α i.succ), q = cons x₀ x :=
  ⟨q 0, tail q, (cons_self_tail q).symm⟩

@[simp]
/--
theorem `forall_fin_zero_pi` / 定理 `forall_fin_zero_pi`

English:
theorem forall_fin_zero_pi
  given: {α : Fin 0 -> Sort*} {P : (forall i, α i) -> Prop}
  proof: ⟨fun h => h _, fun h x => Subsingleton.elim finZeroElim x ▸ h⟩

@[simp]

中文:
定理 对任意_fin_zero_pi
  条件: {α : 有限集 0 -> 类型层*} {P : (对任意 i, α i) -> 命题}
  证明: ⟨fun h => h _, fun h x => Subsingleton.elim finZeroElim x ▸ h⟩

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, finZeroElim
-/
theorem forall_fin_zero_pi {α : Fin 0 -> Sort*} {P : (forall i, α i) -> Prop} :
    (forall x, P x) ↔ P finZeroElim :=
  ⟨fun h => h _, fun h x => Subsingleton.elim finZeroElim x ▸ h⟩

@[simp]
/--
theorem `exists_fin_zero_pi` / 定理 `exists_fin_zero_pi`

English:
theorem exists_fin_zero_pi
  given: {α : Fin 0 -> Sort*} {P : (forall i, α i) -> Prop}
  proof: ⟨fun ⟨x, h⟩ => Subsingleton.elim x finZeroElim ▸ h, fun h => ⟨_, h⟩⟩

中文:
定理 存在_fin_zero_pi
  条件: {α : 有限集 0 -> 类型层*} {P : (对任意 i, α i) -> 命题}
  证明: ⟨fun ⟨x, h⟩ => Subsingleton.elim x finZeroElim ▸ h, fun h => ⟨_, h⟩⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, finZeroElim
-/
theorem exists_fin_zero_pi {α : Fin 0 -> Sort*} {P : (forall i, α i) -> Prop} :
    (exists x, P x) ↔ P finZeroElim :=
  ⟨fun ⟨x, h⟩ => Subsingleton.elim x finZeroElim ▸ h, fun h => ⟨_, h⟩⟩

/--
theorem `forall_fin_succ_pi` / 定理 `forall_fin_succ_pi`

English:
theorem forall_fin_succ_pi
  given: {P : (forall i, α i) -> Prop}
  statement: (forall x, P x) ↔ forall a v, P (Fin.cons a v)
  proof: ⟨fun h a v => h (Fin.cons a v), consCases⟩

中文:
定理 对任意_fin_succ_pi
  条件: {P : (对任意 i, α i) -> 命题}
  结论: (对任意 x, P x) ↔ 对任意 a v, P (有限集.cons a v)
  证明: ⟨fun h a v => h (Fin.cons a v), consCases⟩

Depends on / 依赖: Fin.cons, consCases
-/
theorem forall_fin_succ_pi {P : (forall i, α i) -> Prop} : (forall x, P x) ↔ forall a v, P (Fin.cons a v) :=
  ⟨fun h a v => h (Fin.cons a v), consCases⟩

/--
theorem `exists_fin_succ_pi` / 定理 `exists_fin_succ_pi`

English:
theorem exists_fin_succ_pi
  given: {P : (forall i, α i) -> Prop}
  statement: (exists x, P x) ↔ exists a v, P (Fin.cons a v)
  proof: ⟨fun ⟨x, h⟩ => ⟨x 0, tail x, (cons_self_tail x).symm ▸ h⟩, fun ⟨_, _, h⟩ => ⟨_, h⟩⟩

中文:
定理 存在_fin_succ_pi
  条件: {P : (对任意 i, α i) -> 命题}
  结论: (存在 x, P x) ↔ 存在 a v, P (有限集.cons a v)
  证明: ⟨fun ⟨x, h⟩ => ⟨x 0, tail x, (cons_self_tail x).symm ▸ h⟩, fun ⟨_, _, h⟩ => ⟨_, h⟩⟩

Depends on / 依赖: cons_self_tail
-/
theorem exists_fin_succ_pi {P : (forall i, α i) -> Prop} : (exists x, P x) ↔ exists a v, P (Fin.cons a v) :=
  ⟨fun ⟨x, h⟩ => ⟨x 0, tail x, (cons_self_tail x).symm ▸ h⟩, fun ⟨_, _, h⟩ => ⟨_, h⟩⟩

/-- Updating the first element of a tuple does not change the tail. -/
@[simp]
/--
theorem `tail_update_zero` / 定理 `tail_update_zero`

English:
theorem tail_update_zero
  statement: tail (update q 0 z) = tail q
  proof: by
  ext j
  simp [tail]

中文:
定理 tail_update_zero
  结论: tail (update q 0 z) = tail q
  证明: by
  ext j
  simp [tail]
-/
theorem tail_update_zero : tail (update q 0 z) = tail q := by
  ext j
  simp [tail]

/-- Updating a nonzero element and taking the tail commute. -/
@[simp]
/--
theorem `tail_update_succ` / 定理 `tail_update_succ`

English:
theorem tail_update_succ
  statement: tail (update q i.succ y) = update (tail q) i y
  proof: by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [tail]
  · simp [tail, (Fin.succ_injective n).ne h, h]

中文:
定理 tail_update_succ
  结论: tail (update q i.succ y) = update (tail q) i y
  证明: by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [tail]
  · simp [tail, (Fin.succ_injective n).ne h, h]

Depends on / 依赖: Fin.succ_injective, succ_injective
-/
theorem tail_update_succ : tail (update q i.succ y) = update (tail q) i y := by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [tail]
  · simp [tail, (Fin.succ_injective n).ne h, h]

/--
theorem `comp_cons` / 定理 `comp_cons`

English:
theorem comp_cons
  given: {α : Sort*} {β : Sort*} (g : α -> β) (y : α) (q : Fin n -> α)
  proof: by
  ext j
  by_cases h : j = 0
  · rw [h]
    rfl
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this]; rw [cons_succ]; rw [comp_apply]; rw [comp_apply]; rw [cons_succ]

中文:
定理 comp_cons
  条件: {α : 类型层*} {β : 类型层*} (g : α -> β) (y : α) (q : 有限集 n -> α)
  证明: by
  ext j
  by_cases h : j = 0
  · rw [h]
    rfl
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this]; rw [cons_succ]; rw [comp_apply]; rw [comp_apply]; rw [cons_succ]

Depends on / 依赖: comp_apply, cons_succ, succ_pred
-/
theorem comp_cons {α : Sort*} {β : Sort*} (g : α -> β) (y : α) (q : Fin n -> α) :
    g ∘ cons y q = cons (g y) (g ∘ q) := by
  ext j
  by_cases h : j = 0
  · rw [h]
    rfl
  · let j' := pred j h
    have : j'.succ = j := succ_pred j h
    rw [← this]; rw [cons_succ]; rw [comp_apply]; rw [comp_apply]; rw [cons_succ]

/--
theorem `comp_tail` / 定理 `comp_tail`

English:
theorem comp_tail
  given: {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n.succ -> α)
  proof: by
  ext j
  simp [tail]

中文:
定理 comp_tail
  条件: {α : 类型层*} {β : 类型层*} (g : α -> β) (q : 有限集 n.succ -> α)
  证明: by
  ext j
  simp [tail]
-/
theorem comp_tail {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n.succ -> α) :
    g ∘ tail q = tail (g ∘ q) := by
  ext j
  simp [tail]

section Preorder

variable {α : Fin (n + 1) -> Type*}

/--
theorem `le_cons` / 定理 `le_cons`

English:
theorem le_cons
  given: [forall i, Preorder (α i)] {x : α 0} {q : forall i, α i} {p : forall i : Fin n, α i.succ}
  proof: forall_fin_succ.trans and_congr Iff.rfl forall_congr' fun j => by simp [tail]

中文:
定理 le_cons
  条件: [对任意 i, 预序 (α i)] {x : α 0} {q : 对任意 i, α i} {p : 对任意 i : 有限集 n, α i.succ}
  证明: forall_fin_succ.trans and_congr Iff.rfl forall_congr' fun j => by simp [tail]

Depends on / 依赖: Iff.rfl, and_congr, forall_congr, forall_fin_succ, forall_fin_succ.trans
-/
theorem le_cons [forall i, Preorder (α i)] {x : α 0} {q : forall i, α i} {p : forall i : Fin n, α i.succ} :
    q <= cons x p ↔ q 0 <= x ∧ tail q <= p :=
forall_fin_succ.trans and_congr Iff.rfl forall_congr' fun j => by simp [tail]

/--
theorem `cons_le` / 定理 `cons_le`

English:
theorem cons_le
  given: [forall i, Preorder (α i)] {x : α 0} {q : forall i, α i} {p : forall i : Fin n, α i.succ}
  proof: @le_cons _ (fun i => (α i)ᵒᵈ) _ x q p

中文:
定理 cons_le
  条件: [对任意 i, 预序 (α i)] {x : α 0} {q : 对任意 i, α i} {p : 对任意 i : 有限集 n, α i.succ}
  证明: @le_cons _ (fun i => (α i)ᵒᵈ) _ x q p

Depends on / 依赖: le_cons
-/
theorem cons_le [forall i, Preorder (α i)] {x : α 0} {q : forall i, α i} {p : forall i : Fin n, α i.succ} :
    cons x p <= q ↔ x <= q 0 ∧ p <= tail q :=
  @le_cons _ (fun i => (α i)ᵒᵈ) _ x q p

/--
theorem `cons_le_cons` / 定理 `cons_le_cons`

English:
theorem cons_le_cons
  given: [forall i, Preorder (α i)] {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ}
  proof: forall_fin_succ.trans and_congr_right' by simp only [cons_succ, Pi.le_def]

中文:
定理 cons_le_cons
  条件: [对任意 i, 预序 (α i)] {x₀ y₀ : α 0} {x y : 对任意 i : 有限集 n, α i.succ}
  证明: forall_fin_succ.trans and_congr_right' by simp only [cons_succ, Pi.le_def]

Depends on / 依赖: Pi.le_def, and_congr_right, cons_succ, forall_fin_succ, forall_fin_succ.trans, le_def
-/
theorem cons_le_cons [forall i, Preorder (α i)] {x₀ y₀ : α 0} {x y : forall i : Fin n, α i.succ} :
    cons x₀ x <= cons y₀ y ↔ x₀ <= y₀ ∧ x <= y :=
forall_fin_succ.trans and_congr_right' by simp only [cons_succ, Pi.le_def]

end Preorder

/--
theorem `range_fin_succ` / 定理 `range_fin_succ`

English:
theorem range_fin_succ
  given: {α} (f : Fin (n + 1) -> α)
  proof: Set.ext fun _ => exists_fin_succ.trans eq_comm.or Iff.rfl

@[simp]

中文:
定理 range_fin_succ
  条件: {α} (f : 有限集 (n + 1) -> α)
  证明: Set.ext fun _ => exists_fin_succ.trans eq_comm.or Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl, Set.ext, eq_comm, eq_comm.or, exists_fin_succ, exists_fin_succ.trans
-/
theorem range_fin_succ {α} (f : Fin (n + 1) -> α) :
    Set.range f = insert (f 0) (Set.range (Fin.tail f)) :=
Set.ext fun _ => exists_fin_succ.trans eq_comm.or Iff.rfl

@[simp]
/--
theorem `range_cons` / 定理 `range_cons`

English:
theorem range_cons
  given: {α} {n : Nat} (x : α) (b : Fin n -> α)
  proof: by
  rw [range_fin_succ]; rw [cons_zero]; rw [tail_cons]

中文:
定理 range_cons
  条件: {α} {n : 自然数} (x : α) (b : 有限集 n -> α)
  证明: by
  rw [range_fin_succ]; rw [cons_zero]; rw [tail_cons]

Depends on / 依赖: List.Nodup.of_map, Quot.induction_on, cons_zero, induction_on, of_map, range_fin_succ, tail_cons
-/
theorem range_cons {α} {n : Nat} (x : α) (b : Fin n -> α) :
    Set.range (Fin.cons x b : Fin n.succ -> α) = insert x (Set.range b) := by
  rw [range_fin_succ]; rw [cons_zero]; rw [tail_cons]

section Append

variable {α : Sort*}

/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: (a : Fin m -> α) (b : Fin n -> α)
  body: @Fin.addCases _ _ (fun _ => α) a b

@[simp]

中文:
定义 append
  签名: (a : 有限集 m -> α) (b : 有限集 n -> α)
  定义体: @Fin.addCases _ _ (fun _ => α) a b

@[simp]

Depends on / 依赖: Fin.addCases, List.Nodup.map_on, Quot.induction_on, addCases, induction_on, map_on
-/
def append (a : Fin m -> α) (b : Fin n -> α) : Fin (m + n) -> α :=
  @Fin.addCases _ _ (fun _ => α) a b

@[simp]
/--
theorem `append_left` / 定理 `append_left`

English:
theorem append_left
  given: (u : Fin m -> α) (v : Fin n -> α) (i : Fin m)
  proof: addCases_left _

中文:
定理 append_left
  条件: (u : 有限集 m -> α) (v : 有限集 n -> α) (i : 有限集 m)
  证明: addCases_left _

Depends on / 依赖: addCases_left
-/
theorem append_left (u : Fin m -> α) (v : Fin n -> α) (i : Fin m) :
    append u v (Fin.castAdd n i) = u i :=
  addCases_left _

/-- Variant of `append_left` using `Fin.castLE` instead of `Fin.castAdd`. -/
@[simp]
/--
theorem `append_left'` / 定理 `append_left'`

English:
theorem append_left'
  given: (u : Fin m -> α) (v : Fin n -> α) (i : Fin m)
  proof: addCases_left _

@[simp]

中文:
定理 append_left'
  条件: (u : 有限集 m -> α) (v : 有限集 n -> α) (i : 有限集 m)
  证明: addCases_left _

@[simp]

Depends on / 依赖: addCases_left
-/
theorem append_left' (u : Fin m -> α) (v : Fin n -> α) (i : Fin m) :
    append u v (Fin.castLE (by lia) i) = u i :=
  addCases_left _

@[simp]
/--
theorem `append_right` / 定理 `append_right`

English:
theorem append_right
  given: (u : Fin m -> α) (v : Fin n -> α) (i : Fin n)
  proof: addCases_right _

中文:
定理 append_right
  条件: (u : 有限集 m -> α) (v : 有限集 n -> α) (i : 有限集 n)
  证明: addCases_right _

Depends on / 依赖: addCases_right
-/
theorem append_right (u : Fin m -> α) (v : Fin n -> α) (i : Fin n) :
    append u v (natAdd m i) = v i :=
  addCases_right _

/--
theorem `append_right_nil` / 定理 `append_right_nil`

English:
theorem append_right_nil
  given: (u : Fin m -> α) (v : Fin n -> α) (hv : n = 0)
  proof: by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · rw [append_left, Function.comp_apply]
    refine congr_arg u (Fin.ext ?_)
    simp
  · exact (Fin.cast hv r).elim0

@[simp]

中文:
定理 append_right_nil
  条件: (u : 有限集 m -> α) (v : 有限集 n -> α) (hv : n = 0)
  证明: by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · rw [append_left, Function.comp_apply]
    refine congr_arg u (Fin.ext ?_)
    simp
  · exact (Fin.cast hv r).elim0

@[simp]

Depends on / 依赖: Fin.addCases, Fin.cast, Fin.ext, Function, Function.comp_apply, addCases, append_left, comp_apply, congr_arg
-/
theorem append_right_nil (u : Fin m -> α) (v : Fin n -> α) (hv : n = 0) :
    append u v = u ∘ Fin.cast (by rw [hv, Nat.add_zero]) := by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · rw [append_left, Function.comp_apply]
    refine congr_arg u (Fin.ext ?_)
    simp
  · exact (Fin.cast hv r).elim0

@[simp]
/--
theorem `append_elim0` / 定理 `append_elim0`

English:
theorem append_elim0
  given: (u : Fin m -> α)
  proof: append_right_nil _ _ rfl

中文:
定理 append_elim0
  条件: (u : 有限集 m -> α)
  证明: append_right_nil _ _ rfl

Depends on / 依赖: append_right_nil
-/
theorem append_elim0 (u : Fin m -> α) :
    append u Fin.elim0 = u ∘ Fin.cast (Nat.add_zero _) :=
  append_right_nil _ _ rfl

/--
theorem `append_left_nil` / 定理 `append_left_nil`

English:
theorem append_left_nil
  given: (u : Fin m -> α) (v : Fin n -> α) (hu : m = 0)
  proof: by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · exact (Fin.cast hu l).elim0
  · rw [append_right, Function.comp_apply]
    refine congr_arg v (Fin.ext ?_)
    simp [hu]

@[simp]

中文:
定理 append_left_nil
  条件: (u : 有限集 m -> α) (v : 有限集 n -> α) (hu : m = 0)
  证明: by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · exact (Fin.cast hu l).elim0
  · rw [append_right, Function.comp_apply]
    refine congr_arg v (Fin.ext ?_)
    simp [hu]

@[simp]

Depends on / 依赖: Fin.addCases, Fin.cast, Fin.ext, Function, Function.comp_apply, List.Nodup.pmap, Quot.induction_on, addCases, append_right, comp_apply, congr_arg, induction_on
-/
theorem append_left_nil (u : Fin m -> α) (v : Fin n -> α) (hu : m = 0) :
    append u v = v ∘ Fin.cast (by rw [hu, Nat.zero_add]) := by
  refine funext (Fin.addCases (fun l => ?_) fun r => ?_)
  · exact (Fin.cast hu l).elim0
  · rw [append_right, Function.comp_apply]
    refine congr_arg v (Fin.ext ?_)
    simp [hu]

@[simp]
/--
theorem `elim0_append` / 定理 `elim0_append`

English:
theorem elim0_append
  given: (v : Fin n -> α)
  proof: append_left_nil _ _ rfl

中文:
定理 elim0_append
  条件: (v : 有限集 n -> α)
  证明: append_left_nil _ _ rfl

Depends on / 依赖: append_left_nil
-/
theorem elim0_append (v : Fin n -> α) :
    append Fin.elim0 v = v ∘ Fin.cast (Nat.zero_add _) :=
  append_left_nil _ _ rfl

/--
theorem `append_assoc` / 定理 `append_assoc`

English:
theorem append_assoc
  given: {p : Nat} (a : Fin m -> α) (b : Fin n -> α) (c : Fin p -> α)
  proof: by
  ext i
  rw [Function.comp_apply]
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · rw [append_left]
    refine Fin.addCases (fun ll => ?_) (fun lr => ?_) l
    · rw [append_left]
      simp [castAdd_castAdd]
    · rw [append_right]
      simp [castAdd_natAdd]
  · rw [append_right]
    simp [← natAdd_natAdd]

中文:
定理 append_assoc
  条件: {p : 自然数} (a : 有限集 m -> α) (b : 有限集 n -> α) (c : 有限集 p -> α)
  证明: by
  ext i
  rw [Function.comp_apply]
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · rw [append_left]
    refine Fin.addCases (fun ll => ?_) (fun lr => ?_) l
    · rw [append_left]
      simp [castAdd_castAdd]
    · rw [append_right]
      simp [castAdd_natAdd]
  · rw [append_right]
    simp [← natAdd_natAdd]

Depends on / 依赖: Fin.addCases, Function, Function.comp_apply, addCases, append_left, append_right, castAdd_castAdd, castAdd_natAdd, comp_apply, natAdd_natAdd
-/
theorem append_assoc {p : Nat} (a : Fin m -> α) (b : Fin n -> α) (c : Fin p -> α) :
    append (append a b) c = append a (append b c) ∘ Fin.cast (Nat.add_assoc ..) := by
  ext i
  rw [Function.comp_apply]
  refine Fin.addCases (fun l => ?_) (fun r => ?_) i
  · rw [append_left]
    refine Fin.addCases (fun ll => ?_) (fun lr => ?_) l
    · rw [append_left]
      simp [castAdd_castAdd]
    · rw [append_right]
      simp [castAdd_natAdd]
  · rw [append_right]
    simp [← natAdd_natAdd]

/--
theorem `append_left_eq_cons` / 定理 `append_left_eq_cons`

English:
theorem append_left_eq_cons
  given: {n : Nat} (x₀ : Fin 1 -> α) (x : Fin n -> α)
  proof: by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Subsingleton.elim i 0]; rw [Fin.append_left]; rw [Function.comp_apply]; rw [eq_comm]
    exact Fin.cons_zero _ _
  · intro i
    rw [Fin.append_right]; rw [Function.comp_apply]; rw [Fin.cast_natAdd]; rw [eq_comm]; rw [Fin.addNat_one]
    exact Fin.cons_succ _ _ _

中文:
定理 append_left_eq_cons
  条件: {n : 自然数} (x₀ : 有限集 1 -> α) (x : 有限集 n -> α)
  证明: by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Subsingleton.elim i 0]; rw [Fin.append_left]; rw [Function.comp_apply]; rw [eq_comm]
    exact Fin.cons_zero _ _
  · intro i
    rw [Fin.append_right]; rw [Function.comp_apply]; rw [Fin.cast_natAdd]; rw [eq_comm]; rw [Fin.addNat_one]
    exact Fin.cons_succ _ _ _

Depends on / 依赖: Fin.addCases, Fin.addNat_one, Fin.append_left, Fin.append_right, Fin.cast_natAdd, Fin.cons_succ, Fin.cons_zero, Function, Function.comp_apply, Subsingleton, Subsingleton.elim, addCases, addNat_one, append_left, append_right, cast_natAdd, comp_apply, cons_succ, cons_zero, eq_comm
-/
theorem append_left_eq_cons {n : Nat} (x₀ : Fin 1 -> α) (x : Fin n -> α) :
    Fin.append x₀ x = Fin.cons (x₀ 0) x ∘ Fin.cast (Nat.add_comm ..) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Subsingleton.elim i 0]; rw [Fin.append_left]; rw [Function.comp_apply]; rw [eq_comm]
    exact Fin.cons_zero _ _
  · intro i
    rw [Fin.append_right]; rw [Function.comp_apply]; rw [Fin.cast_natAdd]; rw [eq_comm]; rw [Fin.addNat_one]
    exact Fin.cons_succ _ _ _

/--
theorem `cons_eq_append` / 定理 `cons_eq_append`

English:
theorem cons_eq_append
  given: (x : α) (xs : Fin n -> α)
  proof: by
  funext i; simp [append_left_eq_cons]

中文:
定理 cons_eq_append
  条件: (x : α) (xs : 有限集 n -> α)
  证明: by
  funext i; simp [append_left_eq_cons]

Depends on / 依赖: append_left_eq_cons
-/
theorem cons_eq_append (x : α) (xs : Fin n -> α) :
    cons x xs = append (cons x Fin.elim0) xs ∘ Fin.cast (Nat.add_comm ..) := by
  funext i; simp [append_left_eq_cons]

/--
lemma `append_cast_left` / 引理 `append_cast_left`

English:
lemma append_cast_left
  statement: {n m} (xs : Fin n -> α) (ys : Fin m -> α) (n' : Nat)
  proof: by
  subst h; simp

中文:
引理 append_cast_left
  结论: {n m} (xs : 有限集 n -> α) (ys : 有限集 m -> α) (n' : 自然数)
  证明: by
  subst h; simp
-/
@[simp] lemma append_cast_left {n m} (xs : Fin n -> α) (ys : Fin m -> α) (n' : Nat)
    (h : n' = n) :
    Fin.append (xs ∘ Fin.cast h) ys = Fin.append xs ys ∘ (Fin.cast <| by rw [h]) := by
  subst h; simp

/--
lemma `append_cast_right` / 引理 `append_cast_right`

English:
lemma append_cast_right
  statement: {n m} (xs : Fin n -> α) (ys : Fin m -> α) (m' : Nat)
  proof: by
  subst h; simp

中文:
引理 append_cast_right
  结论: {n m} (xs : 有限集 n -> α) (ys : 有限集 m -> α) (m' : 自然数)
  证明: by
  subst h; simp
-/
@[simp] lemma append_cast_right {n m} (xs : Fin n -> α) (ys : Fin m -> α) (m' : Nat)
    (h : m' = m) :
    Fin.append xs (ys ∘ Fin.cast h) = Fin.append xs ys ∘ (Fin.cast <| by rw [h]) := by
  subst h; simp

/--
lemma `append_rev` / 引理 `append_rev`

English:
lemma append_rev
  given: {m n} (xs : Fin m -> α) (ys : Fin n -> α) (i : Fin (m + n))
  proof: by
  rcases rev_surjective i with ⟨i, rfl⟩
  rw [rev_rev]
  induction i using Fin.addCases
  · simp [rev_castAdd]
  · simp [cast_rev, rev_addNat]

中文:
引理 append_rev
  条件: {m n} (xs : 有限集 m -> α) (ys : 有限集 n -> α) (i : 有限集 (m + n))
  证明: by
  rcases rev_surjective i with ⟨i, rfl⟩
  rw [rev_rev]
  induction i using Fin.addCases
  · simp [rev_castAdd]
  · simp [cast_rev, rev_addNat]

Depends on / 依赖: Fin.addCases, addCases, cast_rev, rev_addNat, rev_castAdd, rev_rev, rev_surjective
-/
lemma append_rev {m n} (xs : Fin m -> α) (ys : Fin n -> α) (i : Fin (m + n)) :
    append xs ys (rev i) = append (ys ∘ rev) (xs ∘ rev) (i.cast (Nat.add_comm ..)) := by
  rcases rev_surjective i with ⟨i, rfl⟩
  rw [rev_rev]
  induction i using Fin.addCases
  · simp [rev_castAdd]
  · simp [cast_rev, rev_addNat]

/--
lemma `append_comp_rev` / 引理 `append_comp_rev`

English:
lemma append_comp_rev
  given: {m n} (xs : Fin m -> α) (ys : Fin n -> α)
  proof: funext append_rev xs ys

中文:
引理 append_comp_rev
  条件: {m n} (xs : 有限集 m -> α) (ys : 有限集 n -> α)
  证明: funext append_rev xs ys

Depends on / 依赖: append_rev
-/
lemma append_comp_rev {m n} (xs : Fin m -> α) (ys : Fin n -> α) :
    append xs ys ∘ rev = append (ys ∘ rev) (xs ∘ rev) ∘ Fin.cast (Nat.add_comm ..) :=
funext append_rev xs ys

/--
theorem `append_castAdd_natAdd` / 定理 `append_castAdd_natAdd`

English:
theorem append_castAdd_natAdd
  given: {f : Fin (m + n) -> α}
  proof: by
  unfold append addCases
  simp

中文:
定理 append_castAdd_natAdd
  条件: {f : 有限集 (m + n) -> α}
  证明: by
  unfold append addCases
  simp

Depends on / 依赖: addCases, append
-/
theorem append_castAdd_natAdd {f : Fin (m + n) -> α} :
    append (fun i => f (castAdd n i)) (fun i => f (natAdd m i)) = f := by
  unfold append addCases
  simp

/--
theorem `addCases_castAdd_natAdd` / 定理 `addCases_castAdd_natAdd`

English:
theorem addCases_castAdd_natAdd
  given: {γ : Fin (m + n) -> Sort*} (v : forall i, γ i) (i : Fin (m + n))
  proof: by
  cases i using addCases <;> simp

中文:
定理 addCases_castAdd_natAdd
  条件: {γ : 有限集 (m + n) -> 类型层*} (v : 对任意 i, γ i) (i : 有限集 (m + n))
  证明: by
  cases i using addCases <;> simp

Depends on / 依赖: addCases
-/
theorem addCases_castAdd_natAdd {γ : Fin (m + n) -> Sort*} (v : forall i, γ i) (i : Fin (m + n)) :
    addCases (fun i => v (castAdd n i)) (fun j => v (natAdd m j)) i = v i := by
  cases i using addCases <;> simp

/--
theorem `append_comp_sumElim` / 定理 `append_comp_sumElim`

English:
theorem append_comp_sumElim
  given: {xs : Fin m -> α} {ys : Fin n -> α}
  proof: by
  ext (i | j) <;> simp

中文:
定理 append_comp_sumElim
  条件: {xs : 有限集 m -> α} {ys : 有限集 n -> α}
  证明: by
  ext (i | j) <;> simp
-/
theorem append_comp_sumElim {xs : Fin m -> α} {ys : Fin n -> α} :
    Fin.append xs ys ∘ Sum.elim (Fin.castAdd _) (Fin.natAdd _) = Sum.elim xs ys := by
  ext (i | j) <;> simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `append_injective_iff` / 定理 `append_injective_iff`

English:
theorem append_injective_iff
  given: {xs : Fin m -> α} {ys : Fin n -> α}
  proof: by
  -- TODO: move things around so we can just import this.
  -- We inline it because it's still shorter than proving from scratch.
  let finSumFinEquiv : Fin m oplus Fin n ≃ Fin (m + n) :=
  { toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
    invFun i := @Fin.addCases m n (fun _ => Fin m oplus Fin n) Sum.inl Sum.inr i
    left_inv x := by rcases x with y | y <;> simp
    right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp }
  rw [← Sum.elim_injective]; rw [← append_comp_sumElim]; rw [← finSumFinEquiv.injective_comp]; rw [Equiv.coe_fn_mk]

中文:
定理 append_injective_iff
  条件: {xs : 有限集 m -> α} {ys : 有限集 n -> α}
  证明: by
  -- TODO: move things around so we can just import this.
  -- We inline it because it's still shorter than proving from scratch.
  let finSumFinEquiv : Fin m oplus Fin n ≃ Fin (m + n) :=
  { toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
    invFun i := @Fin.addCases m n (fun _ => Fin m oplus Fin n) Sum.inl Sum.inr i
    left_inv x := by rcases x with y | y <;> simp
    right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp }
  rw [← Sum.elim_injective]; rw [← append_comp_sumElim]; rw [← finSumFinEquiv.injective_comp]; rw [Equiv.coe_fn_mk]
-/
theorem append_injective_iff {xs : Fin m -> α} {ys : Fin n -> α} :
    Function.Injective (Fin.append xs ys) ↔
      Function.Injective xs ∧ Function.Injective ys ∧ forall i j, xs i != ys j := by
  -- TODO: move things around so we can just import this.
  -- We inline it because it's still shorter than proving from scratch.
  let finSumFinEquiv : Fin m oplus Fin n ≃ Fin (m + n) :=
  { toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
    invFun i := @Fin.addCases m n (fun _ => Fin m oplus Fin n) Sum.inl Sum.inr i
    left_inv x := by rcases x with y | y <;> simp
    right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp }
  rw [← Sum.elim_injective]; rw [← append_comp_sumElim]; rw [← finSumFinEquiv.injective_comp]; rw [Equiv.coe_fn_mk]

end Append

section Repeat

variable {α : Sort*}

/--
Definition of `«repeat»` / `«repeat»` 的定义

English:
definition «repeat»
  signature: (m : Nat) (a : Fin n -> α)

中文:
定义 «repeat»
  签名: (m : 自然数) (a : 有限集 n -> α)
-/
def «repeat» (m : Nat) (a : Fin n -> α) : Fin (m * n) -> α
  | i => a i.modNat

@[simp]
/--
theorem `repeat_apply` / 定理 `repeat_apply`

English:
theorem repeat_apply
  given: (a : Fin n -> α) (i : Fin (m * n))
  proof: rfl

@[simp]

中文:
定理 repeat_apply
  条件: (a : 有限集 n -> α) (i : 有限集 (m * n))
  证明: rfl

@[simp]
-/
theorem repeat_apply (a : Fin n -> α) (i : Fin (m * n)) :
    Fin.repeat m a i = a i.modNat :=
  rfl

@[simp]
/--
theorem `repeat_zero` / 定理 `repeat_zero`

English:
theorem repeat_zero
  given: (a : Fin n -> α)
  proof: funext fun x => (x.cast (Nat.zero_mul _)).elim0

@[simp]

中文:
定理 repeat_zero
  条件: (a : 有限集 n -> α)
  证明: funext fun x => (x.cast (Nat.zero_mul _)).elim0

@[simp]

Depends on / 依赖: Nat.zero_mul, x.cast, zero_mul
-/
theorem repeat_zero (a : Fin n -> α) :
    Fin.repeat 0 a = Fin.elim0 ∘ Fin.cast (Nat.zero_mul _) :=
  funext fun x => (x.cast (Nat.zero_mul _)).elim0

@[simp]
/--
theorem `repeat_one` / 定理 `repeat_one`

English:
theorem repeat_one
  given: (a : Fin n -> α)
  statement: Fin.repeat 1 a = a ∘ Fin.cast (Nat.one_mul _)
  proof: by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  intro i
  simp [modNat, Nat.mod_eq_of_lt i.is_lt]

中文:
定理 repeat_one
  条件: (a : 有限集 n -> α)
  结论: 有限集.repeat 1 a = a ∘ 有限集.cast (自然数.one_mul _)
  证明: by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  intro i
  simp [modNat, Nat.mod_eq_of_lt i.is_lt]

Depends on / 依赖: Fin.rightInverse_cast, Nat.mod_eq_of_lt, generalize_proofs, h.symm, i.is_lt, is_lt, modNat, mod_eq_of_lt, rightInverse_cast, surjective, surjective.forall
-/
theorem repeat_one (a : Fin n -> α) : Fin.repeat 1 a = a ∘ Fin.cast (Nat.one_mul _) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  intro i
  simp [modNat, Nat.mod_eq_of_lt i.is_lt]

/--
theorem `repeat_succ` / 定理 `repeat_succ`

English:
theorem repeat_succ
  given: (a : Fin n -> α) (m : Nat)
  proof: by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat, Nat.mod_eq_of_lt l.is_lt]
  · simp [modNat]

@[simp]

中文:
定理 repeat_succ
  条件: (a : 有限集 n -> α) (m : 自然数)
  证明: by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat, Nat.mod_eq_of_lt l.is_lt]
  · simp [modNat]

@[simp]

Depends on / 依赖: Fin.addCases, Fin.rightInverse_cast, Nat.mod_eq_of_lt, addCases, generalize_proofs, h.symm, is_lt, l.is_lt, modNat, mod_eq_of_lt, rightInverse_cast, surjective, surjective.forall
-/
theorem repeat_succ (a : Fin n -> α) (m : Nat) :
    Fin.repeat m.succ a =
      append a (Fin.repeat m a) ∘ Fin.cast ((Nat.succ_mul _ _).trans (Nat.add_comm ..)) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat, Nat.mod_eq_of_lt l.is_lt]
  · simp [modNat]

@[simp]
/--
theorem `repeat_add` / 定理 `repeat_add`

English:
theorem repeat_add
  given: (a : Fin n -> α) (m₁ m₂ : Nat)
  statement: Fin.repeat (m₁ + m₂) a =
  proof: by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat]
  · simp [modNat, Nat.add_mod]

中文:
定理 repeat_add
  条件: (a : 有限集 n -> α) (m₁ m₂ : 自然数)
  结论: 有限集.repeat (m₁ + m₂) a =
  证明: by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat]
  · simp [modNat, Nat.add_mod]

Depends on / 依赖: Fin.addCases, Fin.rightInverse_cast, Nat.add_mod, addCases, add_mod, generalize_proofs, h.symm, modNat, rightInverse_cast, surjective, surjective.forall
-/
theorem repeat_add (a : Fin n -> α) (m₁ m₂ : Nat) : Fin.repeat (m₁ + m₂) a =
    append (Fin.repeat m₁ a) (Fin.repeat m₂ a) ∘ Fin.cast (Nat.add_mul ..) := by
  generalize_proofs h
  apply funext
  rw [(Fin.rightInverse_cast h.symm).surjective.forall]
  refine Fin.addCases (fun l => ?_) fun r => ?_
  · simp [modNat]
  · simp [modNat, Nat.add_mod]

/--
theorem `repeat_rev` / 定理 `repeat_rev`

English:
theorem repeat_rev
  given: (a : Fin n -> α) (k : Fin (m * n))
  proof: congr_arg a k.modNat_rev

中文:
定理 repeat_rev
  条件: (a : 有限集 n -> α) (k : 有限集 (m * n))
  证明: congr_arg a k.modNat_rev

Depends on / 依赖: congr_arg, k.modNat_rev, modNat_rev
-/
theorem repeat_rev (a : Fin n -> α) (k : Fin (m * n)) :
    Fin.repeat m a k.rev = Fin.repeat m (a ∘ Fin.rev) k :=
  congr_arg a k.modNat_rev

/--
theorem `repeat_comp_rev` / 定理 `repeat_comp_rev`

English:
theorem repeat_comp_rev
  given: (a : Fin n -> α)
  proof: funext repeat_rev a

中文:
定理 repeat_comp_rev
  条件: (a : 有限集 n -> α)
  证明: funext repeat_rev a

Depends on / 依赖: repeat_rev
-/
theorem repeat_comp_rev (a : Fin n -> α) :
    Fin.repeat m a ∘ Fin.rev = Fin.repeat m (a ∘ Fin.rev) :=
funext repeat_rev a

end Repeat

end Tuple

section TupleRight

/-! In the previous section, we have discussed inserting or removing elements on the left of a
tuple. In this section, we do the same on the right. A difference is that `Fin (n+1)` is constructed
inductively from `Fin n` starting from the left, not from the right. This implies that Lean needs
more help to realize that elements belong to the right types, i.e., we need to insert casts at
several places. -/

variable {α : Fin (n + 1) -> Sort*} (x : α (last n)) (q : forall i, α i)
  (p : forall i : Fin n, α i.castSucc) (i : Fin n) (y : α i.castSucc) (z : α (last n))

/--
Definition of `init` / `init` 的定义

English:
definition init
  signature: (q : forall i, α i) (i : Fin n)
  body: q i.castSucc

中文:
定义 init
  签名: (q : 对任意 i, α i) (i : 有限集 n)
  定义体: q i.castSucc

Depends on / 依赖: castSucc, i.castSucc
-/
def init (q : forall i, α i) (i : Fin n) : α i.castSucc :=
  q i.castSucc

/--
theorem `init_def` / 定理 `init_def`

English:
theorem init_def
  given: {q : forall i, α i}
  proof: rfl

中文:
定理 init_def
  条件: {q : 对任意 i, α i}
  证明: rfl
-/
theorem init_def {q : forall i, α i} :
    (init fun k : Fin (n + 1) => q k) = fun k : Fin n => q k.castSucc :=
  rfl

/--
Definition of `snoc` / `snoc` 的定义

English:
definition snoc
  signature: (p : forall i : Fin n, α i.castSucc) (x : α (last n)) (i : Fin (n + 1))
  body: if h : i.val < n then _root_.cast (by rw [Fin.castSucc_castLT i h]) (p (castLT i h))
  else _root_.cast (by rw [eq_last_of_not_lt h]) x

@[simp]

中文:
定义 snoc
  签名: (p : 对任意 i : 有限集 n, α i.castSucc) (x : α (last n)) (i : 有限集 (n + 1))
  定义体: if h : i.val < n then _root_.cast (by rw [Fin.castSucc_castLT i h]) (p (castLT i h))
  else _root_.cast (by rw [eq_last_of_not_lt h]) x

@[simp]

Depends on / 依赖: Fin.castSucc_castLT, _root_, _root_.cast, castLT, castSucc_castLT, eq_last_of_not_lt, i.val
-/
def snoc (p : forall i : Fin n, α i.castSucc) (x : α (last n)) (i : Fin (n + 1)) : α i :=
  if h : i.val < n then _root_.cast (by rw [Fin.castSucc_castLT i h]) (p (castLT i h))
  else _root_.cast (by rw [eq_last_of_not_lt h]) x

@[simp]
/--
theorem `init_snoc` / 定理 `init_snoc`

English:
theorem init_snoc
  statement: init (snoc p x) = p
  proof: by
  ext i
  simp only [init, snoc, val_castSucc, is_lt, dite_true]
  convert! cast_eq rfl (p i)

@[simp]

中文:
定理 init_snoc
  结论: init (snoc p x) = p
  证明: by
  ext i
  simp only [init, snoc, val_castSucc, is_lt, dite_true]
  convert! cast_eq rfl (p i)

@[simp]

Depends on / 依赖: cast_eq, convert, dite_true, is_lt, val_castSucc
-/
theorem init_snoc : init (snoc p x) = p := by
  ext i
  simp only [init, snoc, val_castSucc, is_lt, dite_true]
  convert! cast_eq rfl (p i)

@[simp]
/--
theorem `snoc_castSucc` / 定理 `snoc_castSucc`

English:
theorem snoc_castSucc
  statement: snoc p x i.castSucc = p i
  proof: by
  simp only [snoc, val_castSucc, is_lt, dite_true]
  convert! cast_eq rfl (p i)

@[simp]

中文:
定理 snoc_castSucc
  结论: snoc p x i.castSucc = p i
  证明: by
  simp only [snoc, val_castSucc, is_lt, dite_true]
  convert! cast_eq rfl (p i)

@[simp]

Depends on / 依赖: cast_eq, convert, dite_true, is_lt, val_castSucc
-/
theorem snoc_castSucc : snoc p x i.castSucc = p i := by
  simp only [snoc, val_castSucc, is_lt, dite_true]
  convert! cast_eq rfl (p i)

@[simp]
/--
theorem `snoc_apply_zero` / 定理 `snoc_apply_zero`

English:
theorem snoc_apply_zero
  given: [NeZero n]
  statement: snoc p x 0 = p 0
  proof: snoc_castSucc x p 0

@[simp]

中文:
定理 snoc_apply_zero
  条件: [NeZero n]
  结论: snoc p x 0 = p 0
  证明: snoc_castSucc x p 0

@[simp]

Depends on / 依赖: snoc_castSucc
-/
theorem snoc_apply_zero [NeZero n] : snoc p x 0 = p 0 := snoc_castSucc x p 0

@[simp]
/--
theorem `snoc_comp_castSucc` / 定理 `snoc_comp_castSucc`

English:
theorem snoc_comp_castSucc
  given: {α : Sort*} {a : α} {f : Fin n -> α}
  proof: funext fun i => by rw [Function.comp_apply, snoc_castSucc]

@[simp]

中文:
定理 snoc_comp_castSucc
  条件: {α : 类型层*} {a : α} {f : 有限集 n -> α}
  证明: funext fun i => by rw [Function.comp_apply, snoc_castSucc]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, snoc_castSucc
-/
theorem snoc_comp_castSucc {α : Sort*} {a : α} {f : Fin n -> α} :
    (snoc f a : Fin (n + 1) -> α) ∘ castSucc = f :=
  funext fun i => by rw [Function.comp_apply, snoc_castSucc]

@[simp]
/--
theorem `snoc_last` / 定理 `snoc_last`

English:
theorem snoc_last
  statement: snoc p x (last n) = x
  proof: by simp [snoc]

中文:
定理 snoc_last
  结论: snoc p x (last n) = x
  证明: by simp [snoc]
-/
theorem snoc_last : snoc p x (last n) = x := by simp [snoc]

/--
lemma `snoc_zero` / 引理 `snoc_zero`

English:
lemma snoc_zero
  given: {α : Sort*} (p : Fin 0 -> α) (x : α)
  proof: rfl

@[simp]

中文:
引理 snoc_zero
  条件: {α : 类型层*} (p : 有限集 0 -> α) (x : α)
  证明: rfl

@[simp]
-/
lemma snoc_zero {α : Sort*} (p : Fin 0 -> α) (x : α) :
    Fin.snoc p x = fun _ => x := rfl

@[simp]
/--
theorem `snoc_comp_natAdd` / 定理 `snoc_comp_natAdd`

English:
theorem snoc_comp_natAdd
  given: {n m : Nat} {α : Sort*} (f : Fin (m + n) -> α) (a : α)
  proof: by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Function.comp_apply]
    rw [snoc_last]; rw [natAdd_last]; rw [snoc_last]
  · simp only [comp_apply, snoc_castSucc]
    rw [natAdd_castSucc]; rw [snoc_castSucc]

@[simp]

中文:
定理 snoc_comp_natAdd
  条件: {n m : 自然数} {α : 类型层*} (f : 有限集 (m + n) -> α) (a : α)
  证明: by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Function.comp_apply]
    rw [snoc_last]; rw [natAdd_last]; rw [snoc_last]
  · simp only [comp_apply, snoc_castSucc]
    rw [natAdd_castSucc]; rw [snoc_castSucc]

@[simp]

Depends on / 依赖: Fin.lastCases, Function, Function.comp_apply, comp_apply, lastCases, natAdd_castSucc, natAdd_last, snoc_castSucc, snoc_last
-/
theorem snoc_comp_natAdd {n m : Nat} {α : Sort*} (f : Fin (m + n) -> α) (a : α) :
    (snoc f a : Fin _ -> α) ∘ (natAdd m : Fin (n + 1) -> Fin (m + n + 1)) =
      snoc (f ∘ natAdd m) a := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Function.comp_apply]
    rw [snoc_last]; rw [natAdd_last]; rw [snoc_last]
  · simp only [comp_apply, snoc_castSucc]
    rw [natAdd_castSucc]; rw [snoc_castSucc]

@[simp]
/--
theorem `snoc_castAdd` / 定理 `snoc_castAdd`

English:
theorem snoc_castAdd
  statement: {α : Fin (n + m + 1) -> Sort*} (f : forall i : Fin (n + m), α i.castSucc)
  proof: dif_pos _

@[simp]

中文:
定理 snoc_castAdd
  结论: {α : 有限集 (n + m + 1) -> 类型层*} (f : 对任意 i : 有限集 (n + m), α i.castSucc)
  证明: dif_pos _

@[simp]

Depends on / 依赖: dif_pos
-/
theorem snoc_castAdd {α : Fin (n + m + 1) -> Sort*} (f : forall i : Fin (n + m), α i.castSucc)
    (a : α (last (n + m))) (i : Fin n) : (snoc f a) (castAdd (m + 1) i) = f (castAdd m i) :=
  dif_pos _

@[simp]
/--
theorem `snoc_comp_castAdd` / 定理 `snoc_comp_castAdd`

English:
theorem snoc_comp_castAdd
  given: {n m : Nat} {α : Sort*} (f : Fin (n + m) -> α) (a : α)
  proof: funext (snoc_castAdd _ _)

中文:
定理 snoc_comp_castAdd
  条件: {n m : 自然数} {α : 类型层*} (f : 有限集 (n + m) -> α) (a : α)
  证明: funext (snoc_castAdd _ _)

Depends on / 依赖: snoc_castAdd
-/
theorem snoc_comp_castAdd {n m : Nat} {α : Sort*} (f : Fin (n + m) -> α) (a : α) :
    (snoc f a : Fin _ -> α) ∘ castAdd (m + 1) = f ∘ castAdd m :=
  funext (snoc_castAdd _ _)

/-- Updating a tuple and adding an element at the end commute. -/
@[simp]
/--
theorem `snoc_update` / 定理 `snoc_update`

English:
theorem snoc_update
  statement: snoc (update p i y) x = update (snoc p x) i.castSucc y
  proof: by
  ext j
  cases j using lastCases with
  | cast j => rcases eq_or_ne j i with rfl | hne <;> simp [*]
  | last => simp [Ne.symm]

中文:
定理 snoc_update
  结论: snoc (update p i y) x = update (snoc p x) i.castSucc y
  证明: by
  ext j
  cases j using lastCases with
  | cast j => rcases eq_or_ne j i with rfl | hne <;> simp [*]
  | last => simp [Ne.symm]

Depends on / 依赖: Ne.symm, eq_or_ne, lastCases
-/
theorem snoc_update : snoc (update p i y) x = update (snoc p x) i.castSucc y := by
  ext j
  cases j using lastCases with
  | cast j => rcases eq_or_ne j i with rfl | hne <;> simp [*]
  | last => simp [Ne.symm]

/--
theorem `update_snoc_last` / 定理 `update_snoc_last`

English:
theorem update_snoc_last
  statement: update (snoc p x) (last n) z = snoc p z
  proof: by
  ext j
  cases j using lastCases <;> simp

@[simp]

中文:
定理 update_snoc_last
  结论: update (snoc p x) (last n) z = snoc p z
  证明: by
  ext j
  cases j using lastCases <;> simp

@[simp]

Depends on / 依赖: lastCases
-/
theorem update_snoc_last : update (snoc p x) (last n) z = snoc p z := by
  ext j
  cases j using lastCases <;> simp

@[simp]
/--
lemma `range_snoc` / 引理 `range_snoc`

English:
lemma range_snoc
  given: {α : Type*} (f : Fin n -> α) (x : α)
  proof: by
  ext; simp [Fin.exists_fin_succ', or_comm, eq_comm]

中文:
引理 range_snoc
  条件: {α : 类型} (f : 有限集 n -> α) (x : α)
  证明: by
  ext; simp [Fin.exists_fin_succ', or_comm, eq_comm]

Depends on / 依赖: Fin.exists_fin_succ, eq_comm, exists_fin_succ, or_comm, powersetAux
-/
lemma range_snoc {α : Type*} (f : Fin n -> α) (x : α) :
    Set.range (snoc f x) = insert x (Set.range f) := by
  ext; simp [Fin.exists_fin_succ', or_comm, eq_comm]

/--
theorem `snoc_injective2` / 定理 `snoc_injective2`

English:
theorem snoc_injective2
  statement: Function.Injective2 (@snoc n α)
  proof: fun x y xₙ yₙ h =>
  ⟨funext fun i => by simpa using congr_fun h (castSucc i), by simpa using congr_fun h (last n)⟩

@[simp]

中文:
定理 snoc_injective2
  结论: 函数.Injective2 (@snoc n α)
  证明: fun x y xₙ yₙ h =>
  ⟨funext fun i => by simpa using congr_fun h (castSucc i), by simpa using congr_fun h (last n)⟩

@[simp]
-/
theorem snoc_injective2 : Function.Injective2 (@snoc n α) := fun x y xₙ yₙ h =>
  ⟨funext fun i => by simpa using congr_fun h (castSucc i), by simpa using congr_fun h (last n)⟩

@[simp]
/--
theorem `snoc_inj` / 定理 `snoc_inj`

English:
theorem snoc_inj
  given: {x y : forall i : Fin n, α i.castSucc} {xₙ yₙ : α (last n)}
  proof: snoc_injective2.eq_iff

中文:
定理 snoc_inj
  条件: {x y : 对任意 i : 有限集 n, α i.castSucc} {xₙ yₙ : α (last n)}
  证明: snoc_injective2.eq_iff

Depends on / 依赖: eq_iff, snoc_injective2, snoc_injective2.eq_iff
-/
theorem snoc_inj {x y : forall i : Fin n, α i.castSucc} {xₙ yₙ : α (last n)} :
    snoc x xₙ = snoc y yₙ ↔ x = y ∧ xₙ = yₙ :=
  snoc_injective2.eq_iff

/--
theorem `snoc_right_injective` / 定理 `snoc_right_injective`

English:
theorem snoc_right_injective
  given: (x : forall i : Fin n, α i.castSucc)
  proof: snoc_injective2.right _

中文:
定理 snoc_right_injective
  条件: (x : 对任意 i : 有限集 n, α i.castSucc)
  证明: snoc_injective2.right _

Depends on / 依赖: snoc_injective2, snoc_injective2.right
-/
theorem snoc_right_injective (x : forall i : Fin n, α i.castSucc) :
    Function.Injective (snoc x) :=
  snoc_injective2.right _

/--
theorem `snoc_left_injective` / 定理 `snoc_left_injective`

English:
theorem snoc_left_injective
  given: (xₙ : α (last n))
  statement: Function.Injective (snoc · xₙ)
  proof: snoc_injective2.left _

中文:
定理 snoc_left_injective
  条件: (xₙ : α (last n))
  结论: 函数.单射 (snoc · xₙ)
  证明: snoc_injective2.left _

Depends on / 依赖: snoc_injective2, snoc_injective2.left
-/
theorem snoc_left_injective (xₙ : α (last n)) : Function.Injective (snoc · xₙ) :=
  snoc_injective2.left _

/-- Concatenating the first element of a tuple with its tail gives back the original tuple -/
@[simp]
/--
theorem `snoc_init_self` / 定理 `snoc_init_self`

English:
theorem snoc_init_self
  statement: snoc (init q) (q (last n)) = q
  proof: by
  ext j
  cases j using Fin.lastCases <;> simp [init]

中文:
定理 snoc_init_self
  结论: snoc (init q) (q (last n)) = q
  证明: by
  ext j
  cases j using Fin.lastCases <;> simp [init]

Depends on / 依赖: Fin.lastCases, lastCases
-/
theorem snoc_init_self : snoc (init q) (q (last n)) = q := by
  ext j
  cases j using Fin.lastCases <;> simp [init]

/-- Updating the last element of a tuple does not change the beginning. -/
@[simp]
/--
theorem `init_update_last` / 定理 `init_update_last`

English:
theorem init_update_last
  statement: init (update q (last n) z) = init q
  proof: by
  ext j
  simp [init, Fin.ne_of_lt]

中文:
定理 init_update_last
  结论: init (update q (last n) z) = init q
  证明: by
  ext j
  simp [init, Fin.ne_of_lt]

Depends on / 依赖: Fin.ne_of_lt, ne_of_lt
-/
theorem init_update_last : init (update q (last n) z) = init q := by
  ext j
  simp [init, Fin.ne_of_lt]

/-- Updating an element and taking the beginning commute. -/
@[simp]
/--
theorem `init_update_castSucc` / 定理 `init_update_castSucc`

English:
theorem init_update_castSucc
  statement: init (update q i.castSucc y) = update (init q) i y
  proof: by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [init]
  · simp [init, h, castSucc_inj]

中文:
定理 init_update_castSucc
  结论: init (update q i.castSucc y) = update (init q) i y
  证明: by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [init]
  · simp [init, h, castSucc_inj]

Depends on / 依赖: castSucc_inj
-/
theorem init_update_castSucc : init (update q i.castSucc y) = update (init q) i y := by
  ext j
  by_cases h : j = i
  · rw [h]
    simp [init]
  · simp [init, h, castSucc_inj]

/--
theorem `tail_init_eq_init_tail` / 定理 `tail_init_eq_init_tail`

English:
theorem tail_init_eq_init_tail
  given: {β : Sort*} (q : Fin (n + 2) -> β)
  proof: by
  ext i
  simp [tail, init]

中文:
定理 tail_init_eq_init_tail
  条件: {β : 类型层*} (q : 有限集 (n + 2) -> β)
  证明: by
  ext i
  simp [tail, init]
-/
theorem tail_init_eq_init_tail {β : Sort*} (q : Fin (n + 2) -> β) :
    tail (init q) = init (tail q) := by
  ext i
  simp [tail, init]

/--
theorem `cons_snoc_eq_snoc_cons` / 定理 `cons_snoc_eq_snoc_cons`

English:
theorem cons_snoc_eq_snoc_cons
  given: {β : Sort*} (a : β) (q : Fin n -> β) (b : β)
  proof: by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
    cases j using Fin.lastCases with
    | last => simp
    | cast j =>
      rw [cons_succ]
      simp [← castSucc_succ]

中文:
定理 cons_snoc_eq_snoc_cons
  条件: {β : 类型层*} (a : β) (q : 有限集 n -> β) (b : β)
  证明: by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
    cases j using Fin.lastCases with
    | last => simp
    | cast j =>
      rw [cons_succ]
      simp [← castSucc_succ]

Depends on / 依赖: Fin.cases, Fin.lastCases, castSucc_succ, cons_succ, lastCases
-/
theorem cons_snoc_eq_snoc_cons {β : Sort*} (a : β) (q : Fin n -> β) (b : β) :
    @cons n.succ (fun _ => β) a (snoc q b) = snoc (cons a q) b := by
  ext i
  cases i using Fin.cases with
  | zero => simp
  | succ j =>
    cases j using Fin.lastCases with
    | last => simp
    | cast j =>
      rw [cons_succ]
      simp [← castSucc_succ]

/--
theorem `comp_snoc` / 定理 `comp_snoc`

English:
theorem comp_snoc
  given: {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n -> α) (y : α)
  proof: by
  ext j
  by_cases h : j.val < n
  · simp [h, snoc, castSucc_castLT]
  · rw [eq_last_of_not_lt h]
    simp

中文:
定理 comp_snoc
  条件: {α : 类型层*} {β : 类型层*} (g : α -> β) (q : 有限集 n -> α) (y : α)
  证明: by
  ext j
  by_cases h : j.val < n
  · simp [h, snoc, castSucc_castLT]
  · rw [eq_last_of_not_lt h]
    simp

Depends on / 依赖: castSucc_castLT, eq_last_of_not_lt, j.val
-/
theorem comp_snoc {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n -> α) (y : α) :
    g ∘ snoc q y = snoc (g ∘ q) (g y) := by
  ext j
  by_cases h : j.val < n
  · simp [h, snoc, castSucc_castLT]
  · rw [eq_last_of_not_lt h]
    simp

/--
theorem `append_right_eq_snoc` / 定理 `append_right_eq_snoc`

English:
theorem append_right_eq_snoc
  given: {α : Sort*} {n : Nat} (x : Fin n -> α) (x₀ : Fin 1 -> α)
  proof: by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Fin.append_left]
    exact (@snoc_castSucc _ (fun _ => α) _ _ i).symm
  · intro i
    rw [Subsingleton.elim i 0]; rw [Fin.append_right]
    exact (@snoc_last _ (fun _ => α) _ _).symm

中文:
定理 append_right_eq_snoc
  条件: {α : 类型层*} {n : 自然数} (x : 有限集 n -> α) (x₀ : 有限集 1 -> α)
  证明: by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Fin.append_left]
    exact (@snoc_castSucc _ (fun _ => α) _ _ i).symm
  · intro i
    rw [Subsingleton.elim i 0]; rw [Fin.append_right]
    exact (@snoc_last _ (fun _ => α) _ _).symm

Depends on / 依赖: Fin.addCases, Fin.append_left, Fin.append_right, Subsingleton, Subsingleton.elim, addCases, append_left, append_right, snoc_castSucc, snoc_last
-/
theorem append_right_eq_snoc {α : Sort*} {n : Nat} (x : Fin n -> α) (x₀ : Fin 1 -> α) :
    Fin.append x x₀ = Fin.snoc x (x₀ 0) := by
  ext i
  refine Fin.addCases ?_ ?_ i <;> clear i
  · intro i
    rw [Fin.append_left]
    exact (@snoc_castSucc _ (fun _ => α) _ _ i).symm
  · intro i
    rw [Subsingleton.elim i 0]; rw [Fin.append_right]
    exact (@snoc_last _ (fun _ => α) _ _).symm

/--
theorem `snoc_eq_append` / 定理 `snoc_eq_append`

English:
theorem snoc_eq_append
  given: {α : Sort*} (xs : Fin n -> α) (x : α)
  proof: (append_right_eq_snoc xs (cons x Fin.elim0)).symm

中文:
定理 snoc_eq_append
  条件: {α : 类型层*} (xs : 有限集 n -> α) (x : α)
  证明: (append_right_eq_snoc xs (cons x Fin.elim0)).symm

Depends on / 依赖: Fin.elim0, append_right_eq_snoc
-/
theorem snoc_eq_append {α : Sort*} (xs : Fin n -> α) (x : α) :
    snoc xs x = append xs (cons x Fin.elim0) :=
  (append_right_eq_snoc xs (cons x Fin.elim0)).symm

/--
theorem `append_left_snoc` / 定理 `append_left_snoc`

English:
theorem append_left_snoc
  given: {n m} {α : Sort*} (xs : Fin n -> α) (x : α) (ys : Fin m -> α)
  proof: by
  rw [snoc_eq_append]; rw [append_assoc]; rw [append_left_eq_cons]; rw [append_cast_right]; rfl

中文:
定理 append_left_snoc
  条件: {n m} {α : 类型层*} (xs : 有限集 n -> α) (x : α) (ys : 有限集 m -> α)
  证明: by
  rw [snoc_eq_append]; rw [append_assoc]; rw [append_left_eq_cons]; rw [append_cast_right]; rfl

Depends on / 依赖: append_assoc, append_cast_right, append_left_eq_cons, snoc_eq_append
-/
theorem append_left_snoc {n m} {α : Sort*} (xs : Fin n -> α) (x : α) (ys : Fin m -> α) :
    Fin.append (Fin.snoc xs x) ys =
      Fin.append xs (Fin.cons x ys) ∘ Fin.cast (Nat.succ_add_eq_add_succ ..) := by
  rw [snoc_eq_append]; rw [append_assoc]; rw [append_left_eq_cons]; rw [append_cast_right]; rfl

/--
theorem `append_right_cons` / 定理 `append_right_cons`

English:
theorem append_right_cons
  given: {n m} {α : Sort*} (xs : Fin n -> α) (y : α) (ys : Fin m -> α)
  proof: by
  rw [append_left_snoc]; rfl

中文:
定理 append_right_cons
  条件: {n m} {α : 类型层*} (xs : 有限集 n -> α) (y : α) (ys : 有限集 m -> α)
  证明: by
  rw [append_left_snoc]; rfl

Depends on / 依赖: append_left_snoc
-/
theorem append_right_cons {n m} {α : Sort*} (xs : Fin n -> α) (y : α) (ys : Fin m -> α) :
    Fin.append xs (Fin.cons y ys) =
      Fin.append (Fin.snoc xs y) ys ∘ Fin.cast (Nat.succ_add_eq_add_succ ..).symm := by
  rw [append_left_snoc]; rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `append_cons` / 定理 `append_cons`

English:
theorem append_cons
  given: {α : Sort*} (a : α) (as : Fin n -> α) (bs : Fin m -> α)
  proof: by
  funext i
  rcases i with ⟨i, -⟩
  simp only [append, addCases, cons, castLT, comp_apply]
  rcases i with - | i
  · simp
  · split_ifs with h
    · have : i < n := Nat.lt_of_succ_lt_succ h
      simp [addCases, this]
· have : ¬i < n := Nat.not_le_of_gt Nat.le_of_lt_succ Nat.gt_of_not_le h
      simp [addCases, this]

中文:
定理 append_cons
  条件: {α : 类型层*} (a : α) (as : 有限集 n -> α) (bs : 有限集 m -> α)
  证明: by
  funext i
  rcases i with ⟨i, -⟩
  simp only [append, addCases, cons, castLT, comp_apply]
  rcases i with - | i
  · simp
  · split_ifs with h
    · have : i < n := Nat.lt_of_succ_lt_succ h
      simp [addCases, this]
· have : ¬i < n := Nat.not_le_of_gt Nat.le_of_lt_succ Nat.gt_of_not_le h
      simp [addCases, this]

Depends on / 依赖: Nat.gt_of_not_le, Nat.le_of_lt_succ, Nat.lt_of_succ_lt_succ, Nat.not_le_of_gt, addCases, append, castLT, comp_apply, gt_of_not_le, le_of_lt_succ, lt_of_succ_lt_succ, not_le_of_gt, split_ifs
-/
theorem append_cons {α : Sort*} (a : α) (as : Fin n -> α) (bs : Fin m -> α) :
    Fin.append (cons a as) bs
    = cons a (Fin.append as bs) ∘ (Fin.cast <| Nat.add_right_comm n 1 m) := by
  funext i
  rcases i with ⟨i, -⟩
  simp only [append, addCases, cons, castLT, comp_apply]
  rcases i with - | i
  · simp
  · split_ifs with h
    · have : i < n := Nat.lt_of_succ_lt_succ h
      simp [addCases, this]
· have : ¬i < n := Nat.not_le_of_gt Nat.le_of_lt_succ Nat.gt_of_not_le h
      simp [addCases, this]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `append_snoc` / 定理 `append_snoc`

English:
theorem append_snoc
  given: {α : Sort*} (as : Fin n -> α) (bs : Fin m -> α) (b : α)
  proof: by
  funext i
  rcases i with ⟨i, isLt⟩
  simp only [append, addCases, castLT, cast_mk, subNat_mk, natAdd_mk, cast, snoc.eq_1,
    eq_rec_constant, Nat.add_eq]
  split_ifs with lt_n lt_add sub_lt nlt_add lt_add <;> (try rfl)
  · have := Nat.lt_add_right m lt_n
    contradiction
  · obtain rfl := Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp nlt_add) isLt
    simp [Nat.add_comm n m] at sub_lt
  · have := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp lt_n) lt_add
    contradiction

中文:
定理 append_snoc
  条件: {α : 类型层*} (as : 有限集 n -> α) (bs : 有限集 m -> α) (b : α)
  证明: by
  funext i
  rcases i with ⟨i, isLt⟩
  simp only [append, addCases, castLT, cast_mk, subNat_mk, natAdd_mk, cast, snoc.eq_1,
    eq_rec_constant, Nat.add_eq]
  split_ifs with lt_n lt_add sub_lt nlt_add lt_add <;> (try rfl)
  · have := Nat.lt_add_right m lt_n
    contradiction
  · obtain rfl := Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp nlt_add) isLt
    simp [Nat.add_comm n m] at sub_lt
  · have := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp lt_n) lt_add
    contradiction

Depends on / 依赖: Nat.add_comm, Nat.add_eq, Nat.eq_of_le_of_lt_succ, Nat.lt_add_right, Nat.not_lt.mp, Nat.sub_lt_left_of_lt_add, addCases, add_comm, add_eq, append, castLT, cast_mk, eq_1, eq_of_le_of_lt_succ, eq_rec_constant, lt_add, lt_add_right, lt_n, natAdd_mk, nlt_add
-/
theorem append_snoc {α : Sort*} (as : Fin n -> α) (bs : Fin m -> α) (b : α) :
    Fin.append as (snoc bs b) = snoc (Fin.append as bs) b := by
  funext i
  rcases i with ⟨i, isLt⟩
  simp only [append, addCases, castLT, cast_mk, subNat_mk, natAdd_mk, cast, snoc.eq_1,
    eq_rec_constant, Nat.add_eq]
  split_ifs with lt_n lt_add sub_lt nlt_add lt_add <;> (try rfl)
  · have := Nat.lt_add_right m lt_n
    contradiction
  · obtain rfl := Nat.eq_of_le_of_lt_succ (Nat.not_lt.mp nlt_add) isLt
    simp [Nat.add_comm n m] at sub_lt
  · have := Nat.sub_lt_left_of_lt_add (Nat.not_lt.mp lt_n) lt_add
    contradiction

/--
theorem `comp_init` / 定理 `comp_init`

English:
theorem comp_init
  given: {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n.succ -> α)
  proof: by
  ext j
  simp [init]

中文:
定理 comp_init
  条件: {α : 类型层*} {β : 类型层*} (g : α -> β) (q : 有限集 n.succ -> α)
  证明: by
  ext j
  simp [init]
-/
theorem comp_init {α : Sort*} {β : Sort*} (g : α -> β) (q : Fin n.succ -> α) :
    g ∘ init q = init (g ∘ q) := by
  ext j
  simp [init]

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the last element of the tuple.

This is `Fin.snoc` as an `Equiv`. -/
@[simps]
/--
Definition of `snocEquiv` / `snocEquiv` 的定义

English:
definition snocEquiv
  signature: (α : Fin (n + 1) -> Type*)
  body: Fin.snoc f.2 f.1 _
  invFun f := ⟨f _, Fin.init f⟩
  left_inv f := by simp
  right_inv f := by simp

中文:
定义 snocEquiv
  签名: (α : 有限集 (n + 1) -> 类型)
  定义体: Fin.snoc f.2 f.1 _
  invFun f := ⟨f _, Fin.init f⟩
  left_inv f := by simp
  right_inv f := by simp

Depends on / 依赖: Fin.snoc
-/
def snocEquiv (α : Fin (n + 1) -> Type*) : α (last n) × (forall i, α (castSucc i)) ≃ forall i, α i where
  toFun f _ := Fin.snoc f.2 f.1 _
  invFun f := ⟨f _, Fin.init f⟩
  left_inv f := by simp
  right_inv f := by simp

/-- Recurse on an `n+1`-tuple by splitting it its initial `n`-tuple and its last element. -/
@[elab_as_elim, inline]
/--
Definition of `snocCases` / `snocCases` 的定义

English:
definition snocCases
  signature: {motive : (forall i : Fin n.succ, α i) -> Sort*}
  body: _root_.cast (by rw [Fin.snoc_init_self]) snoc (Fin.init x) (x <| Fin.last _)

中文:
定义 snocCases
  签名: {motive : (对任意 i : 有限集 n.succ, α i) -> 类型层*}
  定义体: _root_.cast (by rw [Fin.snoc_init_self]) snoc (Fin.init x) (x <| Fin.last _)

Depends on / 依赖: Fin.init, Fin.last, Fin.snoc_init_self, _root_, _root_.cast, snoc_init_self
-/
def snocCases {motive : (forall i : Fin n.succ, α i) -> Sort*}
    (snoc : forall xs x, motive (Fin.snoc xs x))
    (x : forall i : Fin n.succ, α i) : motive x :=
_root_.cast (by rw [Fin.snoc_init_self]) snoc (Fin.init x) (x <| Fin.last _)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `snocCases_snoc` / 引理 `snocCases_snoc`

English:
lemma snocCases_snoc
  proof: by
  rw [snocCases]; rw [cast_eq_iff_heq]; rw [Fin.init_snoc]; rw [Fin.snoc_last]

中文:
引理 snocCases_snoc
  证明: by
  rw [snocCases]; rw [cast_eq_iff_heq]; rw [Fin.init_snoc]; rw [Fin.snoc_last]
-/
@[simp] lemma snocCases_snoc
    {motive : (forall i : Fin (n + 1), α i) -> Sort*} (snoc : forall x x₀, motive (Fin.snoc x x₀))
    (x : forall i : Fin n, (Fin.init α) i) (x₀ : α (Fin.last _)) :
    snocCases snoc (Fin.snoc x x₀) = snoc x x₀ := by
  rw [snocCases]; rw [cast_eq_iff_heq]; rw [Fin.init_snoc]; rw [Fin.snoc_last]

/-- Recurse on a tuple by splitting into `Fin.elim0` and `Fin.snoc`. -/
@[elab_as_elim]
/--
Definition of `snocInduction` / `snocInduction` 的定义

English:
definition snocInduction
  signature: {α : Sort*}

中文:
定义 snocInduction
  签名: {α : 类型层*}
-/
def snocInduction {α : Sort*}
    {motive : forall {n : Nat}, (Fin n -> α) -> Sort*}
    (elim0 : motive Fin.elim0)
    (snoc : forall {n} (x : Fin n -> α) (x₀), motive x -> motive (Fin.snoc x x₀)) :
    forall {n : Nat} (x : Fin n -> α), motive x
  | 0, x => by convert! elim0
  | _ + 1, x => snocCases (fun _ _ => snoc _ _ <| snocInduction elim0 snoc _) x

/--
theorem `snoc_injective_of_injective` / 定理 `snoc_injective_of_injective`

English:
theorem snoc_injective_of_injective
  statement: {α} {x₀ : α} {x : Fin n -> α}
  proof: fun i j h => by
  induction i using lastCases with
  | cast i =>
    induction j using lastCases with
    | cast j =>
      simpa only [castSucc_inj, ← Injective.eq_iff hx, snoc_castSucc] using h
    | last =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [← h] at hx₀
      apply hx₀.elim (Set.mem_range_self i)
  | last =>
    induction j using lastCases with
    | cast j =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [h] at hx₀
      apply hx₀.elim (Set.mem_range_self j)
    | last => simp

中文:
定理 snoc_injective_of_injective
  结论: {α} {x₀ : α} {x : 有限集 n -> α}
  证明: fun i j h => by
  induction i using lastCases with
  | cast i =>
    induction j using lastCases with
    | cast j =>
      simpa only [castSucc_inj, ← Injective.eq_iff hx, snoc_castSucc] using h
    | last =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [← h] at hx₀
      apply hx₀.elim (Set.mem_range_self i)
  | last =>
    induction j using lastCases with
    | cast j =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [h] at hx₀
      apply hx₀.elim (Set.mem_range_self j)
    | last => simp

Depends on / 依赖: Injective, Injective.eq_iff, Set.mem_range_self, castSucc_inj, eq_iff, lastCases, mem_range_self, snoc_castSucc, snoc_last
-/
theorem snoc_injective_of_injective {α} {x₀ : α} {x : Fin n -> α}
    (hx : Function.Injective x) (hx₀ : x₀ ∉ Set.range x) :
    Function.Injective (snoc x x₀ : Fin n.succ -> α) := fun i j h => by
  induction i using lastCases with
  | cast i =>
    induction j using lastCases with
    | cast j =>
      simpa only [castSucc_inj, ← Injective.eq_iff hx, snoc_castSucc] using h
    | last =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [← h] at hx₀
      apply hx₀.elim (Set.mem_range_self i)
  | last =>
    induction j using lastCases with
    | cast j =>
      simp only [snoc_castSucc, snoc_last] at h
      rw [h] at hx₀
      apply hx₀.elim (Set.mem_range_self j)
    | last => simp

/--
theorem `snoc_injective_iff` / 定理 `snoc_injective_iff`

English:
theorem snoc_injective_iff
  given: {α} {x₀ : α} {x : Fin n -> α}
  proof: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => snoc_injective_of_injective h.1 h.2⟩
  · simpa [Function.comp] using h.comp (Fin.castSucc_injective _)
  · rintro ⟨i, hi⟩
    rw [← @snoc_last n (fun i => α) x₀ x]; rw [← @snoc_castSucc n (fun i => α) x₀ x i]; rw [h.eq_iff] at hi
    exact ne_last_of_lt i.castSucc_lt_last hi

中文:
定理 snoc_injective_iff
  条件: {α} {x₀ : α} {x : 有限集 n -> α}
  证明: by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => snoc_injective_of_injective h.1 h.2⟩
  · simpa [Function.comp] using h.comp (Fin.castSucc_injective _)
  · rintro ⟨i, hi⟩
    rw [← @snoc_last n (fun i => α) x₀ x]; rw [← @snoc_castSucc n (fun i => α) x₀ x i]; rw [h.eq_iff] at hi
    exact ne_last_of_lt i.castSucc_lt_last hi

Depends on / 依赖: Fin.castSucc_injective, Function, Function.comp, castSucc_injective, castSucc_lt_last, eq_iff, h.comp, h.eq_iff, i.castSucc_lt_last, ne_last_of_lt, snoc_castSucc, snoc_injective_of_injective, snoc_last
-/
theorem snoc_injective_iff {α} {x₀ : α} {x : Fin n -> α} :
    Function.Injective (snoc x x₀ : Fin n.succ -> α) ↔ Function.Injective x ∧ x₀ ∉ Set.range x := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => snoc_injective_of_injective h.1 h.2⟩
  · simpa [Function.comp] using h.comp (Fin.castSucc_injective _)
  · rintro ⟨i, hi⟩
    rw [← @snoc_last n (fun i => α) x₀ x]; rw [← @snoc_castSucc n (fun i => α) x₀ x i]; rw [h.eq_iff] at hi
    exact ne_last_of_lt i.castSucc_lt_last hi

end TupleRight

section InsertNth

variable {α : Fin (n + 1) -> Sort*} {β : Sort*}

/-- Define a function on `Fin (n + 1)` from a value on `i : Fin (n + 1)` and values on each
`Fin.succAbove i j`, `j : Fin n`. This version is elaborated as eliminator and works for
propositions, see also `Fin.insertNth` for a version without an `@[elab_as_elim]`
attribute. -/
@[elab_as_elim]
/--
Definition of `succAboveCases` / `succAboveCases` 的定义

English:
definition succAboveCases
  signature: {α : Fin (n + 1) -> Sort u} (i : Fin (n + 1)) (x : α i)
  body: if hj : j = i then Eq.rec x hj.symm
  else
    if hlt : j < i then (succAbove_castPred_of_lt _ _ hlt) ▸ (p _)
    else (succAbove_pred_of_lt _ _ <| (Fin.lt_or_lt_of_ne hj).resolve_left hlt) ▸ (p _)

中文:
定义 succAboveCases
  签名: {α : 有限集 (n + 1) -> 类型层 u} (i : 有限集 (n + 1)) (x : α i)
  定义体: if hj : j = i then Eq.rec x hj.symm
  else
    if hlt : j < i then (succAbove_castPred_of_lt _ _ hlt) ▸ (p _)
    else (succAbove_pred_of_lt _ _ <| (Fin.lt_or_lt_of_ne hj).resolve_left hlt) ▸ (p _)

Depends on / 依赖: Eq.rec, Fin.lt_or_lt_of_ne, hj.symm, lt_or_lt_of_ne, resolve_left, succAbove_castPred_of_lt, succAbove_pred_of_lt
-/
def succAboveCases {α : Fin (n + 1) -> Sort u} (i : Fin (n + 1)) (x : α i)
    (p : forall j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) : α j :=
  if hj : j = i then Eq.rec x hj.symm
  else
    if hlt : j < i then (succAbove_castPred_of_lt _ _ hlt) ▸ (p _)
    else (succAbove_pred_of_lt _ _ <| (Fin.lt_or_lt_of_ne hj).resolve_left hlt) ▸ (p _)

-- This is a duplicate of `Fin.exists_fin_succ` in Core. We should upstream the name change.
alias forall_iff_succ := forall_fin_succ

-- This is a duplicate of `Fin.exists_fin_succ` in Core. We should upstream the name change.
alias exists_iff_succ := exists_fin_succ

/--
lemma `forall_iff_castSucc` / 引理 `forall_iff_castSucc`

English:
lemma forall_iff_castSucc
  given: {P : Fin (n + 1) -> Prop}
  proof: ⟨fun h => ⟨h _, fun _ => h _⟩, fun h => lastCases h.1 h.2⟩

中文:
引理 对任意_iff_castSucc
  条件: {P : 有限集 (n + 1) -> 命题}
  证明: ⟨fun h => ⟨h _, fun _ => h _⟩, fun h => lastCases h.1 h.2⟩

Depends on / 依赖: lastCases
-/
lemma forall_iff_castSucc {P : Fin (n + 1) -> Prop} :
    (forall i, P i) ↔ P (last n) ∧ forall i : Fin n, P i.castSucc :=
  ⟨fun h => ⟨h _, fun _ => h _⟩, fun h => lastCases h.1 h.2⟩

/--
theorem `forall_fin_add` / 定理 `forall_fin_add`

English:
theorem forall_fin_add
  given: {m n} (P : Fin (m + n) -> Prop)
  proof: ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hm, hn⟩ => Fin.addCases hm hn⟩

中文:
定理 对任意_fin_add
  条件: {m n} (P : 有限集 (m + n) -> 命题)
  证明: ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hm, hn⟩ => Fin.addCases hm hn⟩

Depends on / 依赖: Fin.addCases, addCases
-/
theorem forall_fin_add {m n} (P : Fin (m + n) -> Prop) :
    (forall i, P i) ↔ (forall i, P (castAdd _ i)) ∧ (forall j, P (natAdd _ j)) :=
  ⟨fun h => ⟨fun _ => h _, fun _ => h _⟩, fun ⟨hm, hn⟩ => Fin.addCases hm hn⟩

/--
theorem `forall_fin_add_pi` / 定理 `forall_fin_add_pi`

English:
theorem forall_fin_add_pi
  given: {γ : Fin (m + n) -> Sort*} {P : (forall i, γ i) -> Prop}
  proof: hv (addCases vm vn)
  mpr h v := by
    convert h (fun i => v (castAdd n i)) (fun j => v (natAdd m j))
    exact (addCases_castAdd_natAdd v _).symm

中文:
定理 对任意_fin_add_pi
  条件: {γ : 有限集 (m + n) -> 类型层*} {P : (对任意 i, γ i) -> 命题}
  证明: hv (addCases vm vn)
  mpr h v := by
    convert h (fun i => v (castAdd n i)) (fun j => v (natAdd m j))
    exact (addCases_castAdd_natAdd v _).symm

Depends on / 依赖: addCases
-/
theorem forall_fin_add_pi {γ : Fin (m + n) -> Sort*} {P : (forall i, γ i) -> Prop} :
    (forall v, P v) ↔
      (forall (vₘ : forall i, γ (castAdd n i)) (vₙ : forall j, γ (natAdd m j)), P (addCases vₘ vₙ)) where
  mp hv vm vn := hv (addCases vm vn)
  mpr h v := by
    convert h (fun i => v (castAdd n i)) (fun j => v (natAdd m j))
    exact (addCases_castAdd_natAdd v _).symm

/--
lemma `exists_iff_castSucc` / 引理 `exists_iff_castSucc`

English:
lemma exists_iff_castSucc
  given: {P : Fin (n + 1) -> Prop}
  proof: by
    rintro ⟨i, hi⟩
    cases i using lastCases with
    | last => exact .inl hi
    | cast _ => exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

中文:
引理 存在_iff_castSucc
  条件: {P : 有限集 (n + 1) -> 命题}
  证明: by
    rintro ⟨i, hi⟩
    cases i using lastCases with
    | last => exact .inl hi
    | cast _ => exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

Depends on / 依赖: lastCases
-/
lemma exists_iff_castSucc {P : Fin (n + 1) -> Prop} :
    (exists i, P i) ↔ P (last n) ∨ exists i : Fin n, P i.castSucc where
  mp := by
    rintro ⟨i, hi⟩
    cases i using lastCases with
    | last => exact .inl hi
    | cast _ => exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

/--
theorem `forall_iff_succAbove` / 定理 `forall_iff_succAbove`

English:
theorem forall_iff_succAbove
  given: {P : Fin (n + 1) -> Prop} (p : Fin (n + 1))
  proof: ⟨fun h => ⟨h _, fun _ => h _⟩, fun h => succAboveCases p h.1 h.2⟩

中文:
定理 对任意_iff_succAbove
  条件: {P : 有限集 (n + 1) -> 命题} (p : 有限集 (n + 1))
  证明: ⟨fun h => ⟨h _, fun _ => h _⟩, fun h => succAboveCases p h.1 h.2⟩

Depends on / 依赖: succAboveCases
-/
theorem forall_iff_succAbove {P : Fin (n + 1) -> Prop} (p : Fin (n + 1)) :
    (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i) :=
  ⟨fun h => ⟨h _, fun _ => h _⟩, fun h => succAboveCases p h.1 h.2⟩

/--
lemma `exists_iff_succAbove` / 引理 `exists_iff_succAbove`

English:
lemma exists_iff_succAbove
  given: {P : Fin (n + 1) -> Prop} (p : Fin (n + 1))
  proof: by
    rintro ⟨i, hi⟩
    induction i using p.succAboveCases
    · exact .inl hi
    · exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

中文:
引理 存在_iff_succAbove
  条件: {P : 有限集 (n + 1) -> 命题} (p : 有限集 (n + 1))
  证明: by
    rintro ⟨i, hi⟩
    induction i using p.succAboveCases
    · exact .inl hi
    · exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

Depends on / 依赖: p.succAboveCases, succAboveCases
-/
lemma exists_iff_succAbove {P : Fin (n + 1) -> Prop} (p : Fin (n + 1)) :
    (exists i, P i) ↔ P p ∨ exists i, P (p.succAbove i) where
  mp := by
    rintro ⟨i, hi⟩
    induction i using p.succAboveCases
    · exact .inl hi
    · exact .inr ⟨_, hi⟩
  mpr := by rintro (h | ⟨i, hi⟩) <;> exact ⟨_, ‹_›⟩

/--
theorem `eq_self_or_eq_succAbove` / 定理 `eq_self_or_eq_succAbove`

English:
theorem eq_self_or_eq_succAbove
  given: (p i : Fin (n + 1))
  statement: i = p ∨ exists j, i = p.succAbove j
  proof: succAboveCases p (.inl rfl) (fun j => .inr ⟨j, rfl⟩) i

中文:
定理 eq_self_or_eq_succAbove
  条件: (p i : 有限集 (n + 1))
  结论: i = p ∨ 存在 j, i = p.succAbove j
  证明: succAboveCases p (.inl rfl) (fun j => .inr ⟨j, rfl⟩) i

Depends on / 依赖: succAboveCases
-/
theorem eq_self_or_eq_succAbove (p i : Fin (n + 1)) : i = p ∨ exists j, i = p.succAbove j :=
  succAboveCases p (.inl rfl) (fun j => .inr ⟨j, rfl⟩) i

/--
Definition of `removeNth` / `removeNth` 的定义

English:
definition removeNth
  signature: (p : Fin (n + 1)) (f : forall i, α i)
  body: fun i => f (p.succAbove i)

中文:
定义 removeNth
  签名: (p : 有限集 (n + 1)) (f : 对任意 i, α i)
  定义体: fun i => f (p.succAbove i)

Depends on / 依赖: p.succAbove, succAbove
-/
def removeNth (p : Fin (n + 1)) (f : forall i, α i) : forall i, α (p.succAbove i) := fun i => f (p.succAbove i)

/--
Definition of `insertNth` / `insertNth` 的定义

English:
definition insertNth
  signature: (i : Fin (n + 1)) (x : α i) (p : forall j : Fin n, α (i.succAbove j)) (j : Fin (n + 1))
  body: succAboveCases i x p j

@[simp]

中文:
定义 insertNth
  签名: (i : 有限集 (n + 1)) (x : α i) (p : 对任意 j : 有限集 n, α (i.succAbove j)) (j : 有限集 (n + 1))
  定义体: succAboveCases i x p j

@[simp]

Depends on / 依赖: succAboveCases
-/
def insertNth (i : Fin (n + 1)) (x : α i) (p : forall j : Fin n, α (i.succAbove j)) (j : Fin (n + 1)) :
    α j :=
  succAboveCases i x p j

@[simp]
/--
theorem `insertNth_apply_same` / 定理 `insertNth_apply_same`

English:
theorem insertNth_apply_same
  given: (i : Fin (n + 1)) (x : α i) (p : forall j, α (i.succAbove j))
  proof: by simp [insertNth, succAboveCases]

@[simp]

中文:
定理 insertNth_apply_same
  条件: (i : 有限集 (n + 1)) (x : α i) (p : 对任意 j, α (i.succAbove j))
  证明: by simp [insertNth, succAboveCases]

@[simp]

Depends on / 依赖: insertNth, succAboveCases
-/
theorem insertNth_apply_same (i : Fin (n + 1)) (x : α i) (p : forall j, α (i.succAbove j)) :
    insertNth i x p i = x := by simp [insertNth, succAboveCases]

@[simp]
/--
theorem `insertNth_apply_succAbove` / 定理 `insertNth_apply_succAbove`

English:
theorem insertNth_apply_succAbove
  statement: (i : Fin (n + 1)) (x : α i) (p : forall j, α (i.succAbove j))
  proof: by
  simp only [insertNth, succAboveCases, dif_neg (succAbove_ne _ _), succAbove_lt_iff_castSucc_lt]
  split_ifs with hlt
  · generalize_proofs H₁ H₂; revert H₂
    generalize hk : castPred ((succAbove i) j) H₁ = k
    rw [castPred_succAbove _ _ hlt] at hk; cases hk
    intro; rfl
  · generalize_proofs H₀ H₁ H₂; revert H₂
    generalize hk : pred (succAbove i j) H₁ = k
    rw [pred_succAbove _ _ (Fin.not_lt.1 hlt)] at hk; cases hk
    intro; rfl

@[simp]

中文:
定理 insertNth_apply_succAbove
  结论: (i : 有限集 (n + 1)) (x : α i) (p : 对任意 j, α (i.succAbove j))
  证明: by
  simp only [insertNth, succAboveCases, dif_neg (succAbove_ne _ _), succAbove_lt_iff_castSucc_lt]
  split_ifs with hlt
  · generalize_proofs H₁ H₂; revert H₂
    generalize hk : castPred ((succAbove i) j) H₁ = k
    rw [castPred_succAbove _ _ hlt] at hk; cases hk
    intro; rfl
  · generalize_proofs H₀ H₁ H₂; revert H₂
    generalize hk : pred (succAbove i j) H₁ = k
    rw [pred_succAbove _ _ (Fin.not_lt.1 hlt)] at hk; cases hk
    intro; rfl

@[simp]

Depends on / 依赖: Fin.not_lt, castPred, castPred_succAbove, dif_neg, generalize, generalize_proofs, insertNth, not_lt, pred_succAbove, revert, split_ifs, succAbove, succAboveCases, succAbove_lt_iff_castSucc_lt, succAbove_ne
-/
theorem insertNth_apply_succAbove (i : Fin (n + 1)) (x : α i) (p : forall j, α (i.succAbove j))
    (j : Fin n) : insertNth i x p (i.succAbove j) = p j := by
  simp only [insertNth, succAboveCases, dif_neg (succAbove_ne _ _), succAbove_lt_iff_castSucc_lt]
  split_ifs with hlt
  · generalize_proofs H₁ H₂; revert H₂
    generalize hk : castPred ((succAbove i) j) H₁ = k
    rw [castPred_succAbove _ _ hlt] at hk; cases hk
    intro; rfl
  · generalize_proofs H₀ H₁ H₂; revert H₂
    generalize hk : pred (succAbove i j) H₁ = k
    rw [pred_succAbove _ _ (Fin.not_lt.1 hlt)] at hk; cases hk
    intro; rfl

@[simp]
/--
theorem `succAbove_cases_eq_insertNth` / 定理 `succAbove_cases_eq_insertNth`

English:
theorem succAbove_cases_eq_insertNth
  statement: @succAboveCases = @insertNth
  proof: rfl

中文:
定理 succAbove_cases_eq_insertNth
  结论: @succAboveCases = @insertNth
  证明: rfl
-/
theorem succAbove_cases_eq_insertNth : @succAboveCases = @insertNth :=
  rfl

/--
lemma `removeNth_apply` / 引理 `removeNth_apply`

English:
lemma removeNth_apply
  given: (p : Fin (n + 1)) (f : forall i, α i) (i : Fin n)
  proof: rfl

@[simp]

中文:
引理 removeNth_apply
  条件: (p : 有限集 (n + 1)) (f : 对任意 i, α i) (i : 有限集 n)
  证明: rfl

@[simp]
-/
lemma removeNth_apply (p : Fin (n + 1)) (f : forall i, α i) (i : Fin n) :
    p.removeNth f i = f (p.succAbove i) :=
  rfl

@[simp]
/--
theorem `cons_comp_succ_succAbove` / 定理 `cons_comp_succ_succAbove`

English:
theorem cons_comp_succ_succAbove
  given: (x : β) (p : Fin (n + 1) -> β) (i : Fin (n + 1))
  proof: funext (Fin.cases rfl fun _ => by simp [removeNth])

中文:
定理 cons_comp_succ_succAbove
  条件: (x : β) (p : 有限集 (n + 1) -> β) (i : 有限集 (n + 1))
  证明: funext (Fin.cases rfl fun _ => by simp [removeNth])

Depends on / 依赖: Fin.cases, removeNth
-/
theorem cons_comp_succ_succAbove (x : β) (p : Fin (n + 1) -> β) (i : Fin (n + 1)) :
    cons x p ∘ i.succ.succAbove = cons x (i.removeNth p) :=
  funext (Fin.cases rfl fun _ => by simp [removeNth])

/--
lemma `removeNth_fun_const` / 引理 `removeNth_fun_const`

English:
lemma removeNth_fun_const
  given: {α : Type*} {n : Nat} (i : Fin (n + 1)) (a : α)
  proof: rfl

中文:
引理 removeNth_fun_const
  条件: {α : 类型} {n : 自然数} (i : 有限集 (n + 1)) (a : α)
  证明: rfl
-/
lemma removeNth_fun_const {α : Type*} {n : Nat} (i : Fin (n + 1)) (a : α) :
    i.removeNth (fun _ => a) = (fun _ => a) :=
  rfl

/--
lemma `removeNth_insertNth` / 引理 `removeNth_insertNth`

English:
lemma removeNth_insertNth
  given: (p : Fin (n + 1)) (a : α p) (f : forall i, α (succAbove p i))
  proof: by ext; unfold removeNth; simp

中文:
引理 removeNth_insertNth
  条件: (p : 有限集 (n + 1)) (a : α p) (f : 对任意 i, α (succAbove p i))
  证明: by ext; unfold removeNth; simp
-/
@[simp] lemma removeNth_insertNth (p : Fin (n + 1)) (a : α p) (f : forall i, α (succAbove p i)) :
    removeNth p (insertNth p a f) = f := by ext; unfold removeNth; simp

/--
lemma `removeNth_zero` / 引理 `removeNth_zero`

English:
lemma removeNth_zero
  given: (f : forall i, α i)
  statement: removeNth 0 f = tail f
  proof: by
  ext; simp [tail, removeNth]

中文:
引理 removeNth_zero
  条件: (f : 对任意 i, α i)
  结论: removeNth 0 f = tail f
  证明: by
  ext; simp [tail, removeNth]
-/
@[simp] lemma removeNth_zero (f : forall i, α i) : removeNth 0 f = tail f := by
  ext; simp [tail, removeNth]

/--
lemma `removeNth_last` / 引理 `removeNth_last`

English:
lemma removeNth_last
  given: {α : Type*} (f : Fin (n + 1) -> α)
  statement: removeNth (last n) f = init f
  proof: by
  ext; simp [init, removeNth]

@[simp]

中文:
引理 removeNth_last
  条件: {α : 类型} (f : 有限集 (n + 1) -> α)
  结论: removeNth (last n) f = init f
  证明: by
  ext; simp [init, removeNth]

@[simp]
-/
@[simp] lemma removeNth_last {α : Type*} (f : Fin (n + 1) -> α) : removeNth (last n) f = init f := by
  ext; simp [init, removeNth]

@[simp]
/--
theorem `insertNth_comp_succAbove` / 定理 `insertNth_comp_succAbove`

English:
theorem insertNth_comp_succAbove
  given: (i : Fin (n + 1)) (x : β) (p : Fin n -> β)
  proof: funext (insertNth_apply_succAbove i _ _)

中文:
定理 insertNth_comp_succAbove
  条件: (i : 有限集 (n + 1)) (x : β) (p : 有限集 n -> β)
  证明: funext (insertNth_apply_succAbove i _ _)

Depends on / 依赖: insertNth_apply_succAbove
-/
theorem insertNth_comp_succAbove (i : Fin (n + 1)) (x : β) (p : Fin n -> β) :
    insertNth i x p ∘ i.succAbove = p :=
  funext (insertNth_apply_succAbove i _ _)

/--
theorem `insertNth_eq_iff` / 定理 `insertNth_eq_iff`

English:
theorem insertNth_eq_iff
  given: {p : Fin (n + 1)} {a : α p} {f : forall i, α (p.succAbove i)} {g : forall j, α j}
  proof: by
  simp [funext_iff, forall_iff_succAbove p, removeNth]

中文:
定理 insertNth_eq_iff
  条件: {p : 有限集 (n + 1)} {a : α p} {f : 对任意 i, α (p.succAbove i)} {g : 对任意 j, α j}
  证明: by
  simp [funext_iff, forall_iff_succAbove p, removeNth]

Depends on / 依赖: forall_iff_succAbove, funext_iff, removeNth
-/
theorem insertNth_eq_iff {p : Fin (n + 1)} {a : α p} {f : forall i, α (p.succAbove i)} {g : forall j, α j} :
    insertNth p a f = g ↔ a = g p ∧ f = removeNth p g := by
  simp [funext_iff, forall_iff_succAbove p, removeNth]

/--
theorem `eq_insertNth_iff` / 定理 `eq_insertNth_iff`

English:
theorem eq_insertNth_iff
  given: {p : Fin (n + 1)} {a : α p} {f : forall i, α (p.succAbove i)} {g : forall j, α j}
  proof: by
  simpa [eq_comm] using insertNth_eq_iff

中文:
定理 eq_insertNth_iff
  条件: {p : 有限集 (n + 1)} {a : α p} {f : 对任意 i, α (p.succAbove i)} {g : 对任意 j, α j}
  证明: by
  simpa [eq_comm] using insertNth_eq_iff

Depends on / 依赖: eq_comm, insertNth_eq_iff
-/
theorem eq_insertNth_iff {p : Fin (n + 1)} {a : α p} {f : forall i, α (p.succAbove i)} {g : forall j, α j} :
    g = insertNth p a f ↔ g p = a ∧ removeNth p g = f := by
  simpa [eq_comm] using insertNth_eq_iff

/--
theorem `insertNth_injective2` / 定理 `insertNth_injective2`

English:
theorem insertNth_injective2
  given: {p : Fin (n + 1)}
  proof: fun xₚ yₚ x y h =>
  ⟨by simpa using congr_fun h p, funext fun i => by simpa using congr_fun h (succAbove p i)⟩

@[simp]

中文:
定理 insertNth_injective2
  条件: {p : 有限集 (n + 1)}
  证明: fun xₚ yₚ x y h =>
  ⟨by simpa using congr_fun h p, funext fun i => by simpa using congr_fun h (succAbove p i)⟩

@[simp]
-/
theorem insertNth_injective2 {p : Fin (n + 1)} :
    Function.Injective2 (@insertNth n α p) := fun xₚ yₚ x y h =>
  ⟨by simpa using congr_fun h p, funext fun i => by simpa using congr_fun h (succAbove p i)⟩

@[simp]
/--
theorem `insertNth_inj` / 定理 `insertNth_inj`

English:
theorem insertNth_inj
  given: {p : Fin (n + 1)} {x y : forall i, α (succAbove p i)} {xₚ yₚ : α p}
  proof: insertNth_injective2.eq_iff

中文:
定理 insertNth_inj
  条件: {p : 有限集 (n + 1)} {x y : 对任意 i, α (succAbove p i)} {xₚ yₚ : α p}
  证明: insertNth_injective2.eq_iff

Depends on / 依赖: eq_iff, insertNth_injective2, insertNth_injective2.eq_iff
-/
theorem insertNth_inj {p : Fin (n + 1)} {x y : forall i, α (succAbove p i)} {xₚ yₚ : α p} :
    insertNth p xₚ x = insertNth p yₚ y ↔ xₚ = yₚ ∧ x = y :=
  insertNth_injective2.eq_iff

/--
theorem `insertNth_left_injective` / 定理 `insertNth_left_injective`

English:
theorem insertNth_left_injective
  given: {p : Fin (n + 1)} (x : forall i, α (succAbove p i))
  proof: insertNth_injective2.left _

中文:
定理 insertNth_left_injective
  条件: {p : 有限集 (n + 1)} (x : 对任意 i, α (succAbove p i))
  证明: insertNth_injective2.left _

Depends on / 依赖: insertNth_injective2, insertNth_injective2.left
-/
theorem insertNth_left_injective {p : Fin (n + 1)} (x : forall i, α (succAbove p i)) :
    Function.Injective (insertNth p · x) :=
  insertNth_injective2.left _

/--
theorem `insertNth_right_injective` / 定理 `insertNth_right_injective`

English:
theorem insertNth_right_injective
  given: {p : Fin (n + 1)} (x : α p)
  proof: insertNth_injective2.right _

中文:
定理 insertNth_right_injective
  条件: {p : 有限集 (n + 1)} (x : α p)
  证明: insertNth_injective2.right _

Depends on / 依赖: insertNth_injective2, insertNth_injective2.right
-/
theorem insertNth_right_injective {p : Fin (n + 1)} (x : α p) :
    Function.Injective (insertNth p x) :=
  insertNth_injective2.right _

/--
theorem `insertNth_apply_below` / 定理 `insertNth_apply_below`

English:
theorem insertNth_apply_below
  statement: {i j : Fin (n + 1)} (h : j < i) (x : α i)
  proof: by
  rw [insertNth]; rw [succAboveCases]; rw [dif_neg (Fin.ne_of_lt h)]; rw [dif_pos h]

中文:
定理 insertNth_apply_below
  结论: {i j : 有限集 (n + 1)} (h : j < i) (x : α i)
  证明: by
  rw [insertNth]; rw [succAboveCases]; rw [dif_neg (Fin.ne_of_lt h)]; rw [dif_pos h]

Depends on / 依赖: Fin.ne_of_lt, dif_neg, dif_pos, insertNth, ne_of_lt, succAboveCases
-/
theorem insertNth_apply_below {i j : Fin (n + 1)} (h : j < i) (x : α i)
    (p : forall k, α (i.succAbove k)) :
    i.insertNth x p j = succAbove_castPred_of_lt _ _ h ▸ (p <| j.castPred _) := by
  rw [insertNth]; rw [succAboveCases]; rw [dif_neg (Fin.ne_of_lt h)]; rw [dif_pos h]

/--
theorem `insertNth_apply_above` / 定理 `insertNth_apply_above`

English:
theorem insertNth_apply_above
  statement: {i j : Fin (n + 1)} (h : i < j) (x : α i)
  proof: by
  rw [insertNth]; rw [succAboveCases]; rw [dif_neg (Fin.ne_of_gt h)]; rw [dif_neg (Fin.lt_asymm h)]

中文:
定理 insertNth_apply_above
  结论: {i j : 有限集 (n + 1)} (h : i < j) (x : α i)
  证明: by
  rw [insertNth]; rw [succAboveCases]; rw [dif_neg (Fin.ne_of_gt h)]; rw [dif_neg (Fin.lt_asymm h)]

Depends on / 依赖: Fin.lt_asymm, Fin.ne_of_gt, dif_neg, insertNth, lt_asymm, ne_of_gt, succAboveCases
-/
theorem insertNth_apply_above {i j : Fin (n + 1)} (h : i < j) (x : α i)
    (p : forall k, α (i.succAbove k)) :
    i.insertNth x p j = succAbove_pred_of_lt _ _ h ▸ (p <| j.pred _) := by
  rw [insertNth]; rw [succAboveCases]; rw [dif_neg (Fin.ne_of_gt h)]; rw [dif_neg (Fin.lt_asymm h)]

/--
theorem `insertNth_zero` / 定理 `insertNth_zero`

English:
theorem insertNth_zero
  given: (x : α 0) (p : forall j : Fin n, α (succAbove 0 j))
  proof: by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  convert! (cons_succ x p j).symm

@[simp]

中文:
定理 insertNth_zero
  条件: (x : α 0) (p : 对任意 j : 有限集 n, α (succAbove 0 j))
  证明: by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  convert! (cons_succ x p j).symm

@[simp]

Depends on / 依赖: cons_succ, convert, insertNth_eq_iff
-/
theorem insertNth_zero (x : α 0) (p : forall j : Fin n, α (succAbove 0 j)) :
    insertNth 0 x p =
      cons x fun j => _root_.cast (congr_arg α (congr_fun succAbove_zero j)) (p j) := by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  convert! (cons_succ x p j).symm

@[simp]
/--
theorem `insertNth_zero'` / 定理 `insertNth_zero'`

English:
theorem insertNth_zero'
  given: (x : β) (p : Fin n -> β)
  statement: @insertNth _ (fun _ => β) 0 x p = cons x p
  proof: by
  simp [insertNth_zero]

中文:
定理 insertNth_zero'
  条件: (x : β) (p : 有限集 n -> β)
  结论: @insertNth _ (fun _ => β) 0 x p = cons x p
  证明: by
  simp [insertNth_zero]

Depends on / 依赖: insertNth_zero
-/
theorem insertNth_zero' (x : β) (p : Fin n -> β) : @insertNth _ (fun _ => β) 0 x p = cons x p := by
  simp [insertNth_zero]

/--
theorem `insertNth_last` / 定理 `insertNth_last`

English:
theorem insertNth_last
  given: (x : α (last n)) (p : forall j : Fin n, α ((last n).succAbove j))
  proof: by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  apply eq_of_heq
  trans snoc (fun j => _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x j.castSucc
  · rw [snoc_castSucc]
    exact (cast_heq _ _).symm
  · apply congr_arg_heq
    rw [succAbove_last]

@[simp]

中文:
定理 insertNth_last
  条件: (x : α (last n)) (p : 对任意 j : 有限集 n, α ((last n).succAbove j))
  证明: by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  apply eq_of_heq
  trans snoc (fun j => _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x j.castSucc
  · rw [snoc_castSucc]
    exact (cast_heq _ _).symm
  · apply congr_arg_heq
    rw [succAbove_last]

@[simp]

Depends on / 依赖: _root_, _root_.cast, castSucc, cast_heq, congr_arg, congr_arg_heq, eq_of_heq, insertNth_eq_iff, j.castSucc, snoc_castSucc, succAbove_last, succAbove_last_apply
-/
theorem insertNth_last (x : α (last n)) (p : forall j : Fin n, α ((last n).succAbove j)) :
    insertNth (last n) x p =
      snoc (fun j => _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x := by
  refine insertNth_eq_iff.2 ⟨by simp, ?_⟩
  ext j
  apply eq_of_heq
  trans snoc (fun j => _root_.cast (congr_arg α (succAbove_last_apply j)) (p j)) x j.castSucc
  · rw [snoc_castSucc]
    exact (cast_heq _ _).symm
  · apply congr_arg_heq
    rw [succAbove_last]

@[simp]
/--
theorem `insertNth_last'` / 定理 `insertNth_last'`

English:
theorem insertNth_last'
  given: (x : β) (p : Fin n -> β)
  proof: by simp [insertNth_last]

中文:
定理 insertNth_last'
  条件: (x : β) (p : 有限集 n -> β)
  证明: by simp [insertNth_last]

Depends on / 依赖: insertNth_last
-/
theorem insertNth_last' (x : β) (p : Fin n -> β) :
    @insertNth _ (fun _ => β) (last n) x p = snoc p x := by simp [insertNth_last]

/--
lemma `insertNth_rev` / 引理 `insertNth_rev`

English:
lemma insertNth_rev
  given: {α : Sort*} (i : Fin (n + 1)) (a : α) (f : Fin n -> α) (j : Fin (n + 1))
  proof: by
  induction j using Fin.succAboveCases
  · exact rev i
  · simp
  · simp [rev_succAbove]

中文:
引理 insertNth_rev
  条件: {α : 类型层*} (i : 有限集 (n + 1)) (a : α) (f : 有限集 n -> α) (j : 有限集 (n + 1))
  证明: by
  induction j using Fin.succAboveCases
  · exact rev i
  · simp
  · simp [rev_succAbove]

Depends on / 依赖: Fin.succAboveCases, i.rev, insertNth, rev_succAbove, succAboveCases
-/
lemma insertNth_rev {α : Sort*} (i : Fin (n + 1)) (a : α) (f : Fin n -> α) (j : Fin (n + 1)) :
    insertNth (α := fun _ => α) i a f (rev j) = insertNth (α := fun _ => α) i.rev a (f ∘ rev) j := by
  induction j using Fin.succAboveCases
  · exact rev i
  · simp
  · simp [rev_succAbove]

/--
theorem `insertNth_comp_rev` / 定理 `insertNth_comp_rev`

English:
theorem insertNth_comp_rev
  given: {α} (i : Fin (n + 1)) (x : α) (p : Fin n -> α)
  proof: by
  funext x
  apply insertNth_rev

@[simp]

中文:
定理 insertNth_comp_rev
  条件: {α} (i : 有限集 (n + 1)) (x : α) (p : 有限集 n -> α)
  证明: by
  funext x
  apply insertNth_rev

@[simp]

Depends on / 依赖: insertNth_rev
-/
theorem insertNth_comp_rev {α} (i : Fin (n + 1)) (x : α) (p : Fin n -> α) :
    (Fin.insertNth i x p) ∘ Fin.rev = Fin.insertNth (Fin.rev i) x (p ∘ Fin.rev) := by
  funext x
  apply insertNth_rev

@[simp]
/--
theorem `insertNth_succ_cons` / 定理 `insertNth_succ_cons`

English:
theorem insertNth_succ_cons
  given: {α} (i : Fin (n + 1)) (x a : α) (p : Fin n -> α)
  proof: by
  ext j
  cases j using Fin.succAboveCases i.succ with
  | x => simp
  | p j =>
    simp only [insertNth_apply_succAbove]
    cases j using Fin.cases <;> simp

中文:
定理 insertNth_succ_cons
  条件: {α} (i : 有限集 (n + 1)) (x a : α) (p : 有限集 n -> α)
  证明: by
  ext j
  cases j using Fin.succAboveCases i.succ with
  | x => simp
  | p j =>
    simp only [insertNth_apply_succAbove]
    cases j using Fin.cases <;> simp

Depends on / 依赖: Fin.cases, Fin.succAboveCases, i.succ, insertNth_apply_succAbove, succAboveCases
-/
theorem insertNth_succ_cons {α} (i : Fin (n + 1)) (x a : α) (p : Fin n -> α) :
    (insertNth i.succ x (cons a p) : Fin (n + 2) -> α) = cons a (insertNth i x p) := by
  ext j
  cases j using Fin.succAboveCases i.succ with
  | x => simp
  | p j =>
    simp only [insertNth_apply_succAbove]
    cases j using Fin.cases <;> simp

/--
theorem `cons_rev` / 定理 `cons_rev`

English:
theorem cons_rev
  given: {α n} (a : α) (f : Fin n -> α) (i : Fin <| n + 1)
  proof: by
  simpa using insertNth_rev 0 a f i

中文:
定理 cons_rev
  条件: {α n} (a : α) (f : 有限集 n -> α) (i : 有限集 <| n + 1)
  证明: by
  simpa using insertNth_rev 0 a f i

Depends on / 依赖: Fin.rev, i.rev, insertNth_rev
-/
theorem cons_rev {α n} (a : α) (f : Fin n -> α) (i : Fin <| n + 1) :
    cons (α := fun _ => α) a f i.rev = snoc (α := fun _ => α) (f ∘ Fin.rev : Fin _ -> α) a i := by
  simpa using insertNth_rev 0 a f i

/--
theorem `cons_comp_rev` / 定理 `cons_comp_rev`

English:
theorem cons_comp_rev
  given: {α n} (a : α) (f : Fin n -> α)
  proof: by
  funext i; exact cons_rev ..

中文:
定理 cons_comp_rev
  条件: {α n} (a : α) (f : 有限集 n -> α)
  证明: by
  funext i; exact cons_rev ..

Depends on / 依赖: cons_rev
-/
theorem cons_comp_rev {α n} (a : α) (f : Fin n -> α) :
    Fin.cons a f ∘ Fin.rev = Fin.snoc (f ∘ Fin.rev) a := by
  funext i; exact cons_rev ..

/--
theorem `snoc_rev` / 定理 `snoc_rev`

English:
theorem snoc_rev
  given: {α n} (a : α) (f : Fin n -> α) (i : Fin <| n + 1)
  proof: by
  simpa using insertNth_rev (last n) a f i

中文:
定理 snoc_rev
  条件: {α n} (a : α) (f : 有限集 n -> α) (i : 有限集 <| n + 1)
  证明: by
  simpa using insertNth_rev (last n) a f i

Depends on / 依赖: Fin.rev, i.rev, insertNth_rev
-/
theorem snoc_rev {α n} (a : α) (f : Fin n -> α) (i : Fin <| n + 1) :
    snoc (α := fun _ => α) f a i.rev = cons (α := fun _ => α) a (f ∘ Fin.rev : Fin _ -> α) i := by
  simpa using insertNth_rev (last n) a f i

/--
theorem `snoc_comp_rev` / 定理 `snoc_comp_rev`

English:
theorem snoc_comp_rev
  given: {α n} (a : α) (f : Fin n -> α)
  proof: funext snoc_rev a f

中文:
定理 snoc_comp_rev
  条件: {α n} (a : α) (f : 有限集 n -> α)
  证明: funext snoc_rev a f

Depends on / 依赖: snoc_rev
-/
theorem snoc_comp_rev {α n} (a : α) (f : Fin n -> α) :
    Fin.snoc f a ∘ Fin.rev = Fin.cons a (f ∘ Fin.rev) :=
funext snoc_rev a f

/--
theorem `insertNth_binop` / 定理 `insertNth_binop`

English:
theorem insertNth_binop
  statement: (op : forall j, α j -> α j -> α j) (i : Fin (n + 1)) (x y : α i)
  proof: insertNth_eq_iff.2 by unfold removeNth; simp

中文:
定理 insertNth_binop
  结论: (op : 对任意 j, α j -> α j -> α j) (i : 有限集 (n + 1)) (x y : α i)
  证明: insertNth_eq_iff.2 by unfold removeNth; simp

Depends on / 依赖: insertNth_eq_iff, removeNth
-/
theorem insertNth_binop (op : forall j, α j -> α j -> α j) (i : Fin (n + 1)) (x y : α i)
    (p q : forall j, α (i.succAbove j)) :
    (i.insertNth (op i x y) fun j => op _ (p j) (q j)) = fun j =>
      op j (i.insertNth x p j) (i.insertNth y q j) :=
insertNth_eq_iff.2 by unfold removeNth; simp

section Preorder

variable {α : Fin (n + 1) -> Type*} [forall i, Preorder (α i)]

/--
theorem `insertNth_le_iff` / 定理 `insertNth_le_iff`

English:
theorem insertNth_le_iff
  given: {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbove j)} {q : forall j, α j}
  proof: by
  simp [Pi.le_def, forall_iff_succAbove i]

中文:
定理 insertNth_le_iff
  条件: {i : 有限集 (n + 1)} {x : α i} {p : 对任意 j, α (i.succAbove j)} {q : 对任意 j, α j}
  证明: by
  simp [Pi.le_def, forall_iff_succAbove i]

Depends on / 依赖: Pi.le_def, forall_iff_succAbove, le_def
-/
theorem insertNth_le_iff {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbove j)} {q : forall j, α j} :
    i.insertNth x p <= q ↔ x <= q i ∧ p <= fun j => q (i.succAbove j) := by
  simp [Pi.le_def, forall_iff_succAbove i]

/--
theorem `le_insertNth_iff` / 定理 `le_insertNth_iff`

English:
theorem le_insertNth_iff
  given: {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbove j)} {q : forall j, α j}
  proof: by
  simp [Pi.le_def, forall_iff_succAbove i]

中文:
定理 le_insertNth_iff
  条件: {i : 有限集 (n + 1)} {x : α i} {p : 对任意 j, α (i.succAbove j)} {q : 对任意 j, α j}
  证明: by
  simp [Pi.le_def, forall_iff_succAbove i]

Depends on / 依赖: Pi.le_def, forall_iff_succAbove, le_def
-/
theorem le_insertNth_iff {i : Fin (n + 1)} {x : α i} {p : forall j, α (i.succAbove j)} {q : forall j, α j} :
    q <= i.insertNth x p ↔ q i <= x ∧ (fun j => q (i.succAbove j)) <= p := by
  simp [Pi.le_def, forall_iff_succAbove i]

end Preorder

open Set

/--
lemma `removeNth_update` / 引理 `removeNth_update`

English:
lemma removeNth_update
  given: (p : Fin (n + 1)) (x) (f : forall j, α j)
  proof: by ext i; simp [removeNth]

@[simp]

中文:
引理 removeNth_update
  条件: (p : 有限集 (n + 1)) (x) (f : 对任意 j, α j)
  证明: by ext i; simp [removeNth]

@[simp]
-/
@[simp] lemma removeNth_update (p : Fin (n + 1)) (x) (f : forall j, α j) :
    removeNth p (update f p x) = removeNth p f := by ext i; simp [removeNth]

@[simp]
/--
lemma `removeNth_update_succAbove` / 引理 `removeNth_update_succAbove`

English:
lemma removeNth_update_succAbove
  statement: (p : Fin (n + 1)) (i : Fin n) (x : α (p.succAbove i))
  proof: by
  ext j
  rcases eq_or_ne j i with rfl | hne <;> simp [removeNth, *]

中文:
引理 removeNth_update_succAbove
  结论: (p : 有限集 (n + 1)) (i : 有限集 n) (x : α (p.succAbove i))
  证明: by
  ext j
  rcases eq_or_ne j i with rfl | hne <;> simp [removeNth, *]

Depends on / 依赖: eq_or_ne, removeNth
-/
lemma removeNth_update_succAbove (p : Fin (n + 1)) (i : Fin n) (x : α (p.succAbove i))
    (f : forall j, α j) :
    removeNth p (update f (p.succAbove i) x) = update (removeNth p f) i x := by
  ext j
  rcases eq_or_ne j i with rfl | hne <;> simp [removeNth, *]

/--
lemma `insertNth_removeNth` / 引理 `insertNth_removeNth`

English:
lemma insertNth_removeNth
  given: (p : Fin (n + 1)) (x) (f : forall j, α j)
  proof: by simp [Fin.insertNth_eq_iff]

中文:
引理 insertNth_removeNth
  条件: (p : 有限集 (n + 1)) (x) (f : 对任意 j, α j)
  证明: by simp [Fin.insertNth_eq_iff]
-/
@[simp] lemma insertNth_removeNth (p : Fin (n + 1)) (x) (f : forall j, α j) :
    insertNth p x (removeNth p f) = update f p x := by simp [Fin.insertNth_eq_iff]

/--
lemma `insertNth_self_removeNth` / 引理 `insertNth_self_removeNth`

English:
lemma insertNth_self_removeNth
  given: (p : Fin (n + 1)) (f : forall j, α j)
  proof: by simp

@[simp]

中文:
引理 insertNth_self_removeNth
  条件: (p : 有限集 (n + 1)) (f : 对任意 j, α j)
  证明: by simp

@[simp]
-/
lemma insertNth_self_removeNth (p : Fin (n + 1)) (f : forall j, α j) :
    insertNth p (f p) (removeNth p f) = f := by simp

@[simp]
/--
lemma `range_insertNth` / 引理 `range_insertNth`

English:
lemma range_insertNth
  given: {α : Type*} (p : Fin (n + 1)) (x : α) (f : Fin n -> α)
  proof: by
  ext y
  simp [Fin.exists_iff_succAbove p, Set.insert, eq_comm]

@[simp]

中文:
引理 range_insertNth
  条件: {α : 类型} (p : 有限集 (n + 1)) (x : α) (f : 有限集 n -> α)
  证明: by
  ext y
  simp [Fin.exists_iff_succAbove p, Set.insert, eq_comm]

@[simp]

Depends on / 依赖: Fin.exists_iff_succAbove, Set.insert, eq_comm, exists_iff_succAbove, insert
-/
lemma range_insertNth {α : Type*} (p : Fin (n + 1)) (x : α) (f : Fin n -> α) :
    Set.range (p.insertNth x f) = Set.insert x (Set.range f) := by
  ext y
  simp [Fin.exists_iff_succAbove p, Set.insert, eq_comm]

@[simp]
/--
theorem `update_insertNth` / 定理 `update_insertNth`

English:
theorem update_insertNth
  given: (p : Fin (n + 1)) (x y : α p) (f : forall i, α (p.succAbove i))
  proof: by
  simp [eq_insertNth_iff]

@[simp]

中文:
定理 update_insertNth
  条件: (p : 有限集 (n + 1)) (x y : α p) (f : 对任意 i, α (p.succAbove i))
  证明: by
  simp [eq_insertNth_iff]

@[simp]

Depends on / 依赖: eq_insertNth_iff
-/
theorem update_insertNth (p : Fin (n + 1)) (x y : α p) (f : forall i, α (p.succAbove i)) :
    update (p.insertNth x f) p y = p.insertNth y f := by
  simp [eq_insertNth_iff]

@[simp]
/--
theorem `insertNth_update` / 定理 `insertNth_update`

English:
theorem insertNth_update
  statement: (p : Fin (n + 1)) (x : α p) (i : Fin n) (y : α (p.succAbove i))
  proof: by
  simp [insertNth_eq_iff]

中文:
定理 insertNth_update
  结论: (p : 有限集 (n + 1)) (x : α p) (i : 有限集 n) (y : α (p.succAbove i))
  证明: by
  simp [insertNth_eq_iff]

Depends on / 依赖: insertNth_eq_iff
-/
theorem insertNth_update (p : Fin (n + 1)) (x : α p) (i : Fin n) (y : α (p.succAbove i))
    (f : forall j, α (p.succAbove j)) :
    p.insertNth x (update f i y) = update (p.insertNth x f) (p.succAbove i) y := by
  simp [insertNth_eq_iff]

/-- Equivalence between tuples of length `n + 1` and pairs of an element and a tuple of length `n`
given by separating out the `p`-th element of the tuple.

This is `Fin.insertNth` as an `Equiv`. -/
@[simps]
/--
Definition of `insertNthEquiv` / `insertNthEquiv` 的定义

English:
definition insertNthEquiv
  signature: (α : Fin (n + 1) -> Type u) (p : Fin (n + 1))
  body: insertNth p f.1 f.2
  invFun f := (f p, removeNth p f)
  left_inv f := by ext <;> simp
  right_inv f := by simp

中文:
定义 insertNthEquiv
  签名: (α : 有限集 (n + 1) -> 类型u) (p : 有限集 (n + 1))
  定义体: insertNth p f.1 f.2
  invFun f := (f p, removeNth p f)
  left_inv f := by ext <;> simp
  right_inv f := by simp

Depends on / 依赖: insertNth
-/
def insertNthEquiv (α : Fin (n + 1) -> Type u) (p : Fin (n + 1)) :
    α p × (forall i, α (p.succAbove i)) ≃ forall i, α i where
  toFun f := insertNth p f.1 f.2
  invFun f := (f p, removeNth p f)
  left_inv f := by ext <;> simp
  right_inv f := by simp

/--
lemma `insertNthEquiv_zero` / 引理 `insertNthEquiv_zero`

English:
lemma insertNthEquiv_zero
  given: (α : Fin (n + 1) -> Type*)
  statement: insertNthEquiv α 0 = consEquiv α
  proof: Equiv.symm_bijective.injective by ext <;> rfl

中文:
引理 insertNthEquiv_zero
  条件: (α : 有限集 (n + 1) -> 类型)
  结论: insertNthEquiv α 0 = consEquiv α
  证明: Equiv.symm_bijective.injective by ext <;> rfl
-/
@[simp] lemma insertNthEquiv_zero (α : Fin (n + 1) -> Type*) : insertNthEquiv α 0 = consEquiv α :=
Equiv.symm_bijective.injective by ext <;> rfl

/--
lemma `insertNthEquiv_last` / 引理 `insertNthEquiv_last`

English:
lemma insertNthEquiv_last
  given: (n : Nat) (α : Type*)
  proof: by ext; simp

中文:
引理 insertNthEquiv_last
  条件: (n : 自然数) (α : 类型)
  证明: by ext; simp
-/
@[simp] lemma insertNthEquiv_last (n : Nat) (α : Type*) :
    insertNthEquiv (fun _ => α) (last n) = snocEquiv (fun _ => α) := by ext; simp

/--
theorem `removeNth_removeNth_heq_swap` / 定理 `removeNth_removeNth_heq_swap`

English:
theorem removeNth_removeNth_heq_swap
  statement: {α : Fin (n + 2) -> Sort*} (m : forall i, α i)
  proof: by
  apply Function.hfunext rfl
  simp only [heq_iff_eq]
  rintro k _ rfl
  unfold removeNth
  apply congr_arg_heq
  rw [succAbove_succAbove_succAbove_predAbove]

中文:
定理 removeNth_removeNth_heq_swap
  结论: {α : 有限集 (n + 2) -> 类型层*} (m : 对任意 i, α i)
  证明: by
  apply Function.hfunext rfl
  simp only [heq_iff_eq]
  rintro k _ rfl
  unfold removeNth
  apply congr_arg_heq
  rw [succAbove_succAbove_succAbove_predAbove]

Depends on / 依赖: Function, Function.hfunext, congr_arg_heq, heq_iff_eq, hfunext, removeNth, succAbove_succAbove_succAbove_predAbove
-/
theorem removeNth_removeNth_heq_swap {α : Fin (n + 2) -> Sort*} (m : forall i, α i)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    i.removeNth (j.removeNth m) ≍
      (i.predAbove j).removeNth ((j.succAbove i).removeNth m) := by
  apply Function.hfunext rfl
  simp only [heq_iff_eq]
  rintro k _ rfl
  unfold removeNth
  apply congr_arg_heq
  rw [succAbove_succAbove_succAbove_predAbove]

/--
theorem `removeNth_removeNth_eq_swap` / 定理 `removeNth_removeNth_eq_swap`

English:
theorem removeNth_removeNth_eq_swap
  statement: {α : Sort*} (m : Fin (n + 2) -> α)
  proof: heq_iff_eq.mp (removeNth_removeNth_heq_swap m i j)

中文:
定理 removeNth_removeNth_eq_swap
  结论: {α : 类型层*} (m : 有限集 (n + 2) -> α)
  证明: heq_iff_eq.mp (removeNth_removeNth_heq_swap m i j)

Depends on / 依赖: heq_iff_eq, heq_iff_eq.mp, removeNth_removeNth_heq_swap
-/
theorem removeNth_removeNth_eq_swap {α : Sort*} (m : Fin (n + 2) -> α)
    (i : Fin (n + 1)) (j : Fin (n + 2)) :
    i.removeNth (j.removeNth m) = (i.predAbove j).removeNth ((j.succAbove i).removeNth m) :=
  heq_iff_eq.mp (removeNth_removeNth_heq_swap m i j)

end InsertNth

section Find

variable {p q : Fin n -> Prop} [DecidablePred p] [DecidablePred q] {i j : Fin n}

set_option backward.privateInPublic true in
/--
Definition of `findX` / `findX` 的定义

English:
definition findX
  signature: {n : Nat} (p : Fin n -> Prop) [DecidablePred p] (h : exists k, p k)
  body: go n (by grind) where
  go (m : Nat) (hj : forall j (hm : j < n - m), ¬p ⟨j, by grind⟩) := match m with
  | m + 1 => if hnm : p ⟨_, n.sub_lt h.choose.pos (by grind)⟩
    then ⟨_, ⟨hnm, (hj ·.val)⟩⟩ else go m (by grind)
  | 0 => absurd h (fun ⟨⟨_, _⟩, _⟩ => by grind)

中文:
定义 findX
  签名: {n : 自然数} (p : 有限集 n -> 命题) [DecidablePred p] (h : 存在 k, p k)
  定义体: go n (by grind) where
  go (m : Nat) (hj : forall j (hm : j < n - m), ¬p ⟨j, by grind⟩) := match m with
  | m + 1 => if hnm : p ⟨_, n.sub_lt h.choose.pos (by grind)⟩
    then ⟨_, ⟨hnm, (hj ·.val)⟩⟩ else go m (by grind)
  | 0 => absurd h (fun ⟨⟨_, _⟩, _⟩ => by grind)
-/
private def findX {n : Nat} (p : Fin n -> Prop) [DecidablePred p] (h : exists k, p k) :
    { i : Fin n // p i ∧ forall j < i, ¬ p j } := go n (by grind) where
  go (m : Nat) (hj : forall j (hm : j < n - m), ¬p ⟨j, by grind⟩) := match m with
  | m + 1 => if hnm : p ⟨_, n.sub_lt h.choose.pos (by grind)⟩
    then ⟨_, ⟨hnm, (hj ·.val)⟩⟩ else go m (by grind)
  | 0 => absurd h (fun ⟨⟨_, _⟩, _⟩ => by grind)

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Definition of `find` / `find` 的定义

English:
definition find
  signature: {n : Nat} (p : Fin n -> Prop) [DecidablePred p] (h : exists k, p k)
  body: (Fin.findX p h).1

中文:
定义 find
  签名: {n : 自然数} (p : 有限集 n -> 命题) [DecidablePred p] (h : 存在 k, p k)
  定义体: (Fin.findX p h).1
-/
protected def find {n : Nat} (p : Fin n -> Prop) [DecidablePred p] (h : exists k, p k) : Fin n :=
  (Fin.findX p h).1

/--
theorem `find_spec` / 定理 `find_spec`

English:
theorem find_spec
  given: (h : exists k, p k)
  statement: p (Fin.find p h)
  proof: (Fin.findX p h).2.1

grind_pattern Fin.find_spec => Fin.find p h

中文:
定理 find_spec
  条件: (h : 存在 k, p k)
  结论: p (有限集.find p h)
  证明: (Fin.findX p h).2.1

grind_pattern Fin.find_spec => Fin.find p h
-/
protected theorem find_spec (h : exists k, p k) : p (Fin.find p h) := (Fin.findX p h).2.1

grind_pattern Fin.find_spec => Fin.find p h

/-- For `m : Fin n`, if `m < Fin.find p h` then `m` does not satisfy `p`. -/
@[grind ->]
/--
theorem `find_min` / 定理 `find_min`

English:
theorem find_min
  given: (h : exists k, p k)
  statement: forall {j : Fin n}, j < Fin.find p h -> ¬ p j
  proof: @(Fin.findX p h).2.2

中文:
定理 find_min
  条件: (h : 存在 k, p k)
  结论: 对任意 {j : 有限集 n}, j < 有限集.find p h -> ¬ p j
  证明: @(Fin.findX p h).2.2
-/
protected theorem find_min (h : exists k, p k) : forall {j : Fin n}, j < Fin.find p h -> ¬ p j :=
  @(Fin.findX p h).2.2

/--
theorem `find_le_of_pos` / 定理 `find_le_of_pos`

English:
theorem find_le_of_pos
  given: (h : exists k, p k) {j : Fin n}
  proof: (j.find_min _ <| lt_of_not_ge ·).mtr

中文:
定理 find_le_of_pos
  条件: (h : 存在 k, p k) {j : 有限集 n}
  证明: (j.find_min _ <| lt_of_not_ge ·).mtr
-/
protected theorem find_le_of_pos (h : exists k, p k) {j : Fin n} :
    p j -> Fin.find p h <= j := (j.find_min _ <| lt_of_not_ge ·).mtr

/--
theorem `find_eq_iff` / 定理 `find_eq_iff`

English:
theorem find_eq_iff
  given: {i : Fin n} (h : exists k, p k)
  statement: Fin.find p h = i ↔ p i ∧ forall j < i, ¬ p j
  proof: by
  refine ⟨?_, fun ⟨hm, hlt⟩ => have := Fin.find_le_of_pos h hm; ?_⟩ <;> grind

中文:
定理 find_eq_iff
  条件: {i : 有限集 n} (h : 存在 k, p k)
  结论: 有限集.find p h = i ↔ p i ∧ 对任意 j < i, ¬ p j
  证明: by
  refine ⟨?_, fun ⟨hm, hlt⟩ => have := Fin.find_le_of_pos h hm; ?_⟩ <;> grind

Depends on / 依赖: Fin.find_le_of_pos, find_le_of_pos
-/
theorem find_eq_iff {i : Fin n} (h : exists k, p k) : Fin.find p h = i ↔ p i ∧ forall j < i, ¬ p j := by
  refine ⟨?_, fun ⟨hm, hlt⟩ => have := Fin.find_le_of_pos h hm; ?_⟩ <;> grind

/--
theorem `val_find` / 定理 `val_find`

English:
theorem val_find
  given: (h : exists k, p k)
  proof: ((Nat.find_eq_iff _).mpr ⟨⟨is_lt _, Fin.find_spec _⟩,
    fun _ hm ⟨_, hi⟩ => Fin.find_min h hm hi⟩).symm

中文:
定理 val_find
  条件: (h : 存在 k, p k)
  证明: ((Nat.find_eq_iff _).mpr ⟨⟨is_lt _, Fin.find_spec _⟩,
    fun _ hm ⟨_, hi⟩ => Fin.find_min h hm hi⟩).symm
-/
@[simp] theorem val_find (h : exists k, p k) :
    (Fin.find p h).val = Nat.find ((Fin.exists_iff.mp h)) :=
  ((Nat.find_eq_iff _).mpr ⟨⟨is_lt _, Fin.find_spec _⟩,
    fun _ hm ⟨_, hi⟩ => Fin.find_min h hm hi⟩).symm

/--
theorem `find_nat_lt` / 定理 `find_nat_lt`

English:
theorem find_nat_lt
  given: {p : Nat -> Prop} [DecidablePred p] (h : exists k < n, p k)
  proof: by
  rw [val_find]
  have := h.choose_spec; exact Nat.find_congr (x := h.choose) (by grind) (by grind)

中文:
定理 find_nat_lt
  条件: {p : 自然数 -> 命题} [DecidablePred p] (h : 存在 k < n, p k)
  证明: by
  rw [val_find]
  have := h.choose_spec; exact Nat.find_congr (x := h.choose) (by grind) (by grind)

Depends on / 依赖: Fin.exists_iff.mpr, Fin.find, Nat.find_congr, choose_spec, exists_iff, find_congr, h.choose, h.choose_spec, val_find
-/
theorem find_nat_lt {p : Nat -> Prop} [DecidablePred p] (h : exists k < n, p k) :
    Nat.find (p := p) (by grind) = Fin.find (n := n) (p ·) (Fin.exists_iff.mpr <| by grind) := by
  rw [val_find]
  have := h.choose_spec; exact Nat.find_congr (x := h.choose) (by grind) (by grind)

/--
lemma `find_lt_iff` / 引理 `find_lt_iff`

English:
lemma find_lt_iff
  given: (h : exists k, p k) (i : Fin n)
  statement: Fin.find p h < i ↔ exists m < i, p m
  proof: ⟨by grind, fun ⟨_, hxi, hx⟩ => (Fin.find_le_of_pos h hx).trans_lt hxi⟩

中文:
引理 find_lt_iff
  条件: (h : 存在 k, p k) (i : 有限集 n)
  结论: 有限集.find p h < i ↔ 存在 m < i, p m
  证明: ⟨by grind, fun ⟨_, hxi, hx⟩ => (Fin.find_le_of_pos h hx).trans_lt hxi⟩
-/
@[simp] lemma find_lt_iff (h : exists k, p k) (i : Fin n) : Fin.find p h < i ↔ exists m < i, p m :=
  ⟨by grind, fun ⟨_, hxi, hx⟩ => (Fin.find_le_of_pos h hx).trans_lt hxi⟩

/--
lemma `find_le_iff` / 引理 `find_le_iff`

English:
lemma find_le_iff
  given: (h : exists k, p k) (i : Fin n)
  statement: Fin.find p h <= i ↔ exists m <= i, p m
  proof: ⟨by grind, fun ⟨_, hxi, hx⟩ => (Fin.find_le_of_pos h hx).trans hxi⟩

中文:
引理 find_le_iff
  条件: (h : 存在 k, p k) (i : 有限集 n)
  结论: 有限集.find p h <= i ↔ 存在 m <= i, p m
  证明: ⟨by grind, fun ⟨_, hxi, hx⟩ => (Fin.find_le_of_pos h hx).trans hxi⟩
-/
@[simp] lemma find_le_iff (h : exists k, p k) (i : Fin n) : Fin.find p h <= i ↔ exists m <= i, p m :=
  ⟨by grind, fun ⟨_, hxi, hx⟩ => (Fin.find_le_of_pos h hx).trans hxi⟩

/--
lemma `lt_find_iff` / 引理 `lt_find_iff`

English:
lemma lt_find_iff
  given: (h : exists k, p k) (i : Fin n)
  statement: i < Fin.find p h ↔ forall m <= i, ¬p m
  proof: by
  simp_rw [← not_le, find_le_iff, not_exists, not_and]

中文:
引理 lt_find_iff
  条件: (h : 存在 k, p k) (i : 有限集 n)
  结论: i < 有限集.find p h ↔ 对任意 m <= i, ¬p m
  证明: by
  simp_rw [← not_le, find_le_iff, not_exists, not_and]
-/
@[simp] lemma lt_find_iff (h : exists k, p k) (i : Fin n) : i < Fin.find p h ↔ forall m <= i, ¬p m := by
  simp_rw [← not_le, find_le_iff, not_exists, not_and]

/--
lemma `le_find_iff` / 引理 `le_find_iff`

English:
lemma le_find_iff
  given: (h : exists k, p k) (i : Fin n)
  statement: i <= Fin.find p h ↔ forall m < i, ¬p m
  proof: by
  simp_rw [← not_lt, find_lt_iff, not_exists, not_and]

中文:
引理 le_find_iff
  条件: (h : 存在 k, p k) (i : 有限集 n)
  结论: i <= 有限集.find p h ↔ 对任意 m < i, ¬p m
  证明: by
  simp_rw [← not_lt, find_lt_iff, not_exists, not_and]
-/
@[simp] lemma le_find_iff (h : exists k, p k) (i : Fin n) : i <= Fin.find p h ↔ forall m < i, ¬p m := by
  simp_rw [← not_lt, find_lt_iff, not_exists, not_and]

/--
lemma `find_eq_zero` / 引理 `find_eq_zero`

English:
lemma find_eq_zero
  given: {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists k, p k)
  proof: by simp [find_eq_iff]

中文:
引理 find_eq_zero
  条件: {p : 有限集 (n + 1) -> 命题} [DecidablePred p] (h : 存在 k, p k)
  证明: by simp [find_eq_iff]
-/
@[simp] lemma find_eq_zero {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists k, p k) :
  Fin.find p h = 0 ↔ p 0 := by simp [find_eq_iff]

/--
lemma `find_of_not_zero` / 引理 `find_of_not_zero`

English:
lemma find_of_not_zero
  statement: {p : Fin (n + 1) -> Prop} [DecidablePred p]
  proof: by
  simp_rw [find_eq_iff, forall_fin_succ, h0, not_false_eq_true,
    implies_true, true_and, succ_lt_succ_iff]
  exact ⟨Fin.find_spec (p := fun i => p i.succ) _, fun j => Fin.find_min _⟩

中文:
引理 find_of_not_zero
  结论: {p : 有限集 (n + 1) -> 命题} [DecidablePred p]
  证明: by
  simp_rw [find_eq_iff, forall_fin_succ, h0, not_false_eq_true,
    implies_true, true_and, succ_lt_succ_iff]
  exact ⟨Fin.find_spec (p := fun i => p i.succ) _, fun j => Fin.find_min _⟩

Depends on / 依赖: Fin.find_min, Fin.find_spec, find_eq_iff, find_min, find_spec, forall_fin_succ, i.succ, implies_true, not_false_eq_true, simp_rw, succ_lt_succ_iff, true_and
-/
lemma find_of_not_zero {p : Fin (n + 1) -> Prop} [DecidablePred p]
    (h : exists i, p i) (h0 : ¬p 0) :
    Fin.find p h =
    (Fin.find (fun k => p k.succ) <| (exists_fin_succ.mp h).resolve_left h0).succ := by
  simp_rw [find_eq_iff, forall_fin_succ, h0, not_false_eq_true,
    implies_true, true_and, succ_lt_succ_iff]
  exact ⟨Fin.find_spec (p := fun i => p i.succ) _, fun j => Fin.find_min _⟩

/--
theorem `find_eq_dite` / 定理 `find_eq_dite`

English:
theorem find_eq_dite
  given: {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists i, p i)
  proof: by
  split_ifs
  · grind [find_eq_zero]
  · grind [find_of_not_zero]

中文:
定理 find_eq_dite
  条件: {p : 有限集 (n + 1) -> 命题} [DecidablePred p] (h : 存在 i, p i)
  证明: by
  split_ifs
  · grind [find_eq_zero]
  · grind [find_of_not_zero]

Depends on / 依赖: find_eq_zero, find_of_not_zero, split_ifs
-/
theorem find_eq_dite {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists i, p i) :
    Fin.find p h = if h0 : p 0 then 0 else
    (Fin.find (fun k => p k.succ) <| (exists_fin_succ.mp h).resolve_left h0).succ := by
  split_ifs
  · grind [find_eq_zero]
  · grind [find_of_not_zero]

/--
lemma `find_mono_of_le` / 引理 `find_mono_of_le`

English:
lemma find_mono_of_le
  given: (hi : q i) (hpq : forall j <= i, q j -> p j)
  proof: Fin.find_le_of_pos _ (hpq _ (Fin.find_le_of_pos _ hi) (Fin.find_spec ⟨i, hi⟩))

中文:
引理 find_mono_of_le
  条件: (hi : q i) (hpq : 对任意 j <= i, q j -> p j)
  证明: Fin.find_le_of_pos _ (hpq _ (Fin.find_le_of_pos _ hi) (Fin.find_spec ⟨i, hi⟩))

Depends on / 依赖: Fin.find_le_of_pos, Fin.find_spec, find_le_of_pos, find_spec
-/
lemma find_mono_of_le (hi : q i) (hpq : forall j <= i, q j -> p j) :
    Fin.find p ⟨i, hpq _ le_rfl hi⟩ <= Fin.find q ⟨i, hi⟩ :=
  Fin.find_le_of_pos _ (hpq _ (Fin.find_le_of_pos _ hi) (Fin.find_spec ⟨i, hi⟩))

/--
lemma `find_mono` / 引理 `find_mono`

English:
lemma find_mono
  given: (h : forall i, q i -> p i) {hp : exists i, p i} {hq : exists i, q i}
  proof: let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ => h _

中文:
引理 find_mono
  条件: (h : 对任意 i, q i -> p i) {hp : 存在 i, p i} {hq : 存在 i, q i}
  证明: let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ => h _

Depends on / 依赖: find_mono_of_le
-/
lemma find_mono (h : forall i, q i -> p i) {hp : exists i, p i} {hq : exists i, q i} :
    Fin.find p hp <= Fin.find q hq :=
  let ⟨_, hq⟩ := hq; find_mono_of_le hq fun _ _ => h _

/--
lemma `find_congr` / 引理 `find_congr`

English:
lemma find_congr
  given: (hi : p i) (hpq : forall j <= i, p j ↔ q j)
  proof: Fin.find p ⟨i, hi⟩ = Fin.find q ⟨i, hpq _ le_rfl
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hi) fun _ h => (hpq _ h).mpr)
    (find_mono_of_le hi fun _ h => (hpq _ h).mp)

中文:
引理 find_congr
  条件: (hi : p i) (hpq : 对任意 j <= i, p j ↔ q j)
  证明: Fin.find p ⟨i, hi⟩ = Fin.find q ⟨i, hpq _ le_rfl
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hi) fun _ h => (hpq _ h).mpr)
    (find_mono_of_le hi fun _ h => (hpq _ h).mp)

Depends on / 依赖: Fin.find, le_rfl
-/
lemma find_congr (hi : p i) (hpq : forall j <= i, p j ↔ q j) :
.1 hi⟩ := Fin.find p ⟨i, hi⟩ = Fin.find q ⟨i, hpq _ le_rfl
  le_antisymm (find_mono_of_le (hpq _ le_rfl |>.1 hi) fun _ h => (hpq _ h).mpr)
    (find_mono_of_le hi fun _ h => (hpq _ h).mp)

/--
lemma `find_congr'` / 引理 `find_congr'`

English:
lemma find_congr'
  given: {hp : exists i, p i} {hq : exists i, q i} (hpq : forall {i}, p i ↔ q i)
  proof: let ⟨_, hp⟩ := hp; find_congr hp fun _ _ => hpq

中文:
引理 find_congr'
  条件: {hp : 存在 i, p i} {hq : 存在 i, q i} (hpq : 对任意 {i}, p i ↔ q i)
  证明: let ⟨_, hp⟩ := hp; find_congr hp fun _ _ => hpq

Depends on / 依赖: find_congr
-/
lemma find_congr' {hp : exists i, p i} {hq : exists i, q i} (hpq : forall {i}, p i ↔ q i) :
    Fin.find p hp = Fin.find q hq :=
  let ⟨_, hp⟩ := hp; find_congr hp fun _ _ => hpq

/--
lemma `find_le` / 引理 `find_le`

English:
lemma find_le
  given: (hi : p i)
  statement: Fin.find p ⟨i, hi⟩ <= i
  proof: (Fin.find_le_iff _ _).2 ⟨i, le_refl _, hi⟩

中文:
引理 find_le
  条件: (hi : p i)
  结论: 有限集.find p ⟨i, hi⟩ <= i
  证明: (Fin.find_le_iff _ _).2 ⟨i, le_refl _, hi⟩

Depends on / 依赖: Fin.find_le_iff, find_le_iff, le_refl
-/
lemma find_le (hi : p i) : Fin.find p ⟨i, hi⟩ <= i :=
  (Fin.find_le_iff _ _).2 ⟨i, le_refl _, hi⟩

/--
lemma `find_pos` / 引理 `find_pos`

English:
lemma find_pos
  given: {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists i, p i)
  proof: Fin.pos_iff_ne_zero.trans (Fin.find_eq_zero _).not

中文:
引理 find_pos
  条件: {p : 有限集 (n + 1) -> 命题} [DecidablePred p] (h : 存在 i, p i)
  证明: Fin.pos_iff_ne_zero.trans (Fin.find_eq_zero _).not

Depends on / 依赖: Fin.find_eq_zero, Fin.pos_iff_ne_zero.trans, find_eq_zero, pos_iff_ne_zero
-/
lemma find_pos {p : Fin (n + 1) -> Prop} [DecidablePred p] (h : exists i, p i) :
    0 < Fin.find p h ↔ ¬p 0 := Fin.pos_iff_ne_zero.trans (Fin.find_eq_zero _).not

/--
lemma `find_of_find_le` / 引理 `find_of_find_le`

English:
lemma find_of_find_le
  statement: {p : Fin (m + n) -> Prop} [DecidablePred p]
  proof: by
  have hⱼ : exists j : Fin n, p (j.natAdd m) :=
    ⟨(Fin.cast (Nat.add_comm _ _) (Fin.find p hᵢ)).subNat _ hm, by simp [Fin.find_spec]⟩
  refine (find_eq_iff _).2 ⟨Fin.find_spec hⱼ, fun i hi => ?_⟩
  cases i using addCases with | left i => _ | right i => _
  · exact Fin.find_min hᵢ (Fin.lt_def.mpr <| (Fin.castAdd_lt _ _).trans_le hm)
  · rw [Fin.natAdd_lt_natAdd_iff] at hi
    exact Fin.find_min hⱼ hi

中文:
引理 find_of_find_le
  结论: {p : 有限集 (m + n) -> 命题} [DecidablePred p]
  证明: by
  have hⱼ : exists j : Fin n, p (j.natAdd m) :=
    ⟨(Fin.cast (Nat.add_comm _ _) (Fin.find p hᵢ)).subNat _ hm, by simp [Fin.find_spec]⟩
  refine (find_eq_iff _).2 ⟨Fin.find_spec hⱼ, fun i hi => ?_⟩
  cases i using addCases with | left i => _ | right i => _
  · exact Fin.find_min hᵢ (Fin.lt_def.mpr <| (Fin.castAdd_lt _ _).trans_le hm)
  · rw [Fin.natAdd_lt_natAdd_iff] at hi
    exact Fin.find_min hⱼ hi

Depends on / 依赖: Fin.cast, Fin.castAdd_lt, Fin.find, Fin.find_min, Fin.find_spec, Fin.lt_def.mpr, Fin.natAdd_lt_natAdd_iff, Nat.add_comm, addCases, add_comm, castAdd_lt, find_eq_iff, find_min, find_spec, j.natAdd, lt_def, natAdd, natAdd_lt_natAdd_iff, subNat, trans_le
-/
lemma find_of_find_le {p : Fin (m + n) -> Prop} [DecidablePred p]
    {hᵢ : exists i, p i} (hm : m <= Fin.find p hᵢ) :
    Fin.find p hᵢ = (Fin.find (fun j => p (j.natAdd m))
    ⟨(Fin.cast (Nat.add_comm _ _) (Fin.find p hᵢ)).subNat _ hm, by
      simp [Fin.find_spec]⟩).natAdd m := by
  have hⱼ : exists j : Fin n, p (j.natAdd m) :=
    ⟨(Fin.cast (Nat.add_comm _ _) (Fin.find p hᵢ)).subNat _ hm, by simp [Fin.find_spec]⟩
  refine (find_eq_iff _).2 ⟨Fin.find_spec hⱼ, fun i hi => ?_⟩
  cases i using addCases with | left i => _ | right i => _
  · exact Fin.find_min hᵢ (Fin.lt_def.mpr <| (Fin.castAdd_lt _ _).trans_le hm)
  · rw [Fin.natAdd_lt_natAdd_iff] at hi
    exact Fin.find_min hⱼ hi

/--
theorem `find?_eq_dite` / 定理 `find?_eq_dite`

English:
theorem find?_eq_dite
  given: {p : Fin n -> Bool}
  proof: by
  split_ifs <;> grind

中文:
定理 find?_eq_dite
  条件: {p : 有限集 n -> 布尔值}
  证明: by
  split_ifs <;> grind

Depends on / 依赖: split_ifs
-/
theorem find?_eq_dite {p : Fin n -> Bool} :
    find? p = if h : exists i, p i then some (Fin.find (p ·) h) else none := by
  split_ifs <;> grind

/--
theorem `find?_decide_eq_dite` / 定理 `find?_decide_eq_dite`

English:
theorem find?_decide_eq_dite
  proof: by
  simp_rw [find?_eq_dite, decide_eq_true_eq]

中文:
定理 find?_decide_eq_dite
  证明: by
  simp_rw [find?_eq_dite, decide_eq_true_eq]
-/
theorem find?_decide_eq_dite :
    find? (p ·) = if h : exists i, p i then some (Fin.find p h) else none := by
  simp_rw [find?_eq_dite, decide_eq_true_eq]

/--
theorem `get_find?_eq_find_of_eq_true` / 定理 `get_find?_eq_find_of_eq_true`

English:
theorem get_find?_eq_find_of_eq_true
  given: {p : Fin n -> Bool} (h : p i)
  proof: by
  simp_rw [find?_eq_dite, Option.get_dite]

中文:
定理 get_find?_eq_find_of_eq_true
  条件: {p : 有限集 n -> 布尔值} (h : p i)
  证明: by
  simp_rw [find?_eq_dite, Option.get_dite]

Depends on / 依赖: Option.get_dite, _eq_dite, get_dite, simp_rw
-/
theorem get_find?_eq_find_of_eq_true {p : Fin n -> Bool} (h : p i) :
    (find? p).get (isSome_find?_of_eq_true h) = Fin.find (p ·) ⟨i, h⟩ := by
  simp_rw [find?_eq_dite, Option.get_dite]

/--
theorem `find?_decide_get_eq_find` / 定理 `find?_decide_get_eq_find`

English:
theorem find?_decide_get_eq_find
  given: (h : exists i, p i)
  proof: by
  simp_rw [find?_decide_eq_dite, Option.get_dite]

中文:
定理 find?_decide_get_eq_find
  条件: (h : 存在 i, p i)
  证明: by
  simp_rw [find?_decide_eq_dite, Option.get_dite]
-/
theorem find?_decide_get_eq_find (h : exists i, p i) :
    (find? (p ·)).get (isSome_find?_of_eq_true (i := h.choose)
    (by simp only [h.choose_spec, decide_true])) = Fin.find p h := by
  simp_rw [find?_decide_eq_dite, Option.get_dite]

/--
theorem `find_mem_find?_decide` / 定理 `find_mem_find?_decide`

English:
theorem find_mem_find?_decide
  given: (h : exists i, p i)
  proof: by grind [find?_eq_dite]

中文:
定理 find_mem_find?_decide
  条件: (h : 存在 i, p i)
  证明: by grind [find?_eq_dite]

Depends on / 依赖: _eq_dite
-/
theorem find_mem_find?_decide (h : exists i, p i) :
    Fin.find p h in find? p := by grind [find?_eq_dite]

end Find

section Find?

/--
theorem `mem_find?_iff` / 定理 `mem_find?_iff`

English:
theorem mem_find?_iff
  given: {p : Fin n -> Bool} {i : Fin n}
  proof: by simp

中文:
定理 mem_find?_iff
  条件: {p : 有限集 n -> 布尔值} {i : 有限集 n}
  证明: by simp
-/
theorem mem_find?_iff {p : Fin n -> Bool} {i : Fin n} :
    i in find? p ↔ p i ∧ forall j, j < i -> ¬ p j := by simp

/--
theorem `find?_eq_some_find_of_exists` / 定理 `find?_eq_some_find_of_exists`

English:
theorem find?_eq_some_find_of_exists
  given: {p : Fin n -> Bool} (h : exists i, p i)
  proof: by simp_rw [find?_eq_dite, h, dite_true]

中文:
定理 find?_eq_some_find_of_存在
  条件: {p : 有限集 n -> 布尔值} (h : 存在 i, p i)
  证明: by simp_rw [find?_eq_dite, h, dite_true]
-/
theorem find?_eq_some_find_of_exists {p : Fin n -> Bool} (h : exists i, p i) :
    find? p = some (Fin.find (p ·) h) := by simp_rw [find?_eq_dite, h, dite_true]

/--
theorem `find?_eq_some_find_of_isSome` / 定理 `find?_eq_some_find_of_isSome`

English:
theorem find?_eq_some_find_of_isSome
  given: {p : Fin n -> Bool} (h : (find? p).isSome)
  proof: by
  simp_rw [find?_eq_dite, exists_eq_true_of_isSome_find? h, dite_true]

中文:
定理 find?_eq_some_find_of_isSome
  条件: {p : 有限集 n -> 布尔值} (h : (find? p).isSome)
  证明: by
  simp_rw [find?_eq_dite, exists_eq_true_of_isSome_find? h, dite_true]
-/
theorem find?_eq_some_find_of_isSome {p : Fin n -> Bool} (h : (find? p).isSome) :
    find? p = some (Fin.find (p ·) (exists_eq_true_of_isSome_find? h)) := by
  simp_rw [find?_eq_dite, exists_eq_true_of_isSome_find? h, dite_true]

end Find?

section ContractNth

variable {α : Sort*}

/--
Definition of `contractNth` / `contractNth` 的定义

English:
definition contractNth
  signature: (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
  body: if (k : Nat) < j then g (Fin.castSucc k)
  else if (k : Nat) = j then op (g (Fin.castSucc k)) (g k.succ) else g k.succ

中文:
定义 contractNth
  签名: (j : 有限集 (n + 1)) (op : α -> α -> α) (g : 有限集 (n + 1) -> α) (k : 有限集 n)
  定义体: if (k : Nat) < j then g (Fin.castSucc k)
  else if (k : Nat) = j then op (g (Fin.castSucc k)) (g k.succ) else g k.succ

Depends on / 依赖: Fin.castSucc, castSucc, k.succ
-/
def contractNth (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n) : α :=
  if (k : Nat) < j then g (Fin.castSucc k)
  else if (k : Nat) = j then op (g (Fin.castSucc k)) (g k.succ) else g k.succ

/--
theorem `contractNth_apply_of_lt` / 定理 `contractNth_apply_of_lt`

English:
theorem contractNth_apply_of_lt
  statement: (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
  proof: if_pos h

中文:
定理 contractNth_apply_of_lt
  结论: (j : 有限集 (n + 1)) (op : α -> α -> α) (g : 有限集 (n + 1) -> α) (k : 有限集 n)
  证明: if_pos h

Depends on / 依赖: if_pos
-/
theorem contractNth_apply_of_lt (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
    (h : (k : Nat) < j) : contractNth j op g k = g (Fin.castSucc k) :=
  if_pos h

/--
theorem `contractNth_apply_of_eq` / 定理 `contractNth_apply_of_eq`

English:
theorem contractNth_apply_of_eq
  statement: (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
  proof: by
  have : ¬(k : Nat) < j := not_lt.2 (le_of_eq h.symm)
  rw [contractNth]; rw [if_neg this]; rw [if_pos h]

中文:
定理 contractNth_apply_of_eq
  结论: (j : 有限集 (n + 1)) (op : α -> α -> α) (g : 有限集 (n + 1) -> α) (k : 有限集 n)
  证明: by
  have : ¬(k : Nat) < j := not_lt.2 (le_of_eq h.symm)
  rw [contractNth]; rw [if_neg this]; rw [if_pos h]

Depends on / 依赖: contractNth, h.symm, if_neg, if_pos, le_of_eq, not_lt
-/
theorem contractNth_apply_of_eq (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
    (h : (k : Nat) = j) : contractNth j op g k = op (g (Fin.castSucc k)) (g k.succ) := by
  have : ¬(k : Nat) < j := not_lt.2 (le_of_eq h.symm)
  rw [contractNth]; rw [if_neg this]; rw [if_pos h]

/--
theorem `contractNth_apply_of_gt` / 定理 `contractNth_apply_of_gt`

English:
theorem contractNth_apply_of_gt
  statement: (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
  proof: by
  rw [contractNth]; rw [if_neg (not_lt_of_gt h)]; rw [if_neg (Ne.symm <| ne_of_lt h)]

中文:
定理 contractNth_apply_of_gt
  结论: (j : 有限集 (n + 1)) (op : α -> α -> α) (g : 有限集 (n + 1) -> α) (k : 有限集 n)
  证明: by
  rw [contractNth]; rw [if_neg (not_lt_of_gt h)]; rw [if_neg (Ne.symm <| ne_of_lt h)]

Depends on / 依赖: Ne.symm, contractNth, if_neg, ne_of_lt, not_lt_of_gt
-/
theorem contractNth_apply_of_gt (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
    (h : (j : Nat) < k) : contractNth j op g k = g k.succ := by
  rw [contractNth]; rw [if_neg (not_lt_of_gt h)]; rw [if_neg (Ne.symm <| ne_of_lt h)]

/--
theorem `contractNth_apply_of_ne` / 定理 `contractNth_apply_of_ne`

English:
theorem contractNth_apply_of_ne
  statement: (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
  proof: by
  rcases lt_trichotomy (k : Nat) j with (h | h | h)
  · rwa [j.succAbove_of_castSucc_lt, contractNth_apply_of_lt]
    · rwa [Fin.lt_def]
  · exact False.elim (hjk h.symm)
  · rwa [j.succAbove_of_le_castSucc, contractNth_apply_of_gt]
    · exact Fin.le_iff_val_le_val.2 (le_of_lt h)

中文:
定理 contractNth_apply_of_ne
  结论: (j : 有限集 (n + 1)) (op : α -> α -> α) (g : 有限集 (n + 1) -> α) (k : 有限集 n)
  证明: by
  rcases lt_trichotomy (k : Nat) j with (h | h | h)
  · rwa [j.succAbove_of_castSucc_lt, contractNth_apply_of_lt]
    · rwa [Fin.lt_def]
  · exact False.elim (hjk h.symm)
  · rwa [j.succAbove_of_le_castSucc, contractNth_apply_of_gt]
    · exact Fin.le_iff_val_le_val.2 (le_of_lt h)

Depends on / 依赖: False.elim, Fin.le_iff_val_le_val, Fin.lt_def, contractNth_apply_of_gt, contractNth_apply_of_lt, h.symm, j.succAbove_of_castSucc_lt, j.succAbove_of_le_castSucc, le_iff_val_le_val, le_of_lt, lt_def, lt_trichotomy, succAbove_of_castSucc_lt, succAbove_of_le_castSucc
-/
theorem contractNth_apply_of_ne (j : Fin (n + 1)) (op : α -> α -> α) (g : Fin (n + 1) -> α) (k : Fin n)
    (hjk : (j : Nat) != k) : contractNth j op g k = g (j.succAbove k) := by
  rcases lt_trichotomy (k : Nat) j with (h | h | h)
  · rwa [j.succAbove_of_castSucc_lt, contractNth_apply_of_lt]
    · rwa [Fin.lt_def]
  · exact False.elim (hjk h.symm)
  · rwa [j.succAbove_of_le_castSucc, contractNth_apply_of_gt]
    · exact Fin.le_iff_val_le_val.2 (le_of_lt h)

/--
lemma `comp_contractNth` / 引理 `comp_contractNth`

English:
lemma comp_contractNth
  statement: {β : Sort*} (opα : α -> α -> α) (opβ : β -> β -> β) {f : α -> β}
  proof: by
  ext x
  rcases lt_trichotomy (x : Nat) j with (h | h | h)
  · simp only [Function.comp_apply, contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, contractNth_apply_of_eq, h, hf]
  · simp only [Function.comp_apply, contractNth_apply_of_gt, h]

中文:
引理 comp_contractNth
  结论: {β : 类型层*} (opα : α -> α -> α) (opβ : β -> β -> β) {f : α -> β}
  证明: by
  ext x
  rcases lt_trichotomy (x : Nat) j with (h | h | h)
  · simp only [Function.comp_apply, contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, contractNth_apply_of_eq, h, hf]
  · simp only [Function.comp_apply, contractNth_apply_of_gt, h]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, contractNth_apply_of_eq, contractNth_apply_of_gt, contractNth_apply_of_lt, lt_trichotomy
-/
lemma comp_contractNth {β : Sort*} (opα : α -> α -> α) (opβ : β -> β -> β) {f : α -> β}
    (hf : forall x y, f (opα x y) = opβ (f x) (f y)) (j : Fin (n + 1)) (g : Fin (n + 1) -> α) :
    f ∘ contractNth j opα g = contractNth j opβ (f ∘ g) := by
  ext x
  rcases lt_trichotomy (x : Nat) j with (h | h | h)
  · simp only [Function.comp_apply, contractNth_apply_of_lt, h]
  · simp only [Function.comp_apply, contractNth_apply_of_eq, h, hf]
  · simp only [Function.comp_apply, contractNth_apply_of_gt, h]

end ContractNth

/--
theorem `sigma_eq_of_eq_comp_cast` / 定理 `sigma_eq_of_eq_comp_cast`

English:
theorem sigma_eq_of_eq_comp_cast
  given: {α : Type*}

中文:
定理 sigma_eq_of_eq_comp_cast
  条件: {α : 类型}
-/
theorem sigma_eq_of_eq_comp_cast {α : Type*} :
    forall {a b : Σ ii, Fin ii -> α} (h : a.fst = b.fst), a.snd = b.snd ∘ Fin.cast h -> a = b
  | ⟨ai, a⟩, ⟨bi, b⟩, hi, h => by
    dsimp only at hi
    subst hi
    simpa using h

/--
theorem `sigma_eq_iff_eq_comp_cast` / 定理 `sigma_eq_iff_eq_comp_cast`

English:
theorem sigma_eq_iff_eq_comp_cast
  given: {α : Type*} {a b : Σ ii, Fin ii -> α}
  proof: ⟨fun h => h ▸ ⟨rfl, funext Fin.rec fun _ _ => rfl⟩, fun ⟨_, h'⟩ =>
    sigma_eq_of_eq_comp_cast _ h'⟩

中文:
定理 sigma_eq_iff_eq_comp_cast
  条件: {α : 类型} {a b : Σ ii, 有限集 ii -> α}
  证明: ⟨fun h => h ▸ ⟨rfl, funext Fin.rec fun _ _ => rfl⟩, fun ⟨_, h'⟩ =>
    sigma_eq_of_eq_comp_cast _ h'⟩

Depends on / 依赖: Fin.rec, sigma_eq_of_eq_comp_cast
-/
theorem sigma_eq_iff_eq_comp_cast {α : Type*} {a b : Σ ii, Fin ii -> α} :
    a = b ↔ exists h : a.fst = b.fst, a.snd = b.snd ∘ Fin.cast h :=
⟨fun h => h ▸ ⟨rfl, funext Fin.rec fun _ _ => rfl⟩, fun ⟨_, h'⟩ =>
    sigma_eq_of_eq_comp_cast _ h'⟩

end Fin

/-- `Π i : Fin 2, α i` is equivalent to `α 0 × α 1`. See also `finTwoArrowEquiv` for a
non-dependent version and `prodEquivPiFinTwo` for a version with inputs `α β : Type u`. -/
@[simps -fullyApplied]
/--
Definition of `piFinTwoEquiv` / `piFinTwoEquiv` 的定义

English:
definition piFinTwoEquiv
  signature: (α : Fin 2 -> Type u)
  body: (f 0, f 1)
invFun p := Fin.cons p.1 Fin.cons p.2 finZeroElim
left_inv _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩

中文:
定义 piFinTwoEquiv
  签名: (α : 有限集 2 -> 类型u)
  定义体: (f 0, f 1)
invFun p := Fin.cons p.1 Fin.cons p.2 finZeroElim
left_inv _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩
-/
def piFinTwoEquiv (α : Fin 2 -> Type u) : (forall i, α i) ≃ α 0 × α 1 where
  toFun f := (f 0, f 1)
invFun p := Fin.cons p.1 Fin.cons p.2 finZeroElim
left_inv _ := funext Fin.forall_fin_two.2 ⟨rfl, rfl⟩
