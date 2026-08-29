/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte, Daniel Weber, Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal
public import Mathlib.Data.List.Zip

/-!
# Operations on walks

Operations on walks that produce a new walk in the same graph.

## Main definitions

* `SimpleGraph.Walk.copy`: Change the endpoints of a walk using equalities
* `SimpleGraph.Walk.append`: Concatenate two compatible walks
* `SimpleGraph.Walk.concat`: Concatenate an edge to the end of a walk
* `SimpleGraph.Walk.reverse`: Reverse a walk
* `SimpleGraph.Walk.drop`: Remove the first `n` darts of a walk
* `SimpleGraph.Walk.take`: Take the first `n` darts of a walk
* `SimpleGraph.Walk.tail`: Remove the first dart of a walk
* `SimpleGraph.Walk.dropLast`: Remove the last dart of a walk

## Tags
walks
-/

@[expose] public section

open Function

namespace SimpleGraph

namespace Walk

universe u
variable {V : Type u} {G : SimpleGraph V} {u v w : V}

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  body: hu ▸ hv ▸ p

@[simp]

中文:
定义 copy
  签名: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  定义体: hu ▸ hv ▸ p

@[simp]
-/
protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
  hu ▸ hv ▸ p

@[simp]
/--
theorem `copy_rfl_rfl` / 定理 `copy_rfl_rfl`

English:
theorem copy_rfl_rfl
  given: {u v} (p : G.Walk u v)
  statement: p.copy rfl rfl = p
  proof: rfl

@[simp]

中文:
定理 copy_rfl_rfl
  条件: {u v} (p : G.Walk u v)
  结论: p.copy rfl rfl = p
  证明: rfl

@[simp]
-/
theorem copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p := rfl

@[simp]
/--
theorem `copy_copy` / 定理 `copy_copy`

English:
theorem copy_copy
  statement: {u v u' v' u'' v''} (p : G.Walk u v)
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 copy_copy
  结论: {u v u' v' u'' v''} (p : G.Walk u v)
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem copy_copy {u v u' v' u'' v''} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

@[simp]
/--
theorem `copy_nil` / 定理 `copy_nil`

English:
theorem copy_nil
  given: {u u'} (hu : u = u')
  statement: (Walk.nil : G.Walk u u).copy hu hu = nil
  proof: by
  subst_vars
  rfl

中文:
定理 copy_nil
  条件: {u u'} (hu : u = u')
  结论: (Walk.nil : G.Walk u u).copy hu hu = nil
  证明: by
  subst_vars
  rfl
-/
theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = nil := by
  subst_vars
  rfl

/--
theorem `copy_cons` / 定理 `copy_cons`

English:
theorem copy_cons
  given: {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 copy_cons
  条件: {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
    (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw) := by
  subst_vars
  rfl

@[simp]
/--
theorem `cons_copy` / 定理 `cons_copy`

English:
theorem cons_copy
  given: {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w)
  proof: by
  subst_vars
  rfl

中文:
定理 cons_copy
  条件: {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w)
  证明: by
  subst_vars
  rfl
-/
theorem cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
    cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw := by
  subst_vars
  rfl

/-- The concatenation of two compatible walks. -/
@[trans]
/--
Definition of `append` / `append` 的定义

English:
definition append
  signature: {u v w : V}

中文:
定义 append
  签名: {u v w : V}
-/
def append {u v w : V} : G.Walk u v -> G.Walk v w -> G.Walk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)

/--
Definition of `concat` / `concat` 的定义

English:
definition concat
  signature: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  body: p.append (cons h nil)

中文:
定义 concat
  签名: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  定义体: p.append (cons h nil)

Depends on / 依赖: append, p.append
-/
def concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : G.Walk u w := p.append (cons h nil)

/--
theorem `concat_eq_append` / 定理 `concat_eq_append`

English:
theorem concat_eq_append
  given: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  proof: rfl

中文:
定理 concat_eq_append
  条件: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  证明: rfl
-/
theorem concat_eq_append {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    p.concat h = p.append (cons h nil) := rfl

/--
Definition of `reverseAux` / `reverseAux` 的定义

English:
definition reverseAux
  signature: {u v w : V}

中文:
定义 reverseAux
  签名: {u v w : V}
-/
protected def reverseAux {u v w : V} : G.Walk u v -> G.Walk u w -> G.Walk v w
  | nil, q => q
| cons h p, q => p.reverseAux cons h.symm q

/-- The walk in reverse. -/
@[symm]
/--
Definition of `reverse` / `reverse` 的定义

English:
definition reverse
  signature: {u v : V} (w : G.Walk u v)
  body: w.reverseAux nil

@[simp]

中文:
定义 reverse
  签名: {u v : V} (w : G.Walk u v)
  定义体: w.reverseAux nil

@[simp]

Depends on / 依赖: reverseAux, w.reverseAux
-/
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u := w.reverseAux nil

@[simp]
/--
theorem `cons_append` / 定理 `cons_append`

English:
theorem cons_append
  given: {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x)
  proof: rfl

@[simp]

中文:
定理 cons_append
  条件: {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x)
  证明: rfl

@[simp]
-/
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x) :
    (cons h p).append q = cons h (p.append q) := rfl

@[simp]
/--
theorem `cons_nil_append` / 定理 `cons_nil_append`

English:
theorem cons_nil_append
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: rfl

@[simp]

中文:
定理 cons_nil_append
  条件: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  证明: rfl

@[simp]
-/
theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h nil).append p = cons h p := rfl

@[simp]
/--
theorem `nil_append` / 定理 `nil_append`

English:
theorem nil_append
  given: {u v : V} (p : G.Walk u v)
  statement: nil.append p = p
  proof: rfl

@[simp]

中文:
定理 nil_append
  条件: {u v : V} (p : G.Walk u v)
  结论: nil.append p = p
  证明: rfl

@[simp]
-/
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl

@[simp]
/--
theorem `append_nil` / 定理 `append_nil`

English:
theorem append_nil
  given: {u v : V} (p : G.Walk u v)
  statement: p.append nil = p
  proof: by
  induction p <;> simp [*]

中文:
定理 append_nil
  条件: {u v : V} (p : G.Walk u v)
  结论: p.append nil = p
  证明: by
  induction p <;> simp [*]
-/
theorem append_nil {u v : V} (p : G.Walk u v) : p.append nil = p := by
  induction p <;> simp [*]

/--
theorem `append_assoc` / 定理 `append_assoc`

English:
theorem append_assoc
  given: {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x)
  proof: by
  induction p <;> simp [*]

@[simp]

中文:
定理 append_assoc
  条件: {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x)
  证明: by
  induction p <;> simp [*]

@[simp]
-/
theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x) :
    p.append (q.append r) = (p.append q).append r := by
  induction p <;> simp [*]

@[simp]
/--
theorem `append_copy_copy` / 定理 `append_copy_copy`

English:
theorem append_copy_copy
  statement: {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w)
  proof: by
  subst_vars
  rfl

中文:
定理 append_copy_copy
  结论: {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w)
  证明: by
  subst_vars
  rfl
-/
theorem append_copy_copy {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w)
    (hu : u = u') (hv : v = v') (hw : w = w') :
    (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw := by
  subst_vars
  rfl

/--
theorem `concat_nil` / 定理 `concat_nil`

English:
theorem concat_nil
  given: {u v : V} (h : G.Adj u v)
  statement: nil.concat h = cons h nil
  proof: rfl

@[simp]

中文:
定理 concat_nil
  条件: {u v : V} (h : G.Adj u v)
  结论: nil.concat h = cons h nil
  证明: rfl

@[simp]
-/
theorem concat_nil {u v : V} (h : G.Adj u v) : nil.concat h = cons h nil := rfl

@[simp]
/--
theorem `concat_cons` / 定理 `concat_cons`

English:
theorem concat_cons
  given: {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (h' : G.Adj w x)
  proof: rfl

中文:
定理 concat_cons
  条件: {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (h' : G.Adj w x)
  证明: rfl
-/
theorem concat_cons {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (h' : G.Adj w x) :
    (cons h p).concat h' = cons h (p.concat h') := rfl

/--
theorem `append_concat` / 定理 `append_concat`

English:
theorem append_concat
  given: {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (h : G.Adj w x)
  proof: append_assoc _ _ _

中文:
定理 append_concat
  条件: {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (h : G.Adj w x)
  证明: append_assoc _ _ _

Depends on / 依赖: append_assoc
-/
theorem append_concat {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (h : G.Adj w x) :
    p.append (q.concat h) = (p.append q).concat h := append_assoc _ _ _

/--
theorem `concat_append` / 定理 `concat_append`

English:
theorem concat_append
  given: {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (q : G.Walk w x)
  proof: by
  rw [concat_eq_append]; rw [← append_assoc]; rw [cons_nil_append]

中文:
定理 concat_append
  条件: {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (q : G.Walk w x)
  证明: by
  rw [concat_eq_append]; rw [← append_assoc]; rw [cons_nil_append]

Depends on / 依赖: append_assoc, concat_eq_append, cons_nil_append
-/
theorem concat_append {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (q : G.Walk w x) :
    (p.concat h).append q = p.append (cons h q) := by
  rw [concat_eq_append]; rw [← append_assoc]; rw [cons_nil_append]

/--
theorem `exists_cons_eq_concat` / 定理 `exists_cons_eq_concat`

English:
theorem exists_cons_eq_concat
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: by
  induction p generalizing u with
  | nil => exact ⟨_, nil, h, rfl⟩
  | cons h' p ih =>
    obtain ⟨y, q, h'', hc⟩ := ih h'
    exact ⟨y, cons h q, h'', hc ▸ concat_cons _ _ _ ▸ rfl⟩

中文:
定理 exists_cons_eq_concat
  条件: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  证明: by
  induction p generalizing u with
  | nil => exact ⟨_, nil, h, rfl⟩
  | cons h' p ih =>
    obtain ⟨y, q, h'', hc⟩ := ih h'
    exact ⟨y, cons h q, h'', hc ▸ concat_cons _ _ _ ▸ rfl⟩

Depends on / 依赖: concat_cons, generalizing
-/
theorem exists_cons_eq_concat {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    exists (x : V) (q : G.Walk u x) (h' : G.Adj x w), cons h p = q.concat h' := by
  induction p generalizing u with
  | nil => exact ⟨_, nil, h, rfl⟩
  | cons h' p ih =>
    obtain ⟨y, q, h'', hc⟩ := ih h'
    exact ⟨y, cons h q, h'', hc ▸ concat_cons _ _ _ ▸ rfl⟩

/--
theorem `exists_concat_eq_cons` / 定理 `exists_concat_eq_cons`

English:
theorem exists_concat_eq_cons
  given: {u v w : V}

中文:
定理 exists_concat_eq_cons
  条件: {u v w : V}
-/
theorem exists_concat_eq_cons {u v w : V} :
    forall (p : G.Walk u v) (h : G.Adj v w),
      exists (x : V) (h' : G.Adj u x) (q : G.Walk x w), p.concat h = cons h' q
  | nil, h => ⟨_, h, nil, rfl⟩
  | cons h' p, h => ⟨_, h', Walk.concat p h, concat_cons _ _ _⟩

@[simp]
/--
theorem `reverse_nil` / 定理 `reverse_nil`

English:
theorem reverse_nil
  given: {u : V}
  statement: (nil : G.Walk u u).reverse = nil
  proof: rfl

中文:
定理 reverse_nil
  条件: {u : V}
  结论: (nil : G.Walk u u).reverse = nil
  证明: rfl
-/
theorem reverse_nil {u : V} : (nil : G.Walk u u).reverse = nil := rfl

/--
theorem `reverse_singleton` / 定理 `reverse_singleton`

English:
theorem reverse_singleton
  given: {u v : V} (h : G.Adj u v)
  statement: (cons h nil).reverse = cons h.symm nil
  proof: rfl

@[simp]

中文:
定理 reverse_singleton
  条件: {u v : V} (h : G.Adj u v)
  结论: (cons h nil).reverse = cons h.symm nil
  证明: rfl

@[simp]
-/
theorem reverse_singleton {u v : V} (h : G.Adj u v) : (cons h nil).reverse = cons h.symm nil :=
  rfl

@[simp]
/--
theorem `reverse_toWalk` / 定理 `reverse_toWalk`

English:
theorem reverse_toWalk
  given: {u v : V} (h : G.Adj u v)
  statement: h.toWalk.reverse = h.symm.toWalk
  proof: rfl

@[simp]

中文:
定理 reverse_toWalk
  条件: {u v : V} (h : G.Adj u v)
  结论: h.toWalk.reverse = h.symm.toWalk
  证明: rfl

@[simp]
-/
theorem reverse_toWalk {u v : V} (h : G.Adj u v) : h.toWalk.reverse = h.symm.toWalk := rfl

@[simp]
/--
theorem `cons_reverseAux` / 定理 `cons_reverseAux`

English:
theorem cons_reverseAux
  given: {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u)
  proof: rfl

@[simp]

中文:
定理 cons_reverseAux
  条件: {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u)
  证明: rfl

@[simp]
-/
theorem cons_reverseAux {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u) :
    (cons h p).reverseAux q = p.reverseAux (cons h.symm q) := rfl

@[simp]
/--
theorem `append_reverseAux` / 定理 `append_reverseAux`

English:
theorem append_reverseAux
  statement: {u v w x : V}
  proof: by
  induction p with
  | nil => rfl
  | cons h _ ih => exact ih q (cons h.symm r)

@[simp]

中文:
定理 append_reverseAux
  结论: {u v w x : V}
  证明: by
  induction p with
  | nil => rfl
  | cons h _ ih => exact ih q (cons h.symm r)

@[simp]
-/
protected theorem append_reverseAux {u v w x : V}
    (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk u x) :
    (p.append q).reverseAux r = q.reverseAux (p.reverseAux r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact ih q (cons h.symm r)

@[simp]
/--
theorem `reverseAux_append` / 定理 `reverseAux_append`

English:
theorem reverseAux_append
  statement: {u v w x : V}
  proof: by
  induction p with
  | nil => rfl
  | cons h _ ih => simp [ih (cons h.symm q)]

中文:
定理 reverseAux_append
  结论: {u v w x : V}
  证明: by
  induction p with
  | nil => rfl
  | cons h _ ih => simp [ih (cons h.symm q)]
-/
protected theorem reverseAux_append {u v w x : V}
    (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x) :
    (p.reverseAux q).append r = p.reverseAux (q.append r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => simp [ih (cons h.symm q)]

/--
theorem `reverseAux_eq_reverse_append` / 定理 `reverseAux_eq_reverse_append`

English:
theorem reverseAux_eq_reverse_append
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk u w)
  proof: by simp [reverse]

@[simp]

中文:
定理 reverseAux_eq_reverse_append
  条件: {u v w : V} (p : G.Walk u v) (q : G.Walk u w)
  证明: by simp [reverse]

@[simp]
-/
protected theorem reverseAux_eq_reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    p.reverseAux q = p.reverse.append q := by simp [reverse]

@[simp]
/--
theorem `reverse_cons` / 定理 `reverse_cons`

English:
theorem reverse_cons
  given: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  proof: by simp [reverse]

@[simp]

中文:
定理 reverse_cons
  条件: {u v w : V} (h : G.Adj u v) (p : G.Walk v w)
  证明: by simp [reverse]

@[simp]

Depends on / 依赖: reverse
-/
theorem reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).reverse = p.reverse.append (cons h.symm nil) := by simp [reverse]

@[simp]
/--
theorem `reverse_copy` / 定理 `reverse_copy`

English:
theorem reverse_copy
  given: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 reverse_copy
  条件: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem reverse_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).reverse = p.reverse.copy hv hu := by
  subst_vars
  rfl

@[simp]
/--
theorem `reverse_append` / 定理 `reverse_append`

English:
theorem reverse_append
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  proof: by simp [reverse]

@[simp]

中文:
定理 reverse_append
  条件: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  证明: by simp [reverse]

@[simp]

Depends on / 依赖: reverse
-/
theorem reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by simp [reverse]

@[simp]
/--
theorem `reverse_concat` / 定理 `reverse_concat`

English:
theorem reverse_concat
  given: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  proof: by simp [concat_eq_append]

@[simp]

中文:
定理 reverse_concat
  条件: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  证明: by simp [concat_eq_append]

@[simp]

Depends on / 依赖: concat_eq_append
-/
theorem reverse_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).reverse = cons h.symm p.reverse := by simp [concat_eq_append]

@[simp]
/--
theorem `reverse_reverse` / 定理 `reverse_reverse`

English:
theorem reverse_reverse
  given: {u v : V} (p : G.Walk u v)
  statement: p.reverse.reverse = p
  proof: by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]

中文:
定理 reverse_reverse
  条件: {u v : V} (p : G.Walk u v)
  结论: p.reverse.reverse = p
  证明: by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]
-/
theorem reverse_reverse {u v : V} (p : G.Walk u v) : p.reverse.reverse = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/--
theorem `reverse_surjective` / 定理 `reverse_surjective`

English:
theorem reverse_surjective
  given: {u v : V}
  statement: Function.Surjective (reverse : G.Walk u v -> _)
  proof: RightInverse.surjective reverse_reverse

中文:
定理 reverse_surjective
  条件: {u v : V}
  结论: Function.Surjective (reverse : G.Walk u v -> _)
  证明: RightInverse.surjective reverse_reverse

Depends on / 依赖: RightInverse, RightInverse.surjective, reverse_reverse, surjective
-/
theorem reverse_surjective {u v : V} : Function.Surjective (reverse : G.Walk u v -> _) :=
  RightInverse.surjective reverse_reverse

/--
theorem `reverse_injective` / 定理 `reverse_injective`

English:
theorem reverse_injective
  given: {u v : V}
  statement: Function.Injective (reverse : G.Walk u v -> _)
  proof: RightInverse.injective reverse_reverse

中文:
定理 reverse_injective
  条件: {u v : V}
  结论: Function.Injective (reverse : G.Walk u v -> _)
  证明: RightInverse.injective reverse_reverse

Depends on / 依赖: RightInverse, RightInverse.injective, injective, reverse_reverse
-/
theorem reverse_injective {u v : V} : Function.Injective (reverse : G.Walk u v -> _) :=
  RightInverse.injective reverse_reverse

/--
theorem `reverse_bijective` / 定理 `reverse_bijective`

English:
theorem reverse_bijective
  given: {u v : V}
  statement: Function.Bijective (reverse : G.Walk u v -> _)
  proof: ⟨reverse_injective, reverse_surjective⟩

@[simp]

中文:
定理 reverse_bijective
  条件: {u v : V}
  结论: Function.Bijective (reverse : G.Walk u v -> _)
  证明: ⟨reverse_injective, reverse_surjective⟩

@[simp]

Depends on / 依赖: reverse_injective, reverse_surjective
-/
theorem reverse_bijective {u v : V} : Function.Bijective (reverse : G.Walk u v -> _) :=
  ⟨reverse_injective, reverse_surjective⟩

@[simp]
/--
theorem `length_copy` / 定理 `length_copy`

English:
theorem length_copy
  given: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 length_copy
  条件: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by
  subst_vars
  rfl

@[simp]
/--
theorem `length_append` / 定理 `length_append`

English:
theorem length_append
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  proof: by
  induction p <;> simp [*, add_comm, add_assoc]

@[simp]

中文:
定理 length_append
  条件: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  证明: by
  induction p <;> simp [*, add_comm, add_assoc]

@[simp]

Depends on / 依赖: add_assoc, add_comm
-/
theorem length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  induction p <;> simp [*, add_comm, add_assoc]

@[simp]
/--
theorem `length_concat` / 定理 `length_concat`

English:
theorem length_concat
  given: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  proof: length_append _ _

@[simp]

中文:
定理 length_concat
  条件: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  证明: length_append _ _

@[simp]

Depends on / 依赖: length_append
-/
theorem length_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).length = p.length + 1 := length_append _ _

@[simp]
/--
theorem `length_reverseAux` / 定理 `length_reverseAux`

English:
theorem length_reverseAux
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk u w)
  proof: by
  induction p with
  | nil => simp!
  | cons _ _ ih => simp [ih, Nat.succ_add, add_assoc]

@[simp]

中文:
定理 length_reverseAux
  条件: {u v w : V} (p : G.Walk u v) (q : G.Walk u w)
  证明: by
  induction p with
  | nil => simp!
  | cons _ _ ih => simp [ih, Nat.succ_add, add_assoc]

@[simp]
-/
protected theorem length_reverseAux {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    (p.reverseAux q).length = p.length + q.length := by
  induction p with
  | nil => simp!
  | cons _ _ ih => simp [ih, Nat.succ_add, add_assoc]

@[simp]
/--
theorem `length_reverse` / 定理 `length_reverse`

English:
theorem length_reverse
  given: {u v : V} (p : G.Walk u v)
  statement: p.reverse.length = p.length
  proof: by simp [reverse]

中文:
定理 length_reverse
  条件: {u v : V} (p : G.Walk u v)
  结论: p.reverse.length = p.length
  证明: by simp [reverse]

Depends on / 依赖: reverse
-/
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by simp [reverse]

/--
theorem `getVert_append` / 定理 `getVert_append`

English:
theorem getVert_append
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : Nat)
  proof: by
  induction p generalizing i <;> cases i <;> simp [*]

中文:
定理 getVert_append
  条件: {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : 自然数)
  证明: by
  induction p generalizing i <;> cases i <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem getVert_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : Nat) :
    (p.append q).getVert i = if i < p.length then p.getVert i else q.getVert (i - p.length) := by
  induction p generalizing i <;> cases i <;> simp [*]

/--
theorem `getVert_append'` / 定理 `getVert_append'`

English:
theorem getVert_append'
  given: (p : G.Walk u v) (q : G.Walk v w) (i : Nat)
  proof: by
  induction p generalizing i <;> cases i <;> simp [*]

中文:
定理 getVert_append'
  条件: (p : G.Walk u v) (q : G.Walk v w) (i : 自然数)
  证明: by
  induction p generalizing i <;> cases i <;> simp [*]

Depends on / 依赖: generalizing
-/
theorem getVert_append' (p : G.Walk u v) (q : G.Walk v w) (i : Nat) :
    (p.append q).getVert i = if i <= p.length then p.getVert i else q.getVert (i - p.length) := by
  induction p generalizing i <;> cases i <;> simp [*]

/--
theorem `getVert_reverse` / 定理 `getVert_reverse`

English:
theorem getVert_reverse
  given: {u v : V} (p : G.Walk u v) (i : Nat)
  proof: by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [reverse_cons, getVert_append, length_reverse, ih, length_cons]
    split_ifs
    next hi => simp [Nat.succ_sub hi.le]
    next hi =>
      obtain rfl | hi' := eq_or_gt_of_not_lt hi
      · simp
      · rw [Nat.eq_add_of_sub_eq (N

中文:
定理 getVert_reverse
  条件: {u v : V} (p : G.Walk u v) (i : 自然数)
  证明: by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [reverse_cons, getVert_append, length_reverse, ih, length_cons]
    split_ifs
    next hi => simp [Nat.succ_sub hi.le]
    next hi =>
      obtain rfl | hi' := eq_or_gt_of_not_lt hi
      · simp
      · rw [Nat.eq_add_of_sub_eq (N

Depends on / 依赖: Nat.eq_add_of_sub_eq, Nat.sub_eq_zero_of_le, Nat.sub_pos_of_lt, Nat.succ_sub, eq_add_of_sub_eq, eq_or_gt_of_not_lt, getVert_append, hi.le, length_cons, length_reverse, reverse_cons, split_ifs, sub_eq_zero_of_le, sub_pos_of_lt, succ_sub
-/
theorem getVert_reverse {u v : V} (p : G.Walk u v) (i : Nat) :
    p.reverse.getVert i = p.getVert (p.length - i) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [reverse_cons, getVert_append, length_reverse, ih, length_cons]
    split_ifs
    next hi => simp [Nat.succ_sub hi.le]
    next hi =>
      obtain rfl | hi' := eq_or_gt_of_not_lt hi
      · simp
      · rw [Nat.eq_add_of_sub_eq (Nat.sub_pos_of_lt hi') rfl, Nat.sub_eq_zero_of_le hi']
        simp

section ConcatRec

variable {motive : forall u v : V, G.Walk u v -> Sort*} (Hnil : forall {u : V}, motive u u nil)
  (Hconcat : forall {u v w : V} (p : G.Walk u v) (h : G.Adj v w), motive u v p -> motive u w (p.concat h))

/--
Definition of `concatRecAux` / `concatRecAux` 的定义

English:
definition concatRecAux
  signature: {u v : V}

中文:
定义 concatRecAux
  签名: {u v : V}
-/
def concatRecAux {u v : V} : (p : G.Walk u v) -> motive v u p.reverse
  | nil => Hnil
  | cons h p => reverse_cons h p ▸ Hconcat p.reverse h.symm (concatRecAux p)

/-- Recursor on walks by inducting on `SimpleGraph.Walk.concat`.

This is inducting from the opposite end of the walk compared
to `SimpleGraph.Walk.rec`, which inducts on `SimpleGraph.Walk.cons`. -/
@[elab_as_elim]
/--
Definition of `concatRec` / `concatRec` 的定义

English:
definition concatRec
  signature: {u v : V} (p : G.Walk u v)
  body: reverse_reverse p ▸ concatRecAux @Hnil @Hconcat p.reverse

@[simp]

中文:
定义 concatRec
  签名: {u v : V} (p : G.Walk u v)
  定义体: reverse_reverse p ▸ concatRecAux @Hnil @Hconcat p.reverse

@[simp]

Depends on / 依赖: Hconcat, concatRecAux, p.reverse, reverse, reverse_reverse
-/
def concatRec {u v : V} (p : G.Walk u v) : motive u v p :=
  reverse_reverse p ▸ concatRecAux @Hnil @Hconcat p.reverse

@[simp]
/--
theorem `concatRec_nil` / 定理 `concatRec_nil`

English:
theorem concatRec_nil
  given: (u : V)
  proof: rfl

中文:
定理 concatRec_nil
  条件: (u : V)
  证明: rfl
-/
theorem concatRec_nil (u : V) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (nil : G.Walk u u) = Hnil := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `concatRec_concat` / 定理 `concatRec_concat`

English:
theorem concatRec_concat
  given: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  proof: by
  simp only [concatRec]
  apply eq_of_heq (rec_heq_of_heq _ _)
  trans concatRecAux @Hnil @Hconcat (cons h.symm p.reverse)
  · congr
    simp
  · rw [concatRecAux, eqRec_heq_iff]
    congr <;> simp

中文:
定理 concatRec_concat
  条件: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  证明: by
  simp only [concatRec]
  apply eq_of_heq (rec_heq_of_heq _ _)
  trans concatRecAux @Hnil @Hconcat (cons h.symm p.reverse)
  · congr
    simp
  · rw [concatRecAux, eqRec_heq_iff]
    congr <;> simp

Depends on / 依赖: Hconcat, concatRec, concatRecAux, eqRec_heq_iff, eq_of_heq, h.symm, p.reverse, rec_heq_of_heq, reverse
-/
theorem concatRec_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (p.concat h) =
      Hconcat p h (concatRec @Hnil @Hconcat p) := by
  simp only [concatRec]
  apply eq_of_heq (rec_heq_of_heq _ _)
  trans concatRecAux @Hnil @Hconcat (cons h.symm p.reverse)
  · congr
    simp
  · rw [concatRecAux, eqRec_heq_iff]
    congr <;> simp

end ConcatRec

/--
theorem `concat_ne_nil` / 定理 `concat_ne_nil`

English:
theorem concat_ne_nil
  given: {u v : V} (p : G.Walk u v) (h : G.Adj v u)
  statement: p.concat h != nil
  proof: by
  cases p <;> simp [concat]

中文:
定理 concat_ne_nil
  条件: {u v : V} (p : G.Walk u v) (h : G.Adj v u)
  结论: p.concat h != nil
  证明: by
  cases p <;> simp [concat]

Depends on / 依赖: concat
-/
theorem concat_ne_nil {u v : V} (p : G.Walk u v) (h : G.Adj v u) : p.concat h != nil := by
  cases p <;> simp [concat]

/--
theorem `concat_inj` / 定理 `concat_inj`

English:
theorem concat_inj
  statement: {u v v' w : V} {p : G.Walk u v} {h : G.Adj v w} {p' : G.Walk u v'}
  proof: by
  induction p with
  | nil =>
    cases p'
    · exact ⟨rfl, rfl⟩
    · simp only [concat_nil, concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact (concat_ne_nil _ _ (heq_iff_eq.mp he).symm).elim
  | cons _ _ ih =>
    rw [concat_cons] at he
    cases p'
    · simp only [conca

中文:
定理 concat_inj
  结论: {u v v' w : V} {p : G.Walk u v} {h : G.Adj v w} {p' : G.Walk u v'}
  证明: by
  induction p with
  | nil =>
    cases p'
    · exact ⟨rfl, rfl⟩
    · simp only [concat_nil, concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact (concat_ne_nil _ _ (heq_iff_eq.mp he).symm).elim
  | cons _ _ ih =>
    rw [concat_cons] at he
    cases p'
    · simp only [conca

Depends on / 依赖: concat_cons, concat_ne_nil, concat_nil, cons.injEq, heq_iff_eq, heq_iff_eq.mp
-/
theorem concat_inj {u v v' w : V} {p : G.Walk u v} {h : G.Adj v w} {p' : G.Walk u v'}
    {h' : G.Adj v' w} (he : p.concat h = p'.concat h') : exists hv : v = v', p.copy rfl hv = p' := by
  induction p with
  | nil =>
    cases p'
    · exact ⟨rfl, rfl⟩
    · simp only [concat_nil, concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact (concat_ne_nil _ _ (heq_iff_eq.mp he).symm).elim
  | cons _ _ ih =>
    rw [concat_cons] at he
    cases p'
    · simp only [concat_nil, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact (concat_ne_nil _ _ (heq_iff_eq.mp he)).elim
    · rw [concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih (heq_iff_eq.mp he)
      exact ⟨rfl, rfl⟩

@[simp]
/--
theorem `support_concat` / 定理 `support_concat`

English:
theorem support_concat
  given: (p : G.Walk u v) (h : G.Adj v w)
  proof: by
  induction p <;> simp [*, concat_nil]

@[simp]

中文:
定理 support_concat
  条件: (p : G.Walk u v) (h : G.Adj v w)
  证明: by
  induction p <;> simp [*, concat_nil]

@[simp]

Depends on / 依赖: concat_nil
-/
theorem support_concat (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).support = p.support ++ [w] := by
  induction p <;> simp [*, concat_nil]

@[simp]
/--
theorem `support_copy` / 定理 `support_copy`

English:
theorem support_copy
  given: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

中文:
定理 support_copy
  条件: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl
-/
theorem support_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).support = p.support := by
  subst_vars
  rfl

/--
theorem `support_append` / 定理 `support_append`

English:
theorem support_append
  given: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by
  induction p <;> cases p' <;> simp [*]

@[simp]

中文:
定理 support_append
  条件: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by
  induction p <;> cases p' <;> simp [*]

@[simp]
-/
theorem support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support ++ p'.support.tail := by
  induction p <;> cases p' <;> simp [*]

@[simp]
/--
theorem `support_reverse` / 定理 `support_reverse`

English:
theorem support_reverse
  given: {u v : V} (p : G.Walk u v)
  statement: p.reverse.support = p.support.reverse
  proof: by
  induction p <;> simp [support_append, *]

中文:
定理 support_reverse
  条件: {u v : V} (p : G.Walk u v)
  结论: p.reverse.support = p.support.reverse
  证明: by
  induction p <;> simp [support_append, *]

Depends on / 依赖: support_append
-/
theorem support_reverse {u v : V} (p : G.Walk u v) : p.reverse.support = p.support.reverse := by
  induction p <;> simp [support_append, *]

/--
theorem `support_append_eq_support_dropLast_append` / 定理 `support_append_eq_support_dropLast_append`

English:
theorem support_append_eq_support_dropLast_append
  given: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by
  induction p <;> simp_all [List.dropLast_cons_of_ne_nil]

中文:
定理 support_append_eq_support_dropLast_append
  条件: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by
  induction p <;> simp_all [List.dropLast_cons_of_ne_nil]

Depends on / 依赖: List.dropLast_cons_of_ne_nil, dropLast_cons_of_ne_nil
-/
theorem support_append_eq_support_dropLast_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support.dropLast ++ p'.support := by
  induction p <;> simp_all [List.dropLast_cons_of_ne_nil]

/--
theorem `tail_support_append` / 定理 `tail_support_append`

English:
theorem tail_support_append
  given: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by
  rw [support_append]; rw [List.tail_append_of_ne_nil (support_ne_nil _)]

@[simp]

中文:
定理 tail_support_append
  条件: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by
  rw [support_append]; rw [List.tail_append_of_ne_nil (support_ne_nil _)]

@[simp]

Depends on / 依赖: List.tail_append_of_ne_nil, support_append, support_ne_nil, tail_append_of_ne_nil
-/
theorem tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support.tail = p.support.tail ++ p'.support.tail := by
  rw [support_append]; rw [List.tail_append_of_ne_nil (support_ne_nil _)]

@[simp]
/--
theorem `dropLast_support_concat` / 定理 `dropLast_support_concat`

English:
theorem dropLast_support_concat
  given: (p : G.Walk u v)
  statement: p.support.dropLast ++ [v] = p.support
  proof: by
  cases p with | nil => rfl | cons h p
  have ⟨_, _, _, hp⟩ := p.exists_cons_eq_concat h
  simp [hp]

@[deprecated dropLast_support_concat (since := "2026-03-16")]

中文:
定理 dropLast_support_concat
  条件: (p : G.Walk u v)
  结论: p.support.dropLast ++ [v] = p.support
  证明: by
  cases p with | nil => rfl | cons h p
  have ⟨_, _, _, hp⟩ := p.exists_cons_eq_concat h
  simp [hp]

@[deprecated dropLast_support_concat (since := "2026-03-16")]

Depends on / 依赖: exists_cons_eq_concat, p.exists_cons_eq_concat
-/
theorem dropLast_support_concat (p : G.Walk u v) : p.support.dropLast ++ [v] = p.support := by
  cases p with | nil => rfl | cons h p
  have ⟨_, _, _, hp⟩ := p.exists_cons_eq_concat h
  simp [hp]

@[deprecated dropLast_support_concat (since := "2026-03-16")]
/--
theorem `support_eq_concat` / 定理 `support_eq_concat`

English:
theorem support_eq_concat
  given: (p : G.Walk u v)
  statement: p.support = p.support.dropLast.concat v
  proof: by
  simp

中文:
定理 support_eq_concat
  条件: (p : G.Walk u v)
  结论: p.support = p.support.dropLast.concat v
  证明: by
  simp
-/
theorem support_eq_concat (p : G.Walk u v) : p.support = p.support.dropLast.concat v := by
  simp

/--
lemma `ext_support` / 引理 `ext_support`

English:
lemma ext_support
  given: {u v} {p q : G.Walk u v} (h : p.support = q.support)
  statement: p = q
  proof: by
  refine darts_injective (Dart.toProd_injective.list_map (List.rightInverse_unzip_zip.injective ?_))
  have : Prod.fst ∘ Dart.toProd = fun d : G.Dart => d.fst := rfl
  have : Prod.snd ∘ Dart.toProd = fun d : G.Dart => d.snd := rfl
  grind [map_fst_darts, map_snd_darts]

@[simp]

中文:
引理 ext_support
  条件: {u v} {p q : G.Walk u v} (h : p.support = q.support)
  结论: p = q
  证明: by
  refine darts_injective (Dart.toProd_injective.list_map (List.rightInverse_unzip_zip.injective ?_))
  have : Prod.fst ∘ Dart.toProd = fun d : G.Dart => d.fst := rfl
  have : Prod.snd ∘ Dart.toProd = fun d : G.Dart => d.snd := rfl
  grind [map_fst_darts, map_snd_darts]

@[simp]

Depends on / 依赖: Dart.toProd, Dart.toProd_injective.list_map, G.Dart, List.rightInverse_unzip_zip.injective, Prod.fst, Prod.snd, d.fst, d.snd, darts_injective, injective, list_map, map_fst_darts, map_snd_darts, rightInverse_unzip_zip, toProd, toProd_injective
-/
lemma ext_support {u v} {p q : G.Walk u v} (h : p.support = q.support) : p = q := by
  refine darts_injective (Dart.toProd_injective.list_map (List.rightInverse_unzip_zip.injective ?_))
  have : Prod.fst ∘ Dart.toProd = fun d : G.Dart => d.fst := rfl
  have : Prod.snd ∘ Dart.toProd = fun d : G.Dart => d.snd := rfl
  grind [map_fst_darts, map_snd_darts]

@[simp]
/--
theorem `mem_tail_support_append_iff` / 定理 `mem_tail_support_append_iff`

English:
theorem mem_tail_support_append_iff
  given: {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by
  rw [tail_support_append]; rw [List.mem_append]

@[simp]

中文:
定理 mem_tail_support_append_iff
  条件: {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by
  rw [tail_support_append]; rw [List.mem_append]

@[simp]

Depends on / 依赖: List.mem_append, mem_append, tail_support_append
-/
theorem mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t in (p.append p').support.tail ↔ t in p.support.tail ∨ t in p'.support.tail := by
  rw [tail_support_append]; rw [List.mem_append]

@[simp]
/--
theorem `mem_support_append_iff` / 定理 `mem_support_append_iff`

English:
theorem mem_support_append_iff
  given: {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by
  grind [mem_support_iff, mem_tail_support_append_iff, end_mem_tail_support_of_ne]

中文:
定理 mem_support_append_iff
  条件: {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by
  grind [mem_support_iff, mem_tail_support_append_iff, end_mem_tail_support_of_ne]

Depends on / 依赖: end_mem_tail_support_of_ne, mem_support_iff, mem_tail_support_append_iff
-/
theorem mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t in (p.append p').support ↔ t in p.support ∨ t in p'.support := by
  grind [mem_support_iff, mem_tail_support_append_iff, end_mem_tail_support_of_ne]

/--
theorem `support_prefix_support_concat` / 定理 `support_prefix_support_concat`

English:
theorem support_prefix_support_concat
  given: {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w)
  proof: by
  simp

中文:
定理 support_prefix_support_concat
  条件: {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w)
  证明: by
  simp
-/
theorem support_prefix_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    p.support <+: (p.concat hadj).support := by
  simp

/--
theorem `support_subset_support_concat` / 定理 `support_subset_support_concat`

English:
theorem support_subset_support_concat
  given: {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w)
  proof: by
  simp

中文:
定理 support_subset_support_concat
  条件: {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w)
  证明: by
  simp
-/
theorem support_subset_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    p.support subseteq (p.concat hadj).support := by
  simp

/--
theorem `support_prefix_support_append` / 定理 `support_prefix_support_append`

English:
theorem support_prefix_support_append
  statement: {V : Type u} {G : SimpleGraph V} {u v w : V}
  proof: by
  simp [support_append]

@[simp]

中文:
定理 support_prefix_support_append
  结论: {V : 类型u} {G : SimpleGraph V} {u v w : V}
  证明: by
  simp [support_append]

@[simp]

Depends on / 依赖: support_append
-/
theorem support_prefix_support_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support <+: (p.append q).support := by
  simp [support_append]

@[simp]
/--
theorem `support_subset_support_append_left` / 定理 `support_subset_support_append_left`

English:
theorem support_subset_support_append_left
  statement: {V : Type u} {G : SimpleGraph V} {u v w : V}
  proof: .subset support_prefix_support_append p q

@[deprecated (since := "2026-05-25")]
alias subset_support_append_left := support_subset_support_append_left

中文:
定理 support_subset_support_append_left
  结论: {V : 类型u} {G : SimpleGraph V} {u v w : V}
  证明: .subset support_prefix_support_append p q

@[deprecated (since := "2026-05-25")]
alias subset_support_append_left := support_subset_support_append_left

Depends on / 依赖: subset, support_prefix_support_append
-/
theorem support_subset_support_append_left {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support subseteq (p.append q).support :=
.subset support_prefix_support_append p q

@[deprecated (since := "2026-05-25")]
alias subset_support_append_left := support_subset_support_append_left

/--
theorem `support_suffix_support_append` / 定理 `support_suffix_support_append`

English:
theorem support_suffix_support_append
  statement: {V : Type u} {G : SimpleGraph V} {u v w : V}
  proof: by
  simp [support_append_eq_support_dropLast_append]

@[simp]

中文:
定理 support_suffix_support_append
  结论: {V : 类型u} {G : SimpleGraph V} {u v w : V}
  证明: by
  simp [support_append_eq_support_dropLast_append]

@[simp]

Depends on / 依赖: support_append_eq_support_dropLast_append
-/
theorem support_suffix_support_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support <:+ (p.append q).support := by
  simp [support_append_eq_support_dropLast_append]

@[simp]
/--
theorem `support_subset_support_append_right` / 定理 `support_subset_support_append_right`

English:
theorem support_subset_support_append_right
  statement: {V : Type u} {G : SimpleGraph V} {u v w : V}
  proof: .subset support_suffix_support_append p q

@[deprecated (since := "2026-05-25")]
alias subset_support_append_right := support_subset_support_append_right

中文:
定理 support_subset_support_append_right
  结论: {V : 类型u} {G : SimpleGraph V} {u v w : V}
  证明: .subset support_suffix_support_append p q

@[deprecated (since := "2026-05-25")]
alias subset_support_append_right := support_subset_support_append_right

Depends on / 依赖: subset, support_suffix_support_append
-/
theorem support_subset_support_append_right {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support subseteq (p.append q).support :=
.subset support_suffix_support_append p q

@[deprecated (since := "2026-05-25")]
alias subset_support_append_right := support_subset_support_append_right

/--
theorem `coe_support_append` / 定理 `coe_support_append`

English:
theorem coe_support_append
  given: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by
  rw [support_append]; rw [← Multiset.coe_add]; rw [coe_support]

中文:
定理 coe_support_append
  条件: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by
  rw [support_append]; rw [← Multiset.coe_add]; rw [coe_support]

Depends on / 依赖: Multiset, Multiset.coe_add, coe_add, coe_support, support_append
-/
theorem coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = {u} + p.support.tail + p'.support.tail := by
  rw [support_append]; rw [← Multiset.coe_add]; rw [coe_support]

/--
theorem `coe_support_append'` / 定理 `coe_support_append'`

English:
theorem coe_support_append'
  given: [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by
  simp_rw [support_append, ← Multiset.coe_add, coe_support, add_comm ({v} : Multiset V),
    ← add_assoc, add_tsub_cancel_right]

中文:
定理 coe_support_append'
  条件: [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by
  simp_rw [support_append, ← Multiset.coe_add, coe_support, add_comm ({v} : Multiset V),
    ← add_assoc, add_tsub_cancel_right]

Depends on / 依赖: Multiset, Multiset.coe_add, add_assoc, add_comm, add_tsub_cancel_right, coe_add, coe_support, simp_rw, support_append
-/
theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = p.support + p'.support - {v} := by
  simp_rw [support_append, ← Multiset.coe_add, coe_support, add_comm ({v} : Multiset V),
    ← add_assoc, add_tsub_cancel_right]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofSupport_support` / 定理 `ofSupport_support`

English:
theorem ofSupport_support
  given: {u v : V} (p : G.Walk u v)
  proof: by
  match p with
  | nil => rfl
  | cons (v := w) h .nil => rfl
  | cons (v := u') h₁ (.cons (v := v') h₂ p) =>
.ofSupport_support have := p.cons h₂
    simp at this
    simp [this]

@[simp]

中文:
定理 ofSupport_support
  条件: {u v : V} (p : G.Walk u v)
  证明: by
  match p with
  | nil => rfl
  | cons (v := w) h .nil => rfl
  | cons (v := u') h₁ (.cons (v := v') h₂ p) =>
.ofSupport_support have := p.cons h₂
    simp at this
    simp [this]

@[simp]

Depends on / 依赖: ofSupport_support, p.cons
-/
theorem ofSupport_support {u v : V} (p : G.Walk u v) :
    ofSupport _ p.support_ne_nil p.isChain_adj_support = p.copy (by simp) (by simp) := by
  match p with
  | nil => rfl
  | cons (v := w) h .nil => rfl
  | cons (v := u') h₁ (.cons (v := v') h₂ p) =>
.ofSupport_support have := p.cons h₂
    simp at this
    simp [this]

@[simp]
/--
theorem `darts_concat` / 定理 `darts_concat`

English:
theorem darts_concat
  given: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  proof: by
  induction p <;> simp [*, concat_nil]

@[simp]

中文:
定理 darts_concat
  条件: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  证明: by
  induction p <;> simp [*, concat_nil]

@[simp]

Depends on / 依赖: concat_nil
-/
theorem darts_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).darts = p.darts.concat ⟨(v, w), h⟩ := by
  induction p <;> simp [*, concat_nil]

@[simp]
/--
theorem `darts_copy` / 定理 `darts_copy`

English:
theorem darts_copy
  given: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 darts_copy
  条件: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem darts_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).darts = p.darts := by
  subst_vars
  rfl

@[simp]
/--
theorem `darts_append` / 定理 `darts_append`

English:
theorem darts_append
  given: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by
  induction p <;> simp [*]

@[simp]

中文:
定理 darts_append
  条件: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by
  induction p <;> simp [*]

@[simp]
-/
theorem darts_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').darts = p.darts ++ p'.darts := by
  induction p <;> simp [*]

@[simp]
/--
theorem `darts_reverse` / 定理 `darts_reverse`

English:
theorem darts_reverse
  given: {u v : V} (p : G.Walk u v)
  proof: by
  induction p <;> simp [*]

中文:
定理 darts_reverse
  条件: {u v : V} (p : G.Walk u v)
  证明: by
  induction p <;> simp [*]
-/
theorem darts_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.darts = (p.darts.map Dart.symm).reverse := by
  induction p <;> simp [*]

/--
theorem `mem_darts_reverse` / 定理 `mem_darts_reverse`

English:
theorem mem_darts_reverse
  given: {u v : V} {d : G.Dart} {p : G.Walk u v}
  proof: by simp

中文:
定理 mem_darts_reverse
  条件: {u v : V} {d : G.Dart} {p : G.Walk u v}
  证明: by simp
-/
theorem mem_darts_reverse {u v : V} {d : G.Dart} {p : G.Walk u v} :
    d in p.reverse.darts ↔ d.symm in p.darts := by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `ofDarts_darts` / 定理 `ofDarts_darts`

English:
theorem ofDarts_darts
  given: {u v : V} {p : G.Walk u v} (hp : ¬p.Nil)
  proof: by
  match p, hp with
  | nil, hp => simp at hp
  | cons (v := w) h .nil, _ => rfl
  | cons (v := u') h₁ (.cons (v := v') h₂ p), _ =>
.ofDarts_darts not_nil_cons have := p.cons h₂
    simp at this
    simp [this]

@[simp]

中文:
定理 ofDarts_darts
  条件: {u v : V} {p : G.Walk u v} (hp : ¬p.Nil)
  证明: by
  match p, hp with
  | nil, hp => simp at hp
  | cons (v := w) h .nil, _ => rfl
  | cons (v := u') h₁ (.cons (v := v') h₂ p), _ =>
.ofDarts_darts not_nil_cons have := p.cons h₂
    simp at this
    simp [this]

@[simp]

Depends on / 依赖: not_nil_cons, ofDarts_darts, p.cons
-/
theorem ofDarts_darts {u v : V} {p : G.Walk u v} (hp : ¬p.Nil) :
    ofDarts _ (darts_eq_nil.not.mpr hp) p.isChain_dartAdj_darts = p.copy (by simp) (by simp) := by
  match p, hp with
  | nil, hp => simp at hp
  | cons (v := w) h .nil, _ => rfl
  | cons (v := u') h₁ (.cons (v := v') h₂ p), _ =>
.ofDarts_darts not_nil_cons have := p.cons h₂
    simp at this
    simp [this]

@[simp]
/--
theorem `edges_concat` / 定理 `edges_concat`

English:
theorem edges_concat
  given: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  proof: by simp [edges]

@[simp]

中文:
定理 edges_concat
  条件: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  证明: by simp [edges]

@[simp]
-/
theorem edges_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edges = p.edges.concat s(v, w) := by simp [edges]

@[simp]
/--
theorem `edges_copy` / 定理 `edges_copy`

English:
theorem edges_copy
  given: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

@[simp]

中文:
定理 edges_copy
  条件: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl

@[simp]
-/
theorem edges_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edges = p.edges := by
  subst_vars
  rfl

@[simp]
/--
theorem `edges_append` / 定理 `edges_append`

English:
theorem edges_append
  given: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  proof: by simp [edges]

@[simp]

中文:
定理 edges_append
  条件: {u v w : V} (p : G.Walk u v) (p' : G.Walk v w)
  证明: by simp [edges]

@[simp]
-/
theorem edges_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').edges = p.edges ++ p'.edges := by simp [edges]

@[simp]
/--
theorem `edges_reverse` / 定理 `edges_reverse`

English:
theorem edges_reverse
  given: {u v : V} (p : G.Walk u v)
  statement: p.reverse.edges = p.edges.reverse
  proof: by
  simp [edges]

中文:
定理 edges_reverse
  条件: {u v : V} (p : G.Walk u v)
  结论: p.reverse.edges = p.edges.reverse
  证明: by
  simp [edges]
-/
theorem edges_reverse {u v : V} (p : G.Walk u v) : p.reverse.edges = p.edges.reverse := by
  simp [edges]

/--
theorem `dart_snd_mem_support_of_mem_darts` / 定理 `dart_snd_mem_support_of_mem_darts`

English:
theorem dart_snd_mem_support_of_mem_darts
  statement: {u v : V} (p : G.Walk u v) {d : G.Dart}
  proof: by
  simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm in p.reverse.darts)

中文:
定理 dart_snd_mem_support_of_mem_darts
  结论: {u v : V} (p : G.Walk u v) {d : G.Dart}
  证明: by
  simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm in p.reverse.darts)

Depends on / 依赖: d.symm, dart_fst_mem_support_of_mem_darts, p.reverse.dart_fst_mem_support_of_mem_darts, p.reverse.darts, reverse
-/
theorem dart_snd_mem_support_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart}
    (h : d in p.darts) : d.snd in p.support := by
  simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm in p.reverse.darts)

/--
theorem `fst_mem_support_of_mem_edges` / 定理 `fst_mem_support_of_mem_edges`

English:
theorem fst_mem_support_of_mem_edges
  given: {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges)
  proof: by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp he
  rw [dart_edge_eq_mk'_iff'] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact dart_fst_mem_support_of_mem_darts _ hd
  · exact dart_snd_mem_support_of_mem_darts _ hd

中文:
定理 fst_mem_support_of_mem_edges
  条件: {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges)
  证明: by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp he
  rw [dart_edge_eq_mk'_iff'] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact dart_fst_mem_support_of_mem_darts _ hd
  · exact dart_snd_mem_support_of_mem_darts _ hd

Depends on / 依赖: List.mem_map.mp, _iff, dart_edge_eq_mk, dart_fst_mem_support_of_mem_darts, dart_snd_mem_support_of_mem_darts, mem_map
-/
theorem fst_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) :
    t in p.support := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp he
  rw [dart_edge_eq_mk'_iff'] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact dart_fst_mem_support_of_mem_darts _ hd
  · exact dart_snd_mem_support_of_mem_darts _ hd

/--
theorem `snd_mem_support_of_mem_edges` / 定理 `snd_mem_support_of_mem_edges`

English:
theorem snd_mem_support_of_mem_edges
  given: {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges)
  proof: p.fst_mem_support_of_mem_edges (Sym2.eq_swap ▸ he)

中文:
定理 snd_mem_support_of_mem_edges
  条件: {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges)
  证明: p.fst_mem_support_of_mem_edges (Sym2.eq_swap ▸ he)

Depends on / 依赖: Sym2.eq_swap, eq_swap, fst_mem_support_of_mem_edges, p.fst_mem_support_of_mem_edges
-/
theorem snd_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) :
    u in p.support :=
  p.fst_mem_support_of_mem_edges (Sym2.eq_swap ▸ he)

/--
theorem `mem_support_of_mem_edges` / 定理 `mem_support_of_mem_edges`

English:
theorem mem_support_of_mem_edges
  statement: {u v w : V} {e : Sym2 V} {p : G.Walk u v} (he : e in p.edges)
  proof: hv.elim fun _ heq => p.fst_mem_support_of_mem_edges heq ▸ he

中文:
定理 mem_support_of_mem_edges
  结论: {u v w : V} {e : Sym2 V} {p : G.Walk u v} (he : e in p.edges)
  证明: hv.elim fun _ heq => p.fst_mem_support_of_mem_edges heq ▸ he

Depends on / 依赖: fst_mem_support_of_mem_edges, hv.elim, p.fst_mem_support_of_mem_edges
-/
theorem mem_support_of_mem_edges {u v w : V} {e : Sym2 V} {p : G.Walk u v} (he : e in p.edges)
    (hv : w in e) : w in p.support :=
hv.elim fun _ heq => p.fst_mem_support_of_mem_edges heq ▸ he

/--
theorem `edges_nodup_of_support_nodup` / 定理 `edges_nodup_of_support_nodup`

English:
theorem edges_nodup_of_support_nodup
  given: {u v : V} {p : G.Walk u v} (h : p.support.Nodup)
  proof: by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [support_cons, List.nodup_cons, edges_cons] at h ⊢
    exact ⟨(h.1 <| fst_mem_support_of_mem_edges p' ·), ih h.2⟩

中文:
定理 edges_nodup_of_support_nodup
  条件: {u v : V} {p : G.Walk u v} (h : p.support.Nodup)
  证明: by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [support_cons, List.nodup_cons, edges_cons] at h ⊢
    exact ⟨(h.1 <| fst_mem_support_of_mem_edges p' ·), ih h.2⟩

Depends on / 依赖: List.nodup_cons, edges_cons, fst_mem_support_of_mem_edges, nodup_cons, support_cons
-/
theorem edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.edges.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [support_cons, List.nodup_cons, edges_cons] at h ⊢
    exact ⟨(h.1 <| fst_mem_support_of_mem_edges p' ·), ih h.2⟩

/--
theorem `nodup_tail_support_reverse` / 定理 `nodup_tail_support_reverse`

English:
theorem nodup_tail_support_reverse
  given: {u : V} {p : G.Walk u u}
  proof: by
  refine p.support_reverse ▸ p.support.nodup_tail_reverse ?_
  rw [← getVert_eq_support_getElem? _ (by lia)]; rw [List.getLast?_eq_getElem?]; rw [← getVert_eq_support_getElem? _ (by rw [Walk.length_support]; lia)]
  simp

@[simp]

中文:
定理 nodup_tail_support_reverse
  条件: {u : V} {p : G.Walk u u}
  证明: by
  refine p.support_reverse ▸ p.support.nodup_tail_reverse ?_
  rw [← getVert_eq_support_getElem? _ (by lia)]; rw [List.getLast?_eq_getElem?]; rw [← getVert_eq_support_getElem? _ (by rw [Walk.length_support]; lia)]
  simp

@[simp]

Depends on / 依赖: List.getLast, Walk.length_support, _eq_getElem, getLast, getVert_eq_support_getElem, length_support, nodup_tail_reverse, p.support.nodup_tail_reverse, p.support_reverse, support, support_reverse
-/
theorem nodup_tail_support_reverse {u : V} {p : G.Walk u u} :
    p.reverse.support.tail.Nodup ↔ p.support.tail.Nodup := by
  refine p.support_reverse ▸ p.support.nodup_tail_reverse ?_
  rw [← getVert_eq_support_getElem? _ (by lia)]; rw [List.getLast?_eq_getElem?]; rw [← getVert_eq_support_getElem? _ (by rw [Walk.length_support]; lia)]
  simp

@[simp]
/--
lemma `edgeSet_reverse` / 引理 `edgeSet_reverse`

English:
lemma edgeSet_reverse
  given: {u v : V} (p : G.Walk u v)
  statement: p.reverse.edgeSet = p.edgeSet
  proof: by ext; simp

@[simp]

中文:
引理 edgeSet_reverse
  条件: {u v : V} (p : G.Walk u v)
  结论: p.reverse.edgeSet = p.edgeSet
  证明: by ext; simp

@[simp]
-/
lemma edgeSet_reverse {u v : V} (p : G.Walk u v) : p.reverse.edgeSet = p.edgeSet := by ext; simp

@[simp]
/--
theorem `edgeSet_concat` / 定理 `edgeSet_concat`

English:
theorem edgeSet_concat
  given: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  proof: by ext; simp [or_comm]

中文:
定理 edgeSet_concat
  条件: {u v w : V} (p : G.Walk u v) (h : G.Adj v w)
  证明: by ext; simp [or_comm]

Depends on / 依赖: or_comm
-/
theorem edgeSet_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edgeSet = insert s(v, w) p.edgeSet := by ext; simp [or_comm]

/--
theorem `edgeSet_append` / 定理 `edgeSet_append`

English:
theorem edgeSet_append
  given: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  proof: by ext; simp

@[simp]

中文:
定理 edgeSet_append
  条件: {u v w : V} (p : G.Walk u v) (q : G.Walk v w)
  证明: by ext; simp

@[simp]
-/
theorem edgeSet_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).edgeSet = p.edgeSet union q.edgeSet := by ext; simp

@[simp]
/--
theorem `edgeSet_copy` / 定理 `edgeSet_copy`

English:
theorem edgeSet_copy
  given: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  proof: by ext; simp

@[simp]

中文:
定理 edgeSet_copy
  条件: {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v')
  证明: by ext; simp

@[simp]
-/
theorem edgeSet_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edgeSet = p.edgeSet := by ext; simp

@[simp]
/--
lemma `nil_append_iff` / 引理 `nil_append_iff`

English:
lemma nil_append_iff
  given: {p : G.Walk u v} {q : G.Walk v w}
  statement: (p.append q).Nil ↔ p.Nil ∧ q.Nil
  proof: by
  cases p <;> cases q <;> simp

中文:
引理 nil_append_iff
  条件: {p : G.Walk u v} {q : G.Walk v w}
  结论: (p.append q).Nil ↔ p.Nil ∧ q.Nil
  证明: by
  cases p <;> cases q <;> simp
-/
lemma nil_append_iff {p : G.Walk u v} {q : G.Walk v w} : (p.append q).Nil ↔ p.Nil ∧ q.Nil := by
  cases p <;> cases q <;> simp

/--
lemma `Nil.append` / 引理 `Nil.append`

English:
lemma Nil.append
  given: {p : G.Walk u v} {q : G.Walk v w} (hp : p.Nil) (hq : q.Nil)
  proof: by
  simp [hp, hq]

@[simp]

中文:
引理 Nil.append
  条件: {p : G.Walk u v} {q : G.Walk v w} (hp : p.Nil) (hq : q.Nil)
  证明: by
  simp [hp, hq]

@[simp]
-/
lemma Nil.append {p : G.Walk u v} {q : G.Walk v w} (hp : p.Nil) (hq : q.Nil) :
    (p.append q).Nil := by
  simp [hp, hq]

@[simp]
/--
lemma `nil_reverse` / 引理 `nil_reverse`

English:
lemma nil_reverse
  given: {p : G.Walk v w}
  statement: p.reverse.Nil ↔ p.Nil
  proof: by
  cases p <;> simp

中文:
引理 nil_reverse
  条件: {p : G.Walk v w}
  结论: p.reverse.Nil ↔ p.Nil
  证明: by
  cases p <;> simp
-/
lemma nil_reverse {p : G.Walk v w} : p.reverse.Nil ↔ p.Nil := by
  cases p <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `drop` / `drop` 的定义

English:
definition drop
  signature: {u v : V} (p : G.Walk u v) (n : Nat)
  body: match p, n with
  | .nil, _ => .nil
  | p, 0 => p.copy (getVert_zero p).symm rfl
  | .cons _ q, (n + 1) => q.drop n

@[simp]

中文:
定义 drop
  签名: {u v : V} (p : G.Walk u v) (n : 自然数)
  定义体: match p, n with
  | .nil, _ => .nil
  | p, 0 => p.copy (getVert_zero p).symm rfl
  | .cons _ q, (n + 1) => q.drop n

@[simp]

Depends on / 依赖: getVert_zero, p.copy, q.drop
-/
def drop {u v : V} (p : G.Walk u v) (n : Nat) : G.Walk (p.getVert n) v :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => p.copy (getVert_zero p).symm rfl
  | .cons _ q, (n + 1) => q.drop n

@[simp]
/--
lemma `drop_length` / 引理 `drop_length`

English:
lemma drop_length
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.drop n).length = p.length - n
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

中文:
引理 drop_length
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.drop n).length = p.length - n
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

Depends on / 依赖: generalizing
-/
lemma drop_length (p : G.Walk u v) (n : Nat) : (p.drop n).length = p.length - n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `drop_getVert` / 引理 `drop_getVert`

English:
lemma drop_getVert
  given: (p : G.Walk u v) (n m : Nat)
  statement: (p.drop n).getVert m = p.getVert (n + m)
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, drop, add_right_comm]

中文:
引理 drop_getVert
  条件: (p : G.Walk u v) (n m : 自然数)
  结论: (p.drop n).getVert m = p.getVert (n + m)
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, drop, add_right_comm]

Depends on / 依赖: add_right_comm, generalizing
-/
lemma drop_getVert (p : G.Walk u v) (n m : Nat) : (p.drop n).getVert m = p.getVert (n + m) := by
  induction p generalizing n <;> cases n <;> simp [*, drop, add_right_comm]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `drop_add_heq` / 引理 `drop_add_heq`

English:
lemma drop_add_heq
  given: (p : G.Walk u v) (n m : Nat)
  statement: p.drop (n + m) ≍ (p.drop n).drop m
  proof: by
  rw [add_comm]
  induction p generalizing n <;> cases n <;> simp [*, drop]

中文:
引理 drop_add_heq
  条件: (p : G.Walk u v) (n m : 自然数)
  结论: p.drop (n + m) ≍ (p.drop n).drop m
  证明: by
  rw [add_comm]
  induction p generalizing n <;> cases n <;> simp [*, drop]

Depends on / 依赖: add_comm, generalizing
-/
lemma drop_add_heq (p : G.Walk u v) (n m : Nat) : p.drop (n + m) ≍ (p.drop n).drop m := by
  rw [add_comm]
  induction p generalizing n <;> cases n <;> simp [*, drop]

/--
lemma `drop_add_eq` / 引理 `drop_add_eq`

English:
lemma drop_add_eq
  given: (p : G.Walk u v) (n m : Nat)
  proof: eq_of_heq .trans by simp [Walk.copy] drop_add_heq ..

中文:
引理 drop_add_eq
  条件: (p : G.Walk u v) (n m : 自然数)
  证明: eq_of_heq .trans by simp [Walk.copy] drop_add_heq ..

Depends on / 依赖: Walk.copy, _aux, drop_add_heq, eq_of_heq, sorted_zero_eq_min
-/
lemma drop_add_eq (p : G.Walk u v) (n m : Nat) :
    p.drop (n + m) = ((p.drop n).drop m).copy (drop_getVert ..) rfl :=
eq_of_heq .trans by simp [Walk.copy] drop_add_heq ..

set_option backward.isDefEq.respectTransparency false in
/--
lemma `nil_drop_iff` / 引理 `nil_drop_iff`

English:
lemma nil_drop_iff
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.drop n).Nil ↔ p.length <= n
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

中文:
引理 nil_drop_iff
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.drop n).Nil ↔ p.length <= n
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

Depends on / 依赖: _aux, generalizing, sorted_zero_eq_min
-/
lemma nil_drop_iff (p : G.Walk u v) (n : Nat) : (p.drop n).Nil ↔ p.length <= n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

/--
lemma `drop_cons_eq` / 引理 `drop_cons_eq`

English:
lemma drop_cons_eq
  given: (h : G.Adj u v) (p : G.Walk v w) (n : Nat) (hn : n != 0)
  proof: by
  apply ext_support
  obtain ⟨_, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.ne_zero_iff_zero_lt.mp hn)
  conv_lhs => unfold drop
  simp

中文:
引理 drop_cons_eq
  条件: (h : G.Adj u v) (p : G.Walk v w) (n : 自然数) (hn : n != 0)
  证明: by
  apply ext_support
  obtain ⟨_, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.ne_zero_iff_zero_lt.mp hn)
  conv_lhs => unfold drop
  simp

Depends on / 依赖: Nat.exists_add_one_eq.mpr, Nat.ne_zero_iff_zero_lt.mp, conv_lhs, exists_add_one_eq, ext_support, ne_zero_iff_zero_lt
-/
lemma drop_cons_eq (h : G.Adj u v) (p : G.Walk v w) (n : Nat) (hn : n != 0) :
    (cons h p).drop n = (p.drop (n - 1)).copy (p.getVert_cons h hn).symm rfl := by
  apply ext_support
  obtain ⟨_, rfl⟩ := Nat.exists_add_one_eq.mpr (Nat.ne_zero_iff_zero_lt.mp hn)
  conv_lhs => unfold drop
  simp

/--
lemma `darts_drop` / 引理 `darts_drop`

English:
lemma darts_drop
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.drop n).darts = p.darts.drop n
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

中文:
引理 darts_drop
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.drop n).darts = p.darts.drop n
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

Depends on / 依赖: _aux, generalizing, sorted_last_eq_max
-/
lemma darts_drop (p : G.Walk u v) (n : Nat) : (p.drop n).darts = p.darts.drop n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

/--
lemma `edges_drop` / 引理 `edges_drop`

English:
lemma edges_drop
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.drop n).edges = p.edges.drop n
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

中文:
引理 edges_drop
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.drop n).edges = p.edges.drop n
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

Depends on / 依赖: Nat.sub_lt, Nat.zero_lt_one, _aux, card_pos, card_pos.mpr, generalizing, sorted_last_eq_max, sub_lt, zero_lt_one
-/
lemma edges_drop (p : G.Walk u v) (n : Nat) : (p.drop n).edges = p.edges.drop n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `take` / `take` 的定义

English:
definition take
  signature: {u v : V} (p : G.Walk u v) (n : Nat)
  body: match p, n with
  | .nil, _ => .nil
  | p, 0 => nil.copy rfl (getVert_zero p).symm
  | .cons h q, (n + 1) => .cons h (q.take n)

@[simp]

中文:
定义 take
  签名: {u v : V} (p : G.Walk u v) (n : 自然数)
  定义体: match p, n with
  | .nil, _ => .nil
  | p, 0 => nil.copy rfl (getVert_zero p).symm
  | .cons h q, (n + 1) => .cons h (q.take n)

@[simp]

Depends on / 依赖: getVert_zero, nil.copy, q.take
-/
def take {u v : V} (p : G.Walk u v) (n : Nat) : G.Walk u (p.getVert n) :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => nil.copy rfl (getVert_zero p).symm
  | .cons h q, (n + 1) => .cons h (q.take n)

@[simp]
/--
lemma `take_zero` / 引理 `take_zero`

English:
lemma take_zero
  given: (p : G.Walk u v)
  statement: p.take 0 = nil.copy rfl p.getVert_zero.symm
  proof: by
  cases p <;> simp [take]

@[simp]

中文:
引理 take_zero
  条件: (p : G.Walk u v)
  结论: p.take 0 = nil.copy rfl p.getVert_zero.symm
  证明: by
  cases p <;> simp [take]

@[simp]
-/
lemma take_zero (p : G.Walk u v) : p.take 0 = nil.copy rfl p.getVert_zero.symm := by
  cases p <;> simp [take]

@[simp]
/--
lemma `take_length` / 引理 `take_length`

English:
lemma take_length
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.take n).length = n ⊓ p.length
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, take]

中文:
引理 take_length
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.take n).length = n ⊓ p.length
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, take]

Depends on / 依赖: generalizing
-/
lemma take_length (p : G.Walk u v) (n : Nat) : (p.take n).length = n ⊓ p.length := by
  induction p generalizing n <;> cases n <;> simp [*, take]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `take_getVert` / 引理 `take_getVert`

English:
lemma take_getVert
  given: (p : G.Walk u v) (n m : Nat)
  statement: (p.take n).getVert m = p.getVert (n ⊓ m)
  proof: by
  induction p generalizing n m <;> cases n <;> cases m <;> simp [*, take]

中文:
引理 take_getVert
  条件: (p : G.Walk u v) (n m : 自然数)
  结论: (p.take n).getVert m = p.getVert (n ⊓ m)
  证明: by
  induction p generalizing n m <;> cases n <;> cases m <;> simp [*, take]

Depends on / 依赖: generalizing
-/
lemma take_getVert (p : G.Walk u v) (n m : Nat) : (p.take n).getVert m = p.getVert (n ⊓ m) := by
  induction p generalizing n m <;> cases n <;> cases m <;> simp [*, take]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `take_add_heq` / 引理 `take_add_heq`

English:
lemma take_add_heq
  given: (p : G.Walk u v) (n m : Nat)
  proof: by
  rw [add_comm]
  induction p generalizing n <;> cases n <;> simp [take, drop]
  grind [drop_getVert]

中文:
引理 take_add_heq
  条件: (p : G.Walk u v) (n m : 自然数)
  证明: by
  rw [add_comm]
  induction p generalizing n <;> cases n <;> simp [take, drop]
  grind [drop_getVert]

Depends on / 依赖: add_comm, drop_getVert, generalizing
-/
lemma take_add_heq (p : G.Walk u v) (n m : Nat) :
    p.take (n + m) ≍ (p.take n).append ((p.drop n).take m) := by
  rw [add_comm]
  induction p generalizing n <;> cases n <;> simp [take, drop]
  grind [drop_getVert]

/--
lemma `take_add_eq` / 引理 `take_add_eq`

English:
lemma take_add_eq
  given: (p : G.Walk u v) (n m : Nat)
  proof: eq_of_heq .trans by simp [Walk.copy] take_add_heq ..

中文:
引理 take_add_eq
  条件: (p : G.Walk u v) (n m : 自然数)
  证明: eq_of_heq .trans by simp [Walk.copy] take_add_heq ..

Depends on / 依赖: Walk.copy, eq_of_heq, take_add_heq
-/
lemma take_add_eq (p : G.Walk u v) (n m : Nat) :
    p.take (n + m) = ((p.take n).append ((p.drop n).take m)).copy rfl (drop_getVert ..) :=
eq_of_heq .trans by simp [Walk.copy] take_add_heq ..

set_option backward.isDefEq.respectTransparency false in
/--
lemma `nil_take_iff` / 引理 `nil_take_iff`

English:
lemma nil_take_iff
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.take n).Nil ↔ p.Nil ∨ n = 0
  proof: by
  cases p <;> cases n <;> simp [take]

中文:
引理 nil_take_iff
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.take n).Nil ↔ p.Nil ∨ n = 0
  证明: by
  cases p <;> cases n <;> simp [take]
-/
lemma nil_take_iff (p : G.Walk u v) (n : Nat) : (p.take n).Nil ↔ p.Nil ∨ n = 0 := by
  cases p <;> cases n <;> simp [take]

/--
lemma `support_take` / 引理 `support_take`

English:
lemma support_take
  given: {u v} (p : G.Walk u v) (n : Nat)
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[deprecated (since := "2026-05-20")] alias take_support_eq_support_take_succ := support_take

@[simp]

中文:
引理 support_take
  条件: {u v} (p : G.Walk u v) (n : 自然数)
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[deprecated (since := "2026-05-20")] alias take_support_eq_support_take_succ := support_take

@[simp]

Depends on / 依赖: generalizing
-/
lemma support_take {u v} (p : G.Walk u v) (n : Nat) :
    (p.take n).support = p.support.take (n + 1) := by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[deprecated (since := "2026-05-20")] alias take_support_eq_support_take_succ := support_take

@[simp]
/--
lemma `take_take` / 引理 `take_take`

English:
lemma take_take
  given: (p : G.Walk u v) (n m : Nat)
  proof: by
  apply ext_support
  simp [support_take, List.take_take, Nat.min_left_comm]

中文:
引理 take_take
  条件: (p : G.Walk u v) (n m : 自然数)
  证明: by
  apply ext_support
  simp [support_take, List.take_take, Nat.min_left_comm]

Depends on / 依赖: List.take_take, Nat.min_left_comm, ext_support, min_left_comm, support_take, take_take
-/
lemma take_take (p : G.Walk u v) (n m : Nat) :
    (p.take n).take m = (p.take (min n m)).copy rfl (p.take_getVert n m).symm := by
  apply ext_support
  simp [support_take, List.take_take, Nat.min_left_comm]

/--
lemma `take_of_length_le` / 引理 `take_of_length_le`

English:
lemma take_of_length_le
  given: {u v n} {p : G.Walk u v} (h : p.length <= n)
  proof: by
  induction n generalizing p u with
  | zero => cases p <;> simp [take] at h ⊢
  | succ n ih =>
    cases p
    · simp [take]
    rw [length_cons]; rw [Nat.add_le_add_iff_right] at h
    simp [take, ih h]

中文:
引理 take_of_length_le
  条件: {u v n} {p : G.Walk u v} (h : p.length <= n)
  证明: by
  induction n generalizing p u with
  | zero => cases p <;> simp [take] at h ⊢
  | succ n ih =>
    cases p
    · simp [take]
    rw [length_cons]; rw [Nat.add_le_add_iff_right] at h
    simp [take, ih h]

Depends on / 依赖: Nat.add_le_add_iff_right, add_le_add_iff_right, generalizing, length_cons
-/
lemma take_of_length_le {u v n} {p : G.Walk u v} (h : p.length <= n) :
    p.take n = p.copy rfl (p.getVert_of_length_le h).symm := by
  induction n generalizing p u with
  | zero => cases p <;> simp [take] at h ⊢
  | succ n ih =>
    cases p
    · simp [take]
    rw [length_cons]; rw [Nat.add_le_add_iff_right] at h
    simp [take, ih h]

/--
lemma `take_cons_eq` / 引理 `take_cons_eq`

English:
lemma take_cons_eq
  given: (h : G.Adj u v) (p : G.Walk v w) (n : Nat) (hn : n != 0)
  proof: by
  apply ext_support
  grind [support_copy, support_take]

中文:
引理 take_cons_eq
  条件: (h : G.Adj u v) (p : G.Walk v w) (n : 自然数) (hn : n != 0)
  证明: by
  apply ext_support
  grind [support_copy, support_take]

Depends on / 依赖: ext_support, support_copy, support_take
-/
lemma take_cons_eq (h : G.Adj u v) (p : G.Walk v w) (n : Nat) (hn : n != 0) :
    (cons h p).take n = cons h ((p.take <| n - 1).copy rfl (p.getVert_cons h hn).symm) := by
  apply ext_support
  grind [support_copy, support_take]

/--
lemma `darts_take` / 引理 `darts_take`

English:
lemma darts_take
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.take n).darts = p.darts.take n
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, take]

中文:
引理 darts_take
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.take n).darts = p.darts.take n
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, take]

Depends on / 依赖: generalizing
-/
lemma darts_take (p : G.Walk u v) (n : Nat) : (p.take n).darts = p.darts.take n := by
  induction p generalizing n <;> cases n <;> simp [*, take]

/--
lemma `edges_take` / 引理 `edges_take`

English:
lemma edges_take
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.take n).edges = p.edges.take n
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[simp]

中文:
引理 edges_take
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.take n).edges = p.edges.take n
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[simp]

Depends on / 依赖: generalizing
-/
lemma edges_take (p : G.Walk u v) (n : Nat) : (p.take n).edges = p.edges.take n := by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[simp]
/--
lemma `penultimate_concat` / 引理 `penultimate_concat`

English:
lemma penultimate_concat
  given: {t u v} (p : G.Walk u v) (h : G.Adj v t)
  proof: by simp [concat_eq_append, getVert_append]

@[simp]

中文:
引理 penultimate_concat
  条件: {t u v} (p : G.Walk u v) (h : G.Adj v t)
  证明: by simp [concat_eq_append, getVert_append]

@[simp]

Depends on / 依赖: concat_eq_append, getVert_append
-/
lemma penultimate_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).penultimate = v := by simp [concat_eq_append, getVert_append]

@[simp]
/--
lemma `snd_reverse` / 引理 `snd_reverse`

English:
lemma snd_reverse
  given: (p : G.Walk u v)
  statement: p.reverse.snd = p.penultimate
  proof: by
  simpa using getVert_reverse p 1

@[simp]

中文:
引理 snd_reverse
  条件: (p : G.Walk u v)
  结论: p.reverse.snd = p.penultimate
  证明: by
  simpa using getVert_reverse p 1

@[simp]

Depends on / 依赖: getVert_reverse
-/
lemma snd_reverse (p : G.Walk u v) : p.reverse.snd = p.penultimate := by
  simpa using getVert_reverse p 1

@[simp]
/--
lemma `penultimate_reverse` / 引理 `penultimate_reverse`

English:
lemma penultimate_reverse
  given: (p : G.Walk u v)
  statement: p.reverse.penultimate = p.snd
  proof: by
  cases p <;> simp [snd, getVert_append]

中文:
引理 penultimate_reverse
  条件: (p : G.Walk u v)
  结论: p.reverse.penultimate = p.snd
  证明: by
  cases p <;> simp [snd, getVert_append]

Depends on / 依赖: getVert_append
-/
lemma penultimate_reverse (p : G.Walk u v) : p.reverse.penultimate = p.snd := by
  cases p <;> simp [snd, getVert_append]

/--
Definition of `tail` / `tail` 的定义

English:
definition tail
  signature: (p : G.Walk u v)
  body: p.drop 1

@[simp]

中文:
定义 tail
  签名: (p : G.Walk u v)
  定义体: p.drop 1

@[simp]

Depends on / 依赖: p.drop
-/
def tail (p : G.Walk u v) : G.Walk (p.snd) v := p.drop 1

@[simp]
/--
theorem `darts_tail` / 定理 `darts_tail`

English:
theorem darts_tail
  given: {p : G.Walk u v}
  statement: p.tail.darts = p.darts.tail
  proof: by
  simp [tail, darts_drop]

@[simp]

中文:
定理 darts_tail
  条件: {p : G.Walk u v}
  结论: p.tail.darts = p.darts.tail
  证明: by
  simp [tail, darts_drop]

@[simp]

Depends on / 依赖: darts_drop
-/
theorem darts_tail {p : G.Walk u v} : p.tail.darts = p.darts.tail := by
  simp [tail, darts_drop]

@[simp]
/--
theorem `edges_tail` / 定理 `edges_tail`

English:
theorem edges_tail
  given: {p : G.Walk u v}
  statement: p.tail.edges = p.edges.tail
  proof: by
  simp [tail, edges_drop]

@[simp]

中文:
定理 edges_tail
  条件: {p : G.Walk u v}
  结论: p.tail.edges = p.edges.tail
  证明: by
  simp [tail, edges_drop]

@[simp]

Depends on / 依赖: edges_drop
-/
theorem edges_tail {p : G.Walk u v} : p.tail.edges = p.edges.tail := by
  simp [tail, edges_drop]

@[simp]
/--
lemma `drop_zero` / 引理 `drop_zero`

English:
lemma drop_zero
  given: {u v} (p : G.Walk u v)
  proof: by
  cases p <;> simp [Walk.drop]

中文:
引理 drop_zero
  条件: {u v} (p : G.Walk u v)
  证明: by
  cases p <;> simp [Walk.drop]

Depends on / 依赖: Walk.drop
-/
lemma drop_zero {u v} (p : G.Walk u v) :
    p.drop 0 = p.copy (getVert_zero p).symm rfl := by
  cases p <;> simp [Walk.drop]

/--
lemma `nil_drop_of_length_le` / 引理 `nil_drop_of_length_le`

English:
lemma nil_drop_of_length_le
  given: {u v n} {p : G.Walk u v} (h : p.length <= n)
  proof: by
  rw [← length_eq_zero_iff]; rw [drop_length]; rw [Nat.sub_eq_zero_of_le h]

@[simp]

中文:
引理 nil_drop_of_length_le
  条件: {u v n} {p : G.Walk u v} (h : p.length <= n)
  证明: by
  rw [← length_eq_zero_iff]; rw [drop_length]; rw [Nat.sub_eq_zero_of_le h]

@[simp]

Depends on / 依赖: Nat.sub_eq_zero_of_le, drop_length, length_eq_zero_iff, sub_eq_zero_of_le
-/
lemma nil_drop_of_length_le {u v n} {p : G.Walk u v} (h : p.length <= n) :
    (p.drop n).Nil := by
  rw [← length_eq_zero_iff]; rw [drop_length]; rw [Nat.sub_eq_zero_of_le h]

@[simp]
/--
lemma `drop_support_eq_support_drop_min` / 引理 `drop_support_eq_support_drop_min`

English:
lemma drop_support_eq_support_drop_min
  given: {u v} (p : G.Walk u v) (n : Nat)
  proof: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

@[simp]

中文:
引理 drop_support_eq_support_drop_min
  条件: {u v} (p : G.Walk u v) (n : 自然数)
  证明: by
  induction p generalizing n <;> cases n <;> simp [*, drop]

@[simp]

Depends on / 依赖: generalizing
-/
lemma drop_support_eq_support_drop_min {u v} (p : G.Walk u v) (n : Nat) :
    (p.drop n).support = p.support.drop (n ⊓ p.length) := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

@[simp]
/--
theorem `drop_drop` / 定理 `drop_drop`

English:
theorem drop_drop
  given: (p : G.Walk u v) (n m : Nat)
  proof: by
  apply ext_support
  simp_rw [support_copy, drop_support_eq_support_drop_min, drop_length, List.drop_drop]
  grind

@[simp]

中文:
定理 drop_drop
  条件: (p : G.Walk u v) (n m : 自然数)
  证明: by
  apply ext_support
  simp_rw [support_copy, drop_support_eq_support_drop_min, drop_length, List.drop_drop]
  grind

@[simp]

Depends on / 依赖: List.drop_drop, drop_drop, drop_length, drop_support_eq_support_drop_min, ext_support, simp_rw, support_copy
-/
theorem drop_drop (p : G.Walk u v) (n m : Nat) :
    (p.drop n).drop m = (p.drop (n + m)).copy (drop_getVert ..).symm rfl := by
  apply ext_support
  simp_rw [support_copy, drop_support_eq_support_drop_min, drop_length, List.drop_drop]
  grind

@[simp]
/--
theorem `append_take_drop_eq` / 定理 `append_take_drop_eq`

English:
theorem append_take_drop_eq
  given: (p : G.Walk u v) (n : Nat)
  statement: (p.take n).append (p.drop n) = p
  proof: by
  apply ext_support
  rw [support_append]; rw [support_take]; rw [drop_support_eq_support_drop_min]; rw [List.tail_drop]
  by_cases! h : n < p.length
  · simp [min_eq_left_of_lt h]
  · rw [Nat.min_eq_right h, ← length_support, List.drop_length]
    simp [h]

中文:
定理 append_take_drop_eq
  条件: (p : G.Walk u v) (n : 自然数)
  结论: (p.take n).append (p.drop n) = p
  证明: by
  apply ext_support
  rw [support_append]; rw [support_take]; rw [drop_support_eq_support_drop_min]; rw [List.tail_drop]
  by_cases! h : n < p.length
  · simp [min_eq_left_of_lt h]
  · rw [Nat.min_eq_right h, ← length_support, List.drop_length]
    simp [h]

Depends on / 依赖: List.drop_length, List.tail_drop, Nat.min_eq_right, drop_length, drop_support_eq_support_drop_min, ext_support, length, length_support, min_eq_left_of_lt, min_eq_right, p.length, support_append, support_take, tail_drop
-/
theorem append_take_drop_eq (p : G.Walk u v) (n : Nat) : (p.take n).append (p.drop n) = p := by
  apply ext_support
  rw [support_append]; rw [support_take]; rw [drop_support_eq_support_drop_min]; rw [List.tail_drop]
  by_cases! h : n < p.length
  · simp [min_eq_left_of_lt h]
  · rw [Nat.min_eq_right h, ← length_support, List.drop_length]
    simp [h]

/--
Definition of `dropLast` / `dropLast` 的定义

English:
definition dropLast
  signature: (p : G.Walk u v)
  body: p.take (p.length - 1)

@[simp]

中文:
定义 dropLast
  签名: (p : G.Walk u v)
  定义体: p.take (p.length - 1)

@[simp]

Depends on / 依赖: length, p.length, p.take
-/
def dropLast (p : G.Walk u v) : G.Walk u p.penultimate := p.take (p.length - 1)

@[simp]
/--
lemma `tail_nil` / 引理 `tail_nil`

English:
lemma tail_nil
  statement: (@nil _ G v).tail = .nil
  proof: rfl

@[simp]

中文:
引理 tail_nil
  结论: (@nil _ G v).tail = .nil
  证明: rfl

@[simp]
-/
lemma tail_nil : (@nil _ G v).tail = .nil := rfl

@[simp]
/--
lemma `tail_cons_nil` / 引理 `tail_cons_nil`

English:
lemma tail_cons_nil
  given: (h : G.Adj u v)
  statement: (Walk.cons h .nil).tail = .nil
  proof: rfl

@[simp]

中文:
引理 tail_cons_nil
  条件: (h : G.Adj u v)
  结论: (Walk.cons h .nil).tail = .nil
  证明: rfl

@[simp]
-/
lemma tail_cons_nil (h : G.Adj u v) : (Walk.cons h .nil).tail = .nil := rfl

@[simp]
/--
lemma `tail_cons` / 引理 `tail_cons`

English:
lemma tail_cons
  given: (h : G.Adj u v) (p : G.Walk v w)
  proof: by
  cases p <;> rfl

@[simp]

中文:
引理 tail_cons
  条件: (h : G.Adj u v) (p : G.Walk v w)
  证明: by
  cases p <;> rfl

@[simp]
-/
lemma tail_cons (h : G.Adj u v) (p : G.Walk v w) :
    (p.cons h).tail = p.copy (getVert_zero p).symm rfl := by
  cases p <;> rfl

@[simp]
/--
lemma `dropLast_nil` / 引理 `dropLast_nil`

English:
lemma dropLast_nil
  statement: (@nil _ G v).dropLast = nil
  proof: rfl

@[simp]

中文:
引理 dropLast_nil
  结论: (@nil _ G v).dropLast = nil
  证明: rfl

@[simp]
-/
lemma dropLast_nil : (@nil _ G v).dropLast = nil := rfl

@[simp]
/--
lemma `dropLast_cons_nil` / 引理 `dropLast_cons_nil`

English:
lemma dropLast_cons_nil
  given: (h : G.Adj u v)
  statement: (cons h nil).dropLast = nil
  proof: rfl

@[simp]

中文:
引理 dropLast_cons_nil
  条件: (h : G.Adj u v)
  结论: (cons h nil).dropLast = nil
  证明: rfl

@[simp]
-/
lemma dropLast_cons_nil (h : G.Adj u v) : (cons h nil).dropLast = nil := rfl

@[simp]
/--
lemma `dropLast_cons_cons` / 引理 `dropLast_cons_cons`

English:
lemma dropLast_cons_cons
  given: {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w')
  proof: rfl

中文:
引理 dropLast_cons_cons
  条件: {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w')
  证明: rfl
-/
lemma dropLast_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w') :
    (cons h (cons h₂ p)).dropLast = cons h (cons h₂ p).dropLast := rfl

/--
lemma `dropLast_cons_of_not_nil` / 引理 `dropLast_cons_of_not_nil`

English:
lemma dropLast_cons_of_not_nil
  given: (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil)
  proof: p.notNilRec (by simp) hp h

@[simp]

中文:
引理 dropLast_cons_of_not_nil
  条件: (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil)
  证明: p.notNilRec (by simp) hp h

@[simp]

Depends on / 依赖: notNilRec, p.notNilRec
-/
lemma dropLast_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
    (cons h p).dropLast = cons h (p.dropLast.copy rfl (penultimate_cons_of_not_nil _ _ hp).symm) :=
  p.notNilRec (by simp) hp h

@[simp]
/--
theorem `darts_dropLast` / 定理 `darts_dropLast`

English:
theorem darts_dropLast
  given: {p : G.Walk u v}
  statement: p.dropLast.darts = p.darts.dropLast
  proof: by
  simp [dropLast, darts_take, List.dropLast_eq_take]

@[simp]

中文:
定理 darts_dropLast
  条件: {p : G.Walk u v}
  结论: p.dropLast.darts = p.darts.dropLast
  证明: by
  simp [dropLast, darts_take, List.dropLast_eq_take]

@[simp]

Depends on / 依赖: List.dropLast_eq_take, darts_take, dropLast, dropLast_eq_take
-/
theorem darts_dropLast {p : G.Walk u v} : p.dropLast.darts = p.darts.dropLast := by
  simp [dropLast, darts_take, List.dropLast_eq_take]

@[simp]
/--
theorem `edges_dropLast` / 定理 `edges_dropLast`

English:
theorem edges_dropLast
  given: {p : G.Walk u v}
  statement: p.dropLast.edges = p.edges.dropLast
  proof: by
  simp [dropLast, edges_take, List.dropLast_eq_take]

@[simp]

中文:
定理 edges_dropLast
  条件: {p : G.Walk u v}
  结论: p.dropLast.edges = p.edges.dropLast
  证明: by
  simp [dropLast, edges_take, List.dropLast_eq_take]

@[simp]

Depends on / 依赖: List.dropLast_eq_take, dropLast, dropLast_eq_take, edges_take
-/
theorem edges_dropLast {p : G.Walk u v} : p.dropLast.edges = p.edges.dropLast := by
  simp [dropLast, edges_take, List.dropLast_eq_take]

@[simp]
/--
lemma `dropLast_concat` / 引理 `dropLast_concat`

English:
lemma dropLast_concat
  given: {t u v} (p : G.Walk u v) (h : G.Adj v t)
  proof: by
  induction p
  · rfl
  · rw! [concat_cons, dropLast_cons_of_not_nil] <;>
      simp [*, ← length_eq_zero_iff]

中文:
引理 dropLast_concat
  条件: {t u v} (p : G.Walk u v) (h : G.Adj v t)
  证明: by
  induction p
  · rfl
  · rw! [concat_cons, dropLast_cons_of_not_nil] <;>
      simp [*, ← length_eq_zero_iff]

Depends on / 依赖: concat_cons, dropLast_cons_of_not_nil, length_eq_zero_iff
-/
lemma dropLast_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).dropLast = p.copy rfl (by simp) := by
  induction p
  · rfl
  · rw! [concat_cons, dropLast_cons_of_not_nil] <;>
      simp [*, ← length_eq_zero_iff]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `cons_tail_eq` / 引理 `cons_tail_eq`

English:
lemma cons_tail_eq
  given: (p : G.Walk u v) (hp : ¬ p.Nil)
  proof: by
  cases p <;> simp at hp ⊢

中文:
引理 cons_tail_eq
  条件: (p : G.Walk u v) (hp : ¬ p.Nil)
  证明: by
  cases p <;> simp at hp ⊢
-/
lemma cons_tail_eq (p : G.Walk u v) (hp : ¬ p.Nil) :
    cons (p.adj_snd hp) p.tail = p := by
  cases p <;> simp at hp ⊢

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `concat_dropLast` / 引理 `concat_dropLast`

English:
lemma concat_dropLast
  given: {p : G.Walk u v} (hp : G.Adj p.penultimate v)
  statement: p.dropLast.concat hp = p
  proof: by
  induction p with
  | nil => simp at hp
  | cons hadj p hind =>
    cases p with
    | nil => rfl
    | _ => simp [hind]

@[simp]

中文:
引理 concat_dropLast
  条件: {p : G.Walk u v} (hp : G.Adj p.penultimate v)
  结论: p.dropLast.concat hp = p
  证明: by
  induction p with
  | nil => simp at hp
  | cons hadj p hind =>
    cases p with
    | nil => rfl
    | _ => simp [hind]

@[simp]
-/
lemma concat_dropLast {p : G.Walk u v} (hp : G.Adj p.penultimate v) : p.dropLast.concat hp = p := by
  induction p with
  | nil => simp at hp
  | cons hadj p hind =>
    cases p with
    | nil => rfl
    | _ => simp [hind]

@[simp]
/--
lemma `support_tail_of_not_nil` / 引理 `support_tail_of_not_nil`

English:
lemma support_tail_of_not_nil
  given: (p : G.Walk u v) (hp : ¬ p.Nil)
  proof: by
  simp [← p.cons_tail_eq hp]

中文:
引理 support_tail_of_not_nil
  条件: (p : G.Walk u v) (hp : ¬ p.Nil)
  证明: by
  simp [← p.cons_tail_eq hp]

Depends on / 依赖: cons_tail_eq, p.cons_tail_eq
-/
lemma support_tail_of_not_nil (p : G.Walk u v) (hp : ¬ p.Nil) :
    p.tail.support = p.support.tail := by
  simp [← p.cons_tail_eq hp]

/--
lemma `cons_support_tail` / 引理 `cons_support_tail`

English:
lemma cons_support_tail
  given: {p : G.Walk u v} (hp : ¬p.Nil)
  statement: u :: p.tail.support = p.support
  proof: by
  simp [hp]

中文:
引理 cons_support_tail
  条件: {p : G.Walk u v} (hp : ¬p.Nil)
  结论: u :: p.tail.support = p.support
  证明: by
  simp [hp]
-/
lemma cons_support_tail {p : G.Walk u v} (hp : ¬p.Nil) : u :: p.tail.support = p.support := by
  simp [hp]

/--
theorem `support_dropLast_concat` / 定理 `support_dropLast_concat`

English:
theorem support_dropLast_concat
  given: {p : G.Walk u v} (hp : ¬p.Nil)
  proof: by
  rw [← support_concat _ <| adj_penultimate hp]; rw [concat_dropLast]

@[simp]

中文:
定理 support_dropLast_concat
  条件: {p : G.Walk u v} (hp : ¬p.Nil)
  证明: by
  rw [← support_concat _ <| adj_penultimate hp]; rw [concat_dropLast]

@[simp]

Depends on / 依赖: adj_penultimate, concat_dropLast, support_concat
-/
theorem support_dropLast_concat {p : G.Walk u v} (hp : ¬p.Nil) :
    p.dropLast.support ++ [v] = p.support := by
  rw [← support_concat _ <| adj_penultimate hp]; rw [concat_dropLast]

@[simp]
/--
theorem `support_dropLast` / 定理 `support_dropLast`

English:
theorem support_dropLast
  given: {p : G.Walk u v} (hp : ¬p.Nil)
  proof: by
  simp [← support_dropLast_concat hp]

@[simp]

中文:
定理 support_dropLast
  条件: {p : G.Walk u v} (hp : ¬p.Nil)
  证明: by
  simp [← support_dropLast_concat hp]

@[simp]

Depends on / 依赖: support_dropLast_concat
-/
theorem support_dropLast {p : G.Walk u v} (hp : ¬p.Nil) :
    p.dropLast.support = p.support.dropLast := by
  simp [← support_dropLast_concat hp]

@[simp]
/--
theorem `length_tail` / 定理 `length_tail`

English:
theorem length_tail
  given: (p : G.Walk u v)
  statement: p.tail.length = p.length - 1
  proof: by
  cases p <;> simp

中文:
定理 length_tail
  条件: (p : G.Walk u v)
  结论: p.tail.length = p.length - 1
  证明: by
  cases p <;> simp
-/
theorem length_tail (p : G.Walk u v) : p.tail.length = p.length - 1 := by
  cases p <;> simp

/--
lemma `length_tail_add_one` / 引理 `length_tail_add_one`

English:
lemma length_tail_add_one
  given: {p : G.Walk u v} (hp : ¬ p.Nil)
  proof: by
  rw [← length_cons (p.adj_snd hp)]; rw [cons_tail_eq _ hp]

中文:
引理 length_tail_add_one
  条件: {p : G.Walk u v} (hp : ¬ p.Nil)
  证明: by
  rw [← length_cons (p.adj_snd hp)]; rw [cons_tail_eq _ hp]

Depends on / 依赖: adj_snd, cons_tail_eq, length_cons, p.adj_snd
-/
lemma length_tail_add_one {p : G.Walk u v} (hp : ¬ p.Nil) :
    p.tail.length + 1 = p.length := by
  rw [← length_cons (p.adj_snd hp)]; rw [cons_tail_eq _ hp]

/--
lemma `length_dropLast_add_one` / 引理 `length_dropLast_add_one`

English:
lemma length_dropLast_add_one
  given: {p : G.Walk u v} (hp : ¬p.Nil)
  proof: by
  rw [← length_concat _ <| p.adj_penultimate hp]; rw [concat_dropLast]

@[simp]

中文:
引理 length_dropLast_add_one
  条件: {p : G.Walk u v} (hp : ¬p.Nil)
  证明: by
  rw [← length_concat _ <| p.adj_penultimate hp]; rw [concat_dropLast]

@[simp]

Depends on / 依赖: adj_penultimate, concat_dropLast, length_concat, p.adj_penultimate
-/
lemma length_dropLast_add_one {p : G.Walk u v} (hp : ¬p.Nil) :
    p.dropLast.length + 1 = p.length := by
  rw [← length_concat _ <| p.adj_penultimate hp]; rw [concat_dropLast]

@[simp]
/--
lemma `length_dropLast` / 引理 `length_dropLast`

English:
lemma length_dropLast
  given: (p : G.Walk u v)
  statement: p.dropLast.length = p.length - 1
  proof: by
  cases p <;> simp [← length_dropLast_add_one not_nil_cons]

中文:
引理 length_dropLast
  条件: (p : G.Walk u v)
  结论: p.dropLast.length = p.length - 1
  证明: by
  cases p <;> simp [← length_dropLast_add_one not_nil_cons]

Depends on / 依赖: length_dropLast_add_one, not_nil_cons
-/
lemma length_dropLast (p : G.Walk u v) : p.dropLast.length = p.length - 1 := by
  cases p <;> simp [← length_dropLast_add_one not_nil_cons]

/--
theorem `getVert_dropLast` / 定理 `getVert_dropLast`

English:
theorem getVert_dropLast
  given: {n} {p : G.Walk u v} (h : n < p.length)
  proof: by
  grind [getVert_eq_support_getElem, length_dropLast, support_dropLast]

@[simp]

中文:
定理 getVert_dropLast
  条件: {n} {p : G.Walk u v} (h : n < p.length)
  证明: by
  grind [getVert_eq_support_getElem, length_dropLast, support_dropLast]

@[simp]

Depends on / 依赖: getVert_eq_support_getElem, length_dropLast, support_dropLast
-/
theorem getVert_dropLast {n} {p : G.Walk u v} (h : n < p.length) :
    p.dropLast.getVert n = p.getVert n := by
  grind [getVert_eq_support_getElem, length_dropLast, support_dropLast]

@[simp]
/--
theorem `reverse_tail` / 定理 `reverse_tail`

English:
theorem reverse_tail
  given: (p : G.Walk u v)
  proof: by
  match p with
  | nil => simp
  | cons hadj p =>
    apply ext_support
    rw [support_copy]
    simp [-reverse_cons]

@[simp]

中文:
定理 reverse_tail
  条件: (p : G.Walk u v)
  证明: by
  match p with
  | nil => simp
  | cons hadj p =>
    apply ext_support
    rw [support_copy]
    simp [-reverse_cons]

@[simp]

Depends on / 依赖: ext_support, reverse_cons, support_copy
-/
theorem reverse_tail (p : G.Walk u v) :
    p.tail.reverse = p.reverse.dropLast.copy rfl p.penultimate_reverse := by
  match p with
  | nil => simp
  | cons hadj p =>
    apply ext_support
    rw [support_copy]
    simp [-reverse_cons]

@[simp]
/--
theorem `reverse_dropLast` / 定理 `reverse_dropLast`

English:
theorem reverse_dropLast
  given: (p : G.Walk u v)
  proof: by
  match p with
  | nil => simp
  | cons hadj p =>
    apply ext_support
    simp [-reverse_cons, List.dropLast_cons_of_ne_nil p.support_ne_nil]

中文:
定理 reverse_dropLast
  条件: (p : G.Walk u v)
  证明: by
  match p with
  | nil => simp
  | cons hadj p =>
    apply ext_support
    simp [-reverse_cons, List.dropLast_cons_of_ne_nil p.support_ne_nil]

Depends on / 依赖: List.dropLast_cons_of_ne_nil, dropLast_cons_of_ne_nil, ext_support, p.support_ne_nil, reverse_cons, support_ne_nil
-/
theorem reverse_dropLast (p : G.Walk u v) :
    p.dropLast.reverse = p.reverse.tail.copy p.snd_reverse rfl := by
  match p with
  | nil => simp
  | cons hadj p =>
    apply ext_support
    simp [-reverse_cons, List.dropLast_cons_of_ne_nil p.support_ne_nil]

/--
lemma `Nil.tail` / 引理 `Nil.tail`

English:
lemma Nil.tail
  given: {p : G.Walk v w} (hp : p.Nil)
  statement: p.tail.Nil
  proof: by
  cases p <;> simp at hp ⊢

中文:
引理 Nil.tail
  条件: {p : G.Walk v w} (hp : p.Nil)
  结论: p.tail.Nil
  证明: by
  cases p <;> simp at hp ⊢
-/
protected lemma Nil.tail {p : G.Walk v w} (hp : p.Nil) : p.tail.Nil := by
  cases p <;> simp at hp ⊢

/--
lemma `not_nil_of_tail_not_nil` / 引理 `not_nil_of_tail_not_nil`

English:
lemma not_nil_of_tail_not_nil
  given: {p : G.Walk v w} (hp : ¬ p.tail.Nil)
  statement: ¬ p.Nil
  proof: mt Nil.tail hp

中文:
引理 not_nil_of_tail_not_nil
  条件: {p : G.Walk v w} (hp : ¬ p.tail.Nil)
  结论: ¬ p.Nil
  证明: mt Nil.tail hp

Depends on / 依赖: Nil.tail
-/
lemma not_nil_of_tail_not_nil {p : G.Walk v w} (hp : ¬ p.tail.Nil) : ¬ p.Nil := mt Nil.tail hp

/--
lemma `Nil.dropLast` / 引理 `Nil.dropLast`

English:
lemma Nil.dropLast
  given: {p : G.Walk v w} (hp : p.Nil)
  statement: p.dropLast.Nil
  proof: by
  cases p <;> simp at hp ⊢

中文:
引理 Nil.dropLast
  条件: {p : G.Walk v w} (hp : p.Nil)
  结论: p.dropLast.Nil
  证明: by
  cases p <;> simp at hp ⊢
-/
protected lemma Nil.dropLast {p : G.Walk v w} (hp : p.Nil) : p.dropLast.Nil := by
  cases p <;> simp at hp ⊢

/--
lemma `nil_copy` / 引理 `nil_copy`

English:
lemma nil_copy
  given: {u' v' : V} {p : G.Walk u v} (hu : u = u') (hv : v = v')
  proof: by
  subst_vars
  rfl

中文:
引理 nil_copy
  条件: {u' v' : V} {p : G.Walk u v} (hu : u = u') (hv : v = v')
  证明: by
  subst_vars
  rfl
-/
@[simp] lemma nil_copy {u' v' : V} {p : G.Walk u v} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).Nil = p.Nil := by
  subst_vars
  rfl

/--
lemma `Nil.eq_copy_nil` / 引理 `Nil.eq_copy_nil`

English:
lemma Nil.eq_copy_nil
  given: {p : G.Walk u v} (h : p.Nil)
  statement: p = Walk.nil.copy rfl h.eq
  proof: by
  grind [eq_nil_iff_nil, copy_rfl_rfl]

中文:
引理 Nil.eq_copy_nil
  条件: {p : G.Walk u v} (h : p.Nil)
  结论: p = Walk.nil.copy rfl h.eq
  证明: by
  grind [eq_nil_iff_nil, copy_rfl_rfl]

Depends on / 依赖: copy_rfl_rfl, eq_nil_iff_nil
-/
lemma Nil.eq_copy_nil {p : G.Walk u v} (h : p.Nil) : p = Walk.nil.copy rfl h.eq := by
  grind [eq_nil_iff_nil, copy_rfl_rfl]

/--
lemma `drop_of_length_le` / 引理 `drop_of_length_le`

English:
lemma drop_of_length_le
  given: {u v n} {p : G.Walk u v} (h : p.length <= n)
  proof: (nil_drop_of_length_le h).eq_copy_nil

中文:
引理 drop_of_length_le
  条件: {u v n} {p : G.Walk u v} (h : p.length <= n)
  证明: (nil_drop_of_length_le h).eq_copy_nil

Depends on / 依赖: eq_copy_nil, nil_drop_of_length_le
-/
lemma drop_of_length_le {u v n} {p : G.Walk u v} (h : p.length <= n) :
    p.drop n = nil.copy rfl (p.getVert_of_length_le h) :=
  (nil_drop_of_length_le h).eq_copy_nil

/--
lemma `getVert_copy` / 引理 `getVert_copy`

English:
lemma getVert_copy
  given: {u v w x : V} (p : G.Walk u v) (i : Nat) (h : u = w) (h' : v = x)
  proof: by
  subst_vars
  rfl

中文:
引理 getVert_copy
  条件: {u v w x : V} (p : G.Walk u v) (i : 自然数) (h : u = w) (h' : v = x)
  证明: by
  subst_vars
  rfl
-/
@[simp] lemma getVert_copy {u v w x : V} (p : G.Walk u v) (i : Nat) (h : u = w) (h' : v = x) :
    (p.copy h h').getVert i = p.getVert i := by
  subst_vars
  rfl

/--
lemma `getVert_tail` / 引理 `getVert_tail`

English:
lemma getVert_tail
  given: {u v n} (p : G.Walk u v)
  proof: by
  cases p <;> simp

中文:
引理 getVert_tail
  条件: {u v n} (p : G.Walk u v)
  证明: by
  cases p <;> simp
-/
@[simp] lemma getVert_tail {u v n} (p : G.Walk u v) :
    p.tail.getVert n = p.getVert (n + 1) := by
  cases p <;> simp

/--
lemma `getVert_mem_tail_support` / 引理 `getVert_mem_tail_support`

English:
lemma getVert_mem_tail_support
  given: {u v : V} {p : G.Walk u v} (hp : ¬p.Nil)

中文:
引理 getVert_mem_tail_support
  条件: {u v : V} {p : G.Walk u v} (hp : ¬p.Nil)
-/
lemma getVert_mem_tail_support {u v : V} {p : G.Walk u v} (hp : ¬p.Nil) :
    forall {i : Nat}, i != 0 -> p.getVert i in p.support.tail
  | i + 1, _ => by
    rw [← getVert_tail]; rw [← p.support_tail_of_not_nil hp]
    exact getVert_mem_support ..

/--
lemma `support_injective` / 引理 `support_injective`

English:
lemma support_injective
  given: {u v : V}
  statement: (support (G := G) (u := u) (v := v)).Injective
  proof: fun _ _ => ext_support

中文:
引理 support_injective
  条件: {u v : V}
  结论: (support (G := G) (u := u) (v := v)).Injective
  证明: fun _ _ => ext_support

Depends on / 依赖: Injective
-/
lemma support_injective {u v : V} : (support (G := G) (u := u) (v := v)).Injective :=
  fun _ _ => ext_support

/--
lemma `ext_getVert_le_length` / 引理 `ext_getVert_le_length`

English:
lemma ext_getVert_le_length
  statement: {u v} {p q : G.Walk u v} (hl : p.length = q.length)
  proof: by
  suffices forall k : Nat, p.support[k]? = q.support[k]? by
exact ext_support List.ext_getElem?_iff.mpr this
  intro k
  cases le_or_gt k p.length with
  | inl hk =>
    rw [← getVert_eq_support_getElem? p hk]; rw [← getVert_eq_support_getElem? q (hl ▸ hk)]
    exact congrArg some (h k hk)
  | in

中文:
引理 ext_getVert_le_length
  结论: {u v} {p q : G.Walk u v} (hl : p.length = q.length)
  证明: by
  suffices forall k : Nat, p.support[k]? = q.support[k]? by
exact ext_support List.ext_getElem?_iff.mpr this
  intro k
  cases le_or_gt k p.length with
  | inl hk =>
    rw [← getVert_eq_support_getElem? p hk]; rw [← getVert_eq_support_getElem? q (hl ▸ hk)]
    exact congrArg some (h k hk)
  | in

Depends on / 依赖: List.ext_getElem, List.getElem, _eq_none_iff, _iff, _iff.mpr, ext_getElem, ext_support, getElem, getVert_eq_support_getElem, le_or_gt, length, length_support, p.length, p.support, q.length, q.support, replace, support
-/
lemma ext_getVert_le_length {u v} {p q : G.Walk u v} (hl : p.length = q.length)
    (h : forall k <= p.length, p.getVert k = q.getVert k) :
    p = q := by
  suffices forall k : Nat, p.support[k]? = q.support[k]? by
exact ext_support List.ext_getElem?_iff.mpr this
  intro k
  cases le_or_gt k p.length with
  | inl hk =>
    rw [← getVert_eq_support_getElem? p hk]; rw [← getVert_eq_support_getElem? q (hl ▸ hk)]
    exact congrArg some (h k hk)
  | inr hk =>
    replace hk : p.length + 1 <= k := hk
    have ht : q.length + 1 <= k := hl ▸ hk
    rw [← length_support]; rw [← List.getElem?_eq_none_iff] at hk ht
    rw [hk]; rw [ht]

/--
lemma `ext_getVert` / 引理 `ext_getVert`

English:
lemma ext_getVert
  given: {u v} {p q : G.Walk u v} (h : forall k, p.getVert k = q.getVert k)
  proof: by
  wlog hpq : p.length <= q.length generalizing p q
  · exact (this (h · |>.symm) (le_of_not_ge hpq)).symm
  refine ext_getVert_le_length (hpq.antisymm ?_) fun k _ => h k
  by_contra!
  exact (q.adj_getVert_succ this).ne (by simp [← h, getVert_of_length_le])

中文:
引理 ext_getVert
  条件: {u v} {p q : G.Walk u v} (h : 对任意 k, p.getVert k = q.getVert k)
  证明: by
  wlog hpq : p.length <= q.length generalizing p q
  · exact (this (h · |>.symm) (le_of_not_ge hpq)).symm
  refine ext_getVert_le_length (hpq.antisymm ?_) fun k _ => h k
  by_contra!
  exact (q.adj_getVert_succ this).ne (by simp [← h, getVert_of_length_le])

Depends on / 依赖: adj_getVert_succ, antisymm, ext_getVert_le_length, generalizing, getVert_of_length_le, hpq.antisymm, le_of_not_ge, length, p.length, q.adj_getVert_succ, q.length
-/
lemma ext_getVert {u v} {p q : G.Walk u v} (h : forall k, p.getVert k = q.getVert k) :
    p = q := by
  wlog hpq : p.length <= q.length generalizing p q
  · exact (this (h · |>.symm) (le_of_not_ge hpq)).symm
  refine ext_getVert_le_length (hpq.antisymm ?_) fun k _ => h k
  by_contra!
  exact (q.adj_getVert_succ this).ne (by simp [← h, getVert_of_length_le])

open scoped List in
/--
theorem `support_tail_perm_support_dropLast` / 定理 `support_tail_perm_support_dropLast`

English:
theorem support_tail_perm_support_dropLast
  given: (p : G.Walk u u)
  proof: by
  cases p with | nil => rfl | cons h p
  grw [← List.perm_cons u, List.perm_comm, ← List.perm_append_singleton,
    cons_support_tail not_nil_cons, support_dropLast_concat not_nil_cons]

中文:
定理 support_tail_perm_support_dropLast
  条件: (p : G.Walk u u)
  证明: by
  cases p with | nil => rfl | cons h p
  grw [← List.perm_cons u, List.perm_comm, ← List.perm_append_singleton,
    cons_support_tail not_nil_cons, support_dropLast_concat not_nil_cons]

Depends on / 依赖: List.perm_append_singleton, List.perm_comm, List.perm_cons, cons_support_tail, not_nil_cons, perm_append_singleton, perm_comm, perm_cons, support_dropLast_concat
-/
theorem support_tail_perm_support_dropLast (p : G.Walk u u) :
    p.tail.support ~ p.dropLast.support := by
  cases p with | nil => rfl | cons h p
  grw [← List.perm_cons u, List.perm_comm, ← List.perm_append_singleton,
    cons_support_tail not_nil_cons, support_dropLast_concat not_nil_cons]

open scoped List in
/--
theorem `tail_support_perm_dropLast_support` / 定理 `tail_support_perm_dropLast_support`

English:
theorem tail_support_perm_dropLast_support
  given: (p : G.Walk u u)
  proof: by
  cases p with | nil => rfl | cons h p
simpa using support_tail_perm_support_dropLast p.cons h

中文:
定理 tail_support_perm_dropLast_support
  条件: (p : G.Walk u u)
  证明: by
  cases p with | nil => rfl | cons h p
simpa using support_tail_perm_support_dropLast p.cons h

Depends on / 依赖: p.cons, support_tail_perm_support_dropLast
-/
theorem tail_support_perm_dropLast_support (p : G.Walk u u) :
    p.support.tail ~ p.support.dropLast := by
  cases p with | nil => rfl | cons h p
simpa using support_tail_perm_support_dropLast p.cons h

end Walk

end SimpleGraph
