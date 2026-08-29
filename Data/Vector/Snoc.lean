/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
module

public import Mathlib.Data.Vector.Basic

/-!
  This file establishes a `snoc : Vector α n → α → Vector α (n+1)` operation, that appends a single
  element to the back of a vector.

  It provides a collection of lemmas that show how different `Vector` operations reduce when their
  argument is `snoc xs x`.

  Also, an alternative, reverse, induction principle is added, that breaks down a vector into
  `snoc xs x` for its inductive case. Effectively doing induction from right-to-left
-/

@[expose] public section

namespace List

namespace Vector

variable {α β σ φ : Type*} {n : Nat} {x : α} {s : σ} (xs : Vector α n)

/--
Definition of `snoc` / `snoc` 的定义

English:
definition snoc
  signature: : Vector α n -> α -> Vector α (n + 1)
  body: fun xs x => xs ++ x ::ᵥ Vector.nil

中文:
定义 snoc
  签名: : Vector α n -> α -> Vector α (n + 1)
  定义体: fun xs x => xs ++ x ::ᵥ Vector.nil

Depends on / 依赖: Vector, Vector.nil
-/
def snoc : Vector α n -> α -> Vector α (n + 1) :=
  fun xs x => xs ++ x ::ᵥ Vector.nil

/-! ## Simplification lemmas -/

section Simp

variable {y : α}

@[simp]
/--
theorem `snoc_cons` / 定理 `snoc_cons`

English:
theorem snoc_cons
  statement: (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y)
  proof: rfl

@[simp]

中文:
定理 snoc_cons
  结论: (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y)
  证明: rfl

@[simp]
-/
theorem snoc_cons : (x ::ᵥ xs).snoc y = x ::ᵥ (xs.snoc y) :=
  rfl

@[simp]
/--
theorem `snoc_nil` / 定理 `snoc_nil`

English:
theorem snoc_nil
  statement: (nil.snoc x) = x ::ᵥ nil
  proof: rfl

@[simp]

中文:
定理 snoc_nil
  结论: (nil.snoc x) = x ::ᵥ nil
  证明: rfl

@[simp]
-/
theorem snoc_nil : (nil.snoc x) = x ::ᵥ nil :=
  rfl

@[simp]
/--
theorem `reverse_cons` / 定理 `reverse_cons`

English:
theorem reverse_cons
  statement: reverse (x ::ᵥ xs) = (reverse xs).snoc x
  proof: by
  cases xs
  simp only [reverse, cons, toList_mk, List.reverse_cons, snoc]
  congr

@[simp]

中文:
定理 reverse_cons
  结论: reverse (x ::ᵥ xs) = (reverse xs).snoc x
  证明: by
  cases xs
  simp only [reverse, cons, toList_mk, List.reverse_cons, snoc]
  congr

@[simp]

Depends on / 依赖: List.reverse_cons, reverse, reverse_cons, toList_mk
-/
theorem reverse_cons : reverse (x ::ᵥ xs) = (reverse xs).snoc x := by
  cases xs
  simp only [reverse, cons, toList_mk, List.reverse_cons, snoc]
  congr

@[simp]
/--
theorem `reverse_snoc` / 定理 `reverse_snoc`

English:
theorem reverse_snoc
  statement: reverse (xs.snoc x) = x ::ᵥ (reverse xs)
  proof: by
  cases xs
  simp only [reverse, snoc, cons, toList_mk]
  congr
  simp [toList, append_def]

中文:
定理 reverse_snoc
  结论: reverse (xs.snoc x) = x ::ᵥ (reverse xs)
  证明: by
  cases xs
  simp only [reverse, snoc, cons, toList_mk]
  congr
  simp [toList, append_def]

Depends on / 依赖: append_def, reverse, toList, toList_mk
-/
theorem reverse_snoc : reverse (xs.snoc x) = x ::ᵥ (reverse xs) := by
  cases xs
  simp only [reverse, snoc, cons, toList_mk]
  congr
  simp [toList, append_def]

/--
theorem `replicate_succ_to_snoc` / 定理 `replicate_succ_to_snoc`

English:
theorem replicate_succ_to_snoc
  given: (val : α)
  proof: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replicate_succ]
    conv => rhs; rw [replicate_succ]
    rw [snoc_cons]; rw [ih]

中文:
定理 replicate_succ_to_snoc
  条件: (val : α)
  证明: by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replicate_succ]
    conv => rhs; rw [replicate_succ]
    rw [snoc_cons]; rw [ih]

Depends on / 依赖: replicate_succ, snoc_cons
-/
theorem replicate_succ_to_snoc (val : α) :
    replicate (n + 1) val = (replicate n val).snoc val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [replicate_succ]
    conv => rhs; rw [replicate_succ]
    rw [snoc_cons]; rw [ih]

end Simp

/-! ## Reverse induction principle -/

section Induction

/--
Define `C v` by *reverse* induction on `v : Vector α n`.
That is, break the vector down starting from the right-most element, using `snoc`

This function has two arguments: `nil` handles the base case on `C nil`,
and `snoc` defines the inductive step using `∀ x : α, C xs → C (xs.snoc x)`.

This can be used as `induction v using Vector.revInductionOn`. -/
@[elab_as_elim]
/--
Definition of `revInductionOn` / `revInductionOn` 的定义

English:
definition revInductionOn
  signature: {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vector α n)
  body: cast (by simp) inductionOn
    (C := fun v => C v.reverse)
    v.reverse
    nil
    (@fun n x xs (r : C xs.reverse) => cast (by simp) <| snoc xs.reverse x r)

中文:
定义 revInductionOn
  签名: {C : 对任意 {n : 自然数}, Vector α n -> Sort*} {n : 自然数} (v : Vector α n)
  定义体: cast (by simp) inductionOn
    (C := fun v => C v.reverse)
    v.reverse
    nil
    (@fun n x xs (r : C xs.reverse) => cast (by simp) <| snoc xs.reverse x r)

Depends on / 依赖: inductionOn, reverse, v.reverse, xs.reverse
-/
def revInductionOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vector α n)
    (nil : C nil)
    (snoc : forall {n : Nat} (xs : Vector α n) (x : α), C xs -> C (xs.snoc x)) :
    C v :=
cast (by simp) inductionOn
    (C := fun v => C v.reverse)
    v.reverse
    nil
    (@fun n x xs (r : C xs.reverse) => cast (by simp) <| snoc xs.reverse x r)

/-- Define `C v w` by *reverse* induction on a pair of vectors `v : Vector α n` and
`w : Vector β n`. -/
@[elab_as_elim]
/--
Definition of `revInductionOn₂` / `revInductionOn₂` 的定义

English:
definition revInductionOn₂
  signature: {C : forall {n : Nat}, Vector α n -> Vector β n -> Sort*} {n : Nat}
  body: cast (by simp) inductionOn₂
    (C := fun v w => C v.reverse w.reverse)
    v.reverse
    w.reverse
    nil
    (@fun n x y xs ys (r : C xs.reverse ys.reverse) =>
cast (by simp) snoc xs.reverse ys.reverse x y r)

中文:
定义 revInductionOn₂
  签名: {C : 对任意 {n : 自然数}, Vector α n -> Vector β n -> Sort*} {n : 自然数}
  定义体: cast (by simp) inductionOn₂
    (C := fun v w => C v.reverse w.reverse)
    v.reverse
    w.reverse
    nil
    (@fun n x y xs ys (r : C xs.reverse ys.reverse) =>
cast (by simp) snoc xs.reverse ys.reverse x y r)

Depends on / 依赖: reverse, v.reverse, w.reverse, xs.reverse, ys.reverse
-/
def revInductionOn₂ {C : forall {n : Nat}, Vector α n -> Vector β n -> Sort*} {n : Nat}
    (v : Vector α n) (w : Vector β n)
    (nil : C nil nil)
    (snoc : forall {n : Nat} (xs : Vector α n) (ys : Vector β n) (x : α) (y : β),
      C xs ys -> C (xs.snoc x) (ys.snoc y)) :
    C v w :=
cast (by simp) inductionOn₂
    (C := fun v w => C v.reverse w.reverse)
    v.reverse
    w.reverse
    nil
    (@fun n x y xs ys (r : C xs.reverse ys.reverse) =>
cast (by simp) snoc xs.reverse ys.reverse x y r)

/-- Define `C v` by *reverse* case analysis, i.e. by handling the cases `nil` and `xs.snoc x`
separately -/
@[elab_as_elim]
/--
Definition of `revCasesOn` / `revCasesOn` 的定义

English:
definition revCasesOn
  signature: {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vector α n)
  body: revInductionOn v nil fun xs x _ => snoc xs x

中文:
定义 revCasesOn
  签名: {C : 对任意 {n : 自然数}, Vector α n -> Sort*} {n : 自然数} (v : Vector α n)
  定义体: revInductionOn v nil fun xs x _ => snoc xs x

Depends on / 依赖: revInductionOn
-/
def revCasesOn {C : forall {n : Nat}, Vector α n -> Sort*} {n : Nat} (v : Vector α n)
    (nil : C nil)
    (snoc : forall {n : Nat} (xs : Vector α n) (x : α), C (xs.snoc x)) :
    C v :=
  revInductionOn v nil fun xs x _ => snoc xs x

end Induction

/-! ## More simplification lemmas -/

section Simp

@[simp]
/--
theorem `map_snoc` / 定理 `map_snoc`

English:
theorem map_snoc
  given: {f : α -> β}
  statement: map f (xs.snoc x) = (map f xs).snoc (f x)
  proof: by
  induction xs <;> simp_all

@[simp]

中文:
定理 map_snoc
  条件: {f : α -> β}
  结论: map f (xs.snoc x) = (map f xs).snoc (f x)
  证明: by
  induction xs <;> simp_all

@[simp]
-/
theorem map_snoc {f : α -> β} : map f (xs.snoc x) = (map f xs).snoc (f x) := by
  induction xs <;> simp_all

@[simp]
/--
theorem `mapAccumr_nil` / 定理 `mapAccumr_nil`

English:
theorem mapAccumr_nil
  given: {f : α -> σ -> σ × β} {s : σ}
  statement: mapAccumr f Vector.nil s = (s, Vector.nil)
  proof: rfl

@[simp]

中文:
定理 mapAccumr_nil
  条件: {f : α -> σ -> σ × β} {s : σ}
  结论: mapAccumr f Vector.nil s = (s, Vector.nil)
  证明: rfl

@[simp]
-/
theorem mapAccumr_nil {f : α -> σ -> σ × β} {s : σ} : mapAccumr f Vector.nil s = (s, Vector.nil) :=
  rfl

@[simp]
/--
theorem `mapAccumr_snoc` / 定理 `mapAccumr_snoc`

English:
theorem mapAccumr_snoc
  given: {f : α -> σ -> σ × β} {s : σ}
  proof: f x s
      let r := mapAccumr f xs q.1
      (r.1, r.2.snoc q.2) := by
  induction xs
  · rfl
  · simp [*]

中文:
定理 mapAccumr_snoc
  条件: {f : α -> σ -> σ × β} {s : σ}
  证明: f x s
      let r := mapAccumr f xs q.1
      (r.1, r.2.snoc q.2) := by
  induction xs
  · rfl
  · simp [*]
-/
theorem mapAccumr_snoc {f : α -> σ -> σ × β} {s : σ} :
    mapAccumr f (xs.snoc x) s
    = let q := f x s
      let r := mapAccumr f xs q.1
      (r.1, r.2.snoc q.2) := by
  induction xs
  · rfl
  · simp [*]

variable (ys : Vector β n)

@[simp]
/--
theorem `map₂_snoc` / 定理 `map₂_snoc`

English:
theorem map₂_snoc
  given: {f : α -> β -> σ} {y : β}
  proof: by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

@[simp]

中文:
定理 map₂_snoc
  条件: {f : α -> β -> σ} {y : β}
  证明: by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

@[simp]

Depends on / 依赖: Vector, Vector.inductionOn
-/
theorem map₂_snoc {f : α -> β -> σ} {y : β} :
    map₂ f (xs.snoc x) (ys.snoc y) = (map₂ f xs ys).snoc (f x y) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

@[simp]
/--
theorem `mapAccumr₂_nil` / 定理 `mapAccumr₂_nil`

English:
theorem mapAccumr₂_nil
  given: {f : α -> β -> σ -> σ × φ}
  proof: rfl

@[simp]

中文:
定理 mapAccumr₂_nil
  条件: {f : α -> β -> σ -> σ × φ}
  证明: rfl

@[simp]
-/
theorem mapAccumr₂_nil {f : α -> β -> σ -> σ × φ} :
    mapAccumr₂ f Vector.nil Vector.nil s = (s, Vector.nil) :=
  rfl

@[simp]
/--
theorem `mapAccumr₂_snoc` / 定理 `mapAccumr₂_snoc`

English:
theorem mapAccumr₂_snoc
  given: (f : α -> β -> σ -> σ × φ) (x : α) (y : β)
  proof: f x y s
      let r := mapAccumr₂ f xs ys q.1
      (r.1, r.2.snoc q.2) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

中文:
定理 mapAccumr₂_snoc
  条件: (f : α -> β -> σ -> σ × φ) (x : α) (y : β)
  证明: f x y s
      let r := mapAccumr₂ f xs ys q.1
      (r.1, r.2.snoc q.2) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all
-/
theorem mapAccumr₂_snoc (f : α -> β -> σ -> σ × φ) (x : α) (y : β) :
    mapAccumr₂ f (xs.snoc x) (ys.snoc y) s
    = let q := f x y s
      let r := mapAccumr₂ f xs ys q.1
      (r.1, r.2.snoc q.2) := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

end Simp
end Vector

end List
