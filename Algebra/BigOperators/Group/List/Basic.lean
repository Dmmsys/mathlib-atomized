/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Data.List.TakeDrop
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Order.Basic

/-!
# Sums and products from lists

This file provides basic results about `List.prod`, `List.sum`, which calculate the product and sum
of elements of a list and `List.alternatingProd`, `List.alternatingSum`, their alternating
counterparts.
-/

public section
assert_not_imported Mathlib.Algebra.Order.Group.Nat

variable {ι α β M N P G : Type*}

namespace List

section Monoid

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

open scoped Relator in
@[to_additive]
/--
theorem `rel_prod` / 定理 `rel_prod`

English:
theorem rel_prod
  given: {R : M -> N -> Prop} (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·))
  proof: rel_foldr hf h

@[to_additive]

中文:
定理 rel_prod
  条件: {R : M -> N -> 命题} (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·))
  证明: rel_foldr hf h

@[to_additive]

Depends on / 依赖: rel_foldr
-/
theorem rel_prod {R : M -> N -> Prop} (h : R 1 1) (hf : (R ⇒ R ⇒ R) (· * ·) (· * ·)) :
    (Forall₂ R ⇒ R) prod prod :=
  rel_foldr hf h

@[to_additive]
/--
theorem `prod_hom_nonempty` / 定理 `prod_hom_nonempty`

English:
theorem prod_hom_nonempty
  statement: {l : List M} {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
  proof: match l, hl with | x :: xs, hl => by induction xs generalizing x <;> simp_all

@[to_additive]

中文:
定理 prod_hom_nonempty
  结论: {l : 列表 M} {F : 类型} [函数状 F M N] [乘法态射类 F M N] (f : F)
  证明: match l, hl with | x :: xs, hl => by induction xs generalizing x <;> simp_all

@[to_additive]

Depends on / 依赖: generalizing
-/
theorem prod_hom_nonempty {l : List M} {F : Type*} [FunLike F M N] [MulHomClass F M N] (f : F)
    (hl : l != []) : (l.map f).prod = f l.prod :=
  match l, hl with | x :: xs, hl => by induction xs generalizing x <;> simp_all

@[to_additive]
/--
theorem `prod_hom` / 定理 `prod_hom`

English:
theorem prod_hom
  given: (l : List M) {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F)
  proof: by
  simp only [prod, foldr_map, ← map_one f]
  exact l.foldr_hom f (fun x y => (map_mul f x y).symm)

@[to_additive]

中文:
定理 prod_hom
  条件: (l : 列表 M) {F : 类型} [函数状 F M N] [幺半群态射类 F M N] (f : F)
  证明: by
  simp only [prod, foldr_map, ← map_one f]
  exact l.foldr_hom f (fun x y => (map_mul f x y).symm)

@[to_additive]

Depends on / 依赖: foldr_hom, foldr_map, l.foldr_hom, map_mul, map_one
-/
theorem prod_hom (l : List M) {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) :
    (l.map f).prod = f l.prod := by
  simp only [prod, foldr_map, ← map_one f]
  exact l.foldr_hom f (fun x y => (map_mul f x y).symm)

@[to_additive]
/--
theorem `prod_hom₂_nonempty` / 定理 `prod_hom₂_nonempty`

English:
theorem prod_hom₂_nonempty
  statement: {l : List ι} (f : M -> N -> P)
  proof: by
  match l, hl with | x :: xs, hl => induction xs generalizing x <;> simp_all

@[to_additive]

中文:
定理 prod_hom₂_nonempty
  结论: {l : 列表 ι} (f : M -> N -> P)
  证明: by
  match l, hl with | x :: xs, hl => induction xs generalizing x <;> simp_all

@[to_additive]

Depends on / 依赖: generalizing
-/
theorem prod_hom₂_nonempty {l : List ι} (f : M -> N -> P)
    (hf : forall a b c d, f (a * b) (c * d) = f a c * f b d) (f₁ : ι -> M) (f₂ : ι -> N) (hl : l != []) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  match l, hl with | x :: xs, hl => induction xs generalizing x <;> simp_all

@[to_additive]
/--
theorem `prod_hom₂` / 定理 `prod_hom₂`

English:
theorem prod_hom₂
  statement: (l : List ι) (f : M -> N -> P) (hf : forall a b c d, f (a * b) (c * d) = f a c * f b d)
  proof: by
  simp only [prod_eq_foldr, foldr_map]
  rw [← foldr_hom₂ l f _ _ ((fun x y => f (f₁ x) (f₂ x) * y)) _ _ (by simp [hf]), hf']

@[to_additive (attr := simp)]

中文:
定理 prod_hom₂
  结论: (l : 列表 ι) (f : M -> N -> P) (hf : 对任意 a b c d, f (a * b) (c * d) = f a c * f b d)
  证明: by
  simp only [prod_eq_foldr, foldr_map]
  rw [← foldr_hom₂ l f _ _ ((fun x y => f (f₁ x) (f₂ x) * y)) _ _ (by simp [hf]), hf']

@[to_additive (attr := simp)]

Depends on / 依赖: foldr_map, prod_eq_foldr
-/
theorem prod_hom₂ (l : List ι) (f : M -> N -> P) (hf : forall a b c d, f (a * b) (c * d) = f a c * f b d)
    (hf' : f 1 1 = 1) (f₁ : ι -> M) (f₂ : ι -> N) :
    (l.map fun i => f (f₁ i) (f₂ i)).prod = f (l.map f₁).prod (l.map f₂).prod := by
  simp only [prod_eq_foldr, foldr_map]
  rw [← foldr_hom₂ l f _ _ ((fun x y => f (f₁ x) (f₂ x) * y)) _ _ (by simp [hf]), hf']

@[to_additive (attr := simp)]
/--
theorem `prod_map_mul` / 定理 `prod_map_mul`

English:
theorem prod_map_mul
  given: {M : Type*} [CommMonoid M] {l : List ι} {f g : ι -> M}
  proof: l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]

中文:
定理 prod_map_mul
  条件: {M : 类型} [交换幺半群 M] {l : 列表 ι} {f g : ι -> M}
  证明: l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]

Depends on / 依赖: l.prod_hom, mul_mul_mul_comm, mul_one
-/
theorem prod_map_mul {M : Type*} [CommMonoid M] {l : List ι} {f g : ι -> M} :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod :=
  l.prod_hom₂ (· * ·) mul_mul_mul_comm (mul_one _) _ _

@[to_additive]
/--
theorem `prod_map_hom` / 定理 `prod_map_hom`

English:
theorem prod_map_hom
  statement: (L : List ι) (f : ι -> M) {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
  proof: by rw [← prod_hom, map_map]

@[to_additive (attr := simp)]

中文:
定理 prod_map_hom
  结论: (L : 列表 ι) (f : ι -> M) {G : 类型} [函数状 G M N] [幺半群态射类 G M N]
  证明: by rw [← prod_hom, map_map]

@[to_additive (attr := simp)]

Depends on / 依赖: map_map, prod_hom
-/
theorem prod_map_hom (L : List ι) (f : ι -> M) {G : Type*} [FunLike G M N] [MonoidHomClass G M N]
    (g : G) :
    (L.map (g ∘ f)).prod = g (L.map f).prod := by rw [← prod_hom, map_map]

@[to_additive (attr := simp)]
/--
theorem `prod_take_mul_prod_drop` / 定理 `prod_take_mul_prod_drop`

English:
theorem prod_take_mul_prod_drop
  given: (L : List M) (i : Nat)
  proof: by
  simp [← prod_append]

@[to_additive (attr := simp)]

中文:
定理 prod_take_mul_prod_drop
  条件: (L : 列表 M) (i : 自然数)
  证明: by
  simp [← prod_append]

@[to_additive (attr := simp)]

Depends on / 依赖: prod_append
-/
theorem prod_take_mul_prod_drop (L : List M) (i : Nat) :
    (L.take i).prod * (L.drop i).prod = L.prod := by
  simp [← prod_append]

@[to_additive (attr := simp)]
/--
theorem `prod_take_succ` / 定理 `prod_take_succ`

English:
theorem prod_take_succ
  given: (L : List M) (i : Nat) (p : i < L.length)
  proof: by
  rw [← take_concat_get' _ _ p]; rw [prod_append]
  simp

中文:
定理 prod_take_succ
  条件: (L : 列表 M) (i : 自然数) (p : i < L.length)
  证明: by
  rw [← take_concat_get' _ _ p]; rw [prod_append]
  simp

Depends on / 依赖: prod_append, take_concat_get
-/
theorem prod_take_succ (L : List M) (i : Nat) (p : i < L.length) :
    (L.take (i + 1)).prod = (L.take i).prod * L[i] := by
  rw [← take_concat_get' _ _ p]; rw [prod_append]
  simp

/-- A list with product not one must have positive length. -/
@[to_additive /-- A list with sum not zero must have positive length. -/]
/--
theorem `length_pos_of_prod_ne_one` / 定理 `length_pos_of_prod_ne_one`

English:
theorem length_pos_of_prod_ne_one
  given: (L : List M) (h : L.prod != 1)
  statement: 0 < L.length
  proof: by
  cases L
  · simp at h
  · simp

中文:
定理 length_pos_of_prod_ne_one
  条件: (L : 列表 M) (h : L.乘积 != 1)
  结论: 0 < L.length
  证明: by
  cases L
  · simp at h
  · simp
-/
theorem length_pos_of_prod_ne_one (L : List M) (h : L.prod != 1) : 0 < L.length := by
  cases L
  · simp at h
  · simp

/-- A list with product greater than one must have positive length. -/
@[to_additive length_pos_of_sum_pos /-- A list with positive sum must have positive length. -/]
/--
theorem `length_pos_of_one_lt_prod` / 定理 `length_pos_of_one_lt_prod`

English:
theorem length_pos_of_one_lt_prod
  given: [Preorder M] (L : List M) (h : 1 < L.prod)
  statement: 0 < L.length
  proof: length_pos_of_prod_ne_one L h.ne'

中文:
定理 length_pos_of_one_lt_prod
  条件: [预序 M] (L : 列表 M) (h : 1 < L.乘积)
  结论: 0 < L.length
  证明: length_pos_of_prod_ne_one L h.ne'

Depends on / 依赖: h.ne, length_pos_of_prod_ne_one
-/
theorem length_pos_of_one_lt_prod [Preorder M] (L : List M) (h : 1 < L.prod) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne'

/-- A list with product less than one must have positive length. -/
@[to_additive /-- A list with negative sum must have positive length. -/]
/--
theorem `length_pos_of_prod_lt_one` / 定理 `length_pos_of_prod_lt_one`

English:
theorem length_pos_of_prod_lt_one
  given: [Preorder M] (L : List M) (h : L.prod < 1)
  statement: 0 < L.length
  proof: length_pos_of_prod_ne_one L h.ne

@[to_additive]

中文:
定理 length_pos_of_prod_lt_one
  条件: [预序 M] (L : 列表 M) (h : L.乘积 < 1)
  结论: 0 < L.length
  证明: length_pos_of_prod_ne_one L h.ne

@[to_additive]

Depends on / 依赖: h.ne, length_pos_of_prod_ne_one
-/
theorem length_pos_of_prod_lt_one [Preorder M] (L : List M) (h : L.prod < 1) : 0 < L.length :=
  length_pos_of_prod_ne_one L h.ne

@[to_additive]
/--
theorem `prod_set` / 定理 `prod_set`

English:
theorem prod_set

中文:
定理 prod_set
-/
theorem prod_set :
    forall (L : List M) (n : Nat) (a : M),
      (L.set n a).prod =
        ((L.take n).prod * if n < L.length then a else 1) * (L.drop (n + 1)).prod
  | x :: xs, 0, a => by simp [set]
  | x :: xs, i + 1, a => by simp [set, prod_set xs i a, mul_assoc]
  | [], _, _ => by simp [set]

/-- We'd like to state this as `L.headI * L.tail.prod = L.prod`, but because `L.headI` relies on an
inhabited instance to return a garbage value on the empty list, this is not possible.
Instead, we write the statement in terms of `L[0]?.getD 1`.
-/
@[to_additive /-- We'd like to state this as `L.headI + L.tail.sum = L.sum`, but because `L.headI`
  relies on an inhabited instance to return a garbage value on the empty list, this is not possible.
  Instead, we write the statement in terms of `L[0]?.getD 0`. -/]
/--
theorem `getElem?_zero_mul_tail_prod` / 定理 `getElem?_zero_mul_tail_prod`

English:
theorem getElem?_zero_mul_tail_prod
  given: (l : List M)
  statement: l[0]?.getD 1 * l.tail.prod = l.prod
  proof: by
  cases l <;> simp

中文:
定理 getElem?_zero_mul_tail_prod
  条件: (l : 列表 M)
  结论: l[0]?.getD 1 * l.tail.乘积 = l.乘积
  证明: by
  cases l <;> simp
-/
theorem getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.prod := by
  cases l <;> simp

/-- Same as `get?_zero_mul_tail_prod`, but avoiding the `List.headI` garbage complication by
  requiring the list to be nonempty. -/
@[to_additive /-- Same as `get?_zero_add_tail_sum`, but avoiding the `List.headI` garbage
  complication by requiring the list to be nonempty. -/]
/--
theorem `headI_mul_tail_prod_of_ne_nil` / 定理 `headI_mul_tail_prod_of_ne_nil`

English:
theorem headI_mul_tail_prod_of_ne_nil
  given: [Inhabited M] (l : List M) (h : l != [])
  proof: by cases l <;> [contradiction; simp]

@[to_additive]

中文:
定理 headI_mul_tail_prod_of_ne_nil
  条件: [可居 M] (l : 列表 M) (h : l != [])
  证明: by cases l <;> [contradiction; simp]

@[to_additive]
-/
theorem headI_mul_tail_prod_of_ne_nil [Inhabited M] (l : List M) (h : l != []) :
    l.headI * l.tail.prod = l.prod := by cases l <;> [contradiction; simp]

@[to_additive]
/--
theorem `_root_.Commute.list_prod_right` / 定理 `_root_.Commute.list_prod_right`

English:
theorem _root_.Commute.list_prod_right
  given: (l : List M) (y : M) (h : forall x in l, Commute y x)
  proof: by
  induction l with
  | nil => simp
  | cons z l IH =>
    rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)

@[to_additive]

中文:
定理 _root_.Commute.list_prod_right
  条件: (l : 列表 M) (y : M) (h : 对任意 x in l, Commute y x)
  证明: by
  induction l with
  | nil => simp
  | cons z l IH =>
    rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)

@[to_additive]

Depends on / 依赖: Commute, Commute.mul_right, List.forall_mem_cons, List.prod_cons, forall_mem_cons, mul_right, prod_cons
-/
theorem _root_.Commute.list_prod_right (l : List M) (y : M) (h : forall x in l, Commute y x) :
    Commute y l.prod := by
  induction l with
  | nil => simp
  | cons z l IH =>
    rw [List.forall_mem_cons] at h
    rw [List.prod_cons]
    exact Commute.mul_right h.1 (IH h.2)

@[to_additive]
/--
theorem `_root_.Commute.list_prod_left` / 定理 `_root_.Commute.list_prod_left`

English:
theorem _root_.Commute.list_prod_left
  given: (l : List M) (y : M) (h : forall x in l, Commute x y)
  proof: ((Commute.list_prod_right _ _) fun _ hx => (h _ hx).symm).symm

中文:
定理 _root_.Commute.list_prod_left
  条件: (l : 列表 M) (y : M) (h : 对任意 x in l, Commute x y)
  证明: ((Commute.list_prod_right _ _) fun _ hx => (h _ hx).symm).symm

Depends on / 依赖: Commute, Commute.list_prod_right, list_prod_right
-/
theorem _root_.Commute.list_prod_left (l : List M) (y : M) (h : forall x in l, Commute x y) :
    Commute l.prod y :=
  ((Commute.list_prod_right _ _) fun _ hx => (h _ hx).symm).symm

/--
lemma `prod_range_succ` / 引理 `prod_range_succ`

English:
lemma prod_range_succ
  given: (f : Nat -> M) (n : Nat)
  proof: by
  rw [range_succ]; rw [map_append]; rw [map_singleton]; rw [prod_append]; rw [prod_cons]; rw [prod_nil]; rw [mul_one]

中文:
引理 prod_range_succ
  条件: (f : 自然数 -> M) (n : 自然数)
  证明: by
  rw [range_succ]; rw [map_append]; rw [map_singleton]; rw [prod_append]; rw [prod_cons]; rw [prod_nil]; rw [mul_one]
-/
@[to_additive] lemma prod_range_succ (f : Nat -> M) (n : Nat) :
    ((range n.succ).map f).prod = ((range n).map f).prod * f n := by
  rw [range_succ]; rw [map_append]; rw [map_singleton]; rw [prod_append]; rw [prod_cons]; rw [prod_nil]; rw [mul_one]

/-- A variant of `prod_range_succ` which pulls off the first term in the product rather than the
last. -/
@[to_additive /-- A variant of `sum_range_succ` which pulls off the first term in the sum rather
than the last. -/]
/--
lemma `prod_range_succ'` / 引理 `prod_range_succ'`

English:
lemma prod_range_succ'
  given: (f : Nat -> M) (n : Nat)
  proof: by
  rw [range_succ_eq_map]
  simp [Function.comp_def]

中文:
引理 prod_range_succ'
  条件: (f : 自然数 -> M) (n : 自然数)
  证明: by
  rw [range_succ_eq_map]
  simp [Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, comp_def, range_succ_eq_map
-/
lemma prod_range_succ' (f : Nat -> M) (n : Nat) :
    ((range n.succ).map f).prod = f 0 * ((range n).map fun i => f i.succ).prod := by
  rw [range_succ_eq_map]
  simp [Function.comp_def]

/--
lemma `prod_eq_one` / 引理 `prod_eq_one`

English:
lemma prod_eq_one
  given: (hl : forall x in l, x = 1)
  statement: l.prod = 1
  proof: by
  induction l with
  | nil => rfl
  | cons i l hil =>
    rw [List.prod_cons]; rw [hil fun x hx => hl _ (mem_cons_of_mem i hx)]; rw [hl _ mem_cons_self]; rw [one_mul]

中文:
引理 prod_eq_one
  条件: (hl : 对任意 x in l, x = 1)
  结论: l.乘积 = 1
  证明: by
  induction l with
  | nil => rfl
  | cons i l hil =>
    rw [List.prod_cons]; rw [hil fun x hx => hl _ (mem_cons_of_mem i hx)]; rw [hl _ mem_cons_self]; rw [one_mul]
-/
@[to_additive] lemma prod_eq_one (hl : forall x in l, x = 1) : l.prod = 1 := by
  induction l with
  | nil => rfl
  | cons i l hil =>
    rw [List.prod_cons]; rw [hil fun x hx => hl _ (mem_cons_of_mem i hx)]; rw [hl _ mem_cons_self]; rw [one_mul]

/--
lemma `exists_mem_ne_one_of_prod_ne_one` / 引理 `exists_mem_ne_one_of_prod_ne_one`

English:
lemma exists_mem_ne_one_of_prod_ne_one
  given: (h : l.prod != 1)
  proof: by simpa only [not_forall, exists_prop] using mt prod_eq_one h

@[to_additive]

中文:
引理 存在_mem_ne_one_of_prod_ne_one
  条件: (h : l.乘积 != 1)
  证明: by simpa only [not_forall, exists_prop] using mt prod_eq_one h

@[to_additive]
-/
@[to_additive] lemma exists_mem_ne_one_of_prod_ne_one (h : l.prod != 1) :
    exists x in l, x != (1 : M) := by simpa only [not_forall, exists_prop] using mt prod_eq_one h

@[to_additive]
/--
lemma `prod_erase_of_comm` / 引理 `prod_erase_of_comm`

English:
lemma prod_erase_of_comm
  given: [DecidableEq M] (ha : a in l) (comm : forall x in l, forall y in l, x * y = y * x)
  proof: by
  induction l with
  | nil => simp only [not_mem_nil] at ha
  | cons b l ih =>
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem ha
    · simp only [erase_cons_head, prod_cons]
    rw [List.erase]; rw [beq_false_of_ne ne.symm]; rw [List.prod_cons]; rw [List.prod_cons]; rw [← mul_assoc]; rw [co

中文:
引理 prod_erase_of_comm
  条件: [DecidableEq M] (ha : a in l) (comm : 对任意 x in l, 对任意 y in l, x * y = y * x)
  证明: by
  induction l with
  | nil => simp only [not_mem_nil] at ha
  | cons b l ih =>
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem ha
    · simp only [erase_cons_head, prod_cons]
    rw [List.erase]; rw [beq_false_of_ne ne.symm]; rw [List.prod_cons]; rw [List.prod_cons]; rw [← mul_assoc]; rw [co

Depends on / 依赖: List.eq_or_ne_mem_of_mem, List.erase, List.mem_cons_of_mem, List.prod_cons, beq_false_of_ne, eq_or_ne_mem_of_mem, erase_cons_head, mem_cons_of_mem, mem_cons_self, mul_assoc, ne.symm, not_mem_nil, prod_cons
-/
lemma prod_erase_of_comm [DecidableEq M] (ha : a in l) (comm : forall x in l, forall y in l, x * y = y * x) :
    a * (l.erase a).prod = l.prod := by
  induction l with
  | nil => simp only [not_mem_nil] at ha
  | cons b l ih =>
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem ha
    · simp only [erase_cons_head, prod_cons]
    rw [List.erase]; rw [beq_false_of_ne ne.symm]; rw [List.prod_cons]; rw [List.prod_cons]; rw [← mul_assoc]; rw [comm a ha b mem_cons_self]; rw [mul_assoc]; rw [ih h fun x hx y hy => comm _ (List.mem_cons_of_mem b hx) _ (List.mem_cons_of_mem b hy)]

@[to_additive]
/--
lemma `prod_map_eq_pow_single` / 引理 `prod_map_eq_pow_single`

English:
lemma prod_map_eq_pow_single
  statement: [DecidableEq α] {l : List α} (a : α) (f : α -> M)
  proof: by
  induction l generalizing a with
  | nil => rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  | cons a' as h =>
    specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons]; rw [List.prod_cons]; rw [count_cons]; rw [h]
    simp only [beq_iff_eq]
    split_if

中文:
引理 prod_map_eq_pow_single
  结论: [DecidableEq α] {l : 列表 α} (a : α) (f : α -> M)
  证明: by
  induction l generalizing a with
  | nil => rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  | cons a' as h =>
    specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons]; rw [List.prod_cons]; rw [count_cons]; rw [h]
    simp only [beq_iff_eq]
    split_if

Depends on / 依赖: List.map_cons, List.prod_cons, _root_, _root_.pow_succ, _root_.pow_zero, add_zero, beq_iff_eq, count_cons, count_nil, generalizing, map_cons, map_nil, mem_cons_of_mem, mem_cons_self, one_mul, pow_succ, pow_zero, prod_cons, prod_nil, specialize
-/
lemma prod_map_eq_pow_single [DecidableEq α] {l : List α} (a : α) (f : α -> M)
    (hf : forall a', a' != a -> a' in l -> f a' = 1) : (l.map f).prod = f a ^ l.count a := by
  induction l generalizing a with
  | nil => rw [map_nil, prod_nil, count_nil, _root_.pow_zero]
  | cons a' as h =>
    specialize h a fun a' ha' hfa' => hf a' ha' (mem_cons_of_mem _ hfa')
    rw [List.map_cons]; rw [List.prod_cons]; rw [count_cons]; rw [h]
    simp only [beq_iff_eq]
    split_ifs with ha'
    · rw [ha', _root_.pow_succ']
    · rw [hf a' ha' mem_cons_self, one_mul, add_zero]

@[to_additive]
/--
lemma `prod_eq_pow_single` / 引理 `prod_eq_pow_single`

English:
lemma prod_eq_pow_single
  given: [DecidableEq M] (a : M) (h : forall a', a' != a -> a' in l -> a' = 1)
  proof: _root_.trans (by rw [map_id]) (prod_map_eq_pow_single a id h)

@[to_additive (attr := simp)]

中文:
引理 prod_eq_pow_single
  条件: [DecidableEq M] (a : M) (h : 对任意 a', a' != a -> a' in l -> a' = 1)
  证明: _root_.trans (by rw [map_id]) (prod_map_eq_pow_single a id h)

@[to_additive (attr := simp)]

Depends on / 依赖: _root_, _root_.trans, map_id, prod_map_eq_pow_single
-/
lemma prod_eq_pow_single [DecidableEq M] (a : M) (h : forall a', a' != a -> a' in l -> a' = 1) :
    l.prod = a ^ l.count a :=
  _root_.trans (by rw [map_id]) (prod_map_eq_pow_single a id h)

@[to_additive (attr := simp)]
/--
theorem `prod_insertIdx` / 定理 `prod_insertIdx`

English:
theorem prod_insertIdx
  given: {i} (hlen : i <= l.length) (hcomm : forall a' in l.take i, Commute a a')
  proof: by
  induction i generalizing l
  case zero => rfl
  case succ i ih =>
    obtain ⟨hd, tl, rfl⟩ := exists_cons_of_length_pos (Nat.zero_lt_of_lt hlen)
    simp only [insertIdx_succ_cons, prod_cons,
      ih (Nat.le_of_lt_succ hlen) (fun a' a'_mem => hcomm a' (mem_of_mem_tail a'_mem))]
    exact Commu

中文:
定理 prod_insertIdx
  条件: {i} (hlen : i <= l.length) (hcomm : 对任意 a' in l.take i, Commute a a')
  证明: by
  induction i generalizing l
  case zero => rfl
  case succ i ih =>
    obtain ⟨hd, tl, rfl⟩ := exists_cons_of_length_pos (Nat.zero_lt_of_lt hlen)
    simp only [insertIdx_succ_cons, prod_cons,
      ih (Nat.le_of_lt_succ hlen) (fun a' a'_mem => hcomm a' (mem_of_mem_tail a'_mem))]
    exact Commu

Depends on / 依赖: Commute, Commute.left_comm, Nat.le_of_lt_succ, Nat.zero_lt_of_lt, _mem, exists_cons_of_length_pos, generalizing, insertIdx_succ_cons, le_of_lt_succ, left_comm, mem_of_mem_head, mem_of_mem_tail, prod_cons, tl.prod, zero_lt_of_lt
-/
theorem prod_insertIdx {i} (hlen : i <= l.length) (hcomm : forall a' in l.take i, Commute a a') :
    (l.insertIdx i a).prod = a * l.prod := by
  induction i generalizing l
  case zero => rfl
  case succ i ih =>
    obtain ⟨hd, tl, rfl⟩ := exists_cons_of_length_pos (Nat.zero_lt_of_lt hlen)
    simp only [insertIdx_succ_cons, prod_cons,
      ih (Nat.le_of_lt_succ hlen) (fun a' a'_mem => hcomm a' (mem_of_mem_tail a'_mem))]
    exact Commute.left_comm (hcomm hd (mem_of_mem_head? rfl)).symm tl.prod

@[to_additive (attr := simp)]
/--
theorem `mul_prod_eraseIdx` / 定理 `mul_prod_eraseIdx`

English:
theorem mul_prod_eraseIdx
  given: {i} (hlen : i < l.length) (hcomm : forall a' in l.take i, Commute l[i] a')
  proof: by
  rw [← prod_insertIdx (by grind : i <= (l.eraseIdx i).length) (fun a' a'_mem =>
      hcomm a' (by rwa [take_eraseIdx_eq_take_of_le l i i (Nat.le_refl i)] at a'_mem)),
    insertIdx_eraseIdx_getElem hlen]

@[to_additive (attr := simp)]

中文:
定理 mul_prod_eraseIdx
  条件: {i} (hlen : i < l.length) (hcomm : 对任意 a' in l.take i, Commute l[i] a')
  证明: by
  rw [← prod_insertIdx (by grind : i <= (l.eraseIdx i).length) (fun a' a'_mem =>
      hcomm a' (by rwa [take_eraseIdx_eq_take_of_le l i i (Nat.le_refl i)] at a'_mem)),
    insertIdx_eraseIdx_getElem hlen]

@[to_additive (attr := simp)]

Depends on / 依赖: Nat.le_refl, _mem, eraseIdx, insertIdx_eraseIdx_getElem, l.eraseIdx, le_refl, length, prod_insertIdx, take_eraseIdx_eq_take_of_le
-/
theorem mul_prod_eraseIdx {i} (hlen : i < l.length) (hcomm : forall a' in l.take i, Commute l[i] a') :
    l[i] * (l.eraseIdx i).prod = l.prod := by
  rw [← prod_insertIdx (by grind : i <= (l.eraseIdx i).length) (fun a' a'_mem =>
      hcomm a' (by rwa [take_eraseIdx_eq_take_of_le l i i (Nat.le_refl i)] at a'_mem)),
    insertIdx_eraseIdx_getElem hlen]

@[to_additive (attr := simp)]
/--
theorem `prod_filter_bne_one` / 定理 `prod_filter_bne_one`

English:
theorem prod_filter_bne_one
  given: [BEq M] [LawfulBEq M] (l : List M)
  proof: by
  classical induction l <;> grind

中文:
定理 prod_filter_bne_one
  条件: [BEq M] [LawfulBEq M] (l : 列表 M)
  证明: by
  classical induction l <;> grind

Depends on / 依赖: classical
-/
theorem prod_filter_bne_one [BEq M] [LawfulBEq M] (l : List M) :
    (l.filter (· != 1)).prod = l.prod := by
  classical induction l <;> grind

end Monoid

section CommMonoid
variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

@[to_additive (attr := simp)]
/--
theorem `CommMonoid.prod_insertIdx` / 定理 `CommMonoid.prod_insertIdx`

English:
theorem CommMonoid.prod_insertIdx
  given: {i} (h : i <= l.length)
  statement: (l.insertIdx i a).prod = a * l.prod
  proof: List.prod_insertIdx h (fun a' _ => Commute.all a a')

@[to_additive (attr := simp)]

中文:
定理 交换幺半群.prod_insertIdx
  条件: {i} (h : i <= l.length)
  结论: (l.insertIdx i a).乘积 = a * l.乘积
  证明: List.prod_insertIdx h (fun a' _ => Commute.all a a')

@[to_additive (attr := simp)]

Depends on / 依赖: Commute, Commute.all, List.prod_insertIdx, prod_insertIdx
-/
theorem CommMonoid.prod_insertIdx {i} (h : i <= l.length) : (l.insertIdx i a).prod = a * l.prod :=
  List.prod_insertIdx h (fun a' _ => Commute.all a a')

@[to_additive (attr := simp)]
/--
theorem `CommMonoid.mul_prod_eraseIdx` / 定理 `CommMonoid.mul_prod_eraseIdx`

English:
theorem CommMonoid.mul_prod_eraseIdx
  given: {i} (h : i < l.length)
  statement: l[i] * (l.eraseIdx i).prod = l.prod
  proof: List.mul_prod_eraseIdx h (fun a' _ => Commute.all l[i] a')

@[to_additive (attr := simp)]

中文:
定理 交换幺半群.mul_prod_eraseIdx
  条件: {i} (h : i < l.length)
  结论: l[i] * (l.eraseIdx i).乘积 = l.乘积
  证明: List.mul_prod_eraseIdx h (fun a' _ => Commute.all l[i] a')

@[to_additive (attr := simp)]

Depends on / 依赖: Commute, Commute.all, List.mul_prod_eraseIdx, mul_prod_eraseIdx
-/
theorem CommMonoid.mul_prod_eraseIdx {i} (h : i < l.length) : l[i] * (l.eraseIdx i).prod = l.prod :=
  List.mul_prod_eraseIdx h (fun a' _ => Commute.all l[i] a')

@[to_additive (attr := simp)]
/--
lemma `prod_erase` / 引理 `prod_erase`

English:
lemma prod_erase
  given: [DecidableEq M] (ha : a in l)
  statement: a * (l.erase a).prod = l.prod
  proof: prod_erase_of_comm ha fun x _ y _ => mul_comm x y

@[to_additive (attr := simp)]

中文:
引理 prod_erase
  条件: [DecidableEq M] (ha : a in l)
  结论: a * (l.erase a).乘积 = l.乘积
  证明: prod_erase_of_comm ha fun x _ y _ => mul_comm x y

@[to_additive (attr := simp)]

Depends on / 依赖: mul_comm, prod_erase_of_comm
-/
lemma prod_erase [DecidableEq M] (ha : a in l) : a * (l.erase a).prod = l.prod :=
  prod_erase_of_comm ha fun x _ y _ => mul_comm x y

@[to_additive (attr := simp)]
/--
lemma `prod_map_erase` / 引理 `prod_map_erase`

English:
lemma prod_map_erase
  given: [DecidableEq α] (f : α -> M) {a}
  proof: List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    · simp only [map, erase_cons_tail (not_beq_of_ne ne.symm), prod_cons, prod_map_erase _ h,
        mul_left_comm (f a) (f b)]

中文:
引理 prod_map_erase
  条件: [DecidableEq α] (f : α -> M) {a}
  证明: List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    · simp only [map, erase_cons_tail (not_beq_of_ne ne.symm), prod_cons, prod_map_erase _ h,
        mul_left_comm (f a) (f b)]

Depends on / 依赖: List.eq_or_ne_mem_of_mem, eq_or_ne_mem_of_mem
-/
lemma prod_map_erase [DecidableEq α] (f : α -> M) {a} :
    forall {l : List α}, a in l -> f a * ((l.erase a).map f).prod = (l.map f).prod
  | b :: l, h => by
    obtain rfl | ⟨ne, h⟩ := List.eq_or_ne_mem_of_mem h
    · simp only [map, erase_cons_head, prod_cons]
    · simp only [map, erase_cons_tail (not_beq_of_ne ne.symm), prod_cons, prod_map_erase _ h,
        mul_left_comm (f a) (f b)]

/--
lemma `Perm.prod_eq` / 引理 `Perm.prod_eq`

English:
lemma Perm.prod_eq
  given: (h : Perm l₁ l₂)
  statement: prod l₁ = prod l₂
  proof: h.foldr_op_eq

中文:
引理 置换.prod_eq
  条件: (h : 置换 l₁ l₂)
  结论: 乘积 l₁ = 乘积 l₂
  证明: h.foldr_op_eq
-/
@[to_additive] lemma Perm.prod_eq (h : Perm l₁ l₂) : prod l₁ = prod l₂ := h.foldr_op_eq

attribute [to_additive existing] prod_reverse

@[to_additive]
/--
lemma `prod_mul_prod_eq_prod_zipWith_mul_prod_drop` / 引理 `prod_mul_prod_eq_prod_zipWith_mul_prod_drop`

English:
lemma prod_mul_prod_eq_prod_zipWith_mul_prod_drop

中文:
引理 prod_mul_prod_eq_prod_zipWith_mul_prod_drop
-/
lemma prod_mul_prod_eq_prod_zipWith_mul_prod_drop :
    forall l l' : List M,
      l.prod * l'.prod =
        (zipWith (· * ·) l l').prod * (l.drop l'.length).prod * (l'.drop l.length).prod
  | [], ys => by simp
  | xs, [] => by simp
  | x :: xs, y :: ys => by
    simp only [zipWith_cons_cons, prod_cons]
    conv =>
      lhs; rw [mul_assoc]; right; rw [mul_comm, mul_assoc]; right
      rw [mul_comm]; rw [prod_mul_prod_eq_prod_zipWith_mul_prod_drop xs ys]
    simp [mul_assoc]

@[to_additive]
/--
lemma `prod_mul_prod_eq_prod_zipWith_of_length_eq` / 引理 `prod_mul_prod_eq_prod_zipWith_of_length_eq`

English:
lemma prod_mul_prod_eq_prod_zipWith_of_length_eq
  given: (l l' : List M) (h : l.length = l'.length)
  proof: by
  apply (prod_mul_prod_eq_prod_zipWith_mul_prod_drop l l').trans
  rw [← h]; rw [drop_length]; rw [h]; rw [drop_length]; rw [prod_nil]; rw [mul_one]; rw [mul_one]

@[to_additive]

中文:
引理 prod_mul_prod_eq_prod_zipWith_of_length_eq
  条件: (l l' : 列表 M) (h : l.length = l'.length)
  证明: by
  apply (prod_mul_prod_eq_prod_zipWith_mul_prod_drop l l').trans
  rw [← h]; rw [drop_length]; rw [h]; rw [drop_length]; rw [prod_nil]; rw [mul_one]; rw [mul_one]

@[to_additive]

Depends on / 依赖: drop_length, mul_one, prod_mul_prod_eq_prod_zipWith_mul_prod_drop, prod_nil
-/
lemma prod_mul_prod_eq_prod_zipWith_of_length_eq (l l' : List M) (h : l.length = l'.length) :
    l.prod * l'.prod = (zipWith (· * ·) l l').prod := by
  apply (prod_mul_prod_eq_prod_zipWith_mul_prod_drop l l').trans
  rw [← h]; rw [drop_length]; rw [h]; rw [drop_length]; rw [prod_nil]; rw [mul_one]; rw [mul_one]

@[to_additive]
/--
lemma `prod_map_ite` / 引理 `prod_map_ite`

English:
lemma prod_map_ite
  given: (p : α -> Prop) [DecidablePred p] (f g : α -> M) (l : List α)
  proof: by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, filter_cons, prod_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : p x
    · simp only [hx, ↓reduceIte, decide_not, decide_true, map_cons, prod_cons, not_true_eq_false,
        decide_false, Bool.false_eq_true

中文:
引理 prod_map_ite
  条件: (p : α -> 命题) [DecidablePred p] (f g : α -> M) (l : 列表 α)
  证明: by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, filter_cons, prod_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : p x
    · simp only [hx, ↓reduceIte, decide_not, decide_true, map_cons, prod_cons, not_true_eq_false,
        decide_false, Bool.false_eq_true

Depends on / 依赖: Bool.false_eq_true, decide_false, decide_not, decide_true, false_eq_true, filter_cons, map_cons, mul_assoc, mul_left_comm, not_false_eq_true, not_true_eq_false, prod_cons, reduceIte
-/
lemma prod_map_ite (p : α -> Prop) [DecidablePred p] (f g : α -> M) (l : List α) :
    (l.map fun a => if p a then f a else g a).prod =
      ((l.filter p).map f).prod * ((l.filter fun a => ¬p a).map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, filter_cons, prod_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : p x
    · simp only [hx, ↓reduceIte, decide_not, decide_true, map_cons, prod_cons, not_true_eq_false,
        decide_false, Bool.false_eq_true, mul_assoc]
    · simp only [hx, ↓reduceIte, decide_not, decide_false, Bool.false_eq_true, not_false_eq_true,
      decide_true, map_cons, prod_cons, mul_left_comm]

@[to_additive]
/--
lemma `prod_map_filter_mul_prod_map_filter_not` / 引理 `prod_map_filter_mul_prod_map_filter_not`

English:
lemma prod_map_filter_mul_prod_map_filter_not
  statement: (p : α -> Prop) [DecidablePred p] (f : α -> M)
  proof: by
  rw [← prod_map_ite]
  simp only [ite_self]

中文:
引理 prod_map_filter_mul_prod_map_filter_not
  结论: (p : α -> 命题) [DecidablePred p] (f : α -> M)
  证明: by
  rw [← prod_map_ite]
  simp only [ite_self]

Depends on / 依赖: ite_self, prod_map_ite
-/
lemma prod_map_filter_mul_prod_map_filter_not (p : α -> Prop) [DecidablePred p] (f : α -> M)
    (l : List α) :
    ((l.filter p).map f).prod * ((l.filter fun x => ¬p x).map f).prod = (l.map f).prod := by
  rw [← prod_map_ite]
  simp only [ite_self]

end CommMonoid

@[to_additive]
/--
lemma `eq_of_prod_take_eq` / 引理 `eq_of_prod_take_eq`

English:
lemma eq_of_prod_take_eq
  statement: [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
  proof: by
  refine ext_get h fun i h₁ h₂ => ?_
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [prod_take_succ L i h₁]; rw [prod_take_succ L' i h₂]; rw [h' i (Nat.le_of_lt h₁)] at this
  convert! mul_left_cancel this

中文:
引理 eq_of_prod_take_eq
  结论: [左消去幺半群 M] {L L' : 列表 M} (h : L.length = L'.length)
  证明: by
  refine ext_get h fun i h₁ h₂ => ?_
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [prod_take_succ L i h₁]; rw [prod_take_succ L' i h₂]; rw [h' i (Nat.le_of_lt h₁)] at this
  convert! mul_left_cancel this

Depends on / 依赖: L.take, Nat.le_of_lt, Nat.succ_le_of_lt, convert, ext_get, le_of_lt, mul_left_cancel, prod_take_succ, succ_le_of_lt
-/
lemma eq_of_prod_take_eq [LeftCancelMonoid M] {L L' : List M} (h : L.length = L'.length)
    (h' : forall i <= L.length, (L.take i).prod = (L'.take i).prod) : L = L' := by
  refine ext_get h fun i h₁ h₂ => ?_
  have : (L.take (i + 1)).prod = (L'.take (i + 1)).prod := h' _ (Nat.succ_le_of_lt h₁)
  rw [prod_take_succ L i h₁]; rw [prod_take_succ L' i h₂]; rw [h' i (Nat.le_of_lt h₁)] at this
  convert! mul_left_cancel this

section Group

variable [Group G]

/-- This is the `List.prod` version of `mul_inv_rev` -/
@[to_additive /-- This is the `List.sum` version of `add_neg_rev` -/]
/--
theorem `prod_inv_reverse` / 定理 `prod_inv_reverse`

English:
theorem prod_inv_reverse
  statement: forall L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod

中文:
定理 prod_inv_reverse
  结论: 对任意 L : 列表 G, L.乘积⁻¹ = (L.map fun x => x⁻¹).reverse.乘积
-/
theorem prod_inv_reverse : forall L : List G, L.prod⁻¹ = (L.map fun x => x⁻¹).reverse.prod
  | [] => by simp
  | x :: xs => by simp [prod_append, prod_inv_reverse xs]

/-- A non-commutative variant of `List.prod_reverse` -/
@[to_additive /-- A non-commutative variant of `List.sum_reverse` -/]
/--
theorem `prod_reverse_noncomm` / 定理 `prod_reverse_noncomm`

English:
theorem prod_reverse_noncomm
  statement: forall L : List G, L.reverse.prod = (L.map fun x => x⁻¹).prod⁻¹
  proof: by
  simp [prod_inv_reverse]

中文:
定理 prod_reverse_noncomm
  结论: 对任意 L : 列表 G, L.reverse.乘积 = (L.map fun x => x⁻¹).乘积⁻¹
  证明: by
  simp [prod_inv_reverse]

Depends on / 依赖: prod_inv_reverse
-/
theorem prod_reverse_noncomm : forall L : List G, L.reverse.prod = (L.map fun x => x⁻¹).prod⁻¹ := by
  simp [prod_inv_reverse]

/-- Counterpart to `List.prod_take_succ` when we have an inverse operation -/
@[to_additive (attr := simp)
  /-- Counterpart to `List.sum_take_succ` when we have a negation operation -/]
/--
theorem `prod_drop_succ` / 定理 `prod_drop_succ`

English:
theorem prod_drop_succ

中文:
定理 prod_drop_succ
-/
theorem prod_drop_succ :
    forall (L : List G) (i : Nat) (p : i < L.length), (L.drop (i + 1)).prod = L[i]⁻¹ * (L.drop i).prod
  | [], _, p => False.elim (Nat.not_lt_zero _ p)
  | _ :: _, 0, _ => by simp
  | _ :: xs, i + 1, p => prod_drop_succ xs i (Nat.lt_of_succ_lt_succ p)

/-- Cancellation of a telescoping product. -/
@[to_additive /-- Cancellation of a telescoping sum. -/]
/--
theorem `prod_range_div'` / 定理 `prod_range_div'`

English:
theorem prod_range_div'
  given: (n : Nat) (f : Nat -> G)
  proof: by
  induction n with
  | zero => exact (div_self' (f 0)).symm
  | succ n h => simp [range_succ, prod_append, map_append, h]

中文:
定理 prod_range_div'
  条件: (n : 自然数) (f : 自然数 -> G)
  证明: by
  induction n with
  | zero => exact (div_self' (f 0)).symm
  | succ n h => simp [range_succ, prod_append, map_append, h]

Depends on / 依赖: div_self, map_append, prod_append, range_succ
-/
theorem prod_range_div' (n : Nat) (f : Nat -> G) :
    ((range n).map fun k => f k / f (k + 1)).prod = f 0 / f n := by
  induction n with
  | zero => exact (div_self' (f 0)).symm
  | succ n h => simp [range_succ, prod_append, map_append, h]

end Group

section CommGroup

variable [CommGroup G]

/-- This is the `List.prod` version of `mul_inv` -/
@[to_additive /-- This is the `List.sum` version of `add_neg` -/]
/--
theorem `prod_inv` / 定理 `prod_inv`

English:
theorem prod_inv
  given: {K : Type*} [DivisionCommMonoid K]

中文:
定理 prod_inv
  条件: {K : 类型} [DivisionComm幺半群 K]
-/
theorem prod_inv {K : Type*} [DivisionCommMonoid K] :
    forall L : List K, L.prod⁻¹ = (L.map fun x => x⁻¹).prod
  | [] => by simp
  | x :: xs => by simp [mul_comm, prod_inv xs]

/-- Cancellation of a telescoping product. -/
@[to_additive /-- Cancellation of a telescoping sum. -/]
/--
theorem `prod_range_div` / 定理 `prod_range_div`

English:
theorem prod_range_div
  given: (n : Nat) (f : Nat -> G)
  proof: by
  have h : ((·⁻¹) ∘ fun k => f (k + 1) / f k) = fun k => f k / f (k + 1) := by ext; apply inv_div
  rw [← inv_inj]; rw [prod_inv]; rw [map_map]; rw [inv_div]; rw [h]; rw [prod_range_div']

中文:
定理 prod_range_div
  条件: (n : 自然数) (f : 自然数 -> G)
  证明: by
  have h : ((·⁻¹) ∘ fun k => f (k + 1) / f k) = fun k => f k / f (k + 1) := by ext; apply inv_div
  rw [← inv_inj]; rw [prod_inv]; rw [map_map]; rw [inv_div]; rw [h]; rw [prod_range_div']

Depends on / 依赖: inv_div, inv_inj, map_map, prod_inv, prod_range_div
-/
theorem prod_range_div (n : Nat) (f : Nat -> G) :
    ((range n).map fun k => f (k + 1) / f k).prod = f n / f 0 := by
  have h : ((·⁻¹) ∘ fun k => f (k + 1) / f k) = fun k => f k / f (k + 1) := by ext; apply inv_div
  rw [← inv_inj]; rw [prod_inv]; rw [map_map]; rw [inv_div]; rw [h]; rw [prod_range_div']

/-- Alternative version of `List.prod_set` when the list is over a group -/
@[to_additive /-- Alternative version of `List.sum_set` when the list is over a group -/]
/--
theorem `prod_set'` / 定理 `prod_set'`

English:
theorem prod_set'
  given: (L : List G) (n : Nat) (a : G)
  proof: by
  refine (prod_set L n a).trans ?_
  split_ifs with hn
  · rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).prod, ←
      mul_assoc (take n L).prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  · simp (disch := grind) [take_of_length_le, drop_eq_nil_of_le]

@[to_ad

中文:
定理 prod_set'
  条件: (L : 列表 G) (n : 自然数) (a : G)
  证明: by
  refine (prod_set L n a).trans ?_
  split_ifs with hn
  · rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).prod, ←
      mul_assoc (take n L).prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  · simp (disch := grind) [take_of_length_le, drop_eq_nil_of_le]

@[to_ad

Depends on / 依赖: drop_eq_nil_of_le, mul_assoc, mul_comm, prod_drop_succ, prod_set, prod_take_mul_prod_drop, split_ifs, take_of_length_le
-/
theorem prod_set' (L : List G) (n : Nat) (a : G) :
    (L.set n a).prod = L.prod * if hn : n < L.length then L[n]⁻¹ * a else 1 := by
  refine (prod_set L n a).trans ?_
  split_ifs with hn
  · rw [mul_comm _ a, mul_assoc a, prod_drop_succ L n hn, mul_comm _ (drop n L).prod, ←
      mul_assoc (take n L).prod, prod_take_mul_prod_drop, mul_comm a, mul_assoc]
  · simp (disch := grind) [take_of_length_le, drop_eq_nil_of_le]

@[to_additive]
/--
lemma `prod_map_ite_eq` / 引理 `prod_map_ite_eq`

English:
lemma prod_map_ite_eq
  given: {A : Type*} [DecidableEq A] (l : List A) (f g : A -> G) (a : A)
  proof: by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, prod_cons, count_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : x = a
    · simp only [hx, ite_true, pow_add, pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      mul_inv_cancel_left, beq_self_

中文:
引理 prod_map_ite_eq
  条件: {A : 类型} [DecidableEq A] (l : 列表 A) (f g : A -> G) (a : A)
  证明: by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, prod_cons, count_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : x = a
    · simp only [hx, ite_true, pow_add, pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      mul_inv_cancel_left, beq_self_

Depends on / 依赖: add_zero, beq_iff_eq, beq_self_eq_true, count_cons, div_eq_mul_inv, ite_false, ite_true, map_cons, mul_assoc, mul_comm, mul_inv_cancel_left, mul_left_comm, pow_add, pow_one, prod_cons
-/
lemma prod_map_ite_eq {A : Type*} [DecidableEq A] (l : List A) (f g : A -> G) (a : A) :
    (l.map fun x => if x = a then f x else g x).prod
      = (f a / g a) ^ (l.count a) * (l.map g).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [map_cons, prod_cons, count_cons] at ih ⊢
    rw [ih]
    clear ih
    by_cases hx : x = a
    · simp only [hx, ite_true, pow_add, pow_one, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm,
      mul_inv_cancel_left, beq_self_eq_true]
    · simp only [hx, ite_false, add_zero, mul_assoc, mul_comm (g x) _, beq_iff_eq]

end CommGroup

/--
theorem `sum_const_nat` / 定理 `sum_const_nat`

English:
theorem sum_const_nat
  given: (m n : Nat)
  statement: sum (replicate m n) = m * n
  proof: sum_replicate m n

中文:
定理 sum_const_nat
  条件: (m n : 自然数)
  结论: 求和 (replicate m n) = m * n
  证明: sum_replicate m n

Depends on / 依赖: sum_replicate
-/
theorem sum_const_nat (m n : Nat) : sum (replicate m n) = m * n :=
  sum_replicate m n

/-!
Several lemmas about sum/head/tail for `List ℕ`.
These are hard to generalize well, as they rely on the fact that `default ℕ = 0`.
If desired, we could add a class stating that `default = 0`.
-/

/--
theorem `headI_add_tail_sum` / 定理 `headI_add_tail_sum`

English:
theorem headI_add_tail_sum
  given: (L : List Nat)
  statement: L.headI + L.tail.sum = L.sum
  proof: by
  cases L <;> simp

中文:
定理 headI_add_tail_sum
  条件: (L : 列表 自然数)
  结论: L.headI + L.tail.求和 = L.求和
  证明: by
  cases L <;> simp
-/
theorem headI_add_tail_sum (L : List Nat) : L.headI + L.tail.sum = L.sum := by
  cases L <;> simp

/--
theorem `headI_le_sum` / 定理 `headI_le_sum`

English:
theorem headI_le_sum
  given: (L : List Nat)
  statement: L.headI <= L.sum
  proof: Nat.le.intro (headI_add_tail_sum L)

中文:
定理 headI_le_sum
  条件: (L : 列表 自然数)
  结论: L.headI <= L.求和
  证明: Nat.le.intro (headI_add_tail_sum L)

Depends on / 依赖: Nat.le.intro, headI_add_tail_sum
-/
theorem headI_le_sum (L : List Nat) : L.headI <= L.sum :=
  Nat.le.intro (headI_add_tail_sum L)

/--
theorem `tail_sum` / 定理 `tail_sum`

English:
theorem tail_sum
  given: (L : List Nat)
  statement: L.tail.sum = L.sum - L.headI
  proof: by
  rw [← headI_add_tail_sum L]; rw [add_comm]; rw [Nat.add_sub_cancel_right]

中文:
定理 tail_sum
  条件: (L : 列表 自然数)
  结论: L.tail.求和 = L.求和 - L.headI
  证明: by
  rw [← headI_add_tail_sum L]; rw [add_comm]; rw [Nat.add_sub_cancel_right]

Depends on / 依赖: Nat.add_sub_cancel_right, add_comm, add_sub_cancel_right, headI_add_tail_sum
-/
theorem tail_sum (L : List Nat) : L.tail.sum = L.sum - L.headI := by
  rw [← headI_add_tail_sum L]; rw [add_comm]; rw [Nat.add_sub_cancel_right]

section Alternating

section

variable [One G] [Mul G] [Inv G]

@[to_additive (attr := simp)]
/--
theorem `alternatingProd_nil` / 定理 `alternatingProd_nil`

English:
theorem alternatingProd_nil
  statement: alternatingProd ([] : List G) = 1
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 alternatingProd_nil
  结论: alternatingProd ([] : 列表 G) = 1
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem alternatingProd_nil : alternatingProd ([] : List G) = 1 :=
  rfl

@[to_additive (attr := simp)]
/--
theorem `alternatingProd_singleton` / 定理 `alternatingProd_singleton`

English:
theorem alternatingProd_singleton
  given: (a : G)
  statement: alternatingProd [a] = a
  proof: rfl

@[to_additive]

中文:
定理 alternatingProd_singleton
  条件: (a : G)
  结论: alternatingProd [a] = a
  证明: rfl

@[to_additive]
-/
theorem alternatingProd_singleton (a : G) : alternatingProd [a] = a :=
  rfl

@[to_additive]
/--
theorem `alternatingProd_cons_cons'` / 定理 `alternatingProd_cons_cons'`

English:
theorem alternatingProd_cons_cons'
  given: (a b : G) (l : List G)
  proof: rfl

中文:
定理 alternatingProd_cons_cons'
  条件: (a b : G) (l : 列表 G)
  证明: rfl
-/
theorem alternatingProd_cons_cons' (a b : G) (l : List G) :
    alternatingProd (a :: b :: l) = a * b⁻¹ * alternatingProd l :=
  rfl

end

@[to_additive]
/--
theorem `alternatingProd_cons_cons` / 定理 `alternatingProd_cons_cons`

English:
theorem alternatingProd_cons_cons
  given: [DivInvMonoid G] (a b : G) (l : List G)
  proof: by
  rw [div_eq_mul_inv]; rw [alternatingProd_cons_cons']

中文:
定理 alternatingProd_cons_cons
  条件: [除逆幺半群 G] (a b : G) (l : 列表 G)
  证明: by
  rw [div_eq_mul_inv]; rw [alternatingProd_cons_cons']

Depends on / 依赖: alternatingProd_cons_cons, div_eq_mul_inv
-/
theorem alternatingProd_cons_cons [DivInvMonoid G] (a b : G) (l : List G) :
    alternatingProd (a :: b :: l) = a / b * alternatingProd l := by
  rw [div_eq_mul_inv]; rw [alternatingProd_cons_cons']

variable [CommGroup G]

@[to_additive]
/--
theorem `alternatingProd_cons'` / 定理 `alternatingProd_cons'`

English:
theorem alternatingProd_cons'

中文:
定理 alternatingProd_cons'
-/
theorem alternatingProd_cons' :
    forall (a : G) (l : List G), alternatingProd (a :: l) = a * (alternatingProd l)⁻¹
  | a, [] => by rw [alternatingProd_nil, inv_one, mul_one, alternatingProd_singleton]
  | a, b :: l => by
    rw [alternatingProd_cons_cons']; rw [alternatingProd_cons' b l]; rw [mul_inv]; rw [inv_inv]; rw [mul_assoc]

@[to_additive (attr := simp)]
/--
theorem `alternatingProd_cons` / 定理 `alternatingProd_cons`

English:
theorem alternatingProd_cons
  given: (a : G) (l : List G)
  proof: by
  rw [div_eq_mul_inv]; rw [alternatingProd_cons']

中文:
定理 alternatingProd_cons
  条件: (a : G) (l : 列表 G)
  证明: by
  rw [div_eq_mul_inv]; rw [alternatingProd_cons']

Depends on / 依赖: alternatingProd_cons, div_eq_mul_inv
-/
theorem alternatingProd_cons (a : G) (l : List G) :
    alternatingProd (a :: l) = a / alternatingProd l := by
  rw [div_eq_mul_inv]; rw [alternatingProd_cons']

end Alternating

/--
lemma `sum_nat_mod` / 引理 `sum_nat_mod`

English:
lemma sum_nat_mod
  given: (l : List Nat) (n : Nat)
  statement: l.sum % n = (l.map (· % n)).sum % n
  proof: by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [map_cons, sum_cons, Nat.mod_add_mod, Nat.add_mod_mod] using congr((a + $ih) % n)

中文:
引理 sum_nat_mod
  条件: (l : 列表 自然数) (n : 自然数)
  结论: l.求和 % n = (l.map (· % n)).求和 % n
  证明: by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [map_cons, sum_cons, Nat.mod_add_mod, Nat.add_mod_mod] using congr((a + $ih) % n)

Depends on / 依赖: Nat.add_mod_mod, Nat.mod_add_mod, add_mod_mod, map_cons, map_nil, mod_add_mod, sum_cons
-/
lemma sum_nat_mod (l : List Nat) (n : Nat) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [map_cons, sum_cons, Nat.mod_add_mod, Nat.add_mod_mod] using congr((a + $ih) % n)

/--
lemma `prod_nat_mod` / 引理 `prod_nat_mod`

English:
lemma prod_nat_mod
  given: (l : List Nat) (n : Nat)
  statement: l.prod % n = (l.map (· % n)).prod % n
  proof: by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [prod_cons, map_cons, Nat.mod_mul_mod, Nat.mul_mod_mod] using congr((a * $ih) % n)

中文:
引理 prod_nat_mod
  条件: (l : 列表 自然数) (n : 自然数)
  结论: l.乘积 % n = (l.map (· % n)).乘积 % n
  证明: by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [prod_cons, map_cons, Nat.mod_mul_mod, Nat.mul_mod_mod] using congr((a * $ih) % n)

Depends on / 依赖: Nat.mod_mul_mod, Nat.mul_mod_mod, map_cons, map_nil, mod_mul_mod, mul_mod_mod, prod_cons
-/
lemma prod_nat_mod (l : List Nat) (n : Nat) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l with
  | nil => simp only [map_nil]
  | cons a l ih =>
    simpa only [prod_cons, map_cons, Nat.mod_mul_mod, Nat.mul_mod_mod] using congr((a * $ih) % n)

/--
lemma `sum_int_mod` / 引理 `sum_int_mod`

English:
lemma sum_int_mod
  given: (l : List Int) (n : Int)
  statement: l.sum % n = (l.map (· % n)).sum % n
  proof: by
  induction l <;> simp [Int.add_emod, *]

中文:
引理 sum_int_mod
  条件: (l : 列表 整数) (n : 整数)
  结论: l.求和 % n = (l.map (· % n)).求和 % n
  证明: by
  induction l <;> simp [Int.add_emod, *]

Depends on / 依赖: Int.add_emod, add_emod
-/
lemma sum_int_mod (l : List Int) (n : Int) : l.sum % n = (l.map (· % n)).sum % n := by
  induction l <;> simp [Int.add_emod, *]

/--
lemma `prod_int_mod` / 引理 `prod_int_mod`

English:
lemma prod_int_mod
  given: (l : List Int) (n : Int)
  statement: l.prod % n = (l.map (· % n)).prod % n
  proof: by
  induction l <;> simp [Int.mul_emod, *]

中文:
引理 prod_int_mod
  条件: (l : 列表 整数) (n : 整数)
  结论: l.乘积 % n = (l.map (· % n)).乘积 % n
  证明: by
  induction l <;> simp [Int.mul_emod, *]

Depends on / 依赖: Int.mul_emod, mul_emod
-/
lemma prod_int_mod (l : List Int) (n : Int) : l.prod % n = (l.map (· % n)).prod % n := by
  induction l <;> simp [Int.mul_emod, *]

end List

section MonoidHom

variable [Monoid M] [Monoid N]

@[to_additive]
/--
theorem `map_list_prod` / 定理 `map_list_prod`

English:
theorem map_list_prod
  given: {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) (l : List M)
  proof: (l.prod_hom f).symm

中文:
定理 map_list_prod
  条件: {F : 类型} [函数状 F M N] [幺半群态射类 F M N] (f : F) (l : 列表 M)
  证明: (l.prod_hom f).symm

Depends on / 依赖: l.prod_hom, prod_hom
-/
theorem map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass F M N] (f : F) (l : List M) :
    f l.prod = (l.map f).prod :=
  (l.prod_hom f).symm

namespace MonoidHom

@[to_additive]
/--
theorem `map_list_prod` / 定理 `map_list_prod`

English:
theorem map_list_prod
  given: (f : M ->* N) (l : List M)
  statement: f l.prod = (l.map f).prod
  proof: map_list_prod f l

中文:
定理 map_list_prod
  条件: (f : M ->* N) (l : 列表 M)
  结论: f l.乘积 = (l.map f).乘积
  证明: map_list_prod f l
-/
protected theorem map_list_prod (f : M ->* N) (l : List M) : f l.prod = (l.map f).prod :=
  map_list_prod f l

end MonoidHom

end MonoidHom

namespace List

/--
theorem `prod_zpow` / 定理 `prod_zpow`

English:
theorem prod_zpow
  given: {β : Type*} [DivisionCommMonoid β] {r : Int} {l : List β}
  proof: let fr : β ->* β := ⟨⟨fun b => b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

中文:
定理 prod_zpow
  条件: {β : 类型} [DivisionComm幺半群 β] {r : 整数} {l : 列表 β}
  证明: let fr : β ->* β := ⟨⟨fun b => b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

Depends on / 依赖: map_list_prod, mul_zpow, one_zpow
-/
theorem prod_zpow {β : Type*} [DivisionCommMonoid β] {r : Int} {l : List β} :
    l.prod ^ r = (map (fun x => x ^ r) l).prod :=
  let fr : β ->* β := ⟨⟨fun b => b ^ r, one_zpow r⟩, (mul_zpow · · r)⟩
  map_list_prod fr l

/--
lemma `take_sum_flatten` / 引理 `take_sum_flatten`

English:
lemma take_sum_flatten
  given: (L : List (List α)) (i : Nat)
  proof: by
  induction L generalizing i
  · simp
  · cases i <;> simp [take_length_add_append, *]

中文:
引理 take_sum_flatten
  条件: (L : 列表 (列表 α)) (i : 自然数)
  证明: by
  induction L generalizing i
  · simp
  · cases i <;> simp [take_length_add_append, *]

Depends on / 依赖: generalizing, take_length_add_append
-/
lemma take_sum_flatten (L : List (List α)) (i : Nat) :
    L.flatten.take ((L.map length).take i).sum = (L.take i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [take_length_add_append, *]

/--
lemma `drop_sum_flatten` / 引理 `drop_sum_flatten`

English:
lemma drop_sum_flatten
  given: (L : List (List α)) (i : Nat)
  proof: by
  induction L generalizing i
  · simp
  · cases i <;> simp [*]

中文:
引理 drop_sum_flatten
  条件: (L : 列表 (列表 α)) (i : 自然数)
  证明: by
  induction L generalizing i
  · simp
  · cases i <;> simp [*]

Depends on / 依赖: generalizing
-/
lemma drop_sum_flatten (L : List (List α)) (i : Nat) :
    L.flatten.drop ((L.map length).take i).sum = (L.drop i).flatten := by
  induction L generalizing i
  · simp
  · cases i <;> simp [*]

end List


namespace List

/--
theorem `length_le_sum_of_one_le` / 定理 `length_le_sum_of_one_le`

English:
theorem length_le_sum_of_one_le
  given: (L : List Nat) (h : forall i in L, 1 <= i)
  statement: L.length <= L.sum
  proof: by
  induction L with
  | nil => simp
  | cons j L IH =>
    rw [sum_cons]; rw [length]; rw [add_comm]
    exact Nat.add_le_add (h _ mem_cons_self) (IH fun i hi => h i (mem_cons.2 (Or.inr hi)))

中文:
定理 length_le_sum_of_one_le
  条件: (L : 列表 自然数) (h : 对任意 i in L, 1 <= i)
  结论: L.length <= L.求和
  证明: by
  induction L with
  | nil => simp
  | cons j L IH =>
    rw [sum_cons]; rw [length]; rw [add_comm]
    exact Nat.add_le_add (h _ mem_cons_self) (IH fun i hi => h i (mem_cons.2 (Or.inr hi)))

Depends on / 依赖: Nat.add_le_add, Or.inr, add_comm, add_le_add, length, mem_cons, mem_cons_self, sum_cons
-/
theorem length_le_sum_of_one_le (L : List Nat) (h : forall i in L, 1 <= i) : L.length <= L.sum := by
  induction L with
  | nil => simp
  | cons j L IH =>
    rw [sum_cons]; rw [length]; rw [add_comm]
    exact Nat.add_le_add (h _ mem_cons_self) (IH fun i hi => h i (mem_cons.2 (Or.inr hi)))

end List
