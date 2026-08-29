/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Lists from functions

Theorems and lemmas for dealing with `List.ofFn`, which converts a function on `Fin n` to a list
of length `n`.

## Main Statements

The main statements pertain to lists generated using `List.ofFn`

- `List.get?_ofFn`, which tells us the nth element of such a list
- `List.equivSigmaTuple`, which is an `Equiv` between lists and the functions that generate them
  via `List.ofFn`.
-/

@[expose] public section

assert_not_exists Monoid

universe u

variable {α : Type u}

open Nat

namespace List

/--
theorem `get_ofFn` / 定理 `get_ofFn`

English:
theorem get_ofFn
  given: {n} (f : Fin n -> α) (i)
  statement: get (ofFn f) i = f (Fin.cast (by simp) i)
  proof: by
  simp; congr

中文:
定理 get_ofFn
  条件: {n} (f : 有限集 n -> α) (i)
  结论: get (ofFn f) i = f (有限集.cast (by simp) i)
  证明: by
  simp; congr
-/
theorem get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f (Fin.cast (by simp) i) := by
  simp; congr

/--
theorem `ofFn_comp'` / 定理 `ofFn_comp'`

English:
theorem ofFn_comp'
  given: {β : Type*} {n : Nat} (f : Fin n -> α) (g : α -> β)
  proof: map_ofFn.symm

@[congr]

中文:
定理 ofFn_comp'
  条件: {β : 类型} {n : 自然数} (f : 有限集 n -> α) (g : α -> β)
  证明: map_ofFn.symm

@[congr]

Depends on / 依赖: map_ofFn, map_ofFn.symm
-/
theorem ofFn_comp' {β : Type*} {n : Nat} (f : Fin n -> α) (g : α -> β) :
    ofFn (fun i => g (f i)) = map g (ofFn f) :=
  map_ofFn.symm

@[congr]
/--
theorem `ofFn_congr` / 定理 `ofFn_congr`

English:
theorem ofFn_congr
  given: {m n : Nat} (h : m = n) (f : Fin m -> α)
  proof: by
  subst h
  simp_rw [Fin.cast_refl, id]

中文:
定理 ofFn_congr
  条件: {m n : 自然数} (h : m = n) (f : 有限集 m -> α)
  证明: by
  subst h
  simp_rw [Fin.cast_refl, id]

Depends on / 依赖: Fin.cast_refl, cast_refl, simp_rw
-/
theorem ofFn_congr {m n : Nat} (h : m = n) (f : Fin m -> α) :
    ofFn f = ofFn fun i : Fin n => f (Fin.cast h.symm i) := by
  subst h
  simp_rw [Fin.cast_refl, id]

/--
theorem `ofFn_succ'` / 定理 `ofFn_succ'`

English:
theorem ofFn_succ'
  given: {n} (f : Fin (succ n) -> α)
  proof: by
  induction n with
  | zero => rw [ofFn_zero, concat_nil, ofFn_succ, ofFn_zero, Fin.last_zero]
  | succ n IH =>
    rw [ofFn_succ]; rw [IH]; rw [ofFn_succ]; rw [concat_cons]; rw [Fin.castSucc_zero]; rw [Fin.succ_last]
    simp only [succ_eq_add_one, Fin.castSucc_succ]

@[simp]

中文:
定理 ofFn_succ'
  条件: {n} (f : 有限集 (succ n) -> α)
  证明: by
  induction n with
  | zero => rw [ofFn_zero, concat_nil, ofFn_succ, ofFn_zero, Fin.last_zero]
  | succ n IH =>
    rw [ofFn_succ]; rw [IH]; rw [ofFn_succ]; rw [concat_cons]; rw [Fin.castSucc_zero]; rw [Fin.succ_last]
    simp only [succ_eq_add_one, Fin.castSucc_succ]

@[simp]

Depends on / 依赖: Fin.castSucc_succ, Fin.castSucc_zero, Fin.last_zero, Fin.succ_last, castSucc_succ, castSucc_zero, concat_cons, concat_nil, last_zero, ofFn_succ, ofFn_zero, succ_eq_add_one, succ_last
-/
theorem ofFn_succ' {n} (f : Fin (succ n) -> α) :
    ofFn f = (ofFn fun i => f (Fin.castSucc i)).concat (f (Fin.last _)) := by
  induction n with
  | zero => rw [ofFn_zero, concat_nil, ofFn_succ, ofFn_zero, Fin.last_zero]
  | succ n IH =>
    rw [ofFn_succ]; rw [IH]; rw [ofFn_succ]; rw [concat_cons]; rw [Fin.castSucc_zero]; rw [Fin.succ_last]
    simp only [succ_eq_add_one, Fin.castSucc_succ]

@[simp]
/--
theorem `ofFn_fin_append` / 定理 `ofFn_fin_append`

English:
theorem ofFn_fin_append
  given: {m n} (a : Fin m -> α) (b : Fin n -> α)
  proof: by
  simp_rw [ofFn_add]
  simp [Fin.append_left', Fin.append_right]

中文:
定理 ofFn_fin_append
  条件: {m n} (a : 有限集 m -> α) (b : 有限集 n -> α)
  证明: by
  simp_rw [ofFn_add]
  simp [Fin.append_left', Fin.append_right]

Depends on / 依赖: Fin.append_left, Fin.append_right, append_left, append_right, ofFn_add, simp_rw
-/
theorem ofFn_fin_append {m n} (a : Fin m -> α) (b : Fin n -> α) :
    List.ofFn (Fin.append a b) = List.ofFn a ++ List.ofFn b := by
  simp_rw [ofFn_add]
  simp [Fin.append_left', Fin.append_right]

/--
theorem `ofFn_mul` / 定理 `ofFn_mul`

English:
theorem ofFn_mul
  given: {m n} (f : Fin (m * n) -> α)
  proof: by
  induction m with
  | zero => simp [ofFn_zero, Nat.zero_mul, ofFn_zero]
  | succ m IH =>
    simp_rw [ofFn_succ', succ_mul]
    simp [ofFn_add, IH]
    rfl

中文:
定理 ofFn_mul
  条件: {m n} (f : 有限集 (m * n) -> α)
  证明: by
  induction m with
  | zero => simp [ofFn_zero, Nat.zero_mul, ofFn_zero]
  | succ m IH =>
    simp_rw [ofFn_succ', succ_mul]
    simp [ofFn_add, IH]
    rfl

Depends on / 依赖: Nat.add_lt_add_left, Nat.add_mul, Nat.mul_le_mul_right, Nat.one_mul, Nat.zero_mul, add_lt_add_left, add_mul, i.prop, j.prop, mul_le_mul_right, ofFn_add, ofFn_succ, ofFn_zero, one_mul, simp_rw, succ_mul, trans_eq, zero_mul
-/
theorem ofFn_mul {m n} (f : Fin (m * n) -> α) :
    List.ofFn f = List.flatten (List.ofFn fun i : Fin m => List.ofFn fun j : Fin n => f ⟨i * n + j,
    calc
      ↑i * n + j < (i + 1) * n :=
        (Nat.add_lt_add_left j.prop _).trans_eq (by rw [Nat.add_mul, Nat.one_mul])
      _ <= _ := Nat.mul_le_mul_right _ i.prop⟩) := by
  induction m with
  | zero => simp [ofFn_zero, Nat.zero_mul, ofFn_zero]
  | succ m IH =>
    simp_rw [ofFn_succ', succ_mul]
    simp [ofFn_add, IH]
    rfl

/--
theorem `ofFn_mul'` / 定理 `ofFn_mul'`

English:
theorem ofFn_mul'
  given: {m n} (f : Fin (m * n) -> α)
  proof: by simp_rw [m.mul_comm, ofFn_mul, Fin.cast_mk]

@[simp]

中文:
定理 ofFn_mul'
  条件: {m n} (f : 有限集 (m * n) -> α)
  证明: by simp_rw [m.mul_comm, ofFn_mul, Fin.cast_mk]

@[simp]

Depends on / 依赖: Fin.cast_mk, Nat.add_lt_add_left, Nat.mul_add, Nat.mul_le_mul_left, Nat.mul_one, add_lt_add_left, cast_mk, i.prop, j.prop, m.mul_comm, mul_add, mul_comm, mul_le_mul_left, mul_one, ofFn_mul, simp_rw, trans_eq
-/
theorem ofFn_mul' {m n} (f : Fin (m * n) -> α) :
    List.ofFn f = List.flatten (List.ofFn fun i : Fin n => List.ofFn fun j : Fin m => f ⟨m * i + j,
    calc
      m * i + j < m * (i + 1) :=
        (Nat.add_lt_add_left j.prop _).trans_eq (by rw [Nat.mul_add, Nat.mul_one])
      _ <= _ := Nat.mul_le_mul_left _ i.prop⟩) := by simp_rw [m.mul_comm, ofFn_mul, Fin.cast_mk]

@[simp]
/--
theorem `ofFn_get` / 定理 `ofFn_get`

English:
theorem ofFn_get
  statement: forall l : List α, (ofFn (get l)) = l

中文:
定理 ofFn_get
  结论: 对任意 l : 列表 α, (ofFn (get l)) = l
-/
theorem ofFn_get : forall l : List α, (ofFn (get l)) = l
  | [] => by rw [ofFn_zero]
  | a :: l => by
    rw [ofFn_succ]
    congr
    exact ofFn_get l

@[simp]
/--
theorem `ofFn_getElem_eq_map` / 定理 `ofFn_getElem_eq_map`

English:
theorem ofFn_getElem_eq_map
  given: {β : Type*} (l : List α) (f : α -> β)
  proof: by
  rw [← Function.comp_def]; rw [← map_ofFn]; rw [ofFn_getElem]

中文:
定理 ofFn_getElem_eq_map
  条件: {β : 类型} (l : 列表 α) (f : α -> β)
  证明: by
  rw [← Function.comp_def]; rw [← map_ofFn]; rw [ofFn_getElem]

Depends on / 依赖: Function, Function.comp_def, comp_def, map_ofFn, ofFn_getElem
-/
theorem ofFn_getElem_eq_map {β : Type*} (l : List α) (f : α -> β) :
    ofFn (fun i : Fin l.length => f <| l[(i : Nat)]) = l.map f := by
  rw [← Function.comp_def]; rw [← map_ofFn]; rw [ofFn_getElem]

-- Note there is a now another `mem_ofFn` defined in Lean, with an existential on the RHS,
-- which is marked as a simp lemma.
/--
theorem `mem_ofFn'` / 定理 `mem_ofFn'`

English:
theorem mem_ofFn'
  given: {n} (f : Fin n -> α) (a : α)
  statement: a in ofFn f ↔ a in Set.range f
  proof: by grind

中文:
定理 mem_ofFn'
  条件: {n} (f : 有限集 n -> α) (a : α)
  结论: a in ofFn f ↔ a in 集合.range f
  证明: by grind
-/
theorem mem_ofFn' {n} (f : Fin n -> α) (a : α) : a in ofFn f ↔ a in Set.range f := by grind

/--
theorem `forall_mem_ofFn_iff` / 定理 `forall_mem_ofFn_iff`

English:
theorem forall_mem_ofFn_iff
  given: {n : Nat} {f : Fin n -> α} {P : α -> Prop}
  proof: by simp

@[simp]

中文:
定理 对任意_mem_ofFn_iff
  条件: {n : 自然数} {f : 有限集 n -> α} {P : α -> 命题}
  证明: by simp

@[simp]
-/
theorem forall_mem_ofFn_iff {n : Nat} {f : Fin n -> α} {P : α -> Prop} :
    (forall i in ofFn f, P i) ↔ forall j : Fin n, P (f j) := by simp

@[simp]
/--
theorem `ofFn_const` / 定理 `ofFn_const`

English:
theorem ofFn_const
  statement: forall (n : Nat) (c : α), (ofFn fun _ : Fin n => c) = replicate n c

中文:
定理 ofFn_const
  结论: 对任意 (n : 自然数) (c : α), (ofFn fun _ : 有限集 n => c) = replicate n c
-/
theorem ofFn_const : forall (n : Nat) (c : α), (ofFn fun _ : Fin n => c) = replicate n c
  | 0, c => by rw [ofFn_zero, replicate_zero]
  | n + 1, c => by rw [replicate, ← ofFn_const n]; simp

@[simp]
/--
theorem `ofFn_fin_repeat` / 定理 `ofFn_fin_repeat`

English:
theorem ofFn_fin_repeat
  given: {m} (a : Fin m -> α) (n : Nat)
  proof: by
  simp_rw [ofFn_mul, ← ofFn_const, Fin.repeat, Fin.modNat, Nat.add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fin.is_lt _)]

@[simp]

中文:
定理 ofFn_fin_repeat
  条件: {m} (a : 有限集 m -> α) (n : 自然数)
  证明: by
  simp_rw [ofFn_mul, ← ofFn_const, Fin.repeat, Fin.modNat, Nat.add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fin.is_lt _)]

@[simp]

Depends on / 依赖: Fin.is_lt, Fin.modNat, Fin.repeat, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt, add_comm, add_mul_mod_self_right, is_lt, modNat, mod_eq_of_lt, ofFn_const, ofFn_mul, repeat, simp_rw
-/
theorem ofFn_fin_repeat {m} (a : Fin m -> α) (n : Nat) :
    List.ofFn (Fin.repeat n a) = (List.replicate n (List.ofFn a)).flatten := by
  simp_rw [ofFn_mul, ← ofFn_const, Fin.repeat, Fin.modNat, Nat.add_comm,
    Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Fin.is_lt _)]

@[simp]
/--
theorem `pairwise_ofFn` / 定理 `pairwise_ofFn`

English:
theorem pairwise_ofFn
  given: {R : α -> α -> Prop} {n} {f : Fin n -> α}
  proof: by
  simp only [pairwise_iff_getElem, length_ofFn, List.getElem_ofFn,
    Fin.forall_iff,
    Fin.mk_lt_mk, forall_comm (α := (_ : Prop)) (β := Nat)]

中文:
定理 pairwise_ofFn
  条件: {R : α -> α -> 命题} {n} {f : 有限集 n -> α}
  证明: by
  simp only [pairwise_iff_getElem, length_ofFn, List.getElem_ofFn,
    Fin.forall_iff,
    Fin.mk_lt_mk, forall_comm (α := (_ : Prop)) (β := Nat)]

Depends on / 依赖: Fin.forall_iff, Fin.mk_lt_mk, List.getElem_ofFn, forall_comm, forall_iff, getElem_ofFn, length_ofFn, mk_lt_mk, pairwise_iff_getElem
-/
theorem pairwise_ofFn {R : α -> α -> Prop} {n} {f : Fin n -> α} :
    (ofFn f).Pairwise R ↔ forall ⦃i j⦄, i < j -> R (f i) (f j) := by
  simp only [pairwise_iff_getElem, length_ofFn, List.getElem_ofFn,
    Fin.forall_iff,
    Fin.mk_lt_mk, forall_comm (α := (_ : Prop)) (β := Nat)]

/--
lemma `getLast_ofFn_succ` / 引理 `getLast_ofFn_succ`

English:
lemma getLast_ofFn_succ
  given: {n : Nat} (f : Fin n.succ -> α)
  proof: getLast_ofFn _

中文:
引理 getLast_ofFn_succ
  条件: {n : 自然数} (f : 有限集 n.succ -> α)
  证明: getLast_ofFn _

Depends on / 依赖: getLast_ofFn
-/
lemma getLast_ofFn_succ {n : Nat} (f : Fin n.succ -> α) :
    (ofFn f).getLast (mt ofFn_eq_nil_iff.1 (Nat.succ_ne_zero _)) = f (Fin.last _) :=
  getLast_ofFn _

/--
lemma `ofFn_cons` / 引理 `ofFn_cons`

English:
lemma ofFn_cons
  given: {n} (a : α) (f : Fin n -> α)
  statement: ofFn (Fin.cons a f) = a :: ofFn f
  proof: by
  rw [ofFn_succ]
  rfl

中文:
引理 ofFn_cons
  条件: {n} (a : α) (f : 有限集 n -> α)
  结论: ofFn (有限集.cons a f) = a :: ofFn f
  证明: by
  rw [ofFn_succ]
  rfl

Depends on / 依赖: ofFn_succ
-/
lemma ofFn_cons {n} (a : α) (f : Fin n -> α) : ofFn (Fin.cons a f) = a :: ofFn f := by
  rw [ofFn_succ]
  rfl

/--
lemma `find?_ofFn_eq_some` / 引理 `find?_ofFn_eq_some`

English:
lemma find?_ofFn_eq_some
  given: {n} {f : Fin n -> α} {p : α -> Bool} {b : α}
  proof: by
  rw [find?_eq_some_iff_getElem]
  exact ⟨fun ⟨hpb, i, hi, hfb, h⟩ =>
      ⟨hpb, ⟨⟨i, length_ofFn (f := f) ▸ hi⟩, by simpa
        using! hfb, fun j hj => by simpa using! h j hj⟩⟩,
    fun ⟨hpb, i, hfb, h⟩ =>
      ⟨hpb, ⟨i, (length_ofFn (f := f)).symm ▸ i.isLt, by simpa using! hfb,
        fun j hj => by simpa using! h ⟨j, by lia⟩ (by simpa using! hj)⟩⟩⟩

中文:
引理 find?_ofFn_eq_some
  条件: {n} {f : 有限集 n -> α} {p : α -> 布尔值} {b : α}
  证明: by
  rw [find?_eq_some_iff_getElem]
  exact ⟨fun ⟨hpb, i, hi, hfb, h⟩ =>
      ⟨hpb, ⟨⟨i, length_ofFn (f := f) ▸ hi⟩, by simpa
        using! hfb, fun j hj => by simpa using! h j hj⟩⟩,
    fun ⟨hpb, i, hfb, h⟩ =>
      ⟨hpb, ⟨i, (length_ofFn (f := f)).symm ▸ i.isLt, by simpa using! hfb,
        fun j hj => by simpa using! h ⟨j, by lia⟩ (by simpa using! hj)⟩⟩⟩
-/
lemma find?_ofFn_eq_some {n} {f : Fin n -> α} {p : α -> Bool} {b : α} :
    (ofFn f).find? p = some b ↔ p b = true ∧ exists i, f i = b ∧ forall j < i, ¬(p (f j) = true) := by
  rw [find?_eq_some_iff_getElem]
  exact ⟨fun ⟨hpb, i, hi, hfb, h⟩ =>
      ⟨hpb, ⟨⟨i, length_ofFn (f := f) ▸ hi⟩, by simpa
        using! hfb, fun j hj => by simpa using! h j hj⟩⟩,
    fun ⟨hpb, i, hfb, h⟩ =>
      ⟨hpb, ⟨i, (length_ofFn (f := f)).symm ▸ i.isLt, by simpa using! hfb,
        fun j hj => by simpa using! h ⟨j, by lia⟩ (by simpa using! hj)⟩⟩⟩

/--
lemma `find?_ofFn_eq_some_of_injective` / 引理 `find?_ofFn_eq_some_of_injective`

English:
lemma find?_ofFn_eq_some_of_injective
  statement: {n} {f : Fin n -> α} {p : α -> Bool} {i : Fin n}
  proof: by
  simp only [find?_ofFn_eq_some, h.eq_iff, Bool.not_eq_true, exists_eq_left]

中文:
引理 find?_ofFn_eq_some_of_injective
  结论: {n} {f : 有限集 n -> α} {p : α -> 布尔值} {i : 有限集 n}
  证明: by
  simp only [find?_ofFn_eq_some, h.eq_iff, Bool.not_eq_true, exists_eq_left]
-/
lemma find?_ofFn_eq_some_of_injective {n} {f : Fin n -> α} {p : α -> Bool} {i : Fin n}
    (h : Function.Injective f) :
    (ofFn f).find? p = some (f i) ↔ p (f i) = true ∧ forall j < i, ¬(p (f j) = true) := by
  simp only [find?_ofFn_eq_some, h.eq_iff, Bool.not_eq_true, exists_eq_left]

/-- Lists are equivalent to the sigma type of tuples of a given length. -/
@[simps]
/--
Definition of `equivSigmaTuple` / `equivSigmaTuple` 的定义

English:
definition equivSigmaTuple
  signature: : List α ≃ Σ n, Fin n -> α where
  body: ⟨l.length, l.get⟩
  invFun f := List.ofFn f.2
  left_inv := List.ofFn_get
  right_inv := fun ⟨_, f⟩ =>
Fin.sigma_eq_of_eq_comp_cast length_ofFn funext fun i => get_ofFn f i

中文:
定义 equivSigmaTuple
  签名: : 列表 α ≃ Σ n, 有限集 n -> α where
  定义体: ⟨l.length, l.get⟩
  invFun f := List.ofFn f.2
  left_inv := List.ofFn_get
  right_inv := fun ⟨_, f⟩ =>
Fin.sigma_eq_of_eq_comp_cast length_ofFn funext fun i => get_ofFn f i

Depends on / 依赖: l.get, l.length, length
-/
def equivSigmaTuple : List α ≃ Σ n, Fin n -> α where
  toFun l := ⟨l.length, l.get⟩
  invFun f := List.ofFn f.2
  left_inv := List.ofFn_get
  right_inv := fun ⟨_, f⟩ =>
Fin.sigma_eq_of_eq_comp_cast length_ofFn funext fun i => get_ofFn f i

/-- A recursor for lists that expands a list into a function mapping to its elements.

This can be used with `induction l using List.ofFnRec`. -/
@[elab_as_elim]
/--
Definition of `ofFnRec` / `ofFnRec` 的定义

English:
definition ofFnRec
  signature: {C : List α -> Sort*} (h : forall (n) (f : Fin n -> α), C (List.ofFn f)) (l : List α)
  body: cast (congr_arg C l.ofFn_get)
    h l.length l.get

@[simp]

中文:
定义 ofFnRec
  签名: {C : 列表 α -> 类型层*} (h : 对任意 (n) (f : 有限集 n -> α), C (列表.ofFn f)) (l : 列表 α)
  定义体: cast (congr_arg C l.ofFn_get)
    h l.length l.get

@[simp]

Depends on / 依赖: congr_arg, l.get, l.length, l.ofFn_get, length, ofFn_get
-/
def ofFnRec {C : List α -> Sort*} (h : forall (n) (f : Fin n -> α), C (List.ofFn f)) (l : List α) : C l :=
cast (congr_arg C l.ofFn_get)
    h l.length l.get

@[simp]
/--
theorem `ofFnRec_ofFn` / 定理 `ofFnRec_ofFn`

English:
theorem ofFnRec_ofFn
  statement: {C : List α -> Sort*} (h : forall (n) (f : Fin n -> α), C (List.ofFn f)) {n : Nat}
  proof: equivSigmaTuple.rightInverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩

中文:
定理 ofFnRec_ofFn
  结论: {C : 列表 α -> 类型层*} (h : 对任意 (n) (f : 有限集 n -> α), C (列表.ofFn f)) {n : 自然数}
  证明: equivSigmaTuple.rightInverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩

Depends on / 依赖: cast_eq, equivSigmaTuple, equivSigmaTuple.rightInverse_symm.cast_eq, rightInverse_symm
-/
theorem ofFnRec_ofFn {C : List α -> Sort*} (h : forall (n) (f : Fin n -> α), C (List.ofFn f)) {n : Nat}
    (f : Fin n -> α) : @ofFnRec _ C h (List.ofFn f) = h _ f :=
  equivSigmaTuple.rightInverse_symm.cast_eq (fun s => h s.1 s.2) ⟨n, f⟩

/--
theorem `exists_iff_exists_tuple` / 定理 `exists_iff_exists_tuple`

English:
theorem exists_iff_exists_tuple
  given: {P : List α -> Prop}
  proof: equivSigmaTuple.symm.surjective.exists.trans Sigma.exists

中文:
定理 存在_iff_存在_tuple
  条件: {P : 列表 α -> 命题}
  证明: equivSigmaTuple.symm.surjective.exists.trans Sigma.exists

Depends on / 依赖: Sigma.exists, equivSigmaTuple, equivSigmaTuple.symm.surjective.exists.trans, surjective
-/
theorem exists_iff_exists_tuple {P : List α -> Prop} :
    (exists l : List α, P l) ↔ exists (n : _) (f : Fin n -> α), P (List.ofFn f) :=
  equivSigmaTuple.symm.surjective.exists.trans Sigma.exists

/--
theorem `forall_iff_forall_tuple` / 定理 `forall_iff_forall_tuple`

English:
theorem forall_iff_forall_tuple
  given: {P : List α -> Prop}
  proof: equivSigmaTuple.symm.surjective.forall.trans Sigma.forall

中文:
定理 对任意_iff_对任意_tuple
  条件: {P : 列表 α -> 命题}
  证明: equivSigmaTuple.symm.surjective.forall.trans Sigma.forall

Depends on / 依赖: Sigma.forall, equivSigmaTuple, equivSigmaTuple.symm.surjective.forall.trans, surjective
-/
theorem forall_iff_forall_tuple {P : List α -> Prop} :
    (forall l : List α, P l) ↔ forall (n) (f : Fin n -> α), P (List.ofFn f) :=
  equivSigmaTuple.symm.surjective.forall.trans Sigma.forall

/--
theorem `ofFn_inj'` / 定理 `ofFn_inj'`

English:
theorem ofFn_inj'
  given: {m n : Nat} {f : Fin m -> α} {g : Fin n -> α}
  proof: Iff.symm equivSigmaTuple.symm.injective.eq_iff.symm

中文:
定理 ofFn_inj'
  条件: {m n : 自然数} {f : 有限集 m -> α} {g : 有限集 n -> α}
  证明: Iff.symm equivSigmaTuple.symm.injective.eq_iff.symm

Depends on / 依赖: Iff.symm, eq_iff, equivSigmaTuple, equivSigmaTuple.symm.injective.eq_iff.symm, injective
-/
theorem ofFn_inj' {m n : Nat} {f : Fin m -> α} {g : Fin n -> α} :
    ofFn f = ofFn g ↔ (⟨m, f⟩ : Σ n, Fin n -> α) = ⟨n, g⟩ :=
Iff.symm equivSigmaTuple.symm.injective.eq_iff.symm

/--
theorem `ofFn_injective` / 定理 `ofFn_injective`

English:
theorem ofFn_injective
  given: {n : Nat}
  statement: Function.Injective (ofFn : (Fin n -> α) -> List α)
  proof: fun f g h =>
eq_of_heq by rw [ofFn_inj'] at h; cases h; rfl

中文:
定理 ofFn_injective
  条件: {n : 自然数}
  结论: 函数.单射 (ofFn : (有限集 n -> α) -> 列表 α)
  证明: fun f g h =>
eq_of_heq by rw [ofFn_inj'] at h; cases h; rfl
-/
theorem ofFn_injective {n : Nat} : Function.Injective (ofFn : (Fin n -> α) -> List α) := fun f g h =>
eq_of_heq by rw [ofFn_inj'] at h; cases h; rfl

/-- A special case of `List.ofFn_inj` for when the two functions are indexed by defeq `n`. -/
@[simp]
/--
theorem `ofFn_inj` / 定理 `ofFn_inj`

English:
theorem ofFn_inj
  given: {n : Nat} {f g : Fin n -> α}
  statement: ofFn f = ofFn g ↔ f = g
  proof: ofFn_injective.eq_iff

中文:
定理 ofFn_inj
  条件: {n : 自然数} {f g : 有限集 n -> α}
  结论: ofFn f = ofFn g ↔ f = g
  证明: ofFn_injective.eq_iff

Depends on / 依赖: eq_iff, ofFn_injective, ofFn_injective.eq_iff
-/
theorem ofFn_inj {n : Nat} {f g : Fin n -> α} : ofFn f = ofFn g ↔ f = g :=
  ofFn_injective.eq_iff

end List
