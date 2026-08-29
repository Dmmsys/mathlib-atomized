/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Logic.Embedding.Set
public import Mathlib.Logic.Equiv.Option
public import Mathlib.Data.Int.Init
public import Batteries.Data.Fin.Lemmas

/-!
# Equivalences for `Fin n`
-/

@[expose] public section

assert_not_exists MonoidWithZero

universe u

variable {m n : Nat}

/-!
### Miscellaneous

This is currently not very sorted. PRs welcome!
-/

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Fin.preimage_apply_01_prod` / 定理 `Fin.preimage_apply_01_prod`

English:
theorem Fin.preimage_apply_01_prod
  given: {α : Fin 2 -> Type u} (s : Set (α 0)) (t : Set (α 1))
  proof: by
  ext f
  simp [Fin.forall_fin_two]

中文:
定理 Fin.preimage_apply_01_prod
  条件: {α : Fin 2 -> 类型u} (s : Set (α 0)) (t : Set (α 1))
  证明: by
  ext f
  simp [Fin.forall_fin_two]

Depends on / 依赖: Fin.forall_fin_two, forall_fin_two
-/
theorem Fin.preimage_apply_01_prod {α : Fin 2 -> Type u} (s : Set (α 0)) (t : Set (α 1)) :
    (fun f : forall i, α i => (f 0, f 1)) ⁻¹' s ×ˢ t =
      Set.pi Set.univ (Fin.cons s <| Fin.cons t finZeroElim) := by
  ext f
  simp [Fin.forall_fin_two]

/--
theorem `Fin.preimage_apply_01_prod'` / 定理 `Fin.preimage_apply_01_prod'`

English:
theorem Fin.preimage_apply_01_prod'
  given: {α : Type u} (s t : Set α)
  proof: @Fin.preimage_apply_01_prod (fun _ => α) s t

中文:
定理 Fin.preimage_apply_01_prod'
  条件: {α : 类型u} (s t : Set α)
  证明: @Fin.preimage_apply_01_prod (fun _ => α) s t

Depends on / 依赖: Fin.preimage_apply_01_prod, preimage_apply_01_prod
-/
theorem Fin.preimage_apply_01_prod' {α : Type u} (s t : Set α) :
    (fun f : Fin 2 -> α => (f 0, f 1)) ⁻¹' s ×ˢ t = Set.pi Set.univ ![s, t] :=
  @Fin.preimage_apply_01_prod (fun _ => α) s t

/-- A product space `α × β` is equivalent to the space `Π i : Fin 2, γ i`, where
`γ = Fin.cons α (Fin.cons β finZeroElim)`. See also `piFinTwoEquiv` and
`finTwoArrowEquiv`. -/
@[simps! -fullyApplied]
/--
Definition of `prodEquivPiFinTwo` / `prodEquivPiFinTwo` 的定义

English:
definition prodEquivPiFinTwo
  signature: (α β : Type u)
  body: (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm

中文:
定义 prodEquivPiFinTwo
  签名: (α β : 类型u)
  定义体: (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm

Depends on / 依赖: Fin.cons, finZeroElim, piFinTwoEquiv
-/
def prodEquivPiFinTwo (α β : Type u) : α × β ≃ forall i : Fin 2, ![α, β] i :=
  (piFinTwoEquiv (Fin.cons α (Fin.cons β finZeroElim))).symm

/-- The space of functions `Fin 2 → α` is equivalent to `α × α`. See also `piFinTwoEquiv` and
`prodEquivPiFinTwo`. -/
@[simps -fullyApplied]
/--
Definition of `finTwoArrowEquiv` / `finTwoArrowEquiv` 的定义

English:
definition finTwoArrowEquiv
  signature: (α : Type*)
  body: { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }

中文:
定义 finTwoArrowEquiv
  签名: (α : 类型)
  定义体: { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }

Depends on / 依赖: invFun, piFinTwoEquiv
-/
def finTwoArrowEquiv (α : Type*) : (Fin 2 -> α) ≃ α × α :=
  { piFinTwoEquiv fun _ => α with invFun := fun x => ![x.1, x.2] }

/--
Definition of `finSuccEquiv'` / `finSuccEquiv'` 的定义

English:
definition finSuccEquiv'
  signature: (i : Fin (n + 1))
  body: i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> simp

中文:
定义 finSuccEquiv'
  签名: (i : Fin (n + 1))
  定义体: i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> simp

Depends on / 依赖: i.insertNth, insertNth
-/
def finSuccEquiv' (i : Fin (n + 1)) : Fin (n + 1) ≃ Option (Fin n) where
  toFun := i.insertNth none some
  invFun x := x.casesOn' i (Fin.succAbove i)
  left_inv x := Fin.succAboveCases i (by simp) (fun j => by simp) x
  right_inv x := by cases x <;> simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `finSuccEquiv'_at` / 定理 `finSuccEquiv'_at`

English:
theorem finSuccEquiv'_at
  given: (i : Fin (n + 1))
  statement: (finSuccEquiv' i) i = none
  proof: by
  simp [finSuccEquiv']

@[simp]

中文:
定理 finSuccEquiv'_at
  条件: (i : Fin (n + 1))
  结论: (finSuccEquiv' i) i = none
  证明: by
  simp [finSuccEquiv']

@[simp]
-/
theorem finSuccEquiv'_at (i : Fin (n + 1)) : (finSuccEquiv' i) i = none := by
  simp [finSuccEquiv']

@[simp]
/--
theorem `finSuccEquiv'_succAbove` / 定理 `finSuccEquiv'_succAbove`

English:
theorem finSuccEquiv'_succAbove
  given: (i : Fin (n + 1)) (j : Fin n)
  proof: @Fin.insertNth_apply_succAbove n (fun _ => Option (Fin n)) i _ _ _

中文:
定理 finSuccEquiv'_succAbove
  条件: (i : Fin (n + 1)) (j : Fin n)
  证明: @Fin.insertNth_apply_succAbove n (fun _ => Option (Fin n)) i _ _ _
-/
theorem finSuccEquiv'_succAbove (i : Fin (n + 1)) (j : Fin n) :
    finSuccEquiv' i (i.succAbove j) = some j :=
  @Fin.insertNth_apply_succAbove n (fun _ => Option (Fin n)) i _ _ _

/--
theorem `finSuccEquiv'_below` / 定理 `finSuccEquiv'_below`

English:
theorem finSuccEquiv'_below
  given: {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i)
  proof: by
  rw [← Fin.succAbove_of_castSucc_lt _ _ h]; rw [finSuccEquiv'_succAbove]

中文:
定理 finSuccEquiv'_below
  条件: {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i)
  证明: by
  rw [← Fin.succAbove_of_castSucc_lt _ _ h]; rw [finSuccEquiv'_succAbove]
-/
theorem finSuccEquiv'_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i) (Fin.castSucc m) = m := by
  rw [← Fin.succAbove_of_castSucc_lt _ _ h]; rw [finSuccEquiv'_succAbove]

/--
theorem `finSuccEquiv'_above` / 定理 `finSuccEquiv'_above`

English:
theorem finSuccEquiv'_above
  given: {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m)
  proof: by
  rw [← Fin.succAbove_of_le_castSucc _ _ h]; rw [finSuccEquiv'_succAbove]

@[simp]

中文:
定理 finSuccEquiv'_above
  条件: {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m)
  证明: by
  rw [← Fin.succAbove_of_le_castSucc _ _ h]; rw [finSuccEquiv'_succAbove]

@[simp]
-/
theorem finSuccEquiv'_above {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m) :
    (finSuccEquiv' i) m.succ = some m := by
  rw [← Fin.succAbove_of_le_castSucc _ _ h]; rw [finSuccEquiv'_succAbove]

@[simp]
/--
theorem `finSuccEquiv'_symm_none` / 定理 `finSuccEquiv'_symm_none`

English:
theorem finSuccEquiv'_symm_none
  given: (i : Fin (n + 1))
  statement: (finSuccEquiv' i).symm none = i
  proof: rfl

@[simp]

中文:
定理 finSuccEquiv'_symm_none
  条件: (i : Fin (n + 1))
  结论: (finSuccEquiv' i).symm none = i
  证明: rfl

@[simp]
-/
theorem finSuccEquiv'_symm_none (i : Fin (n + 1)) : (finSuccEquiv' i).symm none = i :=
  rfl

@[simp]
/--
theorem `finSuccEquiv'_symm_some` / 定理 `finSuccEquiv'_symm_some`

English:
theorem finSuccEquiv'_symm_some
  given: (i : Fin (n + 1)) (j : Fin n)
  proof: rfl

@[simp]

中文:
定理 finSuccEquiv'_symm_some
  条件: (i : Fin (n + 1)) (j : Fin n)
  证明: rfl

@[simp]
-/
theorem finSuccEquiv'_symm_some (i : Fin (n + 1)) (j : Fin n) :
    (finSuccEquiv' i).symm (some j) = i.succAbove j :=
  rfl

@[simp]
/--
theorem `finSuccEquiv'_eq_some` / 定理 `finSuccEquiv'_eq_some`

English:
theorem finSuccEquiv'_eq_some
  given: {i j : Fin (n + 1)} {k : Fin n}
  proof: (finSuccEquiv' i).eq_symm_apply.symm

@[simp]

中文:
定理 finSuccEquiv'_eq_some
  条件: {i j : Fin (n + 1)} {k : Fin n}
  证明: (finSuccEquiv' i).eq_symm_apply.symm

@[simp]
-/
theorem finSuccEquiv'_eq_some {i j : Fin (n + 1)} {k : Fin n} :
    finSuccEquiv' i j = k ↔ j = i.succAbove k :=
  (finSuccEquiv' i).eq_symm_apply.symm

@[simp]
/--
theorem `finSuccEquiv'_eq_none` / 定理 `finSuccEquiv'_eq_none`

English:
theorem finSuccEquiv'_eq_none
  given: {i j : Fin (n + 1)}
  statement: finSuccEquiv' i j = none ↔ i = j
  proof: (finSuccEquiv' i).eq_symm_apply.symm.trans eq_comm

中文:
定理 finSuccEquiv'_eq_none
  条件: {i j : Fin (n + 1)}
  结论: finSuccEquiv' i j = none ↔ i = j
  证明: (finSuccEquiv' i).eq_symm_apply.symm.trans eq_comm
-/
theorem finSuccEquiv'_eq_none {i j : Fin (n + 1)} : finSuccEquiv' i j = none ↔ i = j :=
  (finSuccEquiv' i).eq_symm_apply.symm.trans eq_comm

/--
theorem `finSuccEquiv'_symm_some_below` / 定理 `finSuccEquiv'_symm_some_below`

English:
theorem finSuccEquiv'_symm_some_below
  given: {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i)
  proof: Fin.succAbove_of_castSucc_lt i m h

中文:
定理 finSuccEquiv'_symm_some_below
  条件: {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i)
  证明: Fin.succAbove_of_castSucc_lt i m h
-/
theorem finSuccEquiv'_symm_some_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm (some m) = Fin.castSucc m :=
  Fin.succAbove_of_castSucc_lt i m h

/--
theorem `finSuccEquiv'_symm_some_above` / 定理 `finSuccEquiv'_symm_some_above`

English:
theorem finSuccEquiv'_symm_some_above
  given: {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m)
  proof: Fin.succAbove_of_le_castSucc i m h

中文:
定理 finSuccEquiv'_symm_some_above
  条件: {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m)
  证明: Fin.succAbove_of_le_castSucc i m h
-/
theorem finSuccEquiv'_symm_some_above {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m) :
    (finSuccEquiv' i).symm (some m) = m.succ :=
  Fin.succAbove_of_le_castSucc i m h

/--
theorem `finSuccEquiv'_symm_coe_below` / 定理 `finSuccEquiv'_symm_coe_below`

English:
theorem finSuccEquiv'_symm_coe_below
  given: {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i)
  proof: finSuccEquiv'_symm_some_below h

中文:
定理 finSuccEquiv'_symm_coe_below
  条件: {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i)
  证明: finSuccEquiv'_symm_some_below h
-/
theorem finSuccEquiv'_symm_coe_below {i : Fin (n + 1)} {m : Fin n} (h : Fin.castSucc m < i) :
    (finSuccEquiv' i).symm m = Fin.castSucc m :=
  finSuccEquiv'_symm_some_below h

/--
theorem `finSuccEquiv'_symm_coe_above` / 定理 `finSuccEquiv'_symm_coe_above`

English:
theorem finSuccEquiv'_symm_coe_above
  given: {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m)
  proof: finSuccEquiv'_symm_some_above h

中文:
定理 finSuccEquiv'_symm_coe_above
  条件: {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m)
  证明: finSuccEquiv'_symm_some_above h
-/
theorem finSuccEquiv'_symm_coe_above {i : Fin (n + 1)} {m : Fin n} (h : i <= Fin.castSucc m) :
    (finSuccEquiv' i).symm m = m.succ :=
  finSuccEquiv'_symm_some_above h

/--
Definition of `finSuccEquiv` / `finSuccEquiv` 的定义

English:
definition finSuccEquiv
  signature: (n : Nat)
  body: finSuccEquiv' 0

@[simp]

中文:
定义 finSuccEquiv
  签名: (n : 自然数)
  定义体: finSuccEquiv' 0

@[simp]

Depends on / 依赖: finSuccEquiv
-/
def finSuccEquiv (n : Nat) : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' 0

@[simp]
/--
theorem `finSuccEquiv_zero` / 定理 `finSuccEquiv_zero`

English:
theorem finSuccEquiv_zero
  statement: (finSuccEquiv n) 0 = none
  proof: rfl

@[simp]

中文:
定理 finSuccEquiv_zero
  结论: (finSuccEquiv n) 0 = none
  证明: rfl

@[simp]
-/
theorem finSuccEquiv_zero : (finSuccEquiv n) 0 = none :=
  rfl

@[simp]
/--
theorem `finSuccEquiv_succ` / 定理 `finSuccEquiv_succ`

English:
theorem finSuccEquiv_succ
  given: (m : Fin n)
  statement: (finSuccEquiv n) m.succ = some m
  proof: finSuccEquiv'_above (Fin.zero_le _)

@[simp]

中文:
定理 finSuccEquiv_succ
  条件: (m : Fin n)
  结论: (finSuccEquiv n) m.succ = some m
  证明: finSuccEquiv'_above (Fin.zero_le _)

@[simp]

Depends on / 依赖: Fin.zero_le, _above, finSuccEquiv, zero_le
-/
theorem finSuccEquiv_succ (m : Fin n) : (finSuccEquiv n) m.succ = some m :=
  finSuccEquiv'_above (Fin.zero_le _)

@[simp]
/--
theorem `finSuccEquiv_last` / 定理 `finSuccEquiv_last`

English:
theorem finSuccEquiv_last
  given: (n : Nat)
  statement: finSuccEquiv (n + 1) (Fin.last (n + 1)) = Fin.last n
  proof: rfl

@[simp]

中文:
定理 finSuccEquiv_last
  条件: (n : 自然数)
  结论: finSuccEquiv (n + 1) (Fin.last (n + 1)) = Fin.last n
  证明: rfl

@[simp]
-/
theorem finSuccEquiv_last (n : Nat) : finSuccEquiv (n + 1) (Fin.last (n + 1)) = Fin.last n := rfl

@[simp]
/--
theorem `finSuccEquiv_symm_none` / 定理 `finSuccEquiv_symm_none`

English:
theorem finSuccEquiv_symm_none
  statement: (finSuccEquiv n).symm none = 0
  proof: finSuccEquiv'_symm_none _

@[simp]

中文:
定理 finSuccEquiv_symm_none
  结论: (finSuccEquiv n).symm none = 0
  证明: finSuccEquiv'_symm_none _

@[simp]

Depends on / 依赖: _symm_none, finSuccEquiv
-/
theorem finSuccEquiv_symm_none : (finSuccEquiv n).symm none = 0 :=
  finSuccEquiv'_symm_none _

@[simp]
/--
theorem `finSuccEquiv_symm_some` / 定理 `finSuccEquiv_symm_some`

English:
theorem finSuccEquiv_symm_some
  given: (m : Fin n)
  statement: (finSuccEquiv n).symm (some m) = m.succ
  proof: congr_fun Fin.succAbove_zero m

@[simp]

中文:
定理 finSuccEquiv_symm_some
  条件: (m : Fin n)
  结论: (finSuccEquiv n).symm (some m) = m.succ
  证明: congr_fun Fin.succAbove_zero m

@[simp]

Depends on / 依赖: Fin.succAbove_zero, congr_fun, succAbove_zero
-/
theorem finSuccEquiv_symm_some (m : Fin n) : (finSuccEquiv n).symm (some m) = m.succ :=
  congr_fun Fin.succAbove_zero m

@[simp]
/--
theorem `finSuccEquiv_eq_some` / 定理 `finSuccEquiv_eq_some`

English:
theorem finSuccEquiv_eq_some
  given: {i : Fin (n + 1)} {j : Fin n}
  proof: (finSuccEquiv n).eq_symm_apply.symm

@[simp]

中文:
定理 finSuccEquiv_eq_some
  条件: {i : Fin (n + 1)} {j : Fin n}
  证明: (finSuccEquiv n).eq_symm_apply.symm

@[simp]

Depends on / 依赖: eq_symm_apply, eq_symm_apply.symm, finSuccEquiv
-/
theorem finSuccEquiv_eq_some {i : Fin (n + 1)} {j : Fin n} :
    finSuccEquiv n i = j ↔ i = j.succ :=
  (finSuccEquiv n).eq_symm_apply.symm

@[simp]
/--
theorem `finSuccEquiv_eq_none` / 定理 `finSuccEquiv_eq_none`

English:
theorem finSuccEquiv_eq_none
  given: {i : Fin (n + 1)}
  statement: finSuccEquiv n i = none ↔ i = 0
  proof: (finSuccEquiv n).eq_symm_apply.symm

中文:
定理 finSuccEquiv_eq_none
  条件: {i : Fin (n + 1)}
  结论: finSuccEquiv n i = none ↔ i = 0
  证明: (finSuccEquiv n).eq_symm_apply.symm

Depends on / 依赖: eq_symm_apply, eq_symm_apply.symm, finSuccEquiv
-/
theorem finSuccEquiv_eq_none {i : Fin (n + 1)} : finSuccEquiv n i = none ↔ i = 0 :=
  (finSuccEquiv n).eq_symm_apply.symm

/--
theorem `finSuccEquiv'_zero` / 定理 `finSuccEquiv'_zero`

English:
theorem finSuccEquiv'_zero
  statement: finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n
  proof: rfl

中文:
定理 finSuccEquiv'_zero
  结论: finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n
  证明: rfl
-/
theorem finSuccEquiv'_zero : finSuccEquiv' (0 : Fin (n + 1)) = finSuccEquiv n :=
  rfl

/--
theorem `finSuccEquiv'_last_apply_castSucc` / 定理 `finSuccEquiv'_last_apply_castSucc`

English:
theorem finSuccEquiv'_last_apply_castSucc
  given: (i : Fin n)
  proof: by
  rw [← Fin.succAbove_last]; rw [finSuccEquiv'_succAbove]

中文:
定理 finSuccEquiv'_last_apply_castSucc
  条件: (i : Fin n)
  证明: by
  rw [← Fin.succAbove_last]; rw [finSuccEquiv'_succAbove]
-/
theorem finSuccEquiv'_last_apply_castSucc (i : Fin n) :
    finSuccEquiv' (Fin.last n) (Fin.castSucc i) = i := by
  rw [← Fin.succAbove_last]; rw [finSuccEquiv'_succAbove]

/--
theorem `finSuccEquiv'_last_apply` / 定理 `finSuccEquiv'_last_apply`

English:
theorem finSuccEquiv'_last_apply
  given: {i : Fin (n + 1)} (h : i != Fin.last n)
  proof: by
  simp

中文:
定理 finSuccEquiv'_last_apply
  条件: {i : Fin (n + 1)} (h : i != Fin.last n)
  证明: by
  simp
-/
theorem finSuccEquiv'_last_apply {i : Fin (n + 1)} (h : i != Fin.last n) :
    finSuccEquiv' (Fin.last n) i = Fin.castLT i (Fin.val_lt_last h) := by
  simp

/--
theorem `finSuccEquiv'_ne_last_apply` / 定理 `finSuccEquiv'_ne_last_apply`

English:
theorem finSuccEquiv'_ne_last_apply
  given: {i j : Fin (n + 1)} (hi : i != Fin.last n) (hj : j != i)
  proof: by
  rcases Fin.exists_succAbove_eq hj with ⟨j, rfl⟩
  rcases Fin.exists_castSucc_eq.2 hi with ⟨i, rfl⟩
  simp

中文:
定理 finSuccEquiv'_ne_last_apply
  条件: {i j : Fin (n + 1)} (hi : i != Fin.last n) (hj : j != i)
  证明: by
  rcases Fin.exists_succAbove_eq hj with ⟨j, rfl⟩
  rcases Fin.exists_castSucc_eq.2 hi with ⟨i, rfl⟩
  simp
-/
theorem finSuccEquiv'_ne_last_apply {i j : Fin (n + 1)} (hi : i != Fin.last n) (hj : j != i) :
    finSuccEquiv' i j = (i.castLT (Fin.val_lt_last hi)).predAbove j := by
  rcases Fin.exists_succAbove_eq hj with ⟨j, rfl⟩
  rcases Fin.exists_castSucc_eq.2 hi with ⟨i, rfl⟩
  simp

/--
Definition of `finSuccAboveEquiv` / `finSuccAboveEquiv` 的定义

English:
definition finSuccAboveEquiv
  signature: (p : Fin (n + 1))
  body: .optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩

中文:
定义 finSuccAboveEquiv
  签名: (p : Fin (n + 1))
  定义体: .optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩

Depends on / 依赖: finSuccEquiv, optionSubtype
-/
def finSuccAboveEquiv (p : Fin (n + 1)) : Fin n ≃ { x : Fin (n + 1) // x != p } :=
  .optionSubtype p ⟨(finSuccEquiv' p).symm, rfl⟩

/--
theorem `finSuccAboveEquiv_apply` / 定理 `finSuccAboveEquiv_apply`

English:
theorem finSuccAboveEquiv_apply
  given: (p : Fin (n + 1)) (i : Fin n)
  proof: rfl

中文:
定理 finSuccAboveEquiv_apply
  条件: (p : Fin (n + 1)) (i : Fin n)
  证明: rfl

Depends on / 依赖: preNormEDS
-/
theorem finSuccAboveEquiv_apply (p : Fin (n + 1)) (i : Fin n) :
    finSuccAboveEquiv p i = ⟨p.succAbove i, p.succAbove_ne i⟩ :=
  rfl

/--
theorem `finSuccAboveEquiv_symm_apply_last` / 定理 `finSuccAboveEquiv_symm_apply_last`

English:
theorem finSuccAboveEquiv_symm_apply_last
  given: (x : { x : Fin (n + 1) // x != Fin.last n })
  proof: by
  rw [← Option.some_inj]
  simp [finSuccAboveEquiv]

中文:
定理 finSuccAboveEquiv_symm_apply_last
  条件: (x : { x : Fin (n + 1) // x != Fin.last n })
  证明: by
  rw [← Option.some_inj]
  simp [finSuccAboveEquiv]

Depends on / 依赖: Option.some_inj, finSuccAboveEquiv, preNormEDS, some_inj
-/
theorem finSuccAboveEquiv_symm_apply_last (x : { x : Fin (n + 1) // x != Fin.last n }) :
    (finSuccAboveEquiv (Fin.last n)).symm x = Fin.castLT x.1 (Fin.val_lt_last x.2) := by
  rw [← Option.some_inj]
  simp [finSuccAboveEquiv]

/--
theorem `finSuccAboveEquiv_symm_apply_ne_last` / 定理 `finSuccAboveEquiv_symm_apply_ne_last`

English:
theorem finSuccAboveEquiv_symm_apply_ne_last
  statement: {p : Fin (n + 1)} (h : p != Fin.last n)
  proof: by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv] using finSuccEquiv'_ne_last_apply h x.property

中文:
定理 finSuccAboveEquiv_symm_apply_ne_last
  结论: {p : Fin (n + 1)} (h : p != Fin.last n)
  证明: by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv] using finSuccEquiv'_ne_last_apply h x.property

Depends on / 依赖: Option.some_inj, _ne_last_apply, finSuccAboveEquiv, finSuccEquiv, preNormEDS, property, some_inj, x.property
-/
theorem finSuccAboveEquiv_symm_apply_ne_last {p : Fin (n + 1)} (h : p != Fin.last n)
    (x : { x : Fin (n + 1) // x != p }) :
    (finSuccAboveEquiv p).symm x = (p.castLT (Fin.val_lt_last h)).predAbove x := by
  rw [← Option.some_inj]
  simpa [finSuccAboveEquiv] using finSuccEquiv'_ne_last_apply h x.property

/--
Definition of `finSuccEquivLast` / `finSuccEquivLast` 的定义

English:
definition finSuccEquivLast
  signature: : Fin (n + 1) ≃ Option (Fin n)
  body: finSuccEquiv' (Fin.last n)

@[simp]

中文:
定义 finSuccEquivLast
  签名: : Fin (n + 1) ≃ Option (Fin n)
  定义体: finSuccEquiv' (Fin.last n)

@[simp]

Depends on / 依赖: Fin.last, finSuccEquiv, preNormEDS
-/
def finSuccEquivLast : Fin (n + 1) ≃ Option (Fin n) :=
  finSuccEquiv' (Fin.last n)

@[simp]
/--
theorem `finSuccEquivLast_castSucc` / 定理 `finSuccEquivLast_castSucc`

English:
theorem finSuccEquivLast_castSucc
  given: (i : Fin n)
  statement: finSuccEquivLast (Fin.castSucc i) = some i
  proof: finSuccEquiv'_below i.2

@[simp]

中文:
定理 finSuccEquivLast_castSucc
  条件: (i : Fin n)
  结论: finSuccEquivLast (Fin.castSucc i) = some i
  证明: finSuccEquiv'_below i.2

@[simp]

Depends on / 依赖: _below, finSuccEquiv, preNormEDS
-/
theorem finSuccEquivLast_castSucc (i : Fin n) : finSuccEquivLast (Fin.castSucc i) = some i :=
  finSuccEquiv'_below i.2

@[simp]
/--
theorem `finSuccEquivLast_last` / 定理 `finSuccEquivLast_last`

English:
theorem finSuccEquivLast_last
  statement: finSuccEquivLast (Fin.last n) = none
  proof: by
  simp [finSuccEquivLast]

@[simp]

中文:
定理 finSuccEquivLast_last
  结论: finSuccEquivLast (Fin.last n) = none
  证明: by
  simp [finSuccEquivLast]

@[simp]

Depends on / 依赖: Nat.mul_add_div, dif_neg, finSuccEquivLast, m.not_even_two_mul_add_one, mul_add_div, not_even_two_mul_add_one, preNormEDS, two_pos
-/
theorem finSuccEquivLast_last : finSuccEquivLast (Fin.last n) = none := by
  simp [finSuccEquivLast]

@[simp]
/--
theorem `finSuccEquivLast_symm_some` / 定理 `finSuccEquivLast_symm_some`

English:
theorem finSuccEquivLast_symm_some
  given: (i : Fin n)
  proof: finSuccEquiv'_symm_some_below i.2

中文:
定理 finSuccEquivLast_symm_some
  条件: (i : Fin n)
  证明: finSuccEquiv'_symm_some_below i.2

Depends on / 依赖: _symm_some_below, dif_pos, even_two_mul, finSuccEquiv, m.mul_div_cancel_left, mul_div_cancel_left, preNormEDS, two_pos
-/
theorem finSuccEquivLast_symm_some (i : Fin n) :
    finSuccEquivLast.symm (some i) = Fin.castSucc i :=
  finSuccEquiv'_symm_some_below i.2

/--
theorem `finSuccEquivLast_symm_none` / 定理 `finSuccEquivLast_symm_none`

English:
theorem finSuccEquivLast_symm_none
  statement: finSuccEquivLast.symm none = Fin.last n
  proof: finSuccEquiv'_symm_none _

中文:
定理 finSuccEquivLast_symm_none
  结论: finSuccEquivLast.symm none = Fin.last n
  证明: finSuccEquiv'_symm_none _
-/
@[simp] theorem finSuccEquivLast_symm_none : finSuccEquivLast.symm none = Fin.last n :=
  finSuccEquiv'_symm_none _

/--
Definition of `Equiv.embeddingFinSucc` / `Equiv.embeddingFinSucc` 的定义

English:
definition Equiv.embeddingFinSucc
  signature: (n : Nat) (ι : Type*)
  body: ((finSuccEquiv n).embeddingCongr (Equiv.refl ι)).trans
    (Function.Embedding.optionEmbeddingEquiv (Fin n) ι)

中文:
定义 Equiv.embeddingFinSucc
  签名: (n : 自然数) (ι : 类型)
  定义体: ((finSuccEquiv n).embeddingCongr (Equiv.refl ι)).trans
    (Function.Embedding.optionEmbeddingEquiv (Fin n) ι)

Depends on / 依赖: Embedding, Equiv.refl, Function, Function.Embedding.optionEmbeddingEquiv, embeddingCongr, finSuccEquiv, optionEmbeddingEquiv
-/
def Equiv.embeddingFinSucc (n : Nat) (ι : Type*) :
    (Fin (n + 1) ↪ ι) ≃ (Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :=
  ((finSuccEquiv n).embeddingCongr (Equiv.refl ι)).trans
    (Function.Embedding.optionEmbeddingEquiv (Fin n) ι)

/--
lemma `Equiv.embeddingFinSucc_fst` / 引理 `Equiv.embeddingFinSucc_fst`

English:
lemma Equiv.embeddingFinSucc_fst
  given: {n : Nat} {ι : Type*} (e : Fin (n + 1) ↪ ι)
  proof: rfl

中文:
引理 Equiv.embeddingFinSucc_fst
  条件: {n : 自然数} {ι : 类型} (e : Fin (n + 1) ↪ ι)
  证明: rfl
-/
@[simp] lemma Equiv.embeddingFinSucc_fst {n : Nat} {ι : Type*} (e : Fin (n + 1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).1 : Fin n -> ι) = e ∘ Fin.succ := rfl

/--
lemma `Equiv.embeddingFinSucc_snd` / 引理 `Equiv.embeddingFinSucc_snd`

English:
lemma Equiv.embeddingFinSucc_snd
  given: {n : Nat} {ι : Type*} (e : Fin (n + 1) ↪ ι)
  proof: rfl

中文:
引理 Equiv.embeddingFinSucc_snd
  条件: {n : 自然数} {ι : 类型} (e : Fin (n + 1) ↪ ι)
  证明: rfl
-/
@[simp] lemma Equiv.embeddingFinSucc_snd {n : Nat} {ι : Type*} (e : Fin (n + 1) ↪ ι) :
    ((Equiv.embeddingFinSucc n ι e).2 : ι) = e 0 := rfl

/--
lemma `Equiv.coe_embeddingFinSucc_symm` / 引理 `Equiv.coe_embeddingFinSucc_symm`

English:
lemma Equiv.coe_embeddingFinSucc_symm
  statement: {n : Nat} {ι : Type*}
  proof: by
  ext i
  exact Fin.cases rfl (fun j => rfl) i

中文:
引理 Equiv.coe_embeddingFinSucc_symm
  结论: {n : 自然数} {ι : 类型}
  证明: by
  ext i
  exact Fin.cases rfl (fun j => rfl) i
-/
@[simp] lemma Equiv.coe_embeddingFinSucc_symm {n : Nat} {ι : Type*}
    (f : Σ (e : Fin n ↪ ι), {i // i ∉ Set.range e}) :
    ((Equiv.embeddingFinSucc n ι).symm f : Fin (n + 1) -> ι) = Fin.cons f.2.1 f.1 := by
  ext i
  exact Fin.cases rfl (fun j => rfl) i

/--
Definition of `finSumFinEquiv` / `finSumFinEquiv` 的定义

English:
definition finSumFinEquiv
  signature: : Fin m oplus Fin n ≃ Fin (m + n) where
  body: Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Fin m oplus Fin n) Sum.inl Sum.inr i
  left_inv x := by rcases x with y | y <;> simp
  right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp

@[simp]

中文:
定义 finSumFinEquiv
  签名: : Fin m oplus Fin n ≃ Fin (m + n) where
  定义体: Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Fin m oplus Fin n) Sum.inl Sum.inr i
  left_inv x := by rcases x with y | y <;> simp
  right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp

@[simp]

Depends on / 依赖: Fin.castAdd, Fin.natAdd, Sum.elim, castAdd, natAdd
-/
def finSumFinEquiv : Fin m oplus Fin n ≃ Fin (m + n) where
  toFun := Sum.elim (Fin.castAdd n) (Fin.natAdd m)
  invFun i := @Fin.addCases m n (fun _ => Fin m oplus Fin n) Sum.inl Sum.inr i
  left_inv x := by rcases x with y | y <;> simp
  right_inv x := by refine Fin.addCases (fun i => ?_) (fun i => ?_) x <;> simp

@[simp]
/--
theorem `finSumFinEquiv_apply_left` / 定理 `finSumFinEquiv_apply_left`

English:
theorem finSumFinEquiv_apply_left
  given: (i : Fin m)
  proof: rfl

@[simp]

中文:
定理 finSumFinEquiv_apply_left
  条件: (i : Fin m)
  证明: rfl

@[simp]
-/
theorem finSumFinEquiv_apply_left (i : Fin m) :
    (finSumFinEquiv (Sum.inl i) : Fin (m + n)) = Fin.castAdd n i :=
  rfl

@[simp]
/--
theorem `finSumFinEquiv_apply_right` / 定理 `finSumFinEquiv_apply_right`

English:
theorem finSumFinEquiv_apply_right
  given: (i : Fin n)
  proof: rfl

@[simp]

中文:
定理 finSumFinEquiv_apply_right
  条件: (i : Fin n)
  证明: rfl

@[simp]
-/
theorem finSumFinEquiv_apply_right (i : Fin n) :
    (finSumFinEquiv (Sum.inr i) : Fin (m + n)) = Fin.natAdd m i :=
  rfl

@[simp]
/--
theorem `finSumFinEquiv_symm_apply_castAdd` / 定理 `finSumFinEquiv_symm_apply_castAdd`

English:
theorem finSumFinEquiv_symm_apply_castAdd
  given: (x : Fin m)
  proof: finSumFinEquiv.symm_apply_apply (Sum.inl x)

@[simp]

中文:
定理 finSumFinEquiv_symm_apply_castAdd
  条件: (x : Fin m)
  证明: finSumFinEquiv.symm_apply_apply (Sum.inl x)

@[simp]

Depends on / 依赖: Sum.inl, finSumFinEquiv, finSumFinEquiv.symm_apply_apply, symm_apply_apply
-/
theorem finSumFinEquiv_symm_apply_castAdd (x : Fin m) :
    finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x :=
  finSumFinEquiv.symm_apply_apply (Sum.inl x)

@[simp]
/--
theorem `finSumFinEquiv_symm_apply_castSucc` / 定理 `finSumFinEquiv_symm_apply_castSucc`

English:
theorem finSumFinEquiv_symm_apply_castSucc
  given: (x : Fin m)
  proof: finSumFinEquiv_symm_apply_castAdd x

@[simp]

中文:
定理 finSumFinEquiv_symm_apply_castSucc
  条件: (x : Fin m)
  证明: finSumFinEquiv_symm_apply_castAdd x

@[simp]

Depends on / 依赖: finSumFinEquiv_symm_apply_castAdd
-/
theorem finSumFinEquiv_symm_apply_castSucc (x : Fin m) :
    finSumFinEquiv.symm (Fin.castSucc x) = Sum.inl x :=
  finSumFinEquiv_symm_apply_castAdd x

@[simp]
/--
theorem `finSumFinEquiv_symm_apply_natAdd` / 定理 `finSumFinEquiv_symm_apply_natAdd`

English:
theorem finSumFinEquiv_symm_apply_natAdd
  given: (x : Fin n)
  proof: finSumFinEquiv.symm_apply_apply (Sum.inr x)

@[simp]

中文:
定理 finSumFinEquiv_symm_apply_natAdd
  条件: (x : Fin n)
  证明: finSumFinEquiv.symm_apply_apply (Sum.inr x)

@[simp]

Depends on / 依赖: Sum.inr, finSumFinEquiv, finSumFinEquiv.symm_apply_apply, symm_apply_apply
-/
theorem finSumFinEquiv_symm_apply_natAdd (x : Fin n) :
    finSumFinEquiv.symm (Fin.natAdd m x) = Sum.inr x :=
  finSumFinEquiv.symm_apply_apply (Sum.inr x)

@[simp]
/--
theorem `finSumFinEquiv_symm_last` / 定理 `finSumFinEquiv_symm_last`

English:
theorem finSumFinEquiv_symm_last
  statement: finSumFinEquiv.symm (Fin.last n) = Sum.inr 0
  proof: finSumFinEquiv_symm_apply_natAdd 0

中文:
定理 finSumFinEquiv_symm_last
  结论: finSumFinEquiv.symm (Fin.last n) = Sum.inr 0
  证明: finSumFinEquiv_symm_apply_natAdd 0

Depends on / 依赖: finSumFinEquiv_symm_apply_natAdd
-/
theorem finSumFinEquiv_symm_last : finSumFinEquiv.symm (Fin.last n) = Sum.inr 0 :=
  finSumFinEquiv_symm_apply_natAdd 0

/--
Definition of `finSumNatEquiv` / `finSumNatEquiv` 的定义

English:
definition finSumNatEquiv
  signature: (n : Nat)
  body: Sum.elim Fin.val (n + ·)
  invFun i := if hi : i < n then .inl ⟨i, hi⟩ else .inr (i - n)
  left_inv i := (i.casesOn
    (fun _ => dif_pos (Fin.is_lt _))
    (fun _ => (dif_neg (Nat.le_add_right _ _).not_gt).trans <|
      congrArg _ (Nat.add_sub_cancel_left _ _)))
right_inv i := (apply_dite _ _ _ _)

中文:
定义 finSumNatEquiv
  签名: (n : 自然数)
  定义体: Sum.elim Fin.val (n + ·)
  invFun i := if hi : i < n then .inl ⟨i, hi⟩ else .inr (i - n)
  left_inv i := (i.casesOn
    (fun _ => dif_pos (Fin.is_lt _))
    (fun _ => (dif_neg (Nat.le_add_right _ _).not_gt).trans <|
      congrArg _ (Nat.add_sub_cancel_left _ _)))
right_inv i := (apply_dite _ _ _ _)

Depends on / 依赖: Fin.val, Sum.elim
-/
def finSumNatEquiv (n : Nat) : Fin n oplus Nat ≃ Nat where
  toFun := Sum.elim Fin.val (n + ·)
  invFun i := if hi : i < n then .inl ⟨i, hi⟩ else .inr (i - n)
  left_inv i := (i.casesOn
    (fun _ => dif_pos (Fin.is_lt _))
    (fun _ => (dif_neg (Nat.le_add_right _ _).not_gt).trans <|
      congrArg _ (Nat.add_sub_cancel_left _ _)))
right_inv i := (apply_dite _ _ _ _).trans (i.lt_or_ge n).by_cases
    (fun hi => dif_pos hi)
    (fun hi => (dif_neg hi.not_gt).trans <| Nat.add_sub_cancel' hi)

/--
theorem `finSumNatEquiv_apply_left` / 定理 `finSumNatEquiv_apply_left`

English:
theorem finSumNatEquiv_apply_left
  given: (i : Fin n)
  proof: rfl

中文:
定理 finSumNatEquiv_apply_left
  条件: (i : Fin n)
  证明: rfl
-/
@[simp] theorem finSumNatEquiv_apply_left (i : Fin n) :
    finSumNatEquiv n (.inl i) = i := rfl

/--
theorem `finSumNatEquiv_apply_right` / 定理 `finSumNatEquiv_apply_right`

English:
theorem finSumNatEquiv_apply_right
  given: (i : Nat)
  proof: rfl

中文:
定理 finSumNatEquiv_apply_right
  条件: (i : 自然数)
  证明: rfl
-/
@[simp] theorem finSumNatEquiv_apply_right (i : Nat) :
    finSumNatEquiv n (.inr i) = n + i := rfl

/--
theorem `finSumNatEquiv_symm_apply_of_lt` / 定理 `finSumNatEquiv_symm_apply_of_lt`

English:
theorem finSumNatEquiv_symm_apply_of_lt
  given: {i : Nat} (hi : i < n)
  proof: dif_pos hi

中文:
定理 finSumNatEquiv_symm_apply_of_lt
  条件: {i : 自然数} (hi : i < n)
  证明: dif_pos hi
-/
@[simp] theorem finSumNatEquiv_symm_apply_of_lt {i : Nat} (hi : i < n) :
    (finSumNatEquiv n).symm i = .inl ⟨i, hi⟩ := dif_pos hi

/--
theorem `finSumNatEquiv_symm_apply_of_ge` / 定理 `finSumNatEquiv_symm_apply_of_ge`

English:
theorem finSumNatEquiv_symm_apply_of_ge
  given: {i : Nat} (hi : n <= i)
  proof: dif_neg (Nat.not_lt_of_ge hi)

中文:
定理 finSumNatEquiv_symm_apply_of_ge
  条件: {i : 自然数} (hi : n <= i)
  证明: dif_neg (Nat.not_lt_of_ge hi)
-/
@[simp] theorem finSumNatEquiv_symm_apply_of_ge {i : Nat} (hi : n <= i) :
    (finSumNatEquiv n).symm i = .inr (i - n) := dif_neg (Nat.not_lt_of_ge hi)

/--
theorem `finSumNatEquiv_symm_apply_fin` / 定理 `finSumNatEquiv_symm_apply_fin`

English:
theorem finSumNatEquiv_symm_apply_fin
  given: (i : Fin n)
  proof: by simp

中文:
定理 finSumNatEquiv_symm_apply_fin
  条件: (i : Fin n)
  证明: by simp
-/
theorem finSumNatEquiv_symm_apply_fin (i : Fin n) :
    (finSumNatEquiv n).symm i = .inl i := by simp

/--
theorem `finSumNatEquiv_symm_apply_add_left` / 定理 `finSumNatEquiv_symm_apply_add_left`

English:
theorem finSumNatEquiv_symm_apply_add_left
  given: (i : Nat)
  proof: by simp

中文:
定理 finSumNatEquiv_symm_apply_add_left
  条件: (i : 自然数)
  证明: by simp
-/
theorem finSumNatEquiv_symm_apply_add_left (i : Nat) :
    (finSumNatEquiv n).symm (i + n) = .inr i := by simp

/--
theorem `finSumNatEquiv_symm_apply_add_right` / 定理 `finSumNatEquiv_symm_apply_add_right`

English:
theorem finSumNatEquiv_symm_apply_add_right
  given: (i : Nat)
  proof: by simp

中文:
定理 finSumNatEquiv_symm_apply_add_right
  条件: (i : 自然数)
  证明: by simp
-/
theorem finSumNatEquiv_symm_apply_add_right (i : Nat) :
    (finSumNatEquiv n).symm (n + i) = .inr i := by simp

/--
theorem `isLeft_finSumNatEquiv_symm_apply` / 定理 `isLeft_finSumNatEquiv_symm_apply`

English:
theorem isLeft_finSumNatEquiv_symm_apply
  given: (i : Nat)
  proof: by
  rcases i.lt_or_ge n with hi | hi
  · simp_rw [finSumNatEquiv_symm_apply_of_lt hi, hi, Sum.isLeft_inl, decide_true]
  · simp_rw [finSumNatEquiv_symm_apply_of_ge hi, hi.not_gt, Sum.isLeft_inr, decide_false]

中文:
定理 isLeft_finSumNatEquiv_symm_apply
  条件: (i : 自然数)
  证明: by
  rcases i.lt_or_ge n with hi | hi
  · simp_rw [finSumNatEquiv_symm_apply_of_lt hi, hi, Sum.isLeft_inl, decide_true]
  · simp_rw [finSumNatEquiv_symm_apply_of_ge hi, hi.not_gt, Sum.isLeft_inr, decide_false]
-/
@[simp] theorem isLeft_finSumNatEquiv_symm_apply (i : Nat) :
    ((finSumNatEquiv n).symm i).isLeft = decide (i < n) := by
  rcases i.lt_or_ge n with hi | hi
  · simp_rw [finSumNatEquiv_symm_apply_of_lt hi, hi, Sum.isLeft_inl, decide_true]
  · simp_rw [finSumNatEquiv_symm_apply_of_ge hi, hi.not_gt, Sum.isLeft_inr, decide_false]

/--
theorem `isRight_finSumNatEquiv_symm_apply` / 定理 `isRight_finSumNatEquiv_symm_apply`

English:
theorem isRight_finSumNatEquiv_symm_apply
  given: (i : Nat)
  proof: by
  simp_rw [← not_lt, decide_not, ← isLeft_finSumNatEquiv_symm_apply]
  cases (finSumNatEquiv n).symm i <;> rfl

中文:
定理 isRight_finSumNatEquiv_symm_apply
  条件: (i : 自然数)
  证明: by
  simp_rw [← not_lt, decide_not, ← isLeft_finSumNatEquiv_symm_apply]
  cases (finSumNatEquiv n).symm i <;> rfl
-/
@[simp] theorem isRight_finSumNatEquiv_symm_apply (i : Nat) :
    ((finSumNatEquiv n).symm i).isRight = decide (n <= i) := by
  simp_rw [← not_lt, decide_not, ← isLeft_finSumNatEquiv_symm_apply]
  cases (finSumNatEquiv n).symm i <;> rfl

/--
Definition of `finAddFlip` / `finAddFlip` 的定义

English:
definition finAddFlip
  signature: : Fin (m + n) ≃ Fin (n + m)
  body: (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv

@[simp]

中文:
定义 finAddFlip
  签名: : Fin (m + n) ≃ Fin (n + m)
  定义体: (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv

@[simp]

Depends on / 依赖: Equiv.sumComm, finSumFinEquiv, finSumFinEquiv.symm.trans, sumComm
-/
def finAddFlip : Fin (m + n) ≃ Fin (n + m) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm _ _)).trans finSumFinEquiv

@[simp]
/--
theorem `finAddFlip_apply_castAdd` / 定理 `finAddFlip_apply_castAdd`

English:
theorem finAddFlip_apply_castAdd
  given: (k : Fin m) (n : Nat)
  proof: by simp [finAddFlip]

@[simp]

中文:
定理 finAddFlip_apply_castAdd
  条件: (k : Fin m) (n : 自然数)
  证明: by simp [finAddFlip]

@[simp]

Depends on / 依赖: finAddFlip
-/
theorem finAddFlip_apply_castAdd (k : Fin m) (n : Nat) :
    finAddFlip (Fin.castAdd n k) = Fin.natAdd n k := by simp [finAddFlip]

@[simp]
/--
theorem `finAddFlip_apply_natAdd` / 定理 `finAddFlip_apply_natAdd`

English:
theorem finAddFlip_apply_natAdd
  given: (k : Fin n) (m : Nat)
  proof: by simp [finAddFlip]

@[simp]

中文:
定理 finAddFlip_apply_natAdd
  条件: (k : Fin n) (m : 自然数)
  证明: by simp [finAddFlip]

@[simp]

Depends on / 依赖: finAddFlip
-/
theorem finAddFlip_apply_natAdd (k : Fin n) (m : Nat) :
    finAddFlip (Fin.natAdd m k) = Fin.castAdd m k := by simp [finAddFlip]

@[simp]
/--
theorem `finAddFlip_apply_mk_left` / 定理 `finAddFlip_apply_mk_left`

English:
theorem finAddFlip_apply_mk_left
  statement: {k : Nat} (h : k < m) (hk : k < m + n := Nat.lt_add_right n h)
  proof: by
  convert! finAddFlip_apply_castAdd ⟨k, h⟩ n

@[simp]

中文:
定理 finAddFlip_apply_mk_left
  结论: {k : 自然数} (h : k < m) (hk : k < m + n := 自然数.lt_add_right n h)
  证明: by
  convert! finAddFlip_apply_castAdd ⟨k, h⟩ n

@[simp]

Depends on / 依赖: Nat.lt_add_right, lt_add_right
-/
theorem finAddFlip_apply_mk_left {k : Nat} (h : k < m) (hk : k < m + n := Nat.lt_add_right n h)
    (hnk : n + k < n + m := Nat.add_lt_add_left h n) :
    finAddFlip (⟨k, hk⟩ : Fin (m + n)) = ⟨n + k, hnk⟩ := by
  convert! finAddFlip_apply_castAdd ⟨k, h⟩ n

@[simp]
/--
theorem `finAddFlip_apply_mk_right` / 定理 `finAddFlip_apply_mk_right`

English:
theorem finAddFlip_apply_mk_right
  given: {k : Nat} (h₁ : m <= k) (h₂ : k < m + n)
  proof: by
  convert! @finAddFlip_apply_natAdd n ⟨k - m, by lia⟩ m
  simp [Nat.add_sub_cancel' h₁]

中文:
定理 finAddFlip_apply_mk_right
  条件: {k : 自然数} (h₁ : m <= k) (h₂ : k < m + n)
  证明: by
  convert! @finAddFlip_apply_natAdd n ⟨k - m, by lia⟩ m
  simp [Nat.add_sub_cancel' h₁]

Depends on / 依赖: Nat.add_sub_cancel, add_sub_cancel, convert, finAddFlip_apply_natAdd
-/
theorem finAddFlip_apply_mk_right {k : Nat} (h₁ : m <= k) (h₂ : k < m + n) :
    finAddFlip (⟨k, h₂⟩ : Fin (m + n)) = ⟨k - m, by lia⟩ := by
  convert! @finAddFlip_apply_natAdd n ⟨k - m, by lia⟩ m
  simp [Nat.add_sub_cancel' h₁]

/-- Equivalence between `Fin m × Fin n` and `Fin (m * n)` -/
@[simps]
/--
Definition of `finProdFinEquiv` / `finProdFinEquiv` 的定义

English:
definition finProdFinEquiv
  signature: : Fin m × Fin n ≃ Fin (m * n) where
  body: ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ <= x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
_ = (x.1.1 + 1) * n := Eq.symm Nat.succ_mul _ _
        _ <= m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  le

中文:
定义 finProdFinEquiv
  签名: : Fin m × Fin n ≃ Fin (m * n) where
  定义体: ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ <= x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
_ = (x.1.1 + 1) * n := Eq.symm Nat.succ_mul _ _
        _ <= m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  le

Depends on / 依赖: Eq.symm, Fin.eq_of_val_eq, Nat.add_le_add_left, Nat.add_mul_div_left, Nat.div_eq_of_lt, Nat.mul_le_mul_right, Nat.not_lt_zero, Nat.pos_of_ne_zero, Nat.succ_mul, Prod.ext, add_le_add_left, add_mul_div_left, divNat, div_eq_of_lt, eq_of_val_eq, invFun, left_inv, modNat, mul_le_mul_right, not_lt_zero
-/
def finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n) where
  toFun x :=
    ⟨x.2 + n * x.1,
      calc
        x.2.1 + n * x.1.1 + 1 = x.1.1 * n + x.2.1 + 1 := by ac_rfl
        _ <= x.1.1 * n + n := Nat.add_le_add_left x.2.2 _
_ = (x.1.1 + 1) * n := Eq.symm Nat.succ_mul _ _
        _ <= m * n := Nat.mul_le_mul_right _ x.1.2
        ⟩
  invFun x := (x.divNat, x.modNat)
  left_inv := fun ⟨x, y⟩ =>
have H : 0 < n := Nat.pos_of_ne_zero fun H => Nat.not_lt_zero y.1 H ▸ y.2
    Prod.ext
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) / n = y.1 / n + x.1 := Nat.add_mul_div_left _ _ H
          _ = 0 + x.1 := by rw [Nat.div_eq_of_lt y.2]
          _ = x.1 := Nat.zero_add x.1)
      (Fin.eq_of_val_eq <|
        calc
          (y.1 + n * x.1) % n = y.1 % n := Nat.add_mul_mod_self_left _ _ _
          _ = y.1 := Nat.mod_eq_of_lt y.2)
right_inv _ := Fin.eq_of_val_eq Nat.mod_add_div _ _

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
This is like `finProdFinEquiv.symm` but with `m` infinite.
See `Nat.div_mod_unique` for a similar propositional statement. -/
@[simps]
/--
Definition of `Nat.divModEquiv` / `Nat.divModEquiv` 的定义

English:
definition Nat.divModEquiv
  signature: (n : Nat) [NeZero n]
  body: (a / n, Fin.ofNat n a)
  invFun p := p.1 * n + ↑p.2
  -- TODO: is there a canonical order of `*` and `+` here?
  left_inv _ := Nat.div_add_mod' _ _
  right_inv p := by
    refine Prod.ext ?_ (Fin.ext <| Nat.mul_add_mod_of_lt p.2.is_lt)
    dsimp only
    rw [Nat.add_comm]; rw [Nat.add_mul_div_right 

中文:
定义 Nat.divModEquiv
  签名: (n : 自然数) [NeZero n]
  定义体: (a / n, Fin.ofNat n a)
  invFun p := p.1 * n + ↑p.2
  -- TODO: is there a canonical order of `*` and `+` here?
  left_inv _ := Nat.div_add_mod' _ _
  right_inv p := by
    refine Prod.ext ?_ (Fin.ext <| Nat.mul_add_mod_of_lt p.2.is_lt)
    dsimp only
    rw [Nat.add_comm]; rw [Nat.add_mul_div_right 

Depends on / 依赖: Fin.ofNat
-/
def Nat.divModEquiv (n : Nat) [NeZero n] : Nat ≃ Nat × Fin n where
  toFun a := (a / n, Fin.ofNat n a)
  invFun p := p.1 * n + ↑p.2
  -- TODO: is there a canonical order of `*` and `+` here?
  left_inv _ := Nat.div_add_mod' _ _
  right_inv p := by
    refine Prod.ext ?_ (Fin.ext <| Nat.mul_add_mod_of_lt p.2.is_lt)
    dsimp only
    rw [Nat.add_comm]; rw [Nat.add_mul_div_right _ _ n.pos_of_neZero]; rw [Nat.div_eq_of_lt p.2.is_lt]; rw [Nat.zero_add]

/-- The equivalence induced by `a ↦ (a / n, a % n)` for nonzero `n`.
See `Int.ediv_emod_unique` for a similar propositional statement. -/
@[simps]
/--
Definition of `Int.divModEquiv` / `Int.divModEquiv` 的定义

English:
definition Int.divModEquiv
  signature: (n : Nat) [NeZero n]
  body: (a / n, Fin.ofNat n (a.natMod n))
  invFun p := p.1 * n + ↑p.2
  left_inv a := by
    simp_rw [Fin.val_ofNat, natCast_mod, natMod,
      toNat_of_nonneg (emod_nonneg _ <| natCast_eq_zero.not.2 (NeZero.ne n)), emod_emod,
      ediv_mul_add_emod]
  right_inv := fun ⟨q, r, hrn⟩ => by
    simp only [Pro

中文:
定义 Int.divModEquiv
  签名: (n : 自然数) [NeZero n]
  定义体: (a / n, Fin.ofNat n (a.natMod n))
  invFun p := p.1 * n + ↑p.2
  left_inv a := by
    simp_rw [Fin.val_ofNat, natCast_mod, natMod,
      toNat_of_nonneg (emod_nonneg _ <| natCast_eq_zero.not.2 (NeZero.ne n)), emod_emod,
      ediv_mul_add_emod]
  right_inv := fun ⟨q, r, hrn⟩ => by
    simp only [Pro

Depends on / 依赖: Fin.ofNat, a.natMod, natMod
-/
def Int.divModEquiv (n : Nat) [NeZero n] : Int ≃ Int × Fin n where
  -- TODO: could cast from int directly if we import `Data.ZMod.Defs`, though there are few lemmas
  -- about that coercion.
  toFun a := (a / n, Fin.ofNat n (a.natMod n))
  invFun p := p.1 * n + ↑p.2
  left_inv a := by
    simp_rw [Fin.val_ofNat, natCast_mod, natMod,
      toNat_of_nonneg (emod_nonneg _ <| natCast_eq_zero.not.2 (NeZero.ne n)), emod_emod,
      ediv_mul_add_emod]
  right_inv := fun ⟨q, r, hrn⟩ => by
    simp only [Prod.mk_inj, Fin.ext_iff]
    obtain ⟨h1, h2⟩ := Int.natCast_nonneg r, Int.ofNat_lt.2 hrn
    rw [Int.add_comm]; rw [add_mul_ediv_right _ _ (natCast_eq_zero.not.2 (NeZero.ne n))]; rw [ediv_eq_zero_of_lt h1 h2]; rw [natMod]; rw [add_mul_emod_self_right]; rw [emod_eq_of_lt h1 h2]; rw [toNat_natCast]
    exact ⟨q.zero_add, Fin.val_cast_of_lt hrn⟩

/-- Promote a `Fin n` into a larger `Fin m`, as a subtype where the underlying
values are retained.

This is the `Equiv` version of `Fin.castLE`. -/
@[simps apply symm_apply]
/--
Definition of `Fin.castLEquiv` / `Fin.castLEquiv` 的定义

English:
definition Fin.castLEquiv
  signature: {n m : Nat} (h : n <= m)
  body: ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp

中文:
定义 Fin.castLEquiv
  签名: {n m : 自然数} (h : n <= m)
  定义体: ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp

Depends on / 依赖: Fin.castLE, castLE
-/
def Fin.castLEquiv {n m : Nat} (h : n <= m) : Fin n ≃ { i : Fin m // (i : Nat) < n } where
  toFun i := ⟨Fin.castLE h i, by simp⟩
  invFun i := ⟨i, i.prop⟩
  left_inv _ := by simp
  right_inv _ := by simp

/-- The natural `Equiv` between `(Fin m → α) × (Fin n → α)` and `Fin (m + n) → α` -/
@[simps]
/--
Definition of `Fin.appendEquiv` / `Fin.appendEquiv` 的定义

English:
definition Fin.appendEquiv
  signature: {α : Type*} (m n : Nat)
  body: Fin.append fg.1 fg.2
  invFun f := ⟨fun i => f (Fin.castAdd n i), fun i => f (Fin.natAdd m i)⟩
  left_inv fg := by simp
  right_inv f := by simp [Fin.append_castAdd_natAdd]

中文:
定义 Fin.appendEquiv
  签名: {α : 类型} (m n : 自然数)
  定义体: Fin.append fg.1 fg.2
  invFun f := ⟨fun i => f (Fin.castAdd n i), fun i => f (Fin.natAdd m i)⟩
  left_inv fg := by simp
  right_inv f := by simp [Fin.append_castAdd_natAdd]

Depends on / 依赖: Fin.append, append
-/
def Fin.appendEquiv {α : Type*} (m n : Nat) :
    (Fin m -> α) × (Fin n -> α) ≃ (Fin (m + n) -> α) where
  toFun fg := Fin.append fg.1 fg.2
  invFun f := ⟨fun i => f (Fin.castAdd n i), fun i => f (Fin.natAdd m i)⟩
  left_inv fg := by simp
  right_inv f := by simp [Fin.append_castAdd_natAdd]

/-- `Fin (n + 1) → α` and `(Fin n → α) × α` are equivalent. -/
@[simps!]
/--
Definition of `Fin.succFunEquiv` / `Fin.succFunEquiv` 的定义

English:
definition Fin.succFunEquiv
  signature: (α : Type*) (n : Nat)
  body: (appendEquiv n 1).symm.trans (Equiv.prodCongrRight fun _ => Equiv.funUnique (Fin 1) α)

中文:
定义 Fin.succFunEquiv
  签名: (α : 类型) (n : 自然数)
  定义体: (appendEquiv n 1).symm.trans (Equiv.prodCongrRight fun _ => Equiv.funUnique (Fin 1) α)

Depends on / 依赖: Equiv.funUnique, Equiv.prodCongrRight, appendEquiv, funUnique, prodCongrRight, symm.trans
-/
def Fin.succFunEquiv (α : Type*) (n : Nat) : (Fin (n + 1) -> α) ≃ (Fin n -> α) × α :=
  (appendEquiv n 1).symm.trans (Equiv.prodCongrRight fun _ => Equiv.funUnique (Fin 1) α)
