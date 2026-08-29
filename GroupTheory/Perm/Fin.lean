/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Yi Yuan
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Option
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Permutations of `Fin n`
-/

@[expose] public section

assert_not_exists LinearMap

open Equiv

/--
Definition of `Equiv.Perm.decomposeFin` / `Equiv.Perm.decomposeFin` 的定义

English:
definition Equiv.Perm.decomposeFin
  signature: {n : Nat}
  body: ((Equiv.permCongr <| finSuccEquiv n).trans Equiv.Perm.decomposeOption).trans
    (Equiv.prodCongr (finSuccEquiv n).symm (Equiv.refl _))

@[simp]

中文:
定义 等价.置换.decomposeFin
  签名: {n : 自然数}
  定义体: ((Equiv.permCongr <| finSuccEquiv n).trans Equiv.Perm.decomposeOption).trans
    (Equiv.prodCongr (finSuccEquiv n).symm (Equiv.refl _))

@[simp]

Depends on / 依赖: Equiv.Perm.decomposeOption, Equiv.permCongr, Equiv.prodCongr, Equiv.refl, decomposeOption, finSuccEquiv, permCongr, prodCongr
-/
def Equiv.Perm.decomposeFin {n : Nat} : Perm (Fin n.succ) ≃ Fin n.succ × Perm (Fin n) :=
  ((Equiv.permCongr <| finSuccEquiv n).trans Equiv.Perm.decomposeOption).trans
    (Equiv.prodCongr (finSuccEquiv n).symm (Equiv.refl _))

@[simp]
/--
theorem `Equiv.Perm.decomposeFin_symm_of_refl` / 定理 `Equiv.Perm.decomposeFin_symm_of_refl`

English:
theorem Equiv.Perm.decomposeFin_symm_of_refl
  given: {n : Nat} (p : Fin (n + 1))
  proof: by
  simp [Equiv.Perm.decomposeFin, Equiv.permCongr_def, pull_end]

@[simp]

中文:
定理 等价.置换.decomposeFin_symm_of_refl
  条件: {n : 自然数} (p : 有限集 (n + 1))
  证明: by
  simp [Equiv.Perm.decomposeFin, Equiv.permCongr_def, pull_end]

@[simp]

Depends on / 依赖: Equiv.Perm.decomposeFin, Equiv.permCongr_def, decomposeFin, permCongr_def, pull_end
-/
theorem Equiv.Perm.decomposeFin_symm_of_refl {n : Nat} (p : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, Equiv.refl _) = swap 0 p := by
  simp [Equiv.Perm.decomposeFin, Equiv.permCongr_def, pull_end]

@[simp]
/--
theorem `Equiv.Perm.decomposeFin_symm_of_one` / 定理 `Equiv.Perm.decomposeFin_symm_of_one`

English:
theorem Equiv.Perm.decomposeFin_symm_of_one
  given: {n : Nat} (p : Fin (n + 1))
  proof: Equiv.Perm.decomposeFin_symm_of_refl p

@[simp]

中文:
定理 等价.置换.decomposeFin_symm_of_one
  条件: {n : 自然数} (p : 有限集 (n + 1))
  证明: Equiv.Perm.decomposeFin_symm_of_refl p

@[simp]

Depends on / 依赖: Equiv.Perm.decomposeFin_symm_of_refl, decomposeFin_symm_of_refl
-/
theorem Equiv.Perm.decomposeFin_symm_of_one {n : Nat} (p : Fin (n + 1)) :
    Equiv.Perm.decomposeFin.symm (p, 1) = swap 0 p :=
  Equiv.Perm.decomposeFin_symm_of_refl p

@[simp]
/--
theorem `Equiv.Perm.decomposeFin_symm_apply_zero` / 定理 `Equiv.Perm.decomposeFin_symm_apply_zero`

English:
theorem Equiv.Perm.decomposeFin_symm_apply_zero
  given: {n : Nat} (p : Fin (n + 1)) (e : Perm (Fin n))
  proof: by simp [Equiv.Perm.decomposeFin]

@[simp]

中文:
定理 等价.置换.decomposeFin_symm_apply_zero
  条件: {n : 自然数} (p : 有限集 (n + 1)) (e : 置换 (有限集 n))
  证明: by simp [Equiv.Perm.decomposeFin]

@[simp]

Depends on / 依赖: Equiv.Perm.decomposeFin, decomposeFin
-/
theorem Equiv.Perm.decomposeFin_symm_apply_zero {n : Nat} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) 0 = p := by simp [Equiv.Perm.decomposeFin]

@[simp]
/--
theorem `Equiv.Perm.decomposeFin_symm_apply_succ` / 定理 `Equiv.Perm.decomposeFin_symm_apply_succ`

English:
theorem Equiv.Perm.decomposeFin_symm_apply_succ
  statement: {n : Nat} (e : Perm (Fin n)) (p : Fin (n + 1))
  proof: by
  refine Fin.cases ?_ ?_ p
  · simp [Equiv.Perm.decomposeFin]
  · intro i
    by_cases h : i = e x
    · simp [h, Equiv.Perm.decomposeFin]
    · simp [Equiv.Perm.decomposeFin, swap_apply_def, Ne.symm h]

@[simp]

中文:
定理 等价.置换.decomposeFin_symm_apply_succ
  结论: {n : 自然数} (e : 置换 (有限集 n)) (p : 有限集 (n + 1))
  证明: by
  refine Fin.cases ?_ ?_ p
  · simp [Equiv.Perm.decomposeFin]
  · intro i
    by_cases h : i = e x
    · simp [h, Equiv.Perm.decomposeFin]
    · simp [Equiv.Perm.decomposeFin, swap_apply_def, Ne.symm h]

@[simp]

Depends on / 依赖: Equiv.Perm.decomposeFin, Fin.cases, Ne.symm, decomposeFin, swap_apply_def
-/
theorem Equiv.Perm.decomposeFin_symm_apply_succ {n : Nat} (e : Perm (Fin n)) (p : Fin (n + 1))
    (x : Fin n) : Equiv.Perm.decomposeFin.symm (p, e) x.succ = swap 0 p (e x).succ := by
  refine Fin.cases ?_ ?_ p
  · simp [Equiv.Perm.decomposeFin]
  · intro i
    by_cases h : i = e x
    · simp [h, Equiv.Perm.decomposeFin]
    · simp [Equiv.Perm.decomposeFin, swap_apply_def, Ne.symm h]

@[simp]
/--
theorem `Equiv.Perm.decomposeFin_symm_apply_one` / 定理 `Equiv.Perm.decomposeFin_symm_apply_one`

English:
theorem Equiv.Perm.decomposeFin_symm_apply_one
  given: {n : Nat} (e : Perm (Fin (n + 1))) (p : Fin (n + 2))
  proof: by
  rw [← Fin.succ_zero_eq_one]; rw [Equiv.Perm.decomposeFin_symm_apply_succ e p 0]

@[simp]

中文:
定理 等价.置换.decomposeFin_symm_apply_one
  条件: {n : 自然数} (e : 置换 (有限集 (n + 1))) (p : 有限集 (n + 2))
  证明: by
  rw [← Fin.succ_zero_eq_one]; rw [Equiv.Perm.decomposeFin_symm_apply_succ e p 0]

@[simp]

Depends on / 依赖: Equiv.Perm.decomposeFin_symm_apply_succ, Fin.succ_zero_eq_one, decomposeFin_symm_apply_succ, succ_zero_eq_one
-/
theorem Equiv.Perm.decomposeFin_symm_apply_one {n : Nat} (e : Perm (Fin (n + 1))) (p : Fin (n + 2)) :
    Equiv.Perm.decomposeFin.symm (p, e) 1 = swap 0 p (e 0).succ := by
  rw [← Fin.succ_zero_eq_one]; rw [Equiv.Perm.decomposeFin_symm_apply_succ e p 0]

@[simp]
/--
theorem `Equiv.Perm.decomposeFin.symm_sign` / 定理 `Equiv.Perm.decomposeFin.symm_sign`

English:
theorem Equiv.Perm.decomposeFin.symm_sign
  given: {n : Nat} (p : Fin (n + 1)) (e : Perm (Fin n))
  proof: by
  refine Fin.cases ?_ ?_ p <;> simp [Equiv.Perm.decomposeFin]

中文:
定理 等价.置换.decomposeFin.symm_sign
  条件: {n : 自然数} (p : 有限集 (n + 1)) (e : 置换 (有限集 n))
  证明: by
  refine Fin.cases ?_ ?_ p <;> simp [Equiv.Perm.decomposeFin]

Depends on / 依赖: Equiv.Perm.decomposeFin, Fin.cases, decomposeFin
-/
theorem Equiv.Perm.decomposeFin.symm_sign {n : Nat} (p : Fin (n + 1)) (e : Perm (Fin n)) :
    Perm.sign (Equiv.Perm.decomposeFin.symm (p, e)) = ite (p = 0) 1 (-1) * Perm.sign e := by
  refine Fin.cases ?_ ?_ p <;> simp [Equiv.Perm.decomposeFin]

/--
theorem `Finset.univ_perm_fin_succ` / 定理 `Finset.univ_perm_fin_succ`

English:
theorem Finset.univ_perm_fin_succ
  given: {n : Nat}
  proof: (Finset.univ_map_equiv_to_embedding _).symm

中文:
定理 有限集.univ_perm_fin_succ
  条件: {n : 自然数}
  证明: (Finset.univ_map_equiv_to_embedding _).symm

Depends on / 依赖: Finset, Finset.univ_map_equiv_to_embedding, univ_map_equiv_to_embedding
-/
theorem Finset.univ_perm_fin_succ {n : Nat} :
    @Finset.univ (Perm <| Fin n.succ) _ =
      (Finset.univ : Finset <| Fin n.succ × Perm (Fin n)).map
        Equiv.Perm.decomposeFin.symm.toEmbedding :=
  (Finset.univ_map_equiv_to_embedding _).symm

section CycleRange

/-! ### `cycleRange` section

Define the permutations `Fin.cycleRange i`, the cycle `(0 1 2 ... i)`.
-/


open Equiv.Perm

/--
theorem `finRotate_succ_eq_decomposeFin` / 定理 `finRotate_succ_eq_decomposeFin`

English:
theorem finRotate_succ_eq_decomposeFin
  given: {n : Nat}
  proof: by
  ext i
  cases n; · simp
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  rw [coe_finRotate]; rw [decomposeFin_symm_apply_succ]; rw [if_congr i.succ_eq_last_succ rfl rfl]
  split_ifs with h
  · simp [h]
  · rw [Fin.val_succ, Function.Injective.map_swap Fin.val_injective, Fin.val_succ, coe_finRotate,
      if_neg h, Fin.val_zero, Fin.val_one,
      swap_apply_of_ne_of_ne (Nat.succ_ne_zero _) (Nat.succ_succ_ne_one _)]

@[simp]

中文:
定理 finRotate_succ_eq_decomposeFin
  条件: {n : 自然数}
  证明: by
  ext i
  cases n; · simp
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  rw [coe_finRotate]; rw [decomposeFin_symm_apply_succ]; rw [if_congr i.succ_eq_last_succ rfl rfl]
  split_ifs with h
  · simp [h]
  · rw [Fin.val_succ, Function.Injective.map_swap Fin.val_injective, Fin.val_succ, coe_finRotate,
      if_neg h, Fin.val_zero, Fin.val_one,
      swap_apply_of_ne_of_ne (Nat.succ_ne_zero _) (Nat.succ_succ_ne_one _)]

@[simp]

Depends on / 依赖: Fin.cases, Fin.val_injective, Fin.val_one, Fin.val_succ, Fin.val_zero, Function, Function.Injective.map_swap, Injective, Nat.succ_ne_zero, Nat.succ_succ_ne_one, coe_finRotate, decomposeFin_symm_apply_succ, i.succ_eq_last_succ, if_congr, if_neg, map_swap, split_ifs, succ_eq_last_succ, succ_ne_zero, succ_succ_ne_one
-/
theorem finRotate_succ_eq_decomposeFin {n : Nat} :
    finRotate n.succ = decomposeFin.symm (1, finRotate n) := by
  ext i
  cases n; · simp
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  rw [coe_finRotate]; rw [decomposeFin_symm_apply_succ]; rw [if_congr i.succ_eq_last_succ rfl rfl]
  split_ifs with h
  · simp [h]
  · rw [Fin.val_succ, Function.Injective.map_swap Fin.val_injective, Fin.val_succ, coe_finRotate,
      if_neg h, Fin.val_zero, Fin.val_one,
      swap_apply_of_ne_of_ne (Nat.succ_ne_zero _) (Nat.succ_succ_ne_one _)]

@[simp]
/--
theorem `sign_finRotate` / 定理 `sign_finRotate`

English:
theorem sign_finRotate
  given: (n : Nat)
  statement: Perm.sign (finRotate n) = (-1) ^ (n - 1)
  proof: by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [finRotate_succ_eq_decomposeFin]
      simp [ih, pow_succ]

@[simp]

中文:
定理 sign_finRotate
  条件: (n : 自然数)
  结论: 置换.sign (finRotate n) = (-1) ^ (n - 1)
  证明: by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [finRotate_succ_eq_decomposeFin]
      simp [ih, pow_succ]

@[simp]

Depends on / 依赖: finRotate_succ_eq_decomposeFin, pow_succ
-/
theorem sign_finRotate (n : Nat) : Perm.sign (finRotate n) = (-1) ^ (n - 1) := by
  cases n with
  | zero => simp
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih =>
      rw [finRotate_succ_eq_decomposeFin]
      simp [ih, pow_succ]

@[simp]
/--
theorem `support_finRotate` / 定理 `support_finRotate`

English:
theorem support_finRotate
  given: {n : Nat}
  statement: support (finRotate (n + 2)) = Finset.univ
  proof: by
  ext
  simp

中文:
定理 support_finRotate
  条件: {n : 自然数}
  结论: support (finRotate (n + 2)) = 有限集.univ
  证明: by
  ext
  simp
-/
theorem support_finRotate {n : Nat} : support (finRotate (n + 2)) = Finset.univ := by
  ext
  simp

/--
theorem `support_finRotate_of_le` / 定理 `support_finRotate_of_le`

English:
theorem support_finRotate_of_le
  given: {n : Nat} (h : 2 <= n)
  statement: support (finRotate n) = Finset.univ
  proof: by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]; rw [support_finRotate]

中文:
定理 support_finRotate_of_le
  条件: {n : 自然数} (h : 2 <= n)
  结论: support (finRotate n) = 有限集.univ
  证明: by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]; rw [support_finRotate]

Depends on / 依赖: add_comm, exists_add_of_le, support_finRotate
-/
theorem support_finRotate_of_le {n : Nat} (h : 2 <= n) : support (finRotate n) = Finset.univ := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]; rw [support_finRotate]

/--
theorem `isCycle_finRotate` / 定理 `isCycle_finRotate`

English:
theorem isCycle_finRotate
  given: {n : Nat}
  statement: IsCycle (finRotate (n + 2))
  proof: by
  refine ⟨0, by simp, fun x hx' => ⟨x, ?_⟩⟩
  clear hx'
  obtain ⟨x, hx⟩ := x
  rw [zpow_natCast]; rw [Fin.ext_iff]; rw [Fin.val_mk]
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [pow_succ']; rw [Perm.mul_apply]; rw [coe_finRotate_of_ne_last]; rw [ih (lt_trans x.lt_succ_self hx)]
    rw [Ne]; rw [Fin.ext_iff]; rw [ih (lt_trans x.lt_succ_self hx)]; rw [Fin.val_last]
    exact ne_of_lt (Nat.lt_of_succ_lt_succ hx)

中文:
定理 isCycle_finRotate
  条件: {n : 自然数}
  结论: 是环 (finRotate (n + 2))
  证明: by
  refine ⟨0, by simp, fun x hx' => ⟨x, ?_⟩⟩
  clear hx'
  obtain ⟨x, hx⟩ := x
  rw [zpow_natCast]; rw [Fin.ext_iff]; rw [Fin.val_mk]
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [pow_succ']; rw [Perm.mul_apply]; rw [coe_finRotate_of_ne_last]; rw [ih (lt_trans x.lt_succ_self hx)]
    rw [Ne]; rw [Fin.ext_iff]; rw [ih (lt_trans x.lt_succ_self hx)]; rw [Fin.val_last]
    exact ne_of_lt (Nat.lt_of_succ_lt_succ hx)

Depends on / 依赖: Fin.ext_iff, Fin.val_last, Fin.val_mk, Nat.lt_of_succ_lt_succ, Perm.mul_apply, coe_finRotate_of_ne_last, ext_iff, lt_of_succ_lt_succ, lt_succ_self, lt_trans, mul_apply, ne_of_lt, pow_succ, val_last, val_mk, x.lt_succ_self, zpow_natCast
-/
theorem isCycle_finRotate {n : Nat} : IsCycle (finRotate (n + 2)) := by
  refine ⟨0, by simp, fun x hx' => ⟨x, ?_⟩⟩
  clear hx'
  obtain ⟨x, hx⟩ := x
  rw [zpow_natCast]; rw [Fin.ext_iff]; rw [Fin.val_mk]
  induction x with
  | zero => rfl
  | succ x ih =>
    rw [pow_succ']; rw [Perm.mul_apply]; rw [coe_finRotate_of_ne_last]; rw [ih (lt_trans x.lt_succ_self hx)]
    rw [Ne]; rw [Fin.ext_iff]; rw [ih (lt_trans x.lt_succ_self hx)]; rw [Fin.val_last]
    exact ne_of_lt (Nat.lt_of_succ_lt_succ hx)

/--
theorem `isCycle_finRotate_of_le` / 定理 `isCycle_finRotate_of_le`

English:
theorem isCycle_finRotate_of_le
  given: {n : Nat} (h : 2 <= n)
  statement: IsCycle (finRotate n)
  proof: by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]
  exact isCycle_finRotate

@[simp]

中文:
定理 isCycle_finRotate_of_le
  条件: {n : 自然数} (h : 2 <= n)
  结论: 是环 (finRotate n)
  证明: by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]
  exact isCycle_finRotate

@[simp]

Depends on / 依赖: add_comm, exists_add_of_le, isCycle_finRotate
-/
theorem isCycle_finRotate_of_le {n : Nat} (h : 2 <= n) : IsCycle (finRotate n) := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]
  exact isCycle_finRotate

@[simp]
/--
theorem `cycleType_finRotate` / 定理 `cycleType_finRotate`

English:
theorem cycleType_finRotate
  given: {n : Nat}
  statement: cycleType (finRotate (n + 2)) = {n + 2}
  proof: by
  rw [isCycle_finRotate.cycleType]; rw [support_finRotate]; rw [← Fintype.card]; rw [Fintype.card_fin]

中文:
定理 cycleType_finRotate
  条件: {n : 自然数}
  结论: cycleType (finRotate (n + 2)) = {n + 2}
  证明: by
  rw [isCycle_finRotate.cycleType]; rw [support_finRotate]; rw [← Fintype.card]; rw [Fintype.card_fin]

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_fin, card_fin, cycleType, isCycle_finRotate, isCycle_finRotate.cycleType, support_finRotate
-/
theorem cycleType_finRotate {n : Nat} : cycleType (finRotate (n + 2)) = {n + 2} := by
  rw [isCycle_finRotate.cycleType]; rw [support_finRotate]; rw [← Fintype.card]; rw [Fintype.card_fin]

/--
theorem `cycleType_finRotate_of_le` / 定理 `cycleType_finRotate_of_le`

English:
theorem cycleType_finRotate_of_le
  given: {n : Nat} (h : 2 <= n)
  statement: cycleType (finRotate n) = {n}
  proof: by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]; rw [cycleType_finRotate]

中文:
定理 cycleType_finRotate_of_le
  条件: {n : 自然数} (h : 2 <= n)
  结论: cycleType (finRotate n) = {n}
  证明: by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]; rw [cycleType_finRotate]

Depends on / 依赖: add_comm, cycleType_finRotate, exists_add_of_le
-/
theorem cycleType_finRotate_of_le {n : Nat} (h : 2 <= n) : cycleType (finRotate n) = {n} := by
  obtain ⟨m, rfl⟩ := exists_add_of_le h
  rw [add_comm]; rw [cycleType_finRotate]

namespace Fin

variable {n : Nat} {i j : Fin n}

/--
Definition of `cycleRange` / `cycleRange` 的定义

English:
definition cycleRange
  signature: {n : Nat} (i : Fin n)
  body: (finRotate (i + 1)).extendDomain (castLEEmb (by lia)).toEquivRange

中文:
定义 cycleRange
  签名: {n : 自然数} (i : 有限集 n)
  定义体: (finRotate (i + 1)).extendDomain (castLEEmb (by lia)).toEquivRange

Depends on / 依赖: castLEEmb, extendDomain, finRotate, toEquivRange
-/
def cycleRange {n : Nat} (i : Fin n) : Perm (Fin n) :=
  (finRotate (i + 1)).extendDomain (castLEEmb (by lia)).toEquivRange

/--
theorem `cycleRange_of_gt` / 定理 `cycleRange_of_gt`

English:
theorem cycleRange_of_gt
  given: (h : i < j)
  statement: cycleRange i j = j
  proof: by
  rw [cycleRange]; rw [Perm.extendDomain_apply_not_subtype]
  simpa using h

中文:
定理 cycleRange_of_gt
  条件: (h : i < j)
  结论: cycleRange i j = j
  证明: by
  rw [cycleRange]; rw [Perm.extendDomain_apply_not_subtype]
  simpa using h

Depends on / 依赖: Perm.extendDomain_apply_not_subtype, cycleRange, extendDomain_apply_not_subtype
-/
theorem cycleRange_of_gt (h : i < j) : cycleRange i j = j := by
  rw [cycleRange]; rw [Perm.extendDomain_apply_not_subtype]
  simpa using h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cycleRange_of_le` / 定理 `cycleRange_of_le`

English:
theorem cycleRange_of_le
  given: [NeZero n] (h : i <= j)
  proof: by
  have iin : i in Set.range (castLEEmb (n := j + 1) (by lia)) := by
    simp; lia
  have : (castLEEmb (by lia)).toEquivRange (castLT i (by lia)) = ⟨i, iin⟩ := by
    simp [coe_castLEEmb]; rfl
  rw [cycleRange]; rw [(finRotate (j + 1)).extendDomain_apply_subtype (castLEEmb (by lia)).toEquivRange iin]; rw [Function.Embedding.toEquivRange_apply]
  split_ifs with ch
  · have : ((castLEEmb (by lia)).toEquivRange.symm ⟨i, iin⟩) = last j := by
      simpa only [coe_castLEEmb, ← this, symm_apply_apply] using eq_of_val_eq (by simp [ch])
    rw [this]; rw [finRotate_last]
    rfl
  · have hj1 : (i + 1).1 = i.1 + 1 := val_add_one_of_lt' (by lia)
    have hj2 : (i.castLT (by lia) + 1 : Fin (j + 1)).1 =
      (i.castLT (by lia) : Fin (j + 1)) + 1 := val_add_one_of_lt' (by simp; lia)
    exact eq_of_val_eq (by simp [← this, hj1, hj2])

中文:
定理 cycleRange_of_le
  条件: [NeZero n] (h : i <= j)
  证明: by
  have iin : i in Set.range (castLEEmb (n := j + 1) (by lia)) := by
    simp; lia
  have : (castLEEmb (by lia)).toEquivRange (castLT i (by lia)) = ⟨i, iin⟩ := by
    simp [coe_castLEEmb]; rfl
  rw [cycleRange]; rw [(finRotate (j + 1)).extendDomain_apply_subtype (castLEEmb (by lia)).toEquivRange iin]; rw [Function.Embedding.toEquivRange_apply]
  split_ifs with ch
  · have : ((castLEEmb (by lia)).toEquivRange.symm ⟨i, iin⟩) = last j := by
      simpa only [coe_castLEEmb, ← this, symm_apply_apply] using eq_of_val_eq (by simp [ch])
    rw [this]; rw [finRotate_last]
    rfl
  · have hj1 : (i + 1).1 = i.1 + 1 := val_add_one_of_lt' (by lia)
    have hj2 : (i.castLT (by lia) + 1 : Fin (j + 1)).1 =
      (i.castLT (by lia) : Fin (j + 1)) + 1 := val_add_one_of_lt' (by simp; lia)
    exact eq_of_val_eq (by simp [← this, hj1, hj2])

Depends on / 依赖: Embedding, Function, Function.Embedding.toEquivRange_apply, Set.range, castLEEmb, castLT, coe_castLEEmb, cycleRange, eq_of_val_eq, extendDomain_apply_subtype, finRotate, split_ifs, symm_apply_apply, toEquivRange, toEquivRange.symm, toEquivRange_apply
-/
theorem cycleRange_of_le [NeZero n] (h : i <= j) :
    cycleRange j i = if i = j then 0 else i + 1 := by
  have iin : i in Set.range (castLEEmb (n := j + 1) (by lia)) := by
    simp; lia
  have : (castLEEmb (by lia)).toEquivRange (castLT i (by lia)) = ⟨i, iin⟩ := by
    simp [coe_castLEEmb]; rfl
  rw [cycleRange]; rw [(finRotate (j + 1)).extendDomain_apply_subtype (castLEEmb (by lia)).toEquivRange iin]; rw [Function.Embedding.toEquivRange_apply]
  split_ifs with ch
  · have : ((castLEEmb (by lia)).toEquivRange.symm ⟨i, iin⟩) = last j := by
      simpa only [coe_castLEEmb, ← this, symm_apply_apply] using eq_of_val_eq (by simp [ch])
    rw [this]; rw [finRotate_last]
    rfl
  · have hj1 : (i + 1).1 = i.1 + 1 := val_add_one_of_lt' (by lia)
    have hj2 : (i.castLT (by lia) + 1 : Fin (j + 1)).1 =
      (i.castLT (by lia) : Fin (j + 1)) + 1 := val_add_one_of_lt' (by simp; lia)
    exact eq_of_val_eq (by simp [← this, hj1, hj2])

/--
theorem `coe_cycleRange_of_le` / 定理 `coe_cycleRange_of_le`

English:
theorem coe_cycleRange_of_le
  given: (h : i <= j)
  proof: by
  rcases n with - | n
  · exact absurd le_rfl j.pos.not_ge
  rw [cycleRange_of_le h]
  split_ifs with h'
  · rfl
  exact
    val_add_one_of_lt
      (calc
        (i : Nat) < j := Fin.lt_def.mp (lt_of_le_of_ne h h')
        _ <= n := Nat.lt_succ_iff.mp j.2)

中文:
定理 coe_cycleRange_of_le
  条件: (h : i <= j)
  证明: by
  rcases n with - | n
  · exact absurd le_rfl j.pos.not_ge
  rw [cycleRange_of_le h]
  split_ifs with h'
  · rfl
  exact
    val_add_one_of_lt
      (calc
        (i : Nat) < j := Fin.lt_def.mp (lt_of_le_of_ne h h')
        _ <= n := Nat.lt_succ_iff.mp j.2)

Depends on / 依赖: Fin.lt_def.mp, Nat.lt_succ_iff.mp, absurd, cycleRange_of_le, j.pos.not_ge, le_rfl, lt_def, lt_of_le_of_ne, lt_succ_iff, not_ge, split_ifs, val_add_one_of_lt
-/
theorem coe_cycleRange_of_le (h : i <= j) :
    (cycleRange j i : Nat) = if i = j then 0 else (i : Nat) + 1 := by
  rcases n with - | n
  · exact absurd le_rfl j.pos.not_ge
  rw [cycleRange_of_le h]
  split_ifs with h'
  · rfl
  exact
    val_add_one_of_lt
      (calc
        (i : Nat) < j := Fin.lt_def.mp (lt_of_le_of_ne h h')
        _ <= n := Nat.lt_succ_iff.mp j.2)

/--
theorem `cycleRange_of_lt` / 定理 `cycleRange_of_lt`

English:
theorem cycleRange_of_lt
  given: [NeZero n] (h : i < j)
  statement: cycleRange j i = i + 1
  proof: by
  rw [cycleRange_of_le h.le]; rw [if_neg h.ne]

中文:
定理 cycleRange_of_lt
  条件: [NeZero n] (h : i < j)
  结论: cycleRange j i = i + 1
  证明: by
  rw [cycleRange_of_le h.le]; rw [if_neg h.ne]

Depends on / 依赖: cycleRange_of_le, h.le, h.ne, if_neg
-/
theorem cycleRange_of_lt [NeZero n] (h : i < j) : cycleRange j i = i + 1 := by
  rw [cycleRange_of_le h.le]; rw [if_neg h.ne]

/--
theorem `coe_cycleRange_of_lt` / 定理 `coe_cycleRange_of_lt`

English:
theorem coe_cycleRange_of_lt
  given: (h : i < j)
  statement: (cycleRange j i : Nat) = i + 1
  proof: by
  rw [coe_cycleRange_of_le h.le]; rw [if_neg h.ne]

中文:
定理 coe_cycleRange_of_lt
  条件: (h : i < j)
  结论: (cycleRange j i : 自然数) = i + 1
  证明: by
  rw [coe_cycleRange_of_le h.le]; rw [if_neg h.ne]

Depends on / 依赖: coe_cycleRange_of_le, h.le, h.ne, if_neg
-/
theorem coe_cycleRange_of_lt (h : i < j) : (cycleRange j i : Nat) = i + 1 := by
  rw [coe_cycleRange_of_le h.le]; rw [if_neg h.ne]

/--
theorem `cycleRange_of_eq` / 定理 `cycleRange_of_eq`

English:
theorem cycleRange_of_eq
  given: [NeZero n] (h : i = j)
  statement: cycleRange j i = 0
  proof: by
  rw [cycleRange_of_le h.le]; rw [if_pos h]

@[simp]

中文:
定理 cycleRange_of_eq
  条件: [NeZero n] (h : i = j)
  结论: cycleRange j i = 0
  证明: by
  rw [cycleRange_of_le h.le]; rw [if_pos h]

@[simp]

Depends on / 依赖: cycleRange_of_le, h.le, if_pos
-/
theorem cycleRange_of_eq [NeZero n] (h : i = j) : cycleRange j i = 0 := by
  rw [cycleRange_of_le h.le]; rw [if_pos h]

@[simp]
/--
theorem `cycleRange_self` / 定理 `cycleRange_self`

English:
theorem cycleRange_self
  given: [NeZero n] (i : Fin n)
  statement: cycleRange i i = 0
  proof: cycleRange_of_eq rfl

中文:
定理 cycleRange_self
  条件: [NeZero n] (i : 有限集 n)
  结论: cycleRange i i = 0
  证明: cycleRange_of_eq rfl

Depends on / 依赖: cycleRange_of_eq
-/
theorem cycleRange_self [NeZero n] (i : Fin n) : cycleRange i i = 0 :=
  cycleRange_of_eq rfl

/--
theorem `cycleRange_apply` / 定理 `cycleRange_apply`

English:
theorem cycleRange_apply
  given: [NeZero n] (i j : Fin n)
  proof: by
  split_ifs with h₁ h₂
  · exact cycleRange_of_lt h₁
  · exact cycleRange_of_eq h₂
  · exact cycleRange_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm h₂))

@[simp]

中文:
定理 cycleRange_apply
  条件: [NeZero n] (i j : 有限集 n)
  证明: by
  split_ifs with h₁ h₂
  · exact cycleRange_of_lt h₁
  · exact cycleRange_of_eq h₂
  · exact cycleRange_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm h₂))

@[simp]

Depends on / 依赖: Ne.symm, cycleRange_of_eq, cycleRange_of_gt, cycleRange_of_lt, le_of_not_gt, lt_of_le_of_ne, split_ifs
-/
theorem cycleRange_apply [NeZero n] (i j : Fin n) :
    cycleRange i j = if j < i then j + 1 else if j = i then 0 else j := by
  split_ifs with h₁ h₂
  · exact cycleRange_of_lt h₁
  · exact cycleRange_of_eq h₂
  · exact cycleRange_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (Ne.symm h₂))

@[simp]
/--
theorem `cycleRange_zero` / 定理 `cycleRange_zero`

English:
theorem cycleRange_zero
  given: (n : Nat) [NeZero n]
  statement: cycleRange (0 : Fin n) = 1
  proof: by
  ext j
  rcases (Fin.zero_le j).eq_or_lt with rfl | hj
  · simp
  · rw [cycleRange_of_gt hj, one_apply]

@[simp]

中文:
定理 cycleRange_zero
  条件: (n : 自然数) [NeZero n]
  结论: cycleRange (0 : 有限集 n) = 1
  证明: by
  ext j
  rcases (Fin.zero_le j).eq_or_lt with rfl | hj
  · simp
  · rw [cycleRange_of_gt hj, one_apply]

@[simp]

Depends on / 依赖: Fin.zero_le, cycleRange_of_gt, eq_or_lt, one_apply, zero_le
-/
theorem cycleRange_zero (n : Nat) [NeZero n] : cycleRange (0 : Fin n) = 1 := by
  ext j
  rcases (Fin.zero_le j).eq_or_lt with rfl | hj
  · simp
  · rw [cycleRange_of_gt hj, one_apply]

@[simp]
/--
theorem `cycleRange_last` / 定理 `cycleRange_last`

English:
theorem cycleRange_last
  given: (n : Nat)
  statement: cycleRange (last n) = finRotate (n + 1)
  proof: by
  ext i
  rw [coe_cycleRange_of_le (le_last _)]; rw [coe_finRotate]

@[simp]

中文:
定理 cycleRange_last
  条件: (n : 自然数)
  结论: cycleRange (last n) = finRotate (n + 1)
  证明: by
  ext i
  rw [coe_cycleRange_of_le (le_last _)]; rw [coe_finRotate]

@[simp]

Depends on / 依赖: coe_cycleRange_of_le, coe_finRotate, le_last
-/
theorem cycleRange_last (n : Nat) : cycleRange (last n) = finRotate (n + 1) := by
  ext i
  rw [coe_cycleRange_of_le (le_last _)]; rw [coe_finRotate]

@[simp]
/--
theorem `cycleRange_mk_zero` / 定理 `cycleRange_mk_zero`

English:
theorem cycleRange_mk_zero
  given: (h : 0 < n)
  statement: cycleRange ⟨0, h⟩ = 1
  proof: have : NeZero n := .of_pos h
  cycleRange_zero n

中文:
定理 cycleRange_mk_zero
  条件: (h : 0 < n)
  结论: cycleRange ⟨0, h⟩ = 1
  证明: have : NeZero n := .of_pos h
  cycleRange_zero n

Depends on / 依赖: NeZero, cycleRange_zero, of_pos
-/
theorem cycleRange_mk_zero (h : 0 < n) : cycleRange ⟨0, h⟩ = 1 :=
  have : NeZero n := .of_pos h
  cycleRange_zero n

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `sign_cycleRange` / 定理 `sign_cycleRange`

English:
theorem sign_cycleRange
  given: (i : Fin n)
  statement: Perm.sign (cycleRange i) = (-1) ^ (i : Nat)
  proof: by
  simp [cycleRange]

@[simp]

中文:
定理 sign_cycleRange
  条件: (i : 有限集 n)
  结论: 置换.sign (cycleRange i) = (-1) ^ (i : 自然数)
  证明: by
  simp [cycleRange]

@[simp]

Depends on / 依赖: cycleRange
-/
theorem sign_cycleRange (i : Fin n) : Perm.sign (cycleRange i) = (-1) ^ (i : Nat) := by
  simp [cycleRange]

@[simp]
/--
theorem `succAbove_cycleRange` / 定理 `succAbove_cycleRange`

English:
theorem succAbove_cycleRange
  given: (i j : Fin n)
  proof: by
  cases n
  · rcases j with ⟨_, ⟨⟩⟩
  rcases lt_trichotomy j i with (hlt | heq | hgt)
  · have : castSucc (j + 1) = j.succ := by
      ext
      rw [val_castSucc]; rw [val_succ]; rw [Fin.val_add_one_of_lt (lt_of_lt_of_le hlt i.le_last)]
    rw [Fin.cycleRange_of_lt hlt]; rw [Fin.succAbove_of_castSucc_lt]; rw [this]; rw [swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · exact (Fin.succ_injective _).ne hlt.ne
    · rw [Fin.lt_def]
      simpa [this] using hlt
  · rw [heq, Fin.cycleRange_self, Fin.succAbove_of_castSucc_lt, swap_apply_right, Fin.castSucc_zero]
    · rw [Fin.castSucc_zero]
      apply Fin.succ_pos
  · rw [Fin.cycleRange_of_gt hgt, Fin.succAbove_of_le_castSucc, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · apply (Fin.succ_injective _).ne hgt.ne.symm
    · simpa [Fin.le_iff_val_le_val] using hgt

@[simp]

中文:
定理 succAbove_cycleRange
  条件: (i j : 有限集 n)
  证明: by
  cases n
  · rcases j with ⟨_, ⟨⟩⟩
  rcases lt_trichotomy j i with (hlt | heq | hgt)
  · have : castSucc (j + 1) = j.succ := by
      ext
      rw [val_castSucc]; rw [val_succ]; rw [Fin.val_add_one_of_lt (lt_of_lt_of_le hlt i.le_last)]
    rw [Fin.cycleRange_of_lt hlt]; rw [Fin.succAbove_of_castSucc_lt]; rw [this]; rw [swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · exact (Fin.succ_injective _).ne hlt.ne
    · rw [Fin.lt_def]
      simpa [this] using hlt
  · rw [heq, Fin.cycleRange_self, Fin.succAbove_of_castSucc_lt, swap_apply_right, Fin.castSucc_zero]
    · rw [Fin.castSucc_zero]
      apply Fin.succ_pos
  · rw [Fin.cycleRange_of_gt hgt, Fin.succAbove_of_le_castSucc, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · apply (Fin.succ_injective _).ne hgt.ne.symm
    · simpa [Fin.le_iff_val_le_val] using hgt

@[simp]

Depends on / 依赖: Fin.cycleRange_of_lt, Fin.cycleRange_self, Fin.lt_def, Fin.succAbove_of_castSucc_lt, Fin.succ_injective, Fin.succ_ne_zero, Fin.val_add_one_of_lt, castSucc, cycleRange_of_lt, cycleRange_self, hlt.ne, i.le_last, j.succ, le_last, lt_def, lt_of_lt_of_le, lt_trichotomy, succAbove_of_castSucc_lt, succ_injective, succ_ne_zero
-/
theorem succAbove_cycleRange (i j : Fin n) :
    i.succ.succAbove (i.cycleRange j) = swap 0 i.succ j.succ := by
  cases n
  · rcases j with ⟨_, ⟨⟩⟩
  rcases lt_trichotomy j i with (hlt | heq | hgt)
  · have : castSucc (j + 1) = j.succ := by
      ext
      rw [val_castSucc]; rw [val_succ]; rw [Fin.val_add_one_of_lt (lt_of_lt_of_le hlt i.le_last)]
    rw [Fin.cycleRange_of_lt hlt]; rw [Fin.succAbove_of_castSucc_lt]; rw [this]; rw [swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · exact (Fin.succ_injective _).ne hlt.ne
    · rw [Fin.lt_def]
      simpa [this] using hlt
  · rw [heq, Fin.cycleRange_self, Fin.succAbove_of_castSucc_lt, swap_apply_right, Fin.castSucc_zero]
    · rw [Fin.castSucc_zero]
      apply Fin.succ_pos
  · rw [Fin.cycleRange_of_gt hgt, Fin.succAbove_of_le_castSucc, swap_apply_of_ne_of_ne]
    · apply Fin.succ_ne_zero
    · apply (Fin.succ_injective _).ne hgt.ne.symm
    · simpa [Fin.le_iff_val_le_val] using hgt

@[simp]
/--
theorem `cycleRange_succAbove` / 定理 `cycleRange_succAbove`

English:
theorem cycleRange_succAbove
  given: (i : Fin (n + 1)) (j : Fin n)
  proof: by
  rcases lt_or_ge (castSucc j) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.cycleRange_of_lt h, Fin.coeSucc_eq_succ]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.cycleRange_of_gt (Fin.le_castSucc_iff.mp h)]

@[simp]

中文:
定理 cycleRange_succAbove
  条件: (i : 有限集 (n + 1)) (j : 有限集 n)
  证明: by
  rcases lt_or_ge (castSucc j) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.cycleRange_of_lt h, Fin.coeSucc_eq_succ]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.cycleRange_of_gt (Fin.le_castSucc_iff.mp h)]

@[simp]

Depends on / 依赖: Fin.coeSucc_eq_succ, Fin.cycleRange_of_gt, Fin.cycleRange_of_lt, Fin.le_castSucc_iff.mp, Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc, castSucc, coeSucc_eq_succ, cycleRange_of_gt, cycleRange_of_lt, le_castSucc_iff, lt_or_ge, succAbove_of_castSucc_lt, succAbove_of_le_castSucc
-/
theorem cycleRange_succAbove (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange (i.succAbove j) = j.succ := by
  rcases lt_or_ge (castSucc j) i with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.cycleRange_of_lt h, Fin.coeSucc_eq_succ]
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.cycleRange_of_gt (Fin.le_castSucc_iff.mp h)]

@[simp]
/--
theorem `cycleRange_symm_zero` / 定理 `cycleRange_symm_zero`

English:
theorem cycleRange_symm_zero
  given: [NeZero n] (i : Fin n)
  statement: i.cycleRange.symm 0 = i
  proof: i.cycleRange.injective (by simp)

@[simp]

中文:
定理 cycleRange_symm_zero
  条件: [NeZero n] (i : 有限集 n)
  结论: i.cycleRange.symm 0 = i
  证明: i.cycleRange.injective (by simp)

@[simp]

Depends on / 依赖: cycleRange, i.cycleRange.injective, injective
-/
theorem cycleRange_symm_zero [NeZero n] (i : Fin n) : i.cycleRange.symm 0 = i :=
  i.cycleRange.injective (by simp)

@[simp]
/--
theorem `cycleRange_symm_succ` / 定理 `cycleRange_symm_succ`

English:
theorem cycleRange_symm_succ
  given: (i : Fin (n + 1)) (j : Fin n)
  proof: i.cycleRange.injective (by simp)

@[simp]

中文:
定理 cycleRange_symm_succ
  条件: (i : 有限集 (n + 1)) (j : 有限集 n)
  证明: i.cycleRange.injective (by simp)

@[simp]

Depends on / 依赖: cycleRange, i.cycleRange.injective, injective
-/
theorem cycleRange_symm_succ (i : Fin (n + 1)) (j : Fin n) :
    i.cycleRange.symm j.succ = i.succAbove j :=
  i.cycleRange.injective (by simp)

@[simp]
/--
theorem `insertNth_apply_cycleRange_symm` / 定理 `insertNth_apply_cycleRange_symm`

English:
theorem insertNth_apply_cycleRange_symm
  statement: {α : Type*} (p : Fin (n + 1)) (a : α) (x : Fin n -> α)
  proof: by
  cases j using Fin.cases <;> simp

@[simp]

中文:
定理 insertNth_apply_cycleRange_symm
  结论: {α : 类型} (p : 有限集 (n + 1)) (a : α) (x : 有限集 n -> α)
  证明: by
  cases j using Fin.cases <;> simp

@[simp]

Depends on / 依赖: Fin.cases
-/
theorem insertNth_apply_cycleRange_symm {α : Type*} (p : Fin (n + 1)) (a : α) (x : Fin n -> α)
    (j : Fin (n + 1)) :
    (p.insertNth a x : _ -> α) (p.cycleRange.symm j) = (Fin.cons a x : _ -> α) j := by
  cases j using Fin.cases <;> simp

@[simp]
/--
theorem `insertNth_comp_cycleRange_symm` / 定理 `insertNth_comp_cycleRange_symm`

English:
theorem insertNth_comp_cycleRange_symm
  given: {α : Type*} (p : Fin (n + 1)) (a : α) (x : Fin n -> α)
  proof: by
  ext j
  simp

中文:
定理 insertNth_comp_cycleRange_symm
  条件: {α : 类型} (p : 有限集 (n + 1)) (a : α) (x : 有限集 n -> α)
  证明: by
  ext j
  simp
-/
theorem insertNth_comp_cycleRange_symm {α : Type*} (p : Fin (n + 1)) (a : α) (x : Fin n -> α) :
    (p.insertNth a x ∘ p.cycleRange.symm : _ -> α) = Fin.cons a x := by
  ext j
  simp

/--
theorem `cons_removeNth_eq_comp_cycleRange_symm` / 定理 `cons_removeNth_eq_comp_cycleRange_symm`

English:
theorem cons_removeNth_eq_comp_cycleRange_symm
  statement: {α : Type*}
  proof: by
  ext i
  cases i using Fin.cons <;> simp [Fin.removeNth_apply]

@[simp]

中文:
定理 cons_removeNth_eq_comp_cycleRange_symm
  结论: {α : 类型}
  证明: by
  ext i
  cases i using Fin.cons <;> simp [Fin.removeNth_apply]

@[simp]

Depends on / 依赖: Fin.cons, Fin.removeNth_apply, removeNth_apply
-/
theorem cons_removeNth_eq_comp_cycleRange_symm {α : Type*}
    (x : Fin (n + 1) -> α) (p : Fin (n + 1)) :
    Fin.cons (x p) (p.removeNth x) = x ∘ p.cycleRange.symm := by
  ext i
  cases i using Fin.cons <;> simp [Fin.removeNth_apply]

@[simp]
/--
theorem `cons_apply_cycleRange` / 定理 `cons_apply_cycleRange`

English:
theorem cons_apply_cycleRange
  given: {α : Type*} (a : α) (x : Fin n -> α) (p j : Fin (n + 1))
  proof: by
  rw [← insertNth_apply_cycleRange_symm]; rw [Equiv.symm_apply_apply]

@[simp]

中文:
定理 cons_apply_cycleRange
  条件: {α : 类型} (a : α) (x : 有限集 n -> α) (p j : 有限集 (n + 1))
  证明: by
  rw [← insertNth_apply_cycleRange_symm]; rw [Equiv.symm_apply_apply]

@[simp]

Depends on / 依赖: Equiv.symm_apply_apply, insertNth_apply_cycleRange_symm, symm_apply_apply
-/
theorem cons_apply_cycleRange {α : Type*} (a : α) (x : Fin n -> α) (p j : Fin (n + 1)) :
    (Fin.cons a x : _ -> α) (p.cycleRange j) = (p.insertNth a x : _ -> α) j := by
  rw [← insertNth_apply_cycleRange_symm]; rw [Equiv.symm_apply_apply]

@[simp]
/--
theorem `cons_comp_cycleRange` / 定理 `cons_comp_cycleRange`

English:
theorem cons_comp_cycleRange
  given: {α : Type*} (a : α) (x : Fin n -> α) (p : Fin (n + 1))
  proof: by
  ext; simp

中文:
定理 cons_comp_cycleRange
  条件: {α : 类型} (a : α) (x : 有限集 n -> α) (p : 有限集 (n + 1))
  证明: by
  ext; simp
-/
theorem cons_comp_cycleRange {α : Type*} (a : α) (x : Fin n -> α) (p : Fin (n + 1)) :
    (Fin.cons a x : _ -> α) ∘ p.cycleRange = p.insertNth a x := by
  ext; simp

/--
theorem `isCycle_cycleRange` / 定理 `isCycle_cycleRange`

English:
theorem isCycle_cycleRange
  given: [NeZero n] (h0 : i != 0)
  statement: IsCycle (cycleRange i)
  proof: by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  exact isCycle_finRotate.extendDomain _

中文:
定理 isCycle_cycleRange
  条件: [NeZero n] (h0 : i != 0)
  结论: 是环 (cycleRange i)
  证明: by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  exact isCycle_finRotate.extendDomain _

Depends on / 依赖: extendDomain, isCycle_finRotate, isCycle_finRotate.extendDomain
-/
theorem isCycle_cycleRange [NeZero n] (h0 : i != 0) : IsCycle (cycleRange i) := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  exact isCycle_finRotate.extendDomain _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cycleType_cycleRange` / 定理 `cycleType_cycleRange`

English:
theorem cycleType_cycleRange
  given: [NeZero n] (h0 : i != 0)
  proof: by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  simp [cycleRange]

中文:
定理 cycleType_cycleRange
  条件: [NeZero n] (h0 : i != 0)
  证明: by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  simp [cycleRange]

Depends on / 依赖: cycleRange
-/
theorem cycleType_cycleRange [NeZero n] (h0 : i != 0) :
    cycleType (cycleRange i) = {(i + 1 : Nat)} := by
  obtain ⟨i, hi⟩ := i
  cases i
  · exact (h0 rfl).elim
  simp [cycleRange]

/--
theorem `isThreeCycle_cycleRange_two` / 定理 `isThreeCycle_cycleRange_two`

English:
theorem isThreeCycle_cycleRange_two
  statement: IsThreeCycle (cycleRange 2 : Perm (Fin (n + 3)))
  proof: by
  rw [IsThreeCycle]; rw [cycleType_cycleRange two_ne_zero]
  simp

中文:
定理 isThreeCycle_cycleRange_two
  结论: IsThreeCycle (cycleRange 2 : 置换 (有限集 (n + 3)))
  证明: by
  rw [IsThreeCycle]; rw [cycleType_cycleRange two_ne_zero]
  simp

Depends on / 依赖: IsThreeCycle, cycleType_cycleRange, two_ne_zero
-/
theorem isThreeCycle_cycleRange_two : IsThreeCycle (cycleRange 2 : Perm (Fin (n + 3))) := by
  rw [IsThreeCycle]; rw [cycleType_cycleRange two_ne_zero]
  simp

end Fin

end CycleRange

section cycleIcc

/-! ### The permutation `cycleIcc`

In this section, we define the permutation `cycleIcc i j`, which is the cycle `(i i+1 .... j)`
leaving `(0 ... i-1)` and `(j+1 ... n-1)` unchanged when `i ≤ j` and returning the dummy value `id`
when `i > j`. In other words, it rotates elements in `[i, j]` one step to the right.
-/

namespace Fin

local instance {n : Nat} {i : Fin n} : NeZero (n - i) := NeZero.of_pos (by lia)

variable {n : Nat} {i j k : Fin n}

/-- `cycleIcc i j` is the cycle `(i i+1 ... j)` leaving `(0 ... i-1)` and `(j+1 ... n-1)`
unchanged when `i < j` and returning the dummy value `id` when `i > j`.
In other words, it rotates elements in `[i, j]` one step to the right.
-/
/--
Definition of `cycleIcc` / `cycleIcc` 的定义

English:
definition cycleIcc
  signature: (i j : Fin n)
  body: if hij : i <= j then (cycleRange ((j - i).castLT
  (sub_val_lt_sub hij))).extendDomain (natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange else 1

@[simp]

中文:
定义 cycleIcc
  签名: (i j : 有限集 n)
  定义体: if hij : i <= j then (cycleRange ((j - i).castLT
  (sub_val_lt_sub hij))).extendDomain (natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange else 1

@[simp]

Depends on / 依赖: castLT, cycleRange
-/
def cycleIcc (i j : Fin n) : Perm (Fin n) := if hij : i <= j then (cycleRange ((j - i).castLT
  (sub_val_lt_sub hij))).extendDomain (natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange else 1

@[simp]
/--
lemma `cycleIcc_def_le` / 引理 `cycleIcc_def_le`

English:
lemma cycleIcc_def_le
  given: {i j : Fin n} (hij : i <= j)
  statement: cycleIcc i j =
  proof: by simp [cycleIcc, hij]

@[simp]

中文:
引理 cycleIcc_def_le
  条件: {i j : 有限集 n} (hij : i <= j)
  结论: cycleIcc i j =
  证明: by simp [cycleIcc, hij]

@[simp]

Depends on / 依赖: cycleIcc
-/
lemma cycleIcc_def_le {i j : Fin n} (hij : i <= j) : cycleIcc i j =
    (cycleRange ((j - i).castLT (sub_val_lt_sub hij))).extendDomain
      (natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange := by simp [cycleIcc, hij]

@[simp]
/--
theorem `cycleIcc_def_gt` / 定理 `cycleIcc_def_gt`

English:
theorem cycleIcc_def_gt
  given: (hij : i < j)
  statement: cycleIcc j i = 1
  proof: by
  simp [cycleIcc, hij]

@[simp]

中文:
定理 cycleIcc_def_gt
  条件: (hij : i < j)
  结论: cycleIcc j i = 1
  证明: by
  simp [cycleIcc, hij]

@[simp]

Depends on / 依赖: cycleIcc
-/
theorem cycleIcc_def_gt (hij : i < j) : cycleIcc j i = 1 := by
  simp [cycleIcc, hij]

@[simp]
/--
theorem `cycleIcc_def_gt'` / 定理 `cycleIcc_def_gt'`

English:
theorem cycleIcc_def_gt'
  given: (hij : ¬ j <= i)
  statement: cycleIcc j i = 1
  proof: by
  simp [cycleIcc, hij]

中文:
定理 cycleIcc_def_gt'
  条件: (hij : ¬ j <= i)
  结论: cycleIcc j i = 1
  证明: by
  simp [cycleIcc, hij]

Depends on / 依赖: cycleIcc
-/
theorem cycleIcc_def_gt' (hij : ¬ j <= i) : cycleIcc j i = 1 := by
  simp [cycleIcc, hij]

/--
theorem `cycleIcc_of_lt` / 定理 `cycleIcc_of_lt`

English:
theorem cycleIcc_of_lt
  given: (h : k < i)
  statement: (cycleIcc i j) k = k
  proof: by
  by_cases hij : i <= j
  · simpa [hij] using Perm.extendDomain_apply_not_subtype _ _ (by
      simp [range_natAdd_castLEEmb]; lia)
  · simp [hij]

中文:
定理 cycleIcc_of_lt
  条件: (h : k < i)
  结论: (cycleIcc i j) k = k
  证明: by
  by_cases hij : i <= j
  · simpa [hij] using Perm.extendDomain_apply_not_subtype _ _ (by
      simp [range_natAdd_castLEEmb]; lia)
  · simp [hij]

Depends on / 依赖: Perm.extendDomain_apply_not_subtype, extendDomain_apply_not_subtype, range_natAdd_castLEEmb
-/
theorem cycleIcc_of_lt (h : k < i) : (cycleIcc i j) k = k := by
  by_cases hij : i <= j
  · simpa [hij] using Perm.extendDomain_apply_not_subtype _ _ (by
      simp [range_natAdd_castLEEmb]; lia)
  · simp [hij]

/--
lemma `cycleIcc_to_cycleRange` / 引理 `cycleIcc_to_cycleRange`

English:
lemma cycleIcc_to_cycleRange
  statement: (hij : i <= j)
  proof: by
  simp [hij, ((j - i).castLT (sub_val_lt_sub hij)).cycleRange.extendDomain_apply_subtype
    (natAdd_castLEEmb _).toEquivRange kin]

中文:
引理 cycleIcc_to_cycleRange
  结论: (hij : i <= j)
  证明: by
  simp [hij, ((j - i).castLT (sub_val_lt_sub hij)).cycleRange.extendDomain_apply_subtype
    (natAdd_castLEEmb _).toEquivRange kin]

Depends on / 依赖: castLT, cycleRange, cycleRange.extendDomain_apply_subtype, extendDomain_apply_subtype, natAdd_castLEEmb, sub_val_lt_sub, toEquivRange
-/
lemma cycleIcc_to_cycleRange (hij : i <= j)
    (kin : k in Set.range (natAdd_castLEEmb (Nat.sub_le n i))) : (cycleIcc i j) k =
    (natAdd_castLEEmb (Nat.sub_le n i)) (((j - i).castLT (sub_val_lt_sub hij)).cycleRange
    ((natAdd_castLEEmb (Nat.sub_le n i)).toEquivRange.symm ⟨k, kin⟩)) := by
  simp [hij, ((j - i).castLT (sub_val_lt_sub hij)).cycleRange.extendDomain_apply_subtype
    (natAdd_castLEEmb _).toEquivRange kin]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `cycleIcc_of_gt` / 定理 `cycleIcc_of_gt`

English:
theorem cycleIcc_of_gt
  given: (h : j < k)
  statement: (cycleIcc i j) k = k
  proof: by
  by_cases hij : i <= j
  · have kin : k in Set.range (natAdd_castLEEmb (Nat.sub_le n i)) := by
      simp [range_natAdd_castLEEmb]; lia
    have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat i.1 (k.cast (by lia)) (by simp; lia) := by
      simpa [symm_apply_eq] using eq_of_val_eq (by simp; lia)
    simp only [cycleIcc_to_cycleRange hij kin, natAdd_castLEEmb, this,
      Function.Embedding.trans_apply, addNatEmb_apply, coe_toEmbedding, finCongr_apply]
    rw [cycleRange_of_gt]
    · exact eq_of_val_eq (by simp; lia)
    · exact lt_def.mpr (by simp [sub_val_of_le hij]; lia)
  · simp [hij]

中文:
定理 cycleIcc_of_gt
  条件: (h : j < k)
  结论: (cycleIcc i j) k = k
  证明: by
  by_cases hij : i <= j
  · have kin : k in Set.range (natAdd_castLEEmb (Nat.sub_le n i)) := by
      simp [range_natAdd_castLEEmb]; lia
    have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat i.1 (k.cast (by lia)) (by simp; lia) := by
      simpa [symm_apply_eq] using eq_of_val_eq (by simp; lia)
    simp only [cycleIcc_to_cycleRange hij kin, natAdd_castLEEmb, this,
      Function.Embedding.trans_apply, addNatEmb_apply, coe_toEmbedding, finCongr_apply]
    rw [cycleRange_of_gt]
    · exact eq_of_val_eq (by simp; lia)
    · exact lt_def.mpr (by simp [sub_val_of_le hij]; lia)
  · simp [hij]

Depends on / 依赖: Embedding, Function, Function.Embedding.trans_apply, Nat.sub_le, Set.range, addNatEmb, addNatEmb_apply, coe_toEmbedding, cycleIcc_to_cycleRange, cycleRange_o, eq_of_val_eq, finCongr, finCongr_apply, k.cast, natAdd_castLEEmb, range_natAdd_castLEEmb, subNat, sub_le, symm_apply_eq, toEmbedding
-/
theorem cycleIcc_of_gt (h : j < k) : (cycleIcc i j) k = k := by
  by_cases hij : i <= j
  · have kin : k in Set.range (natAdd_castLEEmb (Nat.sub_le n i)) := by
      simp [range_natAdd_castLEEmb]; lia
    have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat i.1 (k.cast (by lia)) (by simp; lia) := by
      simpa [symm_apply_eq] using eq_of_val_eq (by simp; lia)
    simp only [cycleIcc_to_cycleRange hij kin, natAdd_castLEEmb, this,
      Function.Embedding.trans_apply, addNatEmb_apply, coe_toEmbedding, finCongr_apply]
    rw [cycleRange_of_gt]
    · exact eq_of_val_eq (by simp; lia)
    · exact lt_def.mpr (by simp [sub_val_of_le hij]; lia)
  · simp [hij]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `cycleIcc_of_le_of_le` / 定理 `cycleIcc_of_le_of_le`

English:
theorem cycleIcc_of_le_of_le
  given: (hik : i <= k) (hkj : k <= j) [NeZero n]
  proof: by
  have hij : i <= j := le_trans hik hkj
  have kin : k in Set.range (natAdd_castLEEmb (Nat.sub_le n i)) := by
    simp [range_natAdd_castLEEmb]; lia
  have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat i.1 (k.cast (by lia)) (by simp; lia) := by
    simpa [symm_apply_eq] using eq_of_val_eq (by simp; lia)
  simp only [cycleIcc_to_cycleRange hij kin, natAdd_castLEEmb, this, Function.Embedding.trans_apply,
    addNatEmb_apply, coe_toEmbedding, finCongr_apply]
  refine eq_of_val_eq ?_
  split_ifs with ch
  · have : subNat i.1 (j.cast (by lia)) (by simp [hij]) = (j - i).castLT (sub_val_lt_sub hij) :=
      eq_of_val_eq (by simp [sub_val_of_le hij])
    simp [ch, cycleRange_of_eq this]; lia
  · have : subNat i.1 (k.cast (by lia)) (by simp [hik]) < (j - i).castLT (sub_val_lt_sub hij) := by
      simp [lt_def, sub_val_of_le hij]; lia
    rw [cycleRange_of_lt this]; rw [subNat]
    simp only [val_cast, add_def, val_one', Nat.add_mod_mod, addNat_mk, cast_mk]
    rw [Nat.mod_eq_of_lt (by lia)]; rw [Nat.mod_eq_of_lt (by lia)]
    lia

中文:
定理 cycleIcc_of_le_of_le
  条件: (hik : i <= k) (hkj : k <= j) [NeZero n]
  证明: by
  have hij : i <= j := le_trans hik hkj
  have kin : k in Set.range (natAdd_castLEEmb (Nat.sub_le n i)) := by
    simp [range_natAdd_castLEEmb]; lia
  have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat i.1 (k.cast (by lia)) (by simp; lia) := by
    simpa [symm_apply_eq] using eq_of_val_eq (by simp; lia)
  simp only [cycleIcc_to_cycleRange hij kin, natAdd_castLEEmb, this, Function.Embedding.trans_apply,
    addNatEmb_apply, coe_toEmbedding, finCongr_apply]
  refine eq_of_val_eq ?_
  split_ifs with ch
  · have : subNat i.1 (j.cast (by lia)) (by simp [hij]) = (j - i).castLT (sub_val_lt_sub hij) :=
      eq_of_val_eq (by simp [sub_val_of_le hij])
    simp [ch, cycleRange_of_eq this]; lia
  · have : subNat i.1 (k.cast (by lia)) (by simp [hik]) < (j - i).castLT (sub_val_lt_sub hij) := by
      simp [lt_def, sub_val_of_le hij]; lia
    rw [cycleRange_of_lt this]; rw [subNat]
    simp only [val_cast, add_def, val_one', Nat.add_mod_mod, addNat_mk, cast_mk]
    rw [Nat.mod_eq_of_lt (by lia)]; rw [Nat.mod_eq_of_lt (by lia)]
    lia

Depends on / 依赖: Embedding, Function, Function.Embedding.trans_apply, Nat.sub_le, Set.range, addNatEmb, addNatEmb_apply, coe_toEmbedding, cycleIcc_to_cycleRange, eq_of_val_eq, finCongr, finCongr_apply, k.cast, le_trans, natAdd_castLEEmb, range_natAdd_castLEEmb, subNat, sub_le, symm_apply_eq, toEmbedding
-/
theorem cycleIcc_of_le_of_le (hik : i <= k) (hkj : k <= j) [NeZero n] :
    (cycleIcc i j) k = if k = j then i else k + 1 := by
  have hij : i <= j := le_trans hik hkj
  have kin : k in Set.range (natAdd_castLEEmb (Nat.sub_le n i)) := by
    simp [range_natAdd_castLEEmb]; lia
  have : (((addNatEmb (n - (n - i.1))).trans (finCongr _).toEmbedding).toEquivRange.symm ⟨k, kin⟩)
      = subNat i.1 (k.cast (by lia)) (by simp; lia) := by
    simpa [symm_apply_eq] using eq_of_val_eq (by simp; lia)
  simp only [cycleIcc_to_cycleRange hij kin, natAdd_castLEEmb, this, Function.Embedding.trans_apply,
    addNatEmb_apply, coe_toEmbedding, finCongr_apply]
  refine eq_of_val_eq ?_
  split_ifs with ch
  · have : subNat i.1 (j.cast (by lia)) (by simp [hij]) = (j - i).castLT (sub_val_lt_sub hij) :=
      eq_of_val_eq (by simp [sub_val_of_le hij])
    simp [ch, cycleRange_of_eq this]; lia
  · have : subNat i.1 (k.cast (by lia)) (by simp [hik]) < (j - i).castLT (sub_val_lt_sub hij) := by
      simp [lt_def, sub_val_of_le hij]; lia
    rw [cycleRange_of_lt this]; rw [subNat]
    simp only [val_cast, add_def, val_one', Nat.add_mod_mod, addNat_mk, cast_mk]
    rw [Nat.mod_eq_of_lt (by lia)]; rw [Nat.mod_eq_of_lt (by lia)]
    lia

/--
theorem `cycleIcc_of_ge_of_lt` / 定理 `cycleIcc_of_ge_of_lt`

English:
theorem cycleIcc_of_ge_of_lt
  given: (hik : i <= k) (hkj : k < j) [NeZero n]
  statement: (cycleIcc i j) k = k + 1
  proof: by
  simp [cycleIcc_of_le_of_le hik (le_of_lt hkj), Fin.ne_of_lt hkj]

中文:
定理 cycleIcc_of_ge_of_lt
  条件: (hik : i <= k) (hkj : k < j) [NeZero n]
  结论: (cycleIcc i j) k = k + 1
  证明: by
  simp [cycleIcc_of_le_of_le hik (le_of_lt hkj), Fin.ne_of_lt hkj]

Depends on / 依赖: Fin.ne_of_lt, cycleIcc_of_le_of_le, le_of_lt, ne_of_lt
-/
theorem cycleIcc_of_ge_of_lt (hik : i <= k) (hkj : k < j) [NeZero n] : (cycleIcc i j) k = k + 1 := by
  simp [cycleIcc_of_le_of_le hik (le_of_lt hkj), Fin.ne_of_lt hkj]

/--
theorem `cycleIcc_of_last` / 定理 `cycleIcc_of_last`

English:
theorem cycleIcc_of_last
  given: (hij : i <= j) [NeZero n]
  statement: (cycleIcc i j) j = i
  proof: by
  simp [cycleIcc_of_le_of_le hij (ge_of_eq rfl)]

中文:
定理 cycleIcc_of_last
  条件: (hij : i <= j) [NeZero n]
  结论: (cycleIcc i j) j = i
  证明: by
  simp [cycleIcc_of_le_of_le hij (ge_of_eq rfl)]

Depends on / 依赖: cycleIcc_of_le_of_le, ge_of_eq
-/
theorem cycleIcc_of_last (hij : i <= j) [NeZero n] : (cycleIcc i j) j = i := by
  simp [cycleIcc_of_le_of_le hij (ge_of_eq rfl)]

/--
theorem `cycleIcc_eq` / 定理 `cycleIcc_eq`

English:
theorem cycleIcc_eq
  given: [NeZero n]
  statement: cycleIcc i i = 1
  proof: by
  ext k
  simp only [Perm.coe_one, id_eq]
  rcases lt_trichotomy k i with ch | ch | ch
  · simp [-cycleIcc_def_le, cycleIcc_of_lt, ch]
  · simp [-cycleIcc_def_le, ch]
  · simp [-cycleIcc_def_le, cycleIcc_of_gt, ch]

@[simp]

中文:
定理 cycleIcc_eq
  条件: [NeZero n]
  结论: cycleIcc i i = 1
  证明: by
  ext k
  simp only [Perm.coe_one, id_eq]
  rcases lt_trichotomy k i with ch | ch | ch
  · simp [-cycleIcc_def_le, cycleIcc_of_lt, ch]
  · simp [-cycleIcc_def_le, ch]
  · simp [-cycleIcc_def_le, cycleIcc_of_gt, ch]

@[simp]

Depends on / 依赖: Perm.coe_one, coe_one, cycleIcc_def_le, cycleIcc_of_gt, cycleIcc_of_lt, id_eq, lt_trichotomy
-/
theorem cycleIcc_eq [NeZero n] : cycleIcc i i = 1 := by
  ext k
  simp only [Perm.coe_one, id_eq]
  rcases lt_trichotomy k i with ch | ch | ch
  · simp [-cycleIcc_def_le, cycleIcc_of_lt, ch]
  · simp [-cycleIcc_def_le, ch]
  · simp [-cycleIcc_def_le, cycleIcc_of_gt, ch]

@[simp]
/--
theorem `cycleIcc_ge` / 定理 `cycleIcc_ge`

English:
theorem cycleIcc_ge
  given: (hij : i <= j) [NeZero n]
  statement: cycleIcc j i = 1
  proof: by
  rcases Fin.lt_or_eq_of_le hij with hij | hij
  · simp [hij]
  · rw [hij, ← cycleIcc_eq]

中文:
定理 cycleIcc_ge
  条件: (hij : i <= j) [NeZero n]
  结论: cycleIcc j i = 1
  证明: by
  rcases Fin.lt_or_eq_of_le hij with hij | hij
  · simp [hij]
  · rw [hij, ← cycleIcc_eq]

Depends on / 依赖: Fin.lt_or_eq_of_le, cycleIcc_eq, lt_or_eq_of_le
-/
theorem cycleIcc_ge (hij : i <= j) [NeZero n] : cycleIcc j i = 1 := by
  rcases Fin.lt_or_eq_of_le hij with hij | hij
  · simp [hij]
  · rw [hij, ← cycleIcc_eq]

/--
theorem `sign_cycleIcc_of_le` / 定理 `sign_cycleIcc_of_le`

English:
theorem sign_cycleIcc_of_le
  given: (hij : i <= j)
  statement: Perm.sign (cycleIcc i j) = (-1) ^ (j - i : Nat)
  proof: by
  simp [hij, sub_val_of_le hij]

中文:
定理 sign_cycleIcc_of_le
  条件: (hij : i <= j)
  结论: 置换.sign (cycleIcc i j) = (-1) ^ (j - i : 自然数)
  证明: by
  simp [hij, sub_val_of_le hij]

Depends on / 依赖: sub_val_of_le
-/
theorem sign_cycleIcc_of_le (hij : i <= j) : Perm.sign (cycleIcc i j) = (-1) ^ (j - i : Nat) := by
  simp [hij, sub_val_of_le hij]

/--
theorem `sign_cycleIcc_of_eq` / 定理 `sign_cycleIcc_of_eq`

English:
theorem sign_cycleIcc_of_eq
  statement: Perm.sign (cycleIcc i i) = 1
  proof: by
  rw [sign_cycleIcc_of_le (Fin.ge_of_eq rfl)]; rw [tsub_self]; rw [pow_zero]

中文:
定理 sign_cycleIcc_of_eq
  结论: 置换.sign (cycleIcc i i) = 1
  证明: by
  rw [sign_cycleIcc_of_le (Fin.ge_of_eq rfl)]; rw [tsub_self]; rw [pow_zero]

Depends on / 依赖: Fin.ge_of_eq, ge_of_eq, pow_zero, sign_cycleIcc_of_le, tsub_self
-/
theorem sign_cycleIcc_of_eq : Perm.sign (cycleIcc i i) = 1 := by
  rw [sign_cycleIcc_of_le (Fin.ge_of_eq rfl)]; rw [tsub_self]; rw [pow_zero]

/--
theorem `sign_cycleIcc_of_ge` / 定理 `sign_cycleIcc_of_ge`

English:
theorem sign_cycleIcc_of_ge
  given: (hij : i <= j)
  statement: Perm.sign (cycleIcc j i) = 1
  proof: by
  rcases Fin.lt_or_eq_of_le hij with hij | hij
  · simp [Fin.not_le.mpr hij]
  · rw [hij, sign_cycleIcc_of_eq]

中文:
定理 sign_cycleIcc_of_ge
  条件: (hij : i <= j)
  结论: 置换.sign (cycleIcc j i) = 1
  证明: by
  rcases Fin.lt_or_eq_of_le hij with hij | hij
  · simp [Fin.not_le.mpr hij]
  · rw [hij, sign_cycleIcc_of_eq]

Depends on / 依赖: Fin.lt_or_eq_of_le, Fin.not_le.mpr, lt_or_eq_of_le, not_le, sign_cycleIcc_of_eq
-/
theorem sign_cycleIcc_of_ge (hij : i <= j) : Perm.sign (cycleIcc j i) = 1 := by
  rcases Fin.lt_or_eq_of_le hij with hij | hij
  · simp [Fin.not_le.mpr hij]
  · rw [hij, sign_cycleIcc_of_eq]

/--
theorem `isCycle_cycleIcc` / 定理 `isCycle_cycleIcc`

English:
theorem isCycle_cycleIcc
  given: (hij : i < j)
  statement: (cycleIcc i j).IsCycle
  proof: by
  simpa [le_of_lt hij] using Equiv.Perm.IsCycle.extendDomain
    (natAdd_castLEEmb _).toEquivRange (isCycle_cycleRange (castLT_sub_nezero hij))

中文:
定理 isCycle_cycleIcc
  条件: (hij : i < j)
  结论: (cycleIcc i j).是环
  证明: by
  simpa [le_of_lt hij] using Equiv.Perm.IsCycle.extendDomain
    (natAdd_castLEEmb _).toEquivRange (isCycle_cycleRange (castLT_sub_nezero hij))

Depends on / 依赖: Equiv.Perm.IsCycle.extendDomain, IsCycle, castLT_sub_nezero, extendDomain, isCycle_cycleRange, le_of_lt, natAdd_castLEEmb, toEquivRange
-/
theorem isCycle_cycleIcc (hij : i < j) : (cycleIcc i j).IsCycle := by
  simpa [le_of_lt hij] using Equiv.Perm.IsCycle.extendDomain
    (natAdd_castLEEmb _).toEquivRange (isCycle_cycleRange (castLT_sub_nezero hij))

/--
theorem `cycleType_cycleIcc_of_lt` / 定理 `cycleType_cycleIcc_of_lt`

English:
theorem cycleType_cycleIcc_of_lt
  given: (hij : i < j)
  proof: by
  simpa [le_of_lt hij, cycleType_cycleRange (castLT_sub_nezero hij)] using sub_val_of_le
    (le_of_lt hij)

中文:
定理 cycleType_cycleIcc_of_lt
  条件: (hij : i < j)
  证明: by
  simpa [le_of_lt hij, cycleType_cycleRange (castLT_sub_nezero hij)] using sub_val_of_le
    (le_of_lt hij)

Depends on / 依赖: castLT_sub_nezero, cycleType_cycleRange, le_of_lt, sub_val_of_le
-/
theorem cycleType_cycleIcc_of_lt (hij : i < j) :
    Perm.cycleType (cycleIcc i j) = {(j - i + 1: Nat)} := by
  simpa [le_of_lt hij, cycleType_cycleRange (castLT_sub_nezero hij)] using sub_val_of_le
    (le_of_lt hij)

/--
theorem `cycleType_cycleIcc_of_ge` / 定理 `cycleType_cycleIcc_of_ge`

English:
theorem cycleType_cycleIcc_of_ge
  given: (hij : i <= j) [NeZero n]
  statement: Perm.cycleType (cycleIcc j i) = ∅
  proof: by
  simpa using cycleIcc_ge hij

中文:
定理 cycleType_cycleIcc_of_ge
  条件: (hij : i <= j) [NeZero n]
  结论: 置换.cycleType (cycleIcc j i) = ∅
  证明: by
  simpa using cycleIcc_ge hij

Depends on / 依赖: cycleIcc_ge
-/
theorem cycleType_cycleIcc_of_ge (hij : i <= j) [NeZero n] : Perm.cycleType (cycleIcc j i) = ∅ := by
  simpa using cycleIcc_ge hij

/--
theorem `cycleIcc_zero_eq_cycleRange` / 定理 `cycleIcc_zero_eq_cycleRange`

English:
theorem cycleIcc_zero_eq_cycleRange
  given: (i : Fin n) [NeZero n]
  statement: cycleIcc 0 i = cycleRange i
  proof: by
  ext x
  rcases lt_trichotomy x i with ch | ch | ch
  · simp [-cycleIcc_def_le, cycleIcc_of_ge_of_lt (zero_le x) ch, cycleRange_of_lt ch]
  · simp [-cycleIcc_def_le, ch]
  · simp [-cycleIcc_def_le, cycleIcc_of_gt ch, cycleRange_of_gt ch]

中文:
定理 cycleIcc_zero_eq_cycleRange
  条件: (i : 有限集 n) [NeZero n]
  结论: cycleIcc 0 i = cycleRange i
  证明: by
  ext x
  rcases lt_trichotomy x i with ch | ch | ch
  · simp [-cycleIcc_def_le, cycleIcc_of_ge_of_lt (zero_le x) ch, cycleRange_of_lt ch]
  · simp [-cycleIcc_def_le, ch]
  · simp [-cycleIcc_def_le, cycleIcc_of_gt ch, cycleRange_of_gt ch]

Depends on / 依赖: cycleIcc_def_le, cycleIcc_of_ge_of_lt, cycleIcc_of_gt, cycleRange_of_gt, cycleRange_of_lt, lt_trichotomy, zero_le
-/
theorem cycleIcc_zero_eq_cycleRange (i : Fin n) [NeZero n] : cycleIcc 0 i = cycleRange i := by
  ext x
  rcases lt_trichotomy x i with ch | ch | ch
  · simp [-cycleIcc_def_le, cycleIcc_of_ge_of_lt (zero_le x) ch, cycleRange_of_lt ch]
  · simp [-cycleIcc_def_le, ch]
  · simp [-cycleIcc_def_le, cycleIcc_of_gt ch, cycleRange_of_gt ch]

/--
theorem `cycleIcc_comp_succAbove` / 定理 `cycleIcc_comp_succAbove`

English:
theorem cycleIcc_comp_succAbove
  given: {n : Nat} (i j : Fin (n + 1)) (hij : i <= j)
  proof: by
  grind [cycleIcc_of_lt, succAbove_of_castSucc_lt, cycleIcc_of_ge_of_lt,
    succAbove_of_le_castSucc, coeSucc_eq_succ, cycleIcc_of_gt]

中文:
定理 cycleIcc_comp_succAbove
  条件: {n : 自然数} (i j : 有限集 (n + 1)) (hij : i <= j)
  证明: by
  grind [cycleIcc_of_lt, succAbove_of_castSucc_lt, cycleIcc_of_ge_of_lt,
    succAbove_of_le_castSucc, coeSucc_eq_succ, cycleIcc_of_gt]

Depends on / 依赖: coeSucc_eq_succ, cycleIcc_of_ge_of_lt, cycleIcc_of_gt, cycleIcc_of_lt, succAbove_of_castSucc_lt, succAbove_of_le_castSucc
-/
theorem cycleIcc_comp_succAbove {n : Nat} (i j : Fin (n + 1)) (hij : i <= j) :
    (cycleIcc i j) ∘ j.succAbove = i.succAbove := by
  grind [cycleIcc_of_lt, succAbove_of_castSucc_lt, cycleIcc_of_ge_of_lt,
    succAbove_of_le_castSucc, coeSucc_eq_succ, cycleIcc_of_gt]

/--
theorem `cycleIcc.trans` / 定理 `cycleIcc.trans`

English:
theorem cycleIcc.trans
  given: [NeZero n] (hij : i <= j) (hjk : j <= k)
  proof: by
  ext x
  rcases lt_or_ge x i with ch | ch
  · simp [cycleIcc_of_lt (lt_of_lt_of_le ch hij), cycleIcc_of_lt ch]
  rcases lt_or_ge k x with ch | ch1
  · simp [cycleIcc_of_gt (lt_of_le_of_lt hjk ch), cycleIcc_of_gt ch]
  rcases lt_or_ge x j with ch2 | ch2
  · simp [cycleIcc_of_lt ch2, cycleIcc_of_le_of_le ch ch1, cycleIcc_of_le_of_le ch (le_of_lt ch2)]
    split_ifs
    repeat lia
  · simp only [Function.comp_apply, cycleIcc_of_le_of_le ch2 ch1, cycleIcc_of_le_of_le ch ch1]
    split_ifs with h
    · exact val_eq_of_eq (cycleIcc_of_last hij)
    · simp [cycleIcc_of_gt (lt_of_le_of_lt ch2 (lt_add_one_of_succ_lt (by lia)))]

中文:
定理 cycleIcc.trans
  条件: [NeZero n] (hij : i <= j) (hjk : j <= k)
  证明: by
  ext x
  rcases lt_or_ge x i with ch | ch
  · simp [cycleIcc_of_lt (lt_of_lt_of_le ch hij), cycleIcc_of_lt ch]
  rcases lt_or_ge k x with ch | ch1
  · simp [cycleIcc_of_gt (lt_of_le_of_lt hjk ch), cycleIcc_of_gt ch]
  rcases lt_or_ge x j with ch2 | ch2
  · simp [cycleIcc_of_lt ch2, cycleIcc_of_le_of_le ch ch1, cycleIcc_of_le_of_le ch (le_of_lt ch2)]
    split_ifs
    repeat lia
  · simp only [Function.comp_apply, cycleIcc_of_le_of_le ch2 ch1, cycleIcc_of_le_of_le ch ch1]
    split_ifs with h
    · exact val_eq_of_eq (cycleIcc_of_last hij)
    · simp [cycleIcc_of_gt (lt_of_le_of_lt ch2 (lt_add_one_of_succ_lt (by lia)))]

Depends on / 依赖: Function, Function.comp_apply, comp_apply, cycleIcc_of_gt, cycleIcc_of_le_of_le, cycleIcc_of_lt, le_of_lt, lt_of_le_of_lt, lt_of_lt_of_le, lt_or_ge, repeat, split_ifs, val_eq_of_eq
-/
theorem cycleIcc.trans [NeZero n] (hij : i <= j) (hjk : j <= k) :
    (cycleIcc i j) ∘ (cycleIcc j k) = (cycleIcc i k) := by
  ext x
  rcases lt_or_ge x i with ch | ch
  · simp [cycleIcc_of_lt (lt_of_lt_of_le ch hij), cycleIcc_of_lt ch]
  rcases lt_or_ge k x with ch | ch1
  · simp [cycleIcc_of_gt (lt_of_le_of_lt hjk ch), cycleIcc_of_gt ch]
  rcases lt_or_ge x j with ch2 | ch2
  · simp [cycleIcc_of_lt ch2, cycleIcc_of_le_of_le ch ch1, cycleIcc_of_le_of_le ch (le_of_lt ch2)]
    split_ifs
    repeat lia
  · simp only [Function.comp_apply, cycleIcc_of_le_of_le ch2 ch1, cycleIcc_of_le_of_le ch ch1]
    split_ifs with h
    · exact val_eq_of_eq (cycleIcc_of_last hij)
    · simp [cycleIcc_of_gt (lt_of_le_of_lt ch2 (lt_add_one_of_succ_lt (by lia)))]

/--
theorem `cycleIcc.trans_left_one` / 定理 `cycleIcc.trans_left_one`

English:
theorem cycleIcc.trans_left_one
  given: [NeZero n] (hij : i <= j)
  proof: by
  simp [hij]

中文:
定理 cycleIcc.trans_left_one
  条件: [NeZero n] (hij : i <= j)
  证明: by
  simp [hij]
-/
theorem cycleIcc.trans_left_one [NeZero n] (hij : i <= j) :
    (cycleIcc j i) ∘ (cycleIcc i k) = cycleIcc i k := by
  simp [hij]

/--
theorem `cycleIcc.trans_right_one` / 定理 `cycleIcc.trans_right_one`

English:
theorem cycleIcc.trans_right_one
  given: [NeZero n] (hjk : j <= k)
  proof: by
  simp [hjk]

中文:
定理 cycleIcc.trans_right_one
  条件: [NeZero n] (hjk : j <= k)
  证明: by
  simp [hjk]
-/
theorem cycleIcc.trans_right_one [NeZero n] (hjk : j <= k) :
    (cycleIcc i k) ∘ (cycleIcc k j) = cycleIcc i k := by
  simp [hjk]

end Fin

end cycleIcc

section Sign

variable {n : Nat}

/--
theorem `Equiv.Perm.sign_eq_prod_prod_Iio` / 定理 `Equiv.Perm.sign_eq_prod_prod_Iio`

English:
theorem Equiv.Perm.sign_eq_prod_prod_Iio
  given: (σ : Equiv.Perm (Fin n))
  proof: by
  suffices h : σ.sign = σ.signAux by
    rw [h]; rw [Finset.prod_sigma']; rw [Equiv.Perm.signAux]
    convert! rfl using 2 with x hx
    · simp [Finset.ext_iff, Equiv.Perm.mem_finPairsLT]
    simp [← ite_not (p := _ <= _)]
  refine σ.swap_induction_on (by simp) fun π i j hne h_eq => ?_
  rw [Equiv.Perm.signAux_mul]; rw [Equiv.Perm.sign_mul]; rw [h_eq]; rw [Equiv.Perm.sign_swap hne]; rw [Equiv.Perm.signAux_swap hne]

中文:
定理 等价.置换.sign_eq_prod_prod_Iio
  条件: (σ : 等价.置换 (有限集 n))
  证明: by
  suffices h : σ.sign = σ.signAux by
    rw [h]; rw [Finset.prod_sigma']; rw [Equiv.Perm.signAux]
    convert! rfl using 2 with x hx
    · simp [Finset.ext_iff, Equiv.Perm.mem_finPairsLT]
    simp [← ite_not (p := _ <= _)]
  refine σ.swap_induction_on (by simp) fun π i j hne h_eq => ?_
  rw [Equiv.Perm.signAux_mul]; rw [Equiv.Perm.sign_mul]; rw [h_eq]; rw [Equiv.Perm.sign_swap hne]; rw [Equiv.Perm.signAux_swap hne]

Depends on / 依赖: Equiv.Perm.mem_finPairsLT, Equiv.Perm.signAux, Equiv.Perm.signAux_mul, Equiv.Perm.signAux_swap, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap, Finset, Finset.ext_iff, Finset.prod_sigma, convert, ext_iff, h_eq, ite_not, mem_finPairsLT, prod_sigma, signAux, signAux_mul, signAux_swap, sign_mul, sign_swap
-/
theorem Equiv.Perm.sign_eq_prod_prod_Iio (σ : Equiv.Perm (Fin n)) :
    σ.sign = ∏ j, ∏ i in Finset.Iio j, (if σ i < σ j then 1 else -1) := by
  suffices h : σ.sign = σ.signAux by
    rw [h]; rw [Finset.prod_sigma']; rw [Equiv.Perm.signAux]
    convert! rfl using 2 with x hx
    · simp [Finset.ext_iff, Equiv.Perm.mem_finPairsLT]
    simp [← ite_not (p := _ <= _)]
  refine σ.swap_induction_on (by simp) fun π i j hne h_eq => ?_
  rw [Equiv.Perm.signAux_mul]; rw [Equiv.Perm.sign_mul]; rw [h_eq]; rw [Equiv.Perm.sign_swap hne]; rw [Equiv.Perm.signAux_swap hne]

/--
theorem `Equiv.Perm.sign_eq_prod_prod_Ioi` / 定理 `Equiv.Perm.sign_eq_prod_prod_Ioi`

English:
theorem Equiv.Perm.sign_eq_prod_prod_Ioi
  given: (σ : Equiv.Perm (Fin n))
  proof: by
  rw [σ.sign_eq_prod_prod_Iio]
  apply Finset.prod_comm' (by simp)

中文:
定理 等价.置换.sign_eq_prod_prod_Ioi
  条件: (σ : 等价.置换 (有限集 n))
  证明: by
  rw [σ.sign_eq_prod_prod_Iio]
  apply Finset.prod_comm' (by simp)

Depends on / 依赖: Finset, Finset.prod_comm, prod_comm, sign_eq_prod_prod_Iio
-/
theorem Equiv.Perm.sign_eq_prod_prod_Ioi (σ : Equiv.Perm (Fin n)) :
    σ.sign = ∏ i, ∏ j in Finset.Ioi i, (if σ i < σ j then 1 else -1) := by
  rw [σ.sign_eq_prod_prod_Iio]
  apply Finset.prod_comm' (by simp)

/--
theorem `Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod` / 定理 `Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod`

English:
theorem Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod
  statement: {R : Type*} [CommRing R]
  proof: by
  simp_rw [← σ.sign_inv, σ⁻¹.sign_eq_prod_prod_Iio, Finset.prod_sigma', Units.coe_prod,
    Int.cast_prod, ← Finset.prod_mul_distrib]
  set D := (Finset.univ : Finset (Fin n)).sigma Finset.Iio with hD
  have hφD : D.image (fun x => ⟨σ x.1 ⊔ σ x.2, σ x.1 ⊓ σ x.2⟩) = D := by
    ext ⟨x1, x2⟩
    suffices (exists a, exists b < a, σ a ⊔ σ b = x1 ∧ σ a ⊓ σ b = x2) ↔ x2 < x1 by simpa [hD]
    refine ⟨?_, fun hlt => ?_⟩
    · rintro ⟨i, j, hij, rfl, rfl⟩
exact inf_le_sup.lt_of_ne by simp [hij.ne.symm]
    obtain hlt' | hle := lt_or_ge (σ.symm x1) (σ.symm x2)
    · exact ⟨_, _, hlt', by simp [hlt.le]⟩
    exact ⟨_, _, hle.lt_of_ne (by simp [hlt.ne]), by simp [hlt.le]⟩
  nth_rw 2 [← hφD]
  rw [Finset.prod_image fun x hx y hy => Finset.injOn_of_card_image_eq (by rw [hφD]) hx hy]
  refine Finset.prod_congr rfl fun ⟨x₁, x₂⟩ hx => ?_
  replace hx : x₂ < x₁ := by simpa [hD] using hx
  obtain hlt | hle := lt_or_ge (σ x₁) (σ x₂)
  · simp [inf_eq_left.2 hlt.le, sup_eq_right.2 hlt.le, hx.not_gt, ← hf]
  simp [inf_eq_right.2 hle, sup_eq_left.2 hle, hx]

中文:
定理 等价.置换.prod_Iio_comp_eq_sign_mul_prod
  结论: {R : 类型} [交换环 R]
  证明: by
  simp_rw [← σ.sign_inv, σ⁻¹.sign_eq_prod_prod_Iio, Finset.prod_sigma', Units.coe_prod,
    Int.cast_prod, ← Finset.prod_mul_distrib]
  set D := (Finset.univ : Finset (Fin n)).sigma Finset.Iio with hD
  have hφD : D.image (fun x => ⟨σ x.1 ⊔ σ x.2, σ x.1 ⊓ σ x.2⟩) = D := by
    ext ⟨x1, x2⟩
    suffices (exists a, exists b < a, σ a ⊔ σ b = x1 ∧ σ a ⊓ σ b = x2) ↔ x2 < x1 by simpa [hD]
    refine ⟨?_, fun hlt => ?_⟩
    · rintro ⟨i, j, hij, rfl, rfl⟩
exact inf_le_sup.lt_of_ne by simp [hij.ne.symm]
    obtain hlt' | hle := lt_or_ge (σ.symm x1) (σ.symm x2)
    · exact ⟨_, _, hlt', by simp [hlt.le]⟩
    exact ⟨_, _, hle.lt_of_ne (by simp [hlt.ne]), by simp [hlt.le]⟩
  nth_rw 2 [← hφD]
  rw [Finset.prod_image fun x hx y hy => Finset.injOn_of_card_image_eq (by rw [hφD]) hx hy]
  refine Finset.prod_congr rfl fun ⟨x₁, x₂⟩ hx => ?_
  replace hx : x₂ < x₁ := by simpa [hD] using hx
  obtain hlt | hle := lt_or_ge (σ x₁) (σ x₂)
  · simp [inf_eq_left.2 hlt.le, sup_eq_right.2 hlt.le, hx.not_gt, ← hf]
  simp [inf_eq_right.2 hle, sup_eq_left.2 hle, hx]

Depends on / 依赖: D.image, Finset, Finset.Iio, Finset.prod_mul_distrib, Finset.prod_sigma, Finset.univ, Int.cast_prod, Units.coe_prod, cast_prod, coe_prod, hij.ne.symm, inf_le_sup, inf_le_sup.lt_of_ne, lt_of_ne, prod_mul_distrib, prod_sigma, sign_eq_prod_prod_Iio, sign_inv, simp_rw
-/
theorem Equiv.Perm.prod_Iio_comp_eq_sign_mul_prod {R : Type*} [CommRing R]
    (σ : Equiv.Perm (Fin n)) {f : Fin n -> Fin n -> R} (hf : forall i j, f i j = -f j i) :
    ∏ j, ∏ i in Finset.Iio j, f (σ i) (σ j) = σ.sign * ∏ j, ∏ i in Finset.Iio j, f i j := by
  simp_rw [← σ.sign_inv, σ⁻¹.sign_eq_prod_prod_Iio, Finset.prod_sigma', Units.coe_prod,
    Int.cast_prod, ← Finset.prod_mul_distrib]
  set D := (Finset.univ : Finset (Fin n)).sigma Finset.Iio with hD
  have hφD : D.image (fun x => ⟨σ x.1 ⊔ σ x.2, σ x.1 ⊓ σ x.2⟩) = D := by
    ext ⟨x1, x2⟩
    suffices (exists a, exists b < a, σ a ⊔ σ b = x1 ∧ σ a ⊓ σ b = x2) ↔ x2 < x1 by simpa [hD]
    refine ⟨?_, fun hlt => ?_⟩
    · rintro ⟨i, j, hij, rfl, rfl⟩
exact inf_le_sup.lt_of_ne by simp [hij.ne.symm]
    obtain hlt' | hle := lt_or_ge (σ.symm x1) (σ.symm x2)
    · exact ⟨_, _, hlt', by simp [hlt.le]⟩
    exact ⟨_, _, hle.lt_of_ne (by simp [hlt.ne]), by simp [hlt.le]⟩
  nth_rw 2 [← hφD]
  rw [Finset.prod_image fun x hx y hy => Finset.injOn_of_card_image_eq (by rw [hφD]) hx hy]
  refine Finset.prod_congr rfl fun ⟨x₁, x₂⟩ hx => ?_
  replace hx : x₂ < x₁ := by simpa [hD] using hx
  obtain hlt | hle := lt_or_ge (σ x₁) (σ x₂)
  · simp [inf_eq_left.2 hlt.le, sup_eq_right.2 hlt.le, hx.not_gt, ← hf]
  simp [inf_eq_right.2 hle, sup_eq_left.2 hle, hx]

/--
theorem `Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod` / 定理 `Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod`

English:
theorem Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod
  statement: {R : Type*} [CommRing R]
  proof: by
  convert! σ.prod_Iio_comp_eq_sign_mul_prod hf using 1
  · apply Finset.prod_comm' (by simp)
  convert! rfl using 2
  apply Finset.prod_comm' (by simp)

中文:
定理 等价.置换.prod_Ioi_comp_eq_sign_mul_prod
  结论: {R : 类型} [交换环 R]
  证明: by
  convert! σ.prod_Iio_comp_eq_sign_mul_prod hf using 1
  · apply Finset.prod_comm' (by simp)
  convert! rfl using 2
  apply Finset.prod_comm' (by simp)

Depends on / 依赖: Finset, Finset.prod_comm, convert, prod_Iio_comp_eq_sign_mul_prod, prod_comm
-/
theorem Equiv.Perm.prod_Ioi_comp_eq_sign_mul_prod {R : Type*} [CommRing R]
    (σ : Equiv.Perm (Fin n)) {f : Fin n -> Fin n -> R} (hf : forall i j, f i j = -f j i) :
    ∏ i, ∏ j in Finset.Ioi i, f (σ i) (σ j) = σ.sign * ∏ i, ∏ j in Finset.Ioi i, f i j := by
  convert! σ.prod_Iio_comp_eq_sign_mul_prod hf using 1
  · apply Finset.prod_comm' (by simp)
  convert! rfl using 2
  apply Finset.prod_comm' (by simp)

end Sign
