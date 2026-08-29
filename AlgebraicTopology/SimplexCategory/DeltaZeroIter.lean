/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# Iterations of `δ 0` and `σ 0`

This file introduces morphisms `δ₀Iter i` and `σ₀Iter i` in the simplex category:
they are obtained as the `i`th iteration of `δ 0` or `σ 0`.

-/

@[expose] public section

open CategoryTheory Simplicial

namespace SimplexCategory

/--
Definition of `δ₀Iter` / `δ₀Iter` 的定义

English:
definition δ₀Iter
  signature: (i : Nat) {n m : Nat} (hi : n + i = m := by lia)
  body: Hom.mk
    { toFun j := ⟨j.val + i, by lia ⟩
      monotone' _ _ := by grind }

中文:
定义 δ₀Iter
  签名: (i : 自然数) {n m : 自然数} (hi : n + i = m := by lia)
  定义体: Hom.mk
    { toFun j := ⟨j.val + i, by lia ⟩
      monotone' _ _ := by grind }

Depends on / 依赖: Hom.mk, j.val, monotone
-/
def δ₀Iter (i : Nat) {n m : Nat} (hi : n + i = m := by lia) : ⦋n⦌ ⟶ ⦋m⦌ :=
  Hom.mk
    { toFun j := ⟨j.val + i, by lia ⟩
      monotone' _ _ := by grind }

/--
lemma `δ₀Iter_apply` / 引理 `δ₀Iter_apply`

English:
lemma δ₀Iter_apply
  given: (i : Nat) {n m : Nat} (j : Fin (n + 1)) (hi : n + i = m := by lia)
  proof: rfl

@[simp]

中文:
引理 δ₀Iter_apply
  条件: (i : 自然数) {n m : 自然数} (j : 有限集 (n + 1)) (hi : n + i = m := by lia)
  证明: rfl

@[simp]

Depends on / 依赖: j.val
-/
lemma δ₀Iter_apply (i : Nat) {n m : Nat} (j : Fin (n + 1)) (hi : n + i = m := by lia) :
    dsimp% (δ₀Iter i hi j) = ⟨j.val + i, by lia⟩ := rfl

@[simp]
/--
lemma `δ₀Iter_zero` / 引理 `δ₀Iter_zero`

English:
lemma δ₀Iter_zero
  given: (n : Nat)
  proof: rfl

@[simp]

中文:
引理 δ₀Iter_zero
  条件: (n : 自然数)
  证明: rfl

@[simp]
-/
lemma δ₀Iter_zero (n : Nat) :
    δ₀Iter 0 (add_zero n) = 𝟙 _ := rfl

@[simp]
/--
lemma `δ₀Iter_one` / 引理 `δ₀Iter_one`

English:
lemma δ₀Iter_one
  given: (n : Nat)
  proof: rfl

@[reassoc]

中文:
引理 δ₀Iter_one
  条件: (n : 自然数)
  证明: rfl

@[reassoc]
-/
lemma δ₀Iter_one (n : Nat) :
    δ₀Iter 1 (n := n) rfl = δ 0 := rfl

@[reassoc]
/--
lemma `δ₀Iter_succ` / 引理 `δ₀Iter_succ`

English:
lemma δ₀Iter_succ
  given: (i : Nat) {n m : Nat} (h : n + i = m := by lia)
  proof: rfl

@[reassoc]

中文:
引理 δ₀Iter_succ
  条件: (i : 自然数) {n m : 自然数} (h : n + i = m := by lia)
  证明: rfl

@[reassoc]
-/
lemma δ₀Iter_succ (i : Nat) {n m : Nat} (h : n + i = m := by lia) :
    δ₀Iter (i + 1) = δ₀Iter i h ≫ δ 0 := rfl

@[reassoc]
/--
lemma `δ₀Iter_succ'` / 引理 `δ₀Iter_succ'`

English:
lemma δ₀Iter_succ'
  given: (i : Nat) {n m : Nat} (h : n + (i + 1) = m := by lia)
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ 0) (δ₀Iter i)]; rw [coe_δ]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]
  dsimp
  lia

中文:
引理 δ₀Iter_succ'
  条件: (i : 自然数) {n m : 自然数} (h : n + (i + 1) = m := by lia)
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ 0) (δ₀Iter i)]; rw [coe_δ]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]
  dsimp
  lia

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.hom_ext, comp_apply, hom_ext
-/
lemma δ₀Iter_succ' (i : Nat) {n m : Nat} (h : n + (i + 1) = m := by lia) :
    δ₀Iter (i + 1) h = δ 0 ≫ δ₀Iter i := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ 0) (δ₀Iter i)]; rw [coe_δ]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]
  dsimp
  lia

/--
lemma `δ₀Iter_δ` / 引理 `δ₀Iter_δ`

English:
lemma δ₀Iter_δ
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 2))
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter i hi) (δ j)]; rw [coe_δ]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]; rw [Fin.succAbove_of_le_castSucc _ _ (by grind)]
  simp [add_assoc]

@[reassoc]

中文:
引理 δ₀Iter_δ
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 2))
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter i hi) (δ j)]; rw [coe_δ]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]; rw [Fin.succAbove_of_le_castSucc _ _ (by grind)]
  simp [add_assoc]

@[reassoc]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.hom_ext, Fin.succAbove_of_le_castSucc, add_assoc, comp_apply, hom_ext, j.val, succAbove_of_le_castSucc
-/
lemma δ₀Iter_δ (i : Nat) {n m : Nat} (j : Fin (m + 2))
    (hi : n + i = m := by lia) (hj : j.val <= i := by grind) :
    δ₀Iter i hi ≫ δ j = δ₀Iter (i + 1) := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter i hi) (δ j)]; rw [coe_δ]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]; rw [Fin.succAbove_of_le_castSucc _ _ (by grind)]
  simp [add_assoc]

@[reassoc]
/--
lemma `δ₀Iter_δ'` / 引理 `δ₀Iter_δ'`

English:
lemma δ₀Iter_δ'
  statement: {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat}
  proof: by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : i = i' := by lia
    simp
  | succ j hj =>
    rw [δ₀Iter_succ'_assoc ..]; rw [δ₀Iter_succ' ..]; rw [← reassoc_of% dsimp% δ_comp_δ (i := 0) (j := i) (by simp)]; rw [← hj _ i' _ (by grind)]

@[reassoc]

中文:
引理 δ₀Iter_δ'
  结论: {n : 自然数} (i : 有限集 (n + 2)) (j : 自然数) {m : 自然数}
  证明: by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : i = i' := by lia
    simp
  | succ j hj =>
    rw [δ₀Iter_succ'_assoc ..]; rw [δ₀Iter_succ' ..]; rw [← reassoc_of% dsimp% δ_comp_δ (i := 0) (j := i) (by simp)]; rw [← hj _ i' _ (by grind)]

@[reassoc]

Depends on / 依赖: _assoc, generalizing, i.val, reassoc_of
-/
lemma δ₀Iter_δ' {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat}
    (i' : Fin (m + 2)) (h : n + j = m := by lia)
    (hi'' : i'.val = i.val + j := by grind) :
    δ₀Iter j h ≫ δ i' = δ i ≫ δ₀Iter j := by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : i = i' := by lia
    simp
  | succ j hj =>
    rw [δ₀Iter_succ'_assoc ..]; rw [δ₀Iter_succ' ..]; rw [← reassoc_of% dsimp% δ_comp_δ (i := 0) (j := i) (by simp)]; rw [← hj _ i' _ (by grind)]

@[reassoc]
/--
lemma `δ₀Iter_σ` / 引理 `δ₀Iter_σ`

English:
lemma δ₀Iter_σ
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 1))
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter (i + 1)) (σ j)]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]; rw [coe_σ]; rw [Fin.predAbove_of_castSucc_lt _ _ (by grind)]
  dsimp

@[reassoc]

中文:
引理 δ₀Iter_σ
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 1))
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter (i + 1)) (σ j)]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]; rw [coe_σ]; rw [Fin.predAbove_of_castSucc_lt _ _ (by grind)]
  dsimp

@[reassoc]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.hom_ext, Fin.predAbove_of_castSucc_lt, comp_apply, hom_ext, j.val, predAbove_of_castSucc_lt
-/
lemma δ₀Iter_σ (i : Nat) {n m : Nat} (j : Fin (m + 1))
    (hi : n + (i + 1) = m + 1 := by lia)
    (hj : j.val <= i := by grind) :
    δ₀Iter (i + 1) hi ≫ σ j = δ₀Iter i := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (δ₀Iter (i + 1)) (σ j)]; rw [δ₀Iter_apply ..]; rw [δ₀Iter_apply ..]; rw [coe_σ]; rw [Fin.predAbove_of_castSucc_lt _ _ (by grind)]
  dsimp

@[reassoc]
/--
lemma `δ₀Iter_σ'` / 引理 `δ₀Iter_σ'`

English:
lemma δ₀Iter_σ'
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 1))
  proof: by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : j = j' := by lia
    simp
  | succ i hi =>
    obtain _ | m := m
    · grind
    · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero
        (by rintro rfl; dsimp at hj'; lia)
      rw [δ₀Iter_succ_assoc ..]; rw [δ₀Iter_succ ..]; rw [dsimp% δ_comp_σ_of_le (i := 0) (j := j) (by simp)]; rw [reassoc_of% hi j j' (by lia) (by grind)]

中文:
引理 δ₀Iter_σ'
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 1))
  证明: by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : j = j' := by lia
    simp
  | succ i hi =>
    obtain _ | m := m
    · grind
    · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero
        (by rintro rfl; dsimp at hj'; lia)
      rw [δ₀Iter_succ_assoc ..]; rw [δ₀Iter_succ ..]; rw [dsimp% δ_comp_σ_of_le (i := 0) (j := j) (by simp)]; rw [reassoc_of% hi j j' (by lia) (by grind)]

Depends on / 依赖: eq_succ_of_ne_zero, generalizing, j.eq_succ_of_ne_zero, j.val, reassoc_of
-/
lemma δ₀Iter_σ' (i : Nat) {n m : Nat} (j : Fin (m + 1))
    (j' : Fin (n + 1))
    (hi' : n + i = m := by lia)
    (hj' : j.val = j'.val + i := by grind) :
    δ₀Iter i ≫ σ j = σ j' ≫ δ₀Iter i hi' := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : j = j' := by lia
    simp
  | succ i hi =>
    obtain _ | m := m
    · grind
    · obtain ⟨j, rfl⟩ := j.eq_succ_of_ne_zero
        (by rintro rfl; dsimp at hj'; lia)
      rw [δ₀Iter_succ_assoc ..]; rw [δ₀Iter_succ ..]; rw [dsimp% δ_comp_σ_of_le (i := 0) (j := j) (by simp)]; rw [reassoc_of% hi j j' (by lia) (by grind)]

/--
Definition of `σ₀Iter` / `σ₀Iter` 的定义

English:
definition σ₀Iter
  signature: (i : Nat) {n m : Nat} (hi : n + i = m := by lia)
  body: Hom.mk
    { toFun j :=
        if j.val < i then 0 else ⟨j.val - i, by lia⟩
      monotone' _ _ _ := by grind [Fin.zero_le] }

中文:
定义 σ₀Iter
  签名: (i : 自然数) {n m : 自然数} (hi : n + i = m := by lia)
  定义体: Hom.mk
    { toFun j :=
        if j.val < i then 0 else ⟨j.val - i, by lia⟩
      monotone' _ _ _ := by grind [Fin.zero_le] }

Depends on / 依赖: Fin.zero_le, Hom.mk, j.val, monotone, zero_le
-/
def σ₀Iter (i : Nat) {n m : Nat} (hi : n + i = m := by lia) : ⦋m⦌ ⟶ ⦋n⦌ :=
  Hom.mk
    { toFun j :=
        if j.val < i then 0 else ⟨j.val - i, by lia⟩
      monotone' _ _ _ := by grind [Fin.zero_le] }

/--
lemma `σ₀Iter_coe_eq_of_lt` / 引理 `σ₀Iter_coe_eq_of_lt`

English:
lemma σ₀Iter_coe_eq_of_lt
  statement: (i : Nat) {n m : Nat}
  proof: by
  simp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom, if_pos hj]

中文:
引理 σ₀Iter_coe_eq_of_lt
  结论: (i : 自然数) {n m : 自然数}
  证明: by
  simp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom, if_pos hj]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, Hom.mk, Hom.toOrderHom, if_pos, j.val, toOrderHom
-/
lemma σ₀Iter_coe_eq_of_lt (i : Nat) {n m : Nat}
    (j : Fin (m + 1)) (hi : n + i = m := by lia) (hj : j.val < i := by grind) :
    dsimp% (σ₀Iter i hi j).val = 0 := by
  simp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom, if_pos hj]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `σ₀Iter_coe_eq_of_ge` / 引理 `σ₀Iter_coe_eq_of_ge`

English:
lemma σ₀Iter_coe_eq_of_ge
  statement: (i : Nat) {n m : Nat}
  proof: by
  dsimp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom]
  rw [if_neg (by lia)]

中文:
引理 σ₀Iter_coe_eq_of_ge
  结论: (i : 自然数) {n m : 自然数}
  证明: by
  dsimp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom]
  rw [if_neg (by lia)]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom, Hom.mk, Hom.toOrderHom, if_neg, j.val, toOrderHom
-/
lemma σ₀Iter_coe_eq_of_ge (i : Nat) {n m : Nat}
    (j : Fin (m + 1)) (hi : n + i = m := by lia) (hj : i <= j.val := by grind) :
    dsimp% (σ₀Iter i hi j).val = j.val - i := by
  dsimp [σ₀Iter, Hom.mk, ConcreteCategory.hom, Hom.toOrderHom]
  rw [if_neg (by lia)]

/--
lemma `σ₀Iter_coe_eq_of_le` / 引理 `σ₀Iter_coe_eq_of_le`

English:
lemma σ₀Iter_coe_eq_of_le
  statement: (i : Nat) {n m : Nat}
  proof: by
  obtain rfl | hj := hj.eq_or_lt
  · rw [σ₀Iter_coe_eq_of_ge .., tsub_self]
  · exact σ₀Iter_coe_eq_of_lt ..

@[simp]

中文:
引理 σ₀Iter_coe_eq_of_le
  结论: (i : 自然数) {n m : 自然数}
  证明: by
  obtain rfl | hj := hj.eq_or_lt
  · rw [σ₀Iter_coe_eq_of_ge .., tsub_self]
  · exact σ₀Iter_coe_eq_of_lt ..

@[simp]

Depends on / 依赖: eq_or_lt, hj.eq_or_lt, j.val, tsub_self
-/
lemma σ₀Iter_coe_eq_of_le (i : Nat) {n m : Nat}
    (j : Fin (m + 1)) (hi : n + i = m := by lia) (hj : j.val <= i := by grind) :
    dsimp% (σ₀Iter i hi j).val = 0 := by
  obtain rfl | hj := hj.eq_or_lt
  · rw [σ₀Iter_coe_eq_of_ge .., tsub_self]
  · exact σ₀Iter_coe_eq_of_lt ..

@[simp]
/--
lemma `σ₀Iter_zero` / 引理 `σ₀Iter_zero`

English:
lemma σ₀Iter_zero
  given: (n : Nat)
  proof: by
  ext
  simp [σ₀Iter]

@[simp]

中文:
引理 σ₀Iter_zero
  条件: (n : 自然数)
  证明: by
  ext
  simp [σ₀Iter]

@[simp]
-/
lemma σ₀Iter_zero (n : Nat) :
    σ₀Iter 0 (add_zero n) = 𝟙 _ := by
  ext
  simp [σ₀Iter]

@[simp]
/--
lemma `σ₀Iter_one` / 引理 `σ₀Iter_one`

English:
lemma σ₀Iter_one
  given: (n : Nat)
  statement: σ₀Iter 1 (n := n) rfl = σ 0
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  dsimp
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ
  · rw [σ₀Iter_coe_eq_of_lt _ _ _ (by simp), coe_σ,
      Fin.predAbove_of_le_castSucc _ _ (by simp)]
    dsimp
  · rw [σ₀Iter_coe_eq_of_ge .., coe_σ]
    simp

@[reassoc]

中文:
引理 σ₀Iter_one
  条件: (n : 自然数)
  结论: σ₀Iter 1 (n := n) rfl = σ 0
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  dsimp
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ
  · rw [σ₀Iter_coe_eq_of_lt _ _ _ (by simp), coe_σ,
      Fin.predAbove_of_le_castSucc _ _ (by simp)]
    dsimp
  · rw [σ₀Iter_coe_eq_of_ge .., coe_σ]
    simp

@[reassoc]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ext, Fin.predAbove_of_le_castSucc, eq_zero_or_eq_succ, hom_ext, k.eq_zero_or_eq_succ, predAbove_of_le_castSucc
-/
lemma σ₀Iter_one (n : Nat) : σ₀Iter 1 (n := n) rfl = σ 0 := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  dsimp
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_eq_succ
  · rw [σ₀Iter_coe_eq_of_lt _ _ _ (by simp), coe_σ,
      Fin.predAbove_of_le_castSucc _ _ (by simp)]
    dsimp
  · rw [σ₀Iter_coe_eq_of_ge .., coe_σ]
    simp

@[reassoc]
/--
lemma `σ₀Iter_succ` / 引理 `σ₀Iter_succ`

English:
lemma σ₀Iter_succ
  given: (i : Nat) {n m : Nat} (h : n + (i + 1) = m)
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (σ₀Iter i) (σ 0)]
  by_cases! hk : k.val <= i
  · rw [σ₀Iter_coe_eq_of_lt .., coe_σ]
    obtain hk | rfl := hk.lt_or_eq
    · grind [Fin.predAbove_of_le_castSucc, Fin.coe_castPred, σ₀Iter_coe_eq_of_lt]
    · grind [Fin.predAbove_of_le_castSucc, Fin.coe_castPred, σ₀Iter_coe_eq_of_ge, tsub_self]
  · rw [σ₀Iter_coe_eq_of_ge .., coe_σ,
      Fin.predAbove_of_castSucc_lt _ _ ?_, Fin.val_pred,
      σ₀Iter_coe_eq_of_ge .., Nat.sub_add_eq]
    rw [Fin.lt_def]; rw [Fin.castSucc_zero]; rw [σ₀Iter_coe_eq_of_ge ..]; rw [Fin.coe_ofNat_eq_mod]; rw [Nat.zero_mod]
    lia

@[reassoc]

中文:
引理 σ₀Iter_succ
  条件: (i : 自然数) {n m : 自然数} (h : n + (i + 1) = m)
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (σ₀Iter i) (σ 0)]
  by_cases! hk : k.val <= i
  · rw [σ₀Iter_coe_eq_of_lt .., coe_σ]
    obtain hk | rfl := hk.lt_or_eq
    · grind [Fin.predAbove_of_le_castSucc, Fin.coe_castPred, σ₀Iter_coe_eq_of_lt]
    · grind [Fin.predAbove_of_le_castSucc, Fin.coe_castPred, σ₀Iter_coe_eq_of_ge, tsub_self]
  · rw [σ₀Iter_coe_eq_of_ge .., coe_σ,
      Fin.predAbove_of_castSucc_lt _ _ ?_, Fin.val_pred,
      σ₀Iter_coe_eq_of_ge .., Nat.sub_add_eq]
    rw [Fin.lt_def]; rw [Fin.castSucc_zero]; rw [σ₀Iter_coe_eq_of_ge ..]; rw [Fin.coe_ofNat_eq_mod]; rw [Nat.zero_mod]
    lia

@[reassoc]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.hom_ext, Fin.coe_castPred, Fin.predAbove_of_castSucc_lt, Fin.predAbove_of_le_castSucc, Fin.val_pred, Nat.sub_add_e, coe_castPred, comp_apply, hk.lt_or_eq, hom_ext, k.val, lt_or_eq, predAbove_of_castSucc_lt, predAbove_of_le_castSucc, sub_add_e, tsub_self, val_pred
-/
lemma σ₀Iter_succ (i : Nat) {n m : Nat} (h : n + (i + 1) = m) :
    σ₀Iter (i + 1) h = σ₀Iter i ≫ σ 0 := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (σ₀Iter i) (σ 0)]
  by_cases! hk : k.val <= i
  · rw [σ₀Iter_coe_eq_of_lt .., coe_σ]
    obtain hk | rfl := hk.lt_or_eq
    · grind [Fin.predAbove_of_le_castSucc, Fin.coe_castPred, σ₀Iter_coe_eq_of_lt]
    · grind [Fin.predAbove_of_le_castSucc, Fin.coe_castPred, σ₀Iter_coe_eq_of_ge, tsub_self]
  · rw [σ₀Iter_coe_eq_of_ge .., coe_σ,
      Fin.predAbove_of_castSucc_lt _ _ ?_, Fin.val_pred,
      σ₀Iter_coe_eq_of_ge .., Nat.sub_add_eq]
    rw [Fin.lt_def]; rw [Fin.castSucc_zero]; rw [σ₀Iter_coe_eq_of_ge ..]; rw [Fin.coe_ofNat_eq_mod]; rw [Nat.zero_mod]
    lia

@[reassoc]
/--
lemma `σ₀Iter_succ'` / 引理 `σ₀Iter_succ'`

English:
lemma σ₀Iter_succ'
  given: (i : Nat) {n m : Nat} (h : n + i = m := by lia)
  proof: by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ]; rw [hi' (by lia)]; rw [σ₀Iter_succ]; rw [Category.assoc]

@[reassoc]

中文:
引理 σ₀Iter_succ'
  条件: (i : 自然数) {n m : 自然数} (h : n + i = m := by lia)
  证明: by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ]; rw [hi' (by lia)]; rw [σ₀Iter_succ]; rw [Category.assoc]

@[reassoc]

Depends on / 依赖: Category, Category.assoc, generalizing
-/
lemma σ₀Iter_succ' (i : Nat) {n m : Nat} (h : n + i = m := by lia) :
    σ₀Iter (i + 1) = σ 0 ≫ σ₀Iter i h := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ]; rw [hi' (by lia)]; rw [σ₀Iter_succ]; rw [Category.assoc]

@[reassoc]
/--
lemma `δ_σ₀Iter` / 引理 `δ_σ₀Iter`

English:
lemma δ_σ₀Iter
  statement: {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat} (h : m + (j + 1) = n + 1 := by lia)
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ i) (σ₀Iter (j + 1))]
  by_cases! hk : j <= k.val
  · rw [σ₀Iter_coe_eq_of_ge j .., coe_δ]
    by_cases! hk' : i <= k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_ge ..]
      simp
    · obtain rfl : j = k.val := by grind [dsimp% Fin.lt_def.1 hk']
      rw [Fin.succAbove_of_castSucc_lt _ _ (by lia)]; rw [σ₀Iter_coe_eq_of_lt ..]; rw [tsub_self]
  · rw [σ₀Iter_coe_eq_of_lt j .., coe_δ]
    by_cases! hk' : i <= k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_lt ..]
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by lia), σ₀Iter_coe_eq_of_lt ..]

@[reassoc]

中文:
引理 δ_σ₀Iter
  结论: {n : 自然数} (i : 有限集 (n + 2)) (j : 自然数) {m : 自然数} (h : m + (j + 1) = n + 1 := by lia)
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ i) (σ₀Iter (j + 1))]
  by_cases! hk : j <= k.val
  · rw [σ₀Iter_coe_eq_of_ge j .., coe_δ]
    by_cases! hk' : i <= k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_ge ..]
      simp
    · obtain rfl : j = k.val := by grind [dsimp% Fin.lt_def.1 hk']
      rw [Fin.succAbove_of_castSucc_lt _ _ (by lia)]; rw [σ₀Iter_coe_eq_of_lt ..]; rw [tsub_self]
  · rw [σ₀Iter_coe_eq_of_lt j .., coe_δ]
    by_cases! hk' : i <= k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_lt ..]
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by lia), σ₀Iter_coe_eq_of_lt ..]

@[reassoc]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.hom_ext, Fin.lt_def, Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc, castSucc, comp_apply, hom_ext, i.val, k.castSucc, k.val, lt_def, succAbove_of_castSucc_lt, succAbove_of_le_castSucc
-/
lemma δ_σ₀Iter {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat} (h : m + (j + 1) = n + 1 := by lia)
    (hi' : i.val <= j + 1 := by grind) :
    δ i ≫ σ₀Iter (j + 1) h = σ₀Iter j := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  dsimp
  rw [dsimp% ConcreteCategory.comp_apply (δ i) (σ₀Iter (j + 1))]
  by_cases! hk : j <= k.val
  · rw [σ₀Iter_coe_eq_of_ge j .., coe_δ]
    by_cases! hk' : i <= k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_ge ..]
      simp
    · obtain rfl : j = k.val := by grind [dsimp% Fin.lt_def.1 hk']
      rw [Fin.succAbove_of_castSucc_lt _ _ (by lia)]; rw [σ₀Iter_coe_eq_of_lt ..]; rw [tsub_self]
  · rw [σ₀Iter_coe_eq_of_lt j .., coe_δ]
    by_cases! hk' : i <= k.castSucc
    · rw [Fin.succAbove_of_le_castSucc _ _ hk', σ₀Iter_coe_eq_of_lt ..]
    · rw [Fin.succAbove_of_castSucc_lt _ _ (by lia), σ₀Iter_coe_eq_of_lt ..]

@[reassoc]
/--
lemma `δ_σ₀Iter'` / 引理 `δ_σ₀Iter'`

English:
lemma δ_σ₀Iter'
  statement: {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat}
  proof: by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : i = i' := by lia
    simp
  | succ j hj =>
    rw [σ₀Iter_succ _]; rw [σ₀Iter_succ_assoc _]; rw [reassoc_of% hj _ i'.succ (by lia) (by lia) (by grind)]; rw [dsimp% δ_comp_σ_of_gt (i := i') (j := 0)
        (by rw [Fin.lt_def]; dsimp; lia)]

@[reassoc]

中文:
引理 δ_σ₀Iter'
  结论: {n : 自然数} (i : 有限集 (n + 2)) (j : 自然数) {m : 自然数}
  证明: by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : i = i' := by lia
    simp
  | succ j hj =>
    rw [σ₀Iter_succ _]; rw [σ₀Iter_succ_assoc _]; rw [reassoc_of% hj _ i'.succ (by lia) (by lia) (by grind)]; rw [dsimp% δ_comp_σ_of_gt (i := i') (j := 0)
        (by rw [Fin.lt_def]; dsimp; lia)]

@[reassoc]

Depends on / 依赖: Fin.lt_def, generalizing, i.val, lt_def, reassoc_of
-/
lemma δ_σ₀Iter' {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat}
    (i' : Fin (m + 2)) (h : m + j = n := by lia)
    (hi' : j < i.val := by grind)
    (hi'' : i.val = i'.val + j := by grind) :
    δ i ≫ σ₀Iter (n := m + 1) j = σ₀Iter j ≫ δ i' := by
  induction j generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : i = i' := by lia
    simp
  | succ j hj =>
    rw [σ₀Iter_succ _]; rw [σ₀Iter_succ_assoc _]; rw [reassoc_of% hj _ i'.succ (by lia) (by lia) (by grind)]; rw [dsimp% δ_comp_σ_of_gt (i := i') (j := 0)
        (by rw [Fin.lt_def]; dsimp; lia)]

@[reassoc]
/--
lemma `σ_σ₀Iter` / 引理 `σ_σ₀Iter`

English:
lemma σ_σ₀Iter
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 1)) (hi : n + i = m := by lia)
  proof: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (σ j) (σ₀Iter i)]; rw [coe_σ]
  by_cases! hk : i < k.val
  · rw [σ₀Iter_coe_eq_of_ge (i + 1) ..,
      Fin.predAbove_of_castSucc_lt _ _ (by grind),
      σ₀Iter_coe_eq_of_ge ..]
    grind
  · rw [σ₀Iter_coe_eq_of_lt (i + 1) ..]
    rw [σ₀Iter_coe_eq_of_le _ _ _ ?_]
    by_cases! hk' : k <= j.castSucc
    · rwa [Fin.predAbove_of_le_castSucc _ _ (by lia)]
    · grind [Fin.predAbove]

@[reassoc]

中文:
引理 σ_σ₀Iter
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 1)) (hi : n + i = m := by lia)
  证明: by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (σ j) (σ₀Iter i)]; rw [coe_σ]
  by_cases! hk : i < k.val
  · rw [σ₀Iter_coe_eq_of_ge (i + 1) ..,
      Fin.predAbove_of_castSucc_lt _ _ (by grind),
      σ₀Iter_coe_eq_of_ge ..]
    grind
  · rw [σ₀Iter_coe_eq_of_lt (i + 1) ..]
    rw [σ₀Iter_coe_eq_of_le _ _ _ ?_]
    by_cases! hk' : k <= j.castSucc
    · rwa [Fin.predAbove_of_le_castSucc _ _ (by lia)]
    · grind [Fin.predAbove]

@[reassoc]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.hom_ext, Fin.predAbove_of_castSucc_lt, Fin.predAbove_of_le_castSucc, castSucc, comp_apply, hom_ext, j.castSucc, j.val, k.val, predAbove_of_castSucc_lt, predAbove_of_le_castSucc
-/
lemma σ_σ₀Iter (i : Nat) {n m : Nat} (j : Fin (m + 1)) (hi : n + i = m := by lia)
    (hj : j.val <= i := by grind) :
    σ j ≫ σ₀Iter i hi = σ₀Iter (i + 1) := by
  refine ConcreteCategory.hom_ext _ _ (fun k => ?_)
  ext
  rw [dsimp% ConcreteCategory.comp_apply (σ j) (σ₀Iter i)]; rw [coe_σ]
  by_cases! hk : i < k.val
  · rw [σ₀Iter_coe_eq_of_ge (i + 1) ..,
      Fin.predAbove_of_castSucc_lt _ _ (by grind),
      σ₀Iter_coe_eq_of_ge ..]
    grind
  · rw [σ₀Iter_coe_eq_of_lt (i + 1) ..]
    rw [σ₀Iter_coe_eq_of_le _ _ _ ?_]
    by_cases! hk' : k <= j.castSucc
    · rwa [Fin.predAbove_of_le_castSucc _ _ (by lia)]
    · grind [Fin.predAbove]

@[reassoc]
/--
lemma `σ_σ₀Iter'` / 引理 `σ_σ₀Iter'`

English:
lemma σ_σ₀Iter'
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 1)) (j' : Fin (n + 1))
  proof: by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : j = j' := by lia
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ]; rw [σ₀Iter_succ_assoc]; rw [reassoc_of% hi' _ j'.succ (by lia) (by grind)]; rw [← σ_comp_σ (by simp)]; rw [Fin.castSucc_zero]

@[reassoc (attr := simp)]

中文:
引理 σ_σ₀Iter'
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 1)) (j' : 有限集 (n + 1))
  证明: by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : j = j' := by lia
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ]; rw [σ₀Iter_succ_assoc]; rw [reassoc_of% hi' _ j'.succ (by lia) (by grind)]; rw [← σ_comp_σ (by simp)]; rw [Fin.castSucc_zero]

@[reassoc (attr := simp)]

Depends on / 依赖: Fin.castSucc_zero, castSucc_zero, generalizing, j.val, reassoc_of
-/
lemma σ_σ₀Iter' (i : Nat) {n m : Nat} (j : Fin (m + 1)) (j' : Fin (n + 1))
    (hi : n + i = m := by lia)
    (hj : j.val = j'.val + i := by grind) :
    σ j ≫ σ₀Iter i hi = σ₀Iter i ≫ σ j' := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    obtain rfl : j = j' := by lia
    simp
  | succ i hi' =>
    rw [σ₀Iter_succ]; rw [σ₀Iter_succ_assoc]; rw [reassoc_of% hi' _ j'.succ (by lia) (by grind)]; rw [← σ_comp_σ (by simp)]; rw [Fin.castSucc_zero]

@[reassoc (attr := simp)]
/--
lemma `δ₀Iter_σ₀Iter` / 引理 `δ₀Iter_σ₀Iter`

English:
lemma δ₀Iter_σ₀Iter
  given: (i : Nat) {n m : Nat} (hi : n + i = m := by lia)
  proof: by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    simp
  | succ i hi' =>
    obtain rfl : m = (n + i) + 1 := by lia
    rw [δ₀Iter_succ_assoc ..]; rw [σ₀Iter_succ']; rw [dsimp% reassoc_of% δ_comp_σ_self (n := n + i) (i := 0)]; rw [hi']

中文:
引理 δ₀Iter_σ₀Iter
  条件: (i : 自然数) {n m : 自然数} (hi : n + i = m := by lia)
  证明: by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    simp
  | succ i hi' =>
    obtain rfl : m = (n + i) + 1 := by lia
    rw [δ₀Iter_succ_assoc ..]; rw [σ₀Iter_succ']; rw [dsimp% reassoc_of% δ_comp_σ_self (n := n + i) (i := 0)]; rw [hi']

Depends on / 依赖: generalizing, reassoc_of
-/
lemma δ₀Iter_σ₀Iter (i : Nat) {n m : Nat} (hi : n + i = m := by lia) :
    δ₀Iter i hi ≫ σ₀Iter i hi = 𝟙 _ := by
  induction i generalizing n m with
  | zero =>
    obtain rfl : n = m := by lia
    simp
  | succ i hi' =>
    obtain rfl : m = (n + i) + 1 := by lia
    rw [δ₀Iter_succ_assoc ..]; rw [σ₀Iter_succ']; rw [dsimp% reassoc_of% δ_comp_σ_self (n := n + i) (i := 0)]; rw [hi']

instance (i : Nat) {n m : Nat} (hi : n + i = m) : Mono (δ₀Iter i hi) :=
  mono_of_mono_fac (δ₀Iter_σ₀Iter i hi)

instance (i : Nat) {n m : Nat} (hi : n + i = m) : Epi (σ₀Iter i hi) :=
  epi_of_epi_fac (δ₀Iter_σ₀Iter i hi)

end SimplexCategory
