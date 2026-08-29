/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.DeltaZeroIter
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Iterations of `δ 0` and `σ 0`

This file introduces morphisms `δ₀Iter i` and `σ₀Iter i` for simplicial objects:
they are obtained as the `i`th iteration of `δ 0` or `σ 0`.

-/

@[expose] public section

open Simplicial Opposite

namespace CategoryTheory.SimplicialObject

variable {C : Type*} [Category* C] (X : SimplicialObject C)

/--
Definition of `δ₀Iter` / `δ₀Iter` 的定义

English:
definition δ₀Iter
  signature: {n m : Nat} (i : Nat) (hi : n + i = m := by lia)
  body: X.map (SimplexCategory.δ₀Iter i hi).op

@[simp]

中文:
定义 δ₀Iter
  签名: {n m : 自然数} (i : 自然数) (hi : n + i = m := by lia)
  定义体: X.map (SimplexCategory.δ₀Iter i hi).op

@[simp]

Depends on / 依赖: SimplexCategory, X.map
-/
def δ₀Iter {n m : Nat} (i : Nat) (hi : n + i = m := by lia) :
    X _⦋m⦌ ⟶ X _⦋n⦌ :=
  X.map (SimplexCategory.δ₀Iter i hi).op

@[simp]
/--
lemma `δ₀Iter_zero` / 引理 `δ₀Iter_zero`

English:
lemma δ₀Iter_zero
  given: (n : Nat)
  statement: X.δ₀Iter 0 (add_zero n) = 𝟙 _
  proof: by
  simp [δ₀Iter]

@[simp]

中文:
引理 δ₀Iter_zero
  条件: (n : 自然数)
  结论: X.δ₀Iter 0 (add_zero n) = 𝟙 _
  证明: by
  simp [δ₀Iter]

@[simp]
-/
lemma δ₀Iter_zero (n : Nat) : X.δ₀Iter 0 (add_zero n) = 𝟙 _ := by
  simp [δ₀Iter]

@[simp]
/--
lemma `δ₀Iter_one` / 引理 `δ₀Iter_one`

English:
lemma δ₀Iter_one
  given: (n : Nat)
  statement: X.δ₀Iter 1 (n := n) rfl = X.δ 0
  proof: rfl

@[reassoc]

中文:
引理 δ₀Iter_one
  条件: (n : 自然数)
  结论: X.δ₀Iter 1 (n := n) rfl = X.δ 0
  证明: rfl

@[reassoc]
-/
lemma δ₀Iter_one (n : Nat) : X.δ₀Iter 1 (n := n) rfl = X.δ 0 := rfl

@[reassoc]
/--
lemma `δ₀Iter_succ` / 引理 `δ₀Iter_succ`

English:
lemma δ₀Iter_succ
  given: (i : Nat) {n m : Nat} (h : n + i = m := by lia)
  proof: by
  simp [δ₀Iter, SimplexCategory.δ₀Iter_succ _ h, δ_def]

@[reassoc]

中文:
引理 δ₀Iter_succ
  条件: (i : 自然数) {n m : 自然数} (h : n + i = m := by lia)
  证明: by
  simp [δ₀Iter, SimplexCategory.δ₀Iter_succ _ h, δ_def]

@[reassoc]

Depends on / 依赖: SimplexCategory
-/
lemma δ₀Iter_succ (i : Nat) {n m : Nat} (h : n + i = m := by lia) :
    X.δ₀Iter (i + 1) = X.δ 0 ≫ X.δ₀Iter i h := by
  simp [δ₀Iter, SimplexCategory.δ₀Iter_succ _ h, δ_def]

@[reassoc]
/--
lemma `δ₀Iter_succ'` / 引理 `δ₀Iter_succ'`

English:
lemma δ₀Iter_succ'
  given: (i : Nat) {n m : Nat} (h : n + (i + 1) = m := by lia)
  proof: by
  dsimp [δ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_succ' _ h]

@[reassoc]

中文:
引理 δ₀Iter_succ'
  条件: (i : 自然数) {n m : 自然数} (h : n + (i + 1) = m := by lia)
  证明: by
  dsimp [δ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_succ' _ h]

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, map_comp, op_comp
-/
lemma δ₀Iter_succ' (i : Nat) {n m : Nat} (h : n + (i + 1) = m := by lia) :
    X.δ₀Iter (i + 1) h = X.δ₀Iter i ≫ X.δ 0 := by
  dsimp [δ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_succ' _ h]

@[reassoc]
/--
lemma `δ_δ₀Iter` / 引理 `δ_δ₀Iter`

English:
lemma δ_δ₀Iter
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 2))
  proof: by
  dsimp [δ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_δ ..]

@[reassoc]

中文:
引理 δ_δ₀Iter
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 2))
  证明: by
  dsimp [δ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_δ ..]

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, j.val, map_comp, op_comp
-/
lemma δ_δ₀Iter (i : Nat) {n m : Nat} (j : Fin (m + 2))
    (hi : n + i = m := by lia) (hj : j.val <= i := by grind) :
    X.δ j ≫ X.δ₀Iter i hi = X.δ₀Iter (i + 1) := by
  dsimp [δ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_δ ..]

@[reassoc]
/--
lemma `δ_δ₀Iter'` / 引理 `δ_δ₀Iter'`

English:
lemma δ_δ₀Iter'
  statement: {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat}
  proof: by
  dsimp [δ, δ₀Iter]
  simp only [← Functor.map_comp, ← op_comp, SimplexCategory.δ₀Iter_δ' _ _ _ _ hi'']

@[reassoc]

中文:
引理 δ_δ₀Iter'
  结论: {n : 自然数} (i : 有限集 (n + 2)) (j : 自然数) {m : 自然数}
  证明: by
  dsimp [δ, δ₀Iter]
  simp only [← Functor.map_comp, ← op_comp, SimplexCategory.δ₀Iter_δ' _ _ _ _ hi'']

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, i.val, map_comp, op_comp
-/
lemma δ_δ₀Iter' {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat}
    (i' : Fin (m + 2)) (h : n + j = m := by lia)
    (hi'' : i'.val = i.val + j := by grind) :
    X.δ i' ≫ X.δ₀Iter j = X.δ₀Iter j ≫ X.δ i := by
  dsimp [δ, δ₀Iter]
  simp only [← Functor.map_comp, ← op_comp, SimplexCategory.δ₀Iter_δ' _ _ _ _ hi'']

@[reassoc]
/--
lemma `σ_δ₀Iter` / 引理 `σ_δ₀Iter`

English:
lemma σ_δ₀Iter
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 1))
  proof: by
  dsimp [σ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_σ ..]

@[reassoc]

中文:
引理 σ_δ₀Iter
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 1))
  证明: by
  dsimp [σ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_σ ..]

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, j.val, map_comp, op_comp
-/
lemma σ_δ₀Iter (i : Nat) {n m : Nat} (j : Fin (m + 1))
    (hi : n + (i + 1) = m + 1 := by lia)
    (hj : j.val <= i := by grind) :
    X.σ j ≫ X.δ₀Iter (i + 1) hi = X.δ₀Iter i := by
  dsimp [σ, δ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.δ₀Iter_σ ..]

@[reassoc]
/--
lemma `σ_δ₀Iter'` / 引理 `σ_δ₀Iter'`

English:
lemma σ_δ₀Iter'
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 1)) (j' : Fin (n + 1))
  proof: by
  simp [σ, δ₀Iter, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ₀Iter_σ' i j j']

中文:
引理 σ_δ₀Iter'
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 1)) (j' : 有限集 (n + 1))
  证明: by
  simp [σ, δ₀Iter, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ₀Iter_σ' i j j']

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, j.val, map_comp, op_comp
-/
lemma σ_δ₀Iter' (i : Nat) {n m : Nat} (j : Fin (m + 1)) (j' : Fin (n + 1))
    (hi' : n + i = m := by lia)
    (hj' : j.val = j'.val + i := by grind) :
    X.σ j ≫ X.δ₀Iter i = X.δ₀Iter i hi' ≫ X.σ j' := by
  simp [σ, δ₀Iter, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ₀Iter_σ' i j j']

/--
Definition of `σ₀Iter` / `σ₀Iter` 的定义

English:
definition σ₀Iter
  signature: {n m : Nat} (i : Nat) (hi : n + i = m := by lia)
  body: X.map (SimplexCategory.σ₀Iter i hi).op

@[simp]

中文:
定义 σ₀Iter
  签名: {n m : 自然数} (i : 自然数) (hi : n + i = m := by lia)
  定义体: X.map (SimplexCategory.σ₀Iter i hi).op

@[simp]

Depends on / 依赖: SimplexCategory, X.map
-/
def σ₀Iter {n m : Nat} (i : Nat) (hi : n + i = m := by lia) :
    X _⦋n⦌ ⟶ X _⦋m⦌ :=
  X.map (SimplexCategory.σ₀Iter i hi).op

@[simp]
/--
lemma `σ₀Iter_zero` / 引理 `σ₀Iter_zero`

English:
lemma σ₀Iter_zero
  given: (n : Nat)
  statement: X.σ₀Iter 0 (add_zero n) = 𝟙 _
  proof: by
  simp [σ₀Iter]

@[simp]

中文:
引理 σ₀Iter_zero
  条件: (n : 自然数)
  结论: X.σ₀Iter 0 (add_zero n) = 𝟙 _
  证明: by
  simp [σ₀Iter]

@[simp]
-/
lemma σ₀Iter_zero (n : Nat) : X.σ₀Iter 0 (add_zero n) = 𝟙 _ := by
  simp [σ₀Iter]

@[simp]
/--
lemma `σ₀Iter_one` / 引理 `σ₀Iter_one`

English:
lemma σ₀Iter_one
  given: (n : Nat)
  statement: X.σ₀Iter 1 (n := n) rfl = X.σ 0
  proof: by
  simp [σ₀Iter, σ_def]

@[reassoc]

中文:
引理 σ₀Iter_one
  条件: (n : 自然数)
  结论: X.σ₀Iter 1 (n := n) rfl = X.σ 0
  证明: by
  simp [σ₀Iter, σ_def]

@[reassoc]
-/
lemma σ₀Iter_one (n : Nat) : X.σ₀Iter 1 (n := n) rfl = X.σ 0 := by
  simp [σ₀Iter, σ_def]

@[reassoc]
/--
lemma `σ₀Iter_succ` / 引理 `σ₀Iter_succ`

English:
lemma σ₀Iter_succ
  given: (i : Nat) {n m : Nat} (h : n + (i + 1) = m := by lia)
  proof: by
  dsimp [σ, σ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.σ₀Iter_succ ..]

@[reassoc]

中文:
引理 σ₀Iter_succ
  条件: (i : 自然数) {n m : 自然数} (h : n + (i + 1) = m := by lia)
  证明: by
  dsimp [σ, σ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.σ₀Iter_succ ..]

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, map_comp, op_comp
-/
lemma σ₀Iter_succ (i : Nat) {n m : Nat} (h : n + (i + 1) = m := by lia) :
    X.σ₀Iter (i + 1) h = X.σ 0 ≫ X.σ₀Iter i := by
  dsimp [σ, σ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.σ₀Iter_succ ..]

@[reassoc]
/--
lemma `σ₀Iter_succ'` / 引理 `σ₀Iter_succ'`

English:
lemma σ₀Iter_succ'
  given: (i : Nat) {n m : Nat} (h : n + i = m := by lia)
  proof: by
  simp [σ₀Iter, SimplexCategory.σ₀Iter_succ' _ h, σ_def]

@[reassoc]

中文:
引理 σ₀Iter_succ'
  条件: (i : 自然数) {n m : 自然数} (h : n + i = m := by lia)
  证明: by
  simp [σ₀Iter, SimplexCategory.σ₀Iter_succ' _ h, σ_def]

@[reassoc]

Depends on / 依赖: SimplexCategory
-/
lemma σ₀Iter_succ' (i : Nat) {n m : Nat} (h : n + i = m := by lia) :
    X.σ₀Iter (i + 1) = X.σ₀Iter i h ≫ X.σ 0 := by
  simp [σ₀Iter, SimplexCategory.σ₀Iter_succ' _ h, σ_def]

@[reassoc]
/--
lemma `σ₀Iter_δ` / 引理 `σ₀Iter_δ`

English:
lemma σ₀Iter_δ
  statement: {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat} (h : m + (j + 1) = n + 1 := by lia)
  proof: by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp, SimplexCategory.δ_σ₀Iter i j h]

@[reassoc]

中文:
引理 σ₀Iter_δ
  结论: {n : 自然数} (i : 有限集 (n + 2)) (j : 自然数) {m : 自然数} (h : m + (j + 1) = n + 1 := by lia)
  证明: by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp, SimplexCategory.δ_σ₀Iter i j h]

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, i.val, map_comp, op_comp
-/
lemma σ₀Iter_δ {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat} (h : m + (j + 1) = n + 1 := by lia)
    (hi' : i.val <= j + 1 := by grind) :
    X.σ₀Iter (n := m) (j + 1) h ≫ X.δ i = X.σ₀Iter j := by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp, SimplexCategory.δ_σ₀Iter i j h]

@[reassoc]
/--
lemma `σ₀Iter_δ'` / 引理 `σ₀Iter_δ'`

English:
lemma σ₀Iter_δ'
  statement: {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat}
  proof: by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ_σ₀Iter' i j i']

@[reassoc]

中文:
引理 σ₀Iter_δ'
  结论: {n : 自然数} (i : 有限集 (n + 2)) (j : 自然数) {m : 自然数}
  证明: by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ_σ₀Iter' i j i']

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, i.val, map_comp, op_comp
-/
lemma σ₀Iter_δ' {n : Nat} (i : Fin (n + 2)) (j : Nat) {m : Nat}
    (i' : Fin (m + 2)) (h : m + j = n := by lia)
    (hi' : j < i.val := by grind)
    (hi'' : i.val = i'.val + j := by grind) :
    X.σ₀Iter (n := m + 1) j ≫ X.δ i = X.δ i' ≫ X.σ₀Iter j := by
  simp only [σ₀Iter, δ, ← Functor.map_comp, ← op_comp,
    SimplexCategory.δ_σ₀Iter' i j i']

@[reassoc]
/--
lemma `σ₀Iter_σ` / 引理 `σ₀Iter_σ`

English:
lemma σ₀Iter_σ
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 1)) (hi : n + i = m := by lia)
  proof: by
  dsimp [σ, σ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.σ_σ₀Iter ..]

@[reassoc]

中文:
引理 σ₀Iter_σ
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 1)) (hi : n + i = m := by lia)
  证明: by
  dsimp [σ, σ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.σ_σ₀Iter ..]

@[reassoc]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, j.val, map_comp, op_comp
-/
lemma σ₀Iter_σ (i : Nat) {n m : Nat} (j : Fin (m + 1)) (hi : n + i = m := by lia)
    (hj : j.val <= i := by grind) :
    X.σ₀Iter i hi ≫ X.σ j = X.σ₀Iter (i + 1) := by
  dsimp [σ, σ₀Iter]
  rw [← Functor.map_comp]; rw [← op_comp]; rw [SimplexCategory.σ_σ₀Iter ..]

@[reassoc]
/--
lemma `σ₀Iter_σ'` / 引理 `σ₀Iter_σ'`

English:
lemma σ₀Iter_σ'
  statement: (i : Nat) {n m : Nat} (j : Fin (m + 1)) (j' : Fin (n + 1))
  proof: by
  simp [σ, σ₀Iter, ← Functor.map_comp, ← op_comp,
    SimplexCategory.σ_σ₀Iter' i j j']

@[reassoc (attr := simp)]

中文:
引理 σ₀Iter_σ'
  结论: (i : 自然数) {n m : 自然数} (j : 有限集 (m + 1)) (j' : 有限集 (n + 1))
  证明: by
  simp [σ, σ₀Iter, ← Functor.map_comp, ← op_comp,
    SimplexCategory.σ_σ₀Iter' i j j']

@[reassoc (attr := simp)]

Depends on / 依赖: Functor, Functor.map_comp, SimplexCategory, j.val, map_comp, op_comp
-/
lemma σ₀Iter_σ' (i : Nat) {n m : Nat} (j : Fin (m + 1)) (j' : Fin (n + 1))
    (hi : n + i = m := by lia)
    (hj : j.val = j'.val + i := by grind) :
    X.σ₀Iter i hi ≫ X.σ j = X.σ j' ≫ X.σ₀Iter i := by
  simp [σ, σ₀Iter, ← Functor.map_comp, ← op_comp,
    SimplexCategory.σ_σ₀Iter' i j j']

@[reassoc (attr := simp)]
/--
lemma `σ₀Iter_δ₀Iter` / 引理 `σ₀Iter_δ₀Iter`

English:
lemma σ₀Iter_δ₀Iter
  given: (i : Nat) {n m : Nat} (hi : n + i = m := by lia)
  proof: by
  simp [σ₀Iter, δ₀Iter, ← Functor.map_comp, ← op_comp]

中文:
引理 σ₀Iter_δ₀Iter
  条件: (i : 自然数) {n m : 自然数} (hi : n + i = m := by lia)
  证明: by
  simp [σ₀Iter, δ₀Iter, ← Functor.map_comp, ← op_comp]

Depends on / 依赖: Functor, Functor.map_comp, map_comp, op_comp
-/
lemma σ₀Iter_δ₀Iter (i : Nat) {n m : Nat} (hi : n + i = m := by lia) :
    X.σ₀Iter i hi ≫ X.δ₀Iter i hi = 𝟙 _ := by
  simp [σ₀Iter, δ₀Iter, ← Functor.map_comp, ← op_comp]

instance (i : Nat) {n m : Nat} (hi : n + i = m) : Mono (X.σ₀Iter i hi) :=
  mono_of_mono_fac (X.σ₀Iter_δ₀Iter i hi)

instance (i : Nat) {n m : Nat} (hi : n + i = m) : Epi (X.δ₀Iter i hi) :=
  epi_of_epi_fac (X.σ₀Iter_δ₀Iter i hi)

namespace Augmented

variable (Y : Augmented C)

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `δ₀Iter_hom_app` / 引理 `δ₀Iter_hom_app`

English:
lemma δ₀Iter_hom_app
  given: {n m : Nat} (i : Nat) (hi : n + i = m := by lia)
  proof: by
  simpa only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using!
    Y.hom.naturality (SimplexCategory.δ₀Iter i hi).op

中文:
引理 δ₀Iter_hom_app
  条件: {n m : 自然数} (i : 自然数) (hi : n + i = m := by lia)
  证明: by
  simpa only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using!
    Y.hom.naturality (SimplexCategory.δ₀Iter i hi).op

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.const_obj_map, Functor.const_obj_obj, Functor.id_obj, SimplexCategory, Y.hom.app, Y.hom.naturality, Y.left, comp_id, const_obj_map, const_obj_obj, id_obj, naturality
-/
lemma δ₀Iter_hom_app {n m : Nat} (i : Nat) (hi : n + i = m := by lia) :
    dsimp% Y.left.δ₀Iter i hi ≫ Y.hom.app (op ⦋n⦌) = Y.hom.app (op ⦋m⦌) := by
  simpa only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using!
    Y.hom.naturality (SimplexCategory.δ₀Iter i hi).op

set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/--
lemma `σ₀Iter_hom_app` / 引理 `σ₀Iter_hom_app`

English:
lemma σ₀Iter_hom_app
  given: {n m : Nat} (i : Nat) (hi : n + i = m := by lia)
  proof: by
  simpa only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using!
    Y.hom.naturality (SimplexCategory.σ₀Iter i hi).op

中文:
引理 σ₀Iter_hom_app
  条件: {n m : 自然数} (i : 自然数) (hi : n + i = m := by lia)
  证明: by
  simpa only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using!
    Y.hom.naturality (SimplexCategory.σ₀Iter i hi).op

Depends on / 依赖: Category, Category.comp_id, Functor, Functor.const_obj_map, Functor.const_obj_obj, Functor.id_obj, SimplexCategory, Y.hom.app, Y.hom.naturality, Y.left, comp_id, const_obj_map, const_obj_obj, id_obj, naturality
-/
lemma σ₀Iter_hom_app {n m : Nat} (i : Nat) (hi : n + i = m := by lia) :
    dsimp% Y.left.σ₀Iter i hi ≫ Y.hom.app (op ⦋m⦌) = Y.hom.app (op ⦋n⦌) := by
  simpa only [Functor.id_obj, Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] using!
    Y.hom.naturality (SimplexCategory.σ₀Iter i hi).op

end Augmented

end CategoryTheory.SimplicialObject
