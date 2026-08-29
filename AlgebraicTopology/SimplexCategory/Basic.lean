/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz, Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.Data.Fintype.Sort
public import Mathlib.Order.Category.NonemptyFinLinOrd
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-! # Basic properties of the simplex category

In `Mathlib/AlgebraicTopology/SimplexCategory/Defs.lean`, we define the simplex
category with objects `ℕ` and morphisms `n ⟶ m` the monotone maps from
`Fin (n + 1)` to `Fin (m + 1)`.

In this file, we define the generating maps for the simplex category, show that
this category is equivalent to `NonemptyFinLinOrd`, and establish basic
properties of its epimorphisms and monomorphisms.
-/

@[expose] public section

universe u

open Simplicial CategoryTheory Limits

namespace SimplexCategory

instance {a b : SimplexCategory} : Finite (a ⟶ b) :=
  Finite.of_injective (fun f => f.toOrderHom.toFun)
    (fun _ _ _ => by aesop)

instance {n m : SimplexCategory} : DecidableEq (n ⟶ m) := fun a b =>
  decidable_of_iff (a.toOrderHom = b.toOrderHom) SimplexCategory.Hom.ext_iff.symm

section Init

/--
lemma `congr_toOrderHom_apply` / 引理 `congr_toOrderHom_apply`

English:
lemma congr_toOrderHom_apply
  statement: {a b : SimplexCategory} {f g : a ⟶ b} (h : f = g)
  proof: by rw [h]

中文:
引理 congr_toOrderHom_apply
  结论: {a b : SimplexCategory} {f g : a ⟶ b} (h : f = g)
  证明: by rw [h]
-/
lemma congr_toOrderHom_apply {a b : SimplexCategory} {f g : a ⟶ b} (h : f = g)
    (x : Fin (a.len + 1)) : f.toOrderHom x = g.toOrderHom x := by rw [h]

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (x y : SimplexCategory) (i : Fin (y.len + 1))
  body: Hom.mk ⟨fun _ => i, by tauto⟩

@[simp]

中文:
定义 const
  签名: (x y : SimplexCategory) (i : Fin (y.len + 1))
  定义体: Hom.mk ⟨fun _ => i, by tauto⟩

@[simp]

Depends on / 依赖: Hom.mk
-/
def const (x y : SimplexCategory) (i : Fin (y.len + 1)) : x ⟶ y :=
Hom.mk ⟨fun _ => i, by tauto⟩

@[simp]
/--
lemma `const_eq_id` / 引理 `const_eq_id`

English:
lemma const_eq_id
  statement: const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _
  proof: by aesop

@[simp]

中文:
引理 const_eq_id
  结论: const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _
  证明: by aesop

@[simp]
-/
lemma const_eq_id : const ⦋0⦌ ⦋0⦌ 0 = 𝟙 _ := by aesop

@[simp]
/--
lemma `const_apply` / 引理 `const_apply`

English:
lemma const_apply
  given: (x y : SimplexCategory) (i : Fin (y.len + 1)) (a : Fin (x.len + 1))
  proof: rfl

@[simp]

中文:
引理 const_apply
  条件: (x y : SimplexCategory) (i : Fin (y.len + 1)) (a : Fin (x.len + 1))
  证明: rfl

@[simp]
-/
lemma const_apply (x y : SimplexCategory) (i : Fin (y.len + 1)) (a : Fin (x.len + 1)) :
    (const x y i).toOrderHom a = i := rfl

@[simp]
/--
theorem `const_comp` / 定理 `const_comp`

English:
theorem const_comp
  statement: (x : SimplexCategory) {y z : SimplexCategory}
  proof: rfl

中文:
定理 const_comp
  结论: (x : SimplexCategory) {y z : SimplexCategory}
  证明: rfl
-/
theorem const_comp (x : SimplexCategory) {y z : SimplexCategory}
    (f : y ⟶ z) (i : Fin (y.len + 1)) :
    const x y i ≫ f = const x z (f.toOrderHom i) :=
  rfl

/--
theorem `const_fac_thru_zero` / 定理 `const_fac_thru_zero`

English:
theorem const_fac_thru_zero
  given: (n m : SimplexCategory) (i : Fin (m.len + 1))
  proof: by
  rw [const_comp]; rfl

中文:
定理 const_fac_thru_zero
  条件: (n m : SimplexCategory) (i : Fin (m.len + 1))
  证明: by
  rw [const_comp]; rfl

Depends on / 依赖: const_comp
-/
theorem const_fac_thru_zero (n m : SimplexCategory) (i : Fin (m.len + 1)) :
    const n m i = const n ⦋0⦌ 0 ≫ SimplexCategory.const ⦋0⦌ m i := by
  rw [const_comp]; rfl

/--
theorem `Hom.ext_zero_left` / 定理 `Hom.ext_zero_left`

English:
theorem Hom.ext_zero_left
  statement: {n : SimplexCategory} (f g : ⦋0⦌ ⟶ n)
  proof: by
  ext i; match i with | 0 => exact h0 ▸ rfl

中文:
定理 Hom.ext_zero_left
  结论: {n : SimplexCategory} (f g : ⦋0⦌ ⟶ n)
  证明: by
  ext i; match i with | 0 => exact h0 ▸ rfl
-/
theorem Hom.ext_zero_left {n : SimplexCategory} (f g : ⦋0⦌ ⟶ n)
    (h0 : f.toOrderHom 0 = g.toOrderHom 0 := by rfl) : f = g := by
  ext i; match i with | 0 => exact h0 ▸ rfl

/--
theorem `eq_const_of_zero` / 定理 `eq_const_of_zero`

English:
theorem eq_const_of_zero
  given: {n : SimplexCategory} (f : ⦋0⦌ ⟶ n)
  proof: by
  ext x; match x with | 0 => rfl

中文:
定理 eq_const_of_zero
  条件: {n : SimplexCategory} (f : ⦋0⦌ ⟶ n)
  证明: by
  ext x; match x with | 0 => rfl
-/
theorem eq_const_of_zero {n : SimplexCategory} (f : ⦋0⦌ ⟶ n) :
    f = const _ n (f.toOrderHom 0) := by
  ext x; match x with | 0 => rfl

/--
theorem `exists_eq_const_of_zero` / 定理 `exists_eq_const_of_zero`

English:
theorem exists_eq_const_of_zero
  given: {n : SimplexCategory} (f : ⦋0⦌ ⟶ n)
  proof: ⟨_, eq_const_of_zero _⟩

中文:
定理 exists_eq_const_of_zero
  条件: {n : SimplexCategory} (f : ⦋0⦌ ⟶ n)
  证明: ⟨_, eq_const_of_zero _⟩

Depends on / 依赖: eq_const_of_zero
-/
theorem exists_eq_const_of_zero {n : SimplexCategory} (f : ⦋0⦌ ⟶ n) :
    exists a, f = const _ n a := ⟨_, eq_const_of_zero _⟩

/--
theorem `eq_const_to_zero` / 定理 `eq_const_to_zero`

English:
theorem eq_const_to_zero
  given: {n : SimplexCategory} (f : n ⟶ ⦋0⦌)
  proof: by
  ext : 3
  apply @Subsingleton.elim (Fin 1)

中文:
定理 eq_const_to_zero
  条件: {n : SimplexCategory} (f : n ⟶ ⦋0⦌)
  证明: by
  ext : 3
  apply @Subsingleton.elim (Fin 1)

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem eq_const_to_zero {n : SimplexCategory} (f : n ⟶ ⦋0⦌) :
    f = const n _ 0 := by
  ext : 3
  apply @Subsingleton.elim (Fin 1)

/--
theorem `Hom.ext_one_left` / 定理 `Hom.ext_one_left`

English:
theorem Hom.ext_one_left
  statement: {n : SimplexCategory} (f g : ⦋1⦌ ⟶ n)
  proof: by
  ext i
  match i with
  | 0 => exact h0 ▸ rfl
  | 1 => exact h1 ▸ rfl

中文:
定理 Hom.ext_one_left
  结论: {n : SimplexCategory} (f g : ⦋1⦌ ⟶ n)
  证明: by
  ext i
  match i with
  | 0 => exact h0 ▸ rfl
  | 1 => exact h1 ▸ rfl

Depends on / 依赖: f.toOrderHom, g.toOrderHom, toOrderHom
-/
theorem Hom.ext_one_left {n : SimplexCategory} (f g : ⦋1⦌ ⟶ n)
    (h0 : f.toOrderHom 0 = g.toOrderHom 0 := by rfl)
    (h1 : f.toOrderHom 1 = g.toOrderHom 1 := by rfl) : f = g := by
  ext i
  match i with
  | 0 => exact h0 ▸ rfl
  | 1 => exact h1 ▸ rfl

/--
theorem `eq_of_one_to_one` / 定理 `eq_of_one_to_one`

English:
theorem eq_of_one_to_one
  given: (f : ⦋1⦌ ⟶ ⦋1⦌)
  proof: by
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 0, 0 | 1, 1 =>
    refine .inl ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 0, 1 =>
    right
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 1, 0 =>
  

中文:
定理 eq_of_one_to_one
  条件: (f : ⦋1⦌ ⟶ ⦋1⦌)
  证明: by
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 0, 0 | 1, 1 =>
    refine .inl ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 0, 1 =>
    right
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 1, 0 =>
  

Depends on / 依赖: Not.elim, e0.symm, e1.trans, f.toOrderHom, f.toOrderHom.monotone, monotone, toOrderHom
-/
theorem eq_of_one_to_one (f : ⦋1⦌ ⟶ ⦋1⦌) :
    (exists a, f = const ⦋1⦌ _ a) ∨ f = 𝟙 _ := by
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 0, 0 | 1, 1 =>
    refine .inl ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 0, 1 =>
    right
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 1, 0 =>
    have := f.toOrderHom.monotone (by decide : (0 : Fin 2) <= 1)
    rw [e0]; rw [e1] at this
    exact Not.elim (by decide) this

/-- Make a morphism `⦋n⦌ ⟶ ⦋m⦌` from a monotone map between fin's.
This is useful for constructing morphisms between `⦋n⦌` directly
without identifying `n` with `⦋n⦌.len`.
-/
@[simp]
/--
Definition of `mkHom` / `mkHom` 的定义

English:
definition mkHom
  signature: {n m : Nat} (f : Fin (n + 1) ->o Fin (m + 1))
  body: SimplexCategory.Hom.mk f

中文:
定义 mkHom
  签名: {n m : 自然数} (f : Fin (n + 1) ->o Fin (m + 1))
  定义体: SimplexCategory.Hom.mk f

Depends on / 依赖: SimplexCategory, SimplexCategory.Hom.mk
-/
def mkHom {n m : Nat} (f : Fin (n + 1) ->o Fin (m + 1)) : ⦋n⦌ ⟶ ⦋m⦌ :=
  SimplexCategory.Hom.mk f

/--
Definition of `mkOfLe` / `mkOfLe` 的定义

English:
definition mkOfLe
  signature: {n} (i j : Fin (n + 1)) (h : i <= j)
  body: SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => h
  }

@[simp]

中文:
定义 mkOfLe
  签名: {n} (i j : Fin (n + 1)) (h : i <= j)
  定义体: SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => h
  }

@[simp]

Depends on / 依赖: SimplexCategory, SimplexCategory.mkHom, le_rfl, monotone
-/
def mkOfLe {n} (i j : Fin (n + 1)) (h : i <= j) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => h
  }

@[simp]
/--
lemma `mkOfLe_refl` / 引理 `mkOfLe_refl`

English:
lemma mkOfLe_refl
  given: {n} (j : Fin (n + 1))
  proof: Hom.ext_one_left _ _

中文:
引理 mkOfLe_refl
  条件: {n} (j : Fin (n + 1))
  证明: Hom.ext_one_left _ _

Depends on / 依赖: Hom.ext_one_left, ext_one_left
-/
lemma mkOfLe_refl {n} (j : Fin (n + 1)) :
    mkOfLe j j (by lia) = ⦋1⦌.const ⦋n⦌ j := Hom.ext_one_left _ _

/--
Definition of `diag` / `diag` 的定义

English:
definition diag
  signature: (n : Nat)
  body: mkOfLe 0 (Fin.last n) (Fin.zero_le _)

中文:
定义 diag
  签名: (n : 自然数)
  定义体: mkOfLe 0 (Fin.last n) (Fin.zero_le _)

Depends on / 依赖: Fin.last, Fin.zero_le, mkOfLe, zero_le
-/
def diag (n : Nat) : ⦋1⦌ ⟶ ⦋n⦌ :=
  mkOfLe 0 (Fin.last n) (Fin.zero_le _)

/--
Definition of `intervalEdge` / `intervalEdge` 的定义

English:
definition intervalEdge
  signature: {n} (j l : Nat) (hjl : j + l <= n)
  body: mkOfLe ⟨j, (by lia)⟩ ⟨j + l, (by lia)⟩ (Nat.le_add_right j l)

中文:
定义 intervalEdge
  签名: {n} (j l : 自然数) (hjl : j + l <= n)
  定义体: mkOfLe ⟨j, (by lia)⟩ ⟨j + l, (by lia)⟩ (Nat.le_add_right j l)

Depends on / 依赖: Nat.le_add_right, le_add_right, mkOfLe
-/
def intervalEdge {n} (j l : Nat) (hjl : j + l <= n) : ⦋1⦌ ⟶ ⦋n⦌ :=
  mkOfLe ⟨j, (by lia)⟩ ⟨j + l, (by lia)⟩ (Nat.le_add_right j l)

/--
Definition of `mkOfSucc` / `mkOfSucc` 的定义

English:
definition mkOfSucc
  signature: {n} (i : Fin n)
  body: SimplexCategory.mkHom {
    toFun := fun | 0 => i.castSucc | 1 => i.succ
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => Fin.castSucc_le_succ i
  }

@[simp]

中文:
定义 mkOfSucc
  签名: {n} (i : Fin n)
  定义体: SimplexCategory.mkHom {
    toFun := fun | 0 => i.castSucc | 1 => i.succ
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => Fin.castSucc_le_succ i
  }

@[simp]

Depends on / 依赖: Fin.castSucc_le_succ, SimplexCategory, SimplexCategory.mkHom, castSucc, castSucc_le_succ, i.castSucc, i.succ, le_rfl, monotone
-/
def mkOfSucc {n} (i : Fin n) : ⦋1⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i.castSucc | 1 => i.succ
    monotone' := fun
      | 0, 0, _ | 1, 1, _ => le_rfl
      | 0, 1, _ => Fin.castSucc_le_succ i
  }

@[simp]
/--
lemma `mkOfSucc_homToOrderHom_zero` / 引理 `mkOfSucc_homToOrderHom_zero`

English:
lemma mkOfSucc_homToOrderHom_zero
  given: {n} (i : Fin n)
  proof: rfl

@[simp]

中文:
引理 mkOfSucc_homToOrderHom_zero
  条件: {n} (i : Fin n)
  证明: rfl

@[simp]

Depends on / 依赖: Hom.toOrderHom, castSucc, i.castSucc, mkOfSucc, toOrderHom
-/
lemma mkOfSucc_homToOrderHom_zero {n} (i : Fin n) :
    DFunLike.coe (F := Fin 2 ->o Fin (n + 1)) (Hom.toOrderHom (mkOfSucc i)) 0 = i.castSucc := rfl

@[simp]
/--
lemma `mkOfSucc_homToOrderHom_one` / 引理 `mkOfSucc_homToOrderHom_one`

English:
lemma mkOfSucc_homToOrderHom_one
  given: {n} (i : Fin n)
  proof: rfl

@[simp]

中文:
引理 mkOfSucc_homToOrderHom_one
  条件: {n} (i : Fin n)
  证明: rfl

@[simp]

Depends on / 依赖: Hom.toOrderHom, i.succ, mkOfSucc, toOrderHom
-/
lemma mkOfSucc_homToOrderHom_one {n} (i : Fin n) :
    DFunLike.coe (F := Fin 2 ->o Fin (n + 1)) (Hom.toOrderHom (mkOfSucc i)) 1 = i.succ := rfl

@[simp]
/--
lemma `mkOfSucc_eq_id` / 引理 `mkOfSucc_eq_id`

English:
lemma mkOfSucc_eq_id
  statement: mkOfSucc (0 : Fin 1) = 𝟙 _
  proof: by decide

中文:
引理 mkOfSucc_eq_id
  结论: mkOfSucc (0 : Fin 1) = 𝟙 _
  证明: by decide
-/
lemma mkOfSucc_eq_id : mkOfSucc (0 : Fin 1) = 𝟙 _ := by decide

/--
Definition of `mkOfLeComp` / `mkOfLeComp` 的定义

English:
definition mkOfLeComp
  signature: {n} (i j k : Fin (n + 1)) (h₁ : i <= j) (h₂ : j <= k)
  body: SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j | 2 => k
    monotone' := fun
      | 0, 0, _ | 1, 1, _ | 2, 2, _ => le_rfl
      | 0, 1, _ => h₁
      | 1, 2, _ => h₂
      | 0, 2, _ => Fin.le_trans h₁ h₂
  }

中文:
定义 mkOfLeComp
  签名: {n} (i j k : Fin (n + 1)) (h₁ : i <= j) (h₂ : j <= k)
  定义体: SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j | 2 => k
    monotone' := fun
      | 0, 0, _ | 1, 1, _ | 2, 2, _ => le_rfl
      | 0, 1, _ => h₁
      | 1, 2, _ => h₂
      | 0, 2, _ => Fin.le_trans h₁ h₂
  }

Depends on / 依赖: Fin.le_trans, SimplexCategory, SimplexCategory.mkHom, le_rfl, le_trans, monotone
-/
def mkOfLeComp {n} (i j k : Fin (n + 1)) (h₁ : i <= j) (h₂ : j <= k) :
    ⦋2⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun | 0 => i | 1 => j | 2 => k
    monotone' := fun
      | 0, 0, _ | 1, 1, _ | 2, 2, _ => le_rfl
      | 0, 1, _ => h₁
      | 1, 2, _ => h₂
      | 0, 2, _ => Fin.le_trans h₁ h₂
  }

/--
Definition of `subinterval` / `subinterval` 的定义

English:
definition subinterval
  signature: {n} (j l : Nat) (hjl : j + l <= n)
  body: SimplexCategory.mkHom {
    toFun := fun i => ⟨i.1 + j, (by lia)⟩
    monotone' := fun i i' hii' => by simpa only [Fin.mk_le_mk, add_le_add_iff_right] using! hii'
  }

中文:
定义 subinterval
  签名: {n} (j l : 自然数) (hjl : j + l <= n)
  定义体: SimplexCategory.mkHom {
    toFun := fun i => ⟨i.1 + j, (by lia)⟩
    monotone' := fun i i' hii' => by simpa only [Fin.mk_le_mk, add_le_add_iff_right] using! hii'
  }

Depends on / 依赖: Fin.mk_le_mk, SimplexCategory, SimplexCategory.mkHom, add_le_add_iff_right, mk_le_mk, monotone
-/
def subinterval {n} (j l : Nat) (hjl : j + l <= n) :
    ⦋l⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.mkHom {
    toFun := fun i => ⟨i.1 + j, (by lia)⟩
    monotone' := fun i i' hii' => by simpa only [Fin.mk_le_mk, add_le_add_iff_right] using! hii'
  }

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `const_subinterval_eq` / 引理 `const_subinterval_eq`

English:
lemma const_subinterval_eq
  given: {n} (j l : Nat) (hjl : j + l <= n) (i : Fin (l + 1))
  proof: by
  rw [const_comp]
  congr
  ext
  dsimp [subinterval]
  rw [add_comm]

中文:
引理 const_subinterval_eq
  条件: {n} (j l : 自然数) (hjl : j + l <= n) (i : Fin (l + 1))
  证明: by
  rw [const_comp]
  congr
  ext
  dsimp [subinterval]
  rw [add_comm]

Depends on / 依赖: add_comm, const_comp, subinterval
-/
lemma const_subinterval_eq {n} (j l : Nat) (hjl : j + l <= n) (i : Fin (l + 1)) :
    ⦋0⦌.const ⦋l⦌ i ≫ subinterval j l hjl =
    ⦋0⦌.const ⦋n⦌ ⟨j + i.1, lt_add_of_lt_add_right (Nat.add_lt_add_left i.2 j) hjl⟩ := by
  rw [const_comp]
  congr
  ext
  dsimp [subinterval]
  rw [add_comm]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `mkOfSucc_subinterval_eq` / 引理 `mkOfSucc_subinterval_eq`

English:
lemma mkOfSucc_subinterval_eq
  given: {n} (j l : Nat) (hjl : j + l <= n) (i : Fin l)
  proof: by
  unfold subinterval mkOfSucc
  ext (i : Fin 2)
  match i with | 0 | 1 => simp; lia

中文:
引理 mkOfSucc_subinterval_eq
  条件: {n} (j l : 自然数) (hjl : j + l <= n) (i : Fin l)
  证明: by
  unfold subinterval mkOfSucc
  ext (i : Fin 2)
  match i with | 0 | 1 => simp; lia

Depends on / 依赖: mkOfSucc, subinterval
-/
lemma mkOfSucc_subinterval_eq {n} (j l : Nat) (hjl : j + l <= n) (i : Fin l) :
    mkOfSucc i ≫ subinterval j l hjl =
    mkOfSucc ⟨j + i.1, Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.2 j) hjl⟩ := by
  unfold subinterval mkOfSucc
  ext (i : Fin 2)
  match i with | 0 | 1 => simp; lia

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `diag_subinterval_eq` / 引理 `diag_subinterval_eq`

English:
lemma diag_subinterval_eq
  given: {n} (j l : Nat) (hjl : j + l <= n)
  proof: by
  unfold subinterval intervalEdge diag mkOfLe
  ext (i : Fin 2)
  match i with | 0 | 1 => simp <;> lia

中文:
引理 diag_subinterval_eq
  条件: {n} (j l : 自然数) (hjl : j + l <= n)
  证明: by
  unfold subinterval intervalEdge diag mkOfLe
  ext (i : Fin 2)
  match i with | 0 | 1 => simp <;> lia

Depends on / 依赖: intervalEdge, mkOfLe, subinterval
-/
lemma diag_subinterval_eq {n} (j l : Nat) (hjl : j + l <= n) :
    diag l ≫ subinterval j l hjl = intervalEdge j l hjl := by
  unfold subinterval intervalEdge diag mkOfLe
  ext (i : Fin 2)
  match i with | 0 | 1 => simp <;> lia

instance (Δ : SimplexCategory) : Subsingleton (Δ ⟶ ⦋0⦌) where
  allEq f g := by ext : 3; apply Subsingleton.elim (α := Fin 1)

/--
theorem `hom_zero_zero` / 定理 `hom_zero_zero`

English:
theorem hom_zero_zero
  given: (f : ⦋0⦌ ⟶ ⦋0⦌)
  statement: f = 𝟙 _
  proof: by
  apply Subsingleton.elim

@[simp]

中文:
定理 hom_zero_zero
  条件: (f : ⦋0⦌ ⟶ ⦋0⦌)
  结论: f = 𝟙 _
  证明: by
  apply Subsingleton.elim

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem hom_zero_zero (f : ⦋0⦌ ⟶ ⦋0⦌) : f = 𝟙 _ := by
  apply Subsingleton.elim

@[simp]
/--
lemma `eqToHom_toOrderHom` / 引理 `eqToHom_toOrderHom`

English:
lemma eqToHom_toOrderHom
  given: {x y : SimplexCategory} (h : x = y)
  proof: by
  subst h
  rfl

中文:
引理 eqToHom_toOrderHom
  条件: {x y : SimplexCategory} (h : x = y)
  证明: by
  subst h
  rfl
-/
lemma eqToHom_toOrderHom {x y : SimplexCategory} (h : x = y) :
  SimplexCategory.Hom.toOrderHom (eqToHom h) =
    (Fin.castOrderIso (congrArg (fun t => t.len + 1) h)).toOrderEmbedding.toOrderHom := by
  subst h
  rfl

end Init

section Generators

/-!
## Generating maps for the simplex category

TODO: prove that the simplex category is equivalent to
one given by the following generators and relations.
-/

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: {n} (i : Fin (n + 2))
  body: mkHom (Fin.succAboveOrderEmb i).toOrderHom

中文:
定义 δ
  签名: {n} (i : Fin (n + 2))
  定义体: mkHom (Fin.succAboveOrderEmb i).toOrderHom

Depends on / 依赖: Fin.succAboveOrderEmb, succAboveOrderEmb, toOrderHom
-/
def δ {n} (i : Fin (n + 2)) : ⦋n⦌ ⟶ ⦋n + 1⦌ :=
  mkHom (Fin.succAboveOrderEmb i).toOrderHom

/--
Definition of `σ` / `σ` 的定义

English:
definition σ
  signature: {n} (i : Fin (n + 1))
  body: mkHom i.predAboveOrderHom

中文:
定义 σ
  签名: {n} (i : Fin (n + 1))
  定义体: mkHom i.predAboveOrderHom

Depends on / 依赖: i.predAboveOrderHom, predAboveOrderHom
-/
def σ {n} (i : Fin (n + 1)) : ⦋n + 1⦌ ⟶ ⦋n⦌ :=
  mkHom i.predAboveOrderHom

set_option backward.defeqAttrib.useBackward true in
/--
theorem `δ_comp_δ` / 定理 `δ_comp_δ`

English:
theorem δ_comp_δ
  given: {n} {i j : Fin (n + 2)} (H : i <= j)
  proof: by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> lia

中文:
定理 δ_comp_δ
  条件: {n} {i j : Fin (n + 2)} (H : i <= j)
  证明: by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> lia

Depends on / 依赖: Fin.succAbove, split_ifs, succAbove
-/
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i <= j) :
    δ i ≫ δ j.succ = δ j ≫ δ i.castSucc := by
  ext k
  dsimp [δ, Fin.succAbove]
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  rcases k with ⟨k, _⟩
  split_ifs <;> · simp at * <;> lia

/--
theorem `δ_comp_δ'` / 定理 `δ_comp_δ'`

English:
theorem δ_comp_δ'
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.castSucc < j)
  proof: by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_def] using! H

中文:
定理 δ_comp_δ'
  条件: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.castSucc < j)
  证明: by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_def] using! H

Depends on / 依赖: Fin.le_iff_val_le_val, Fin.lt_def, Fin.succ_pred, Fin.val_succ, Nat.lt_succ_iff, Nat.succ_eq_add_one, j.succ_pred, le_iff_val_le_val, lt_def, lt_succ_iff, succ_eq_add_one, succ_pred, val_succ
-/
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.castSucc < j) :
    δ i ≫ δ j =
      δ (j.pred H.ne_zero) ≫
        δ (Fin.castSucc i) := by
  rw [← δ_comp_δ]
  · rw [Fin.succ_pred]
  · simpa only [Fin.le_iff_val_le_val, ← Nat.lt_succ_iff, Nat.succ_eq_add_one, ← Fin.val_succ,
      j.succ_pred, Fin.lt_def] using! H

/--
theorem `δ_comp_δ''` / 定理 `δ_comp_δ''`

English:
theorem δ_comp_δ''
  given: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j)
  proof: by
  rw [δ_comp_δ]
  · rfl
  · exact H

中文:
定理 δ_comp_δ''
  条件: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j)
  证明: by
  rw [δ_comp_δ]
  · rfl
  · exact H
-/
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i <= Fin.castSucc j) :
    δ (i.castLT (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ δ j.succ =
      δ j ≫ δ i := by
  rw [δ_comp_δ]
  · rfl
  · exact H

/-- The special case of the first simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_δ_self` / 定理 `δ_comp_δ_self`

English:
theorem δ_comp_δ_self
  given: {n} {i : Fin (n + 2)}
  statement: δ i ≫ δ i.castSucc = δ i ≫ δ i.succ
  proof: (δ_comp_δ (le_refl i)).symm

@[reassoc]

中文:
定理 δ_comp_δ_self
  条件: {n} {i : Fin (n + 2)}
  结论: δ i ≫ δ i.castSucc = δ i ≫ δ i.succ
  证明: (δ_comp_δ (le_refl i)).symm

@[reassoc]

Depends on / 依赖: le_refl
-/
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : δ i ≫ δ i.castSucc = δ i ≫ δ i.succ :=
  (δ_comp_δ (le_refl i)).symm

@[reassoc]
/--
theorem `δ_comp_δ_self'` / 定理 `δ_comp_δ_self'`

English:
theorem δ_comp_δ_self'
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = i.castSucc)
  proof: by
  subst H
  rw [δ_comp_δ_self]

中文:
定理 δ_comp_δ_self'
  条件: {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = i.castSucc)
  证明: by
  subst H
  rw [δ_comp_δ_self]
-/
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = i.castSucc) :
    δ i ≫ δ j = δ i ≫ δ i.succ := by
  subst H
  rw [δ_comp_δ_self]

set_option backward.defeqAttrib.useBackward true in
/-- The second simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_of_le` / 定理 `δ_comp_σ_of_le`

English:
theorem δ_comp_σ_of_le
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc)
  proof: by
  ext k : 3
  dsimp [σ, δ]
  rcases le_or_gt i k with (hik | hik)
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik),
    Fin.succ_predAbove_succ, Fin.succAbove_of_le_castSucc]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rwa [Fin.predAbove_of_le_castSucc

中文:
定理 δ_comp_σ_of_le
  条件: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc)
  证明: by
  ext k : 3
  dsimp [σ, δ]
  rcases le_or_gt i k with (hik | hik)
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik),
    Fin.succ_predAbove_succ, Fin.succAbove_of_le_castSucc]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rwa [Fin.predAbove_of_le_castSucc

Depends on / 依赖: Fin.castSucc_castPred, Fin.castSucc_le_castSucc_iff.mpr, Fin.castSucc_lt_castSucc_iff.mpr, Fin.le_castSucc_iff, Fin.predAbove_of_castSucc_lt, Fin.predAbove_of_le_castSucc, Fin.succAbove_of_castSucc_lt, Fin.succAbove_of_le_castSucc, Fin.succ_pred, Fin.succ_predAbove_succ, H.trans_lt, castSucc, castSucc_castPred, castSucc_le_castSucc_iff, castSucc_lt_castSucc_iff, j.castSucc, le_castSucc_iff, le_or_gt, predAbove_of_castSucc_lt, predAbove_of_le_castSucc
-/
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i <= j.castSucc) :
    δ i.castSucc ≫ σ j.succ = σ j ≫ δ i := by
  ext k : 3
  dsimp [σ, δ]
  rcases le_or_gt i k with (hik | hik)
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hik),
    Fin.succ_predAbove_succ, Fin.succAbove_of_le_castSucc]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rwa [Fin.predAbove_of_le_castSucc _ _ hjk, Fin.castSucc_castPred]
    · rw [Fin.le_castSucc_iff, Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.succ_pred]
      exact H.trans_lt hjk
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hik)]
    have hjk := H.trans_lt' hik
    rw [Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr
      (hjk.trans Fin.castSucc_lt_succ).le)]; rw [Fin.predAbove_of_le_castSucc _ _ hjk.le]; rw [Fin.castPred_castSucc]; rw [Fin.succAbove_of_castSucc_lt]; rw [Fin.castSucc_castPred]
    rwa [Fin.castSucc_castPred]

set_option backward.defeqAttrib.useBackward true in
/-- The first part of the third simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_self` / 定理 `δ_comp_σ_self`

English:
theorem δ_comp_σ_self
  given: {n} {i : Fin (n + 1)}
  proof: by
  rcases i with ⟨i, hi⟩
  ext ⟨j, hj⟩
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_def, Fin.dite_val, Fin.ite_val, Fin.val_pred]
  split_ifs
  any_goals simp
  all_goals lia

@[reassoc]

中文:
定理 δ_comp_σ_self
  条件: {n} {i : Fin (n + 1)}
  证明: by
  rcases i with ⟨i, hi⟩
  ext ⟨j, hj⟩
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_def, Fin.dite_val, Fin.ite_val, Fin.val_pred]
  split_ifs
  any_goals simp
  all_goals lia

@[reassoc]

Depends on / 依赖: Fin.dite_val, Fin.ite_val, Fin.lt_def, Fin.predAbove, Fin.succAbove, Fin.val_pred, all_goals, any_goals, dite_val, ite_val, lt_def, predAbove, split_ifs, succAbove, val_pred
-/
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} :
    δ (Fin.castSucc i) ≫ σ i = 𝟙 ⦋n⦌ := by
  rcases i with ⟨i, hi⟩
  ext ⟨j, hj⟩
  dsimp [σ, δ, Fin.predAbove, Fin.succAbove]
  simp only [Fin.lt_def, Fin.dite_val, Fin.ite_val, Fin.val_pred]
  split_ifs
  any_goals simp
  all_goals lia

@[reassoc]
/--
theorem `δ_comp_σ_self'` / 定理 `δ_comp_σ_self'`

English:
theorem δ_comp_σ_self'
  given: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.castSucc)
  proof: by
  subst H
  rw [δ_comp_σ_self]

中文:
定理 δ_comp_σ_self'
  条件: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.castSucc)
  证明: by
  subst H
  rw [δ_comp_σ_self]
-/
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.castSucc) :
    δ j ≫ σ i = 𝟙 ⦋n⦌ := by
  subst H
  rw [δ_comp_σ_self]

set_option backward.defeqAttrib.useBackward true in
/-- The second part of the third simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_succ` / 定理 `δ_comp_σ_succ`

English:
theorem δ_comp_σ_succ
  given: {n} {i : Fin (n + 1)}
  statement: δ i.succ ≫ σ i = 𝟙 ⦋n⦌
  proof: by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  split_ifs <;> simp <;> simp at * <;> lia

@[reassoc]

中文:
定理 δ_comp_σ_succ
  条件: {n} {i : Fin (n + 1)}
  结论: δ i.succ ≫ σ i = 𝟙 ⦋n⦌
  证明: by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  split_ifs <;> simp <;> simp at * <;> lia

@[reassoc]

Depends on / 依赖: Fin.predAbove, Fin.succAbove, predAbove, split_ifs, succAbove
-/
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : δ i.succ ≫ σ i = 𝟙 ⦋n⦌ := by
  ext j
  rcases i with ⟨i, _⟩
  rcases j with ⟨j, _⟩
  dsimp [δ, σ, Fin.succAbove, Fin.predAbove]
  split_ifs <;> simp <;> simp at * <;> lia

@[reassoc]
/--
theorem `δ_comp_σ_succ'` / 定理 `δ_comp_σ_succ'`

English:
theorem δ_comp_σ_succ'
  given: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ)
  proof: by
  subst H
  rw [δ_comp_σ_succ]

中文:
定理 δ_comp_σ_succ'
  条件: {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ)
  证明: by
  subst H
  rw [δ_comp_σ_succ]
-/
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    δ j ≫ σ i = 𝟙 ⦋n⦌ := by
  subst H
  rw [δ_comp_σ_succ]

set_option backward.defeqAttrib.useBackward true in
/-- The fourth simplicial identity -/
@[reassoc]
/--
theorem `δ_comp_σ_of_gt` / 定理 `δ_comp_σ_of_gt`

English:
theorem δ_comp_σ_of_gt
  given: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i)
  proof: by
  ext k : 3
  dsimp [δ, σ]
  rcases le_or_gt k i with (hik | hik)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hik)]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rw [Fin.predAbove_of_le_castSucc _ _
      (Fin.castSucc_le_castSucc_iff.mpr hjk), Fin.castPred_

中文:
定理 δ_comp_σ_of_gt
  条件: {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i)
  证明: by
  ext k : 3
  dsimp [δ, σ]
  rcases le_or_gt k i with (hik | hik)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hik)]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rw [Fin.predAbove_of_le_castSucc _ _
      (Fin.castSucc_le_castSucc_iff.mpr hjk), Fin.castPred_

Depends on / 依赖: Fin.castPred_castSucc, Fin.castSucc_castPred, Fin.castSucc_le_castSucc_iff.mpr, Fin.castSucc_lt_castSucc_iff.mpr, Fin.castSucc_lt_succ_iff.mpr, Fin.predAbove_of_castSucc_lt, Fin.predAbove_of_le_castSucc, Fin.succAbove_of_castSucc_lt, castPred_castSucc, castSucc, castSucc_castPred, castSucc_le_castSucc_iff, castSucc_lt_castSucc_iff, castSucc_lt_succ_iff, hjk.trans_lt, j.castSucc, le_or_gt, predAbove_of_castSucc_lt, predAbove_of_le_castSucc, succAbove_of_castSucc_lt
-/
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.castSucc < i) :
    δ i.succ ≫ σ j.castSucc = σ j ≫ δ i := by
  ext k : 3
  dsimp [δ, σ]
  rcases le_or_gt k i with (hik | hik)
  · rw [Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_succ_iff.mpr hik)]
    rcases le_or_gt k (j.castSucc) with (hjk | hjk)
    · rw [Fin.predAbove_of_le_castSucc _ _
      (Fin.castSucc_le_castSucc_iff.mpr hjk), Fin.castPred_castSucc,
      Fin.predAbove_of_le_castSucc _ _ hjk, Fin.succAbove_of_castSucc_lt, Fin.castSucc_castPred]
      rw [Fin.castSucc_castPred]
      exact hjk.trans_lt H
    · rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hjk),
      Fin.predAbove_of_castSucc_lt _ _ hjk, Fin.succAbove_of_castSucc_lt,
      Fin.castSucc_pred_eq_pred_castSucc]
      rwa [Fin.castSucc_lt_iff_succ_le, Fin.succ_pred]
  · rw [Fin.succAbove_of_le_castSucc _ _ (Fin.succ_le_castSucc_iff.mpr hik)]
    have hjk := H.trans hik
    rw [Fin.predAbove_of_castSucc_lt _ _ hjk]; rw [Fin.predAbove_of_castSucc_lt _ _
      (Fin.castSucc_lt_succ_iff.mpr hjk.le)]; rw [Fin.pred_succ]; rw [Fin.succAbove_of_le_castSucc]; rw [Fin.succ_pred]
    rwa [Fin.le_castSucc_pred_iff]

@[reassoc]
/--
theorem `δ_comp_σ_of_gt'` / 定理 `δ_comp_σ_of_gt'`

English:
theorem δ_comp_σ_of_gt'
  given: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
  proof: by
  rw [← δ_comp_σ_of_gt]
  · simp
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H

中文:
定理 δ_comp_σ_of_gt'
  条件: {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i)
  证明: by
  rw [← δ_comp_σ_of_gt]
  · simp
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H

Depends on / 依赖: Fin.castSucc_castLT, Fin.succ_lt_succ_iff, Fin.succ_pred, castSucc_castLT, succ_lt_succ_iff, succ_pred
-/
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    δ i ≫ σ j = σ (j.castLT ((add_lt_add_iff_right 1).mp (lt_of_lt_of_le H i.is_le))) ≫
      δ (i.pred H.ne_zero) := by
  rw [← δ_comp_σ_of_gt]
  · simp
  · rw [Fin.castSucc_castLT, ← Fin.succ_lt_succ_iff, Fin.succ_pred]
    exact H

set_option backward.defeqAttrib.useBackward true in
/-- The fifth simplicial identity -/
@[reassoc]
/--
theorem `σ_comp_σ` / 定理 `σ_comp_σ`

English:
theorem σ_comp_σ
  given: {n} {i j : Fin (n + 1)} (H : i <= j)
  proof: by
  ext k : 3
  dsimp [σ]
  cases k using Fin.lastCases with
  | last => simp only [len_mk, Fin.predAbove_right_last]
  | cast k =>
    cases k using Fin.cases with
    | zero =>
      simp
    | succ k =>
      rcases le_or_gt i k with (h | h)
      · simp_rw [Fin.predAbove_of_castSucc_lt i.castSu

中文:
定理 σ_comp_σ
  条件: {n} {i j : Fin (n + 1)} (H : i <= j)
  证明: by
  ext k : 3
  dsimp [σ]
  cases k using Fin.lastCases with
  | last => simp only [len_mk, Fin.predAbove_right_last]
  | cast k =>
    cases k using Fin.cases with
    | zero =>
      simp
    | succ k =>
      rcases le_or_gt i k with (h | h)
      · simp_rw [Fin.predAbove_of_castSucc_lt i.castSu

Depends on / 依赖: Fin.cases, Fin.castSucc_lt_castSucc_iff.mpr, Fin.castSucc_lt_succ_iff.mpr, Fin.lastCases, Fin.predAbove_of_castSucc_lt, Fin.predAbove_right_last, Fin.pred_succ, Fin.succ_castSucc, Fin.succ_predAbove_succ, castSucc, castSucc_lt_castSucc_iff, castSucc_lt_succ_iff, i.castSucc, lastCases, le_or_g, le_or_gt, len_mk, predAbove_of_castSucc_lt, predAbove_right_last, pred_succ
-/
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i <= j) :
    σ (Fin.castSucc i) ≫ σ j = σ j.succ ≫ σ i := by
  ext k : 3
  dsimp [σ]
  cases k using Fin.lastCases with
  | last => simp only [len_mk, Fin.predAbove_right_last]
  | cast k =>
    cases k using Fin.cases with
    | zero =>
      simp
    | succ k =>
      rcases le_or_gt i k with (h | h)
      · simp_rw [Fin.predAbove_of_castSucc_lt i.castSucc _ (Fin.castSucc_lt_castSucc_iff.mpr
        (Fin.castSucc_lt_succ_iff.mpr h)), ← Fin.succ_castSucc, Fin.pred_succ,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_castSucc_lt i _ (Fin.castSucc_lt_succ_iff.mpr _)]; rw [Fin.pred_succ]
        rcases le_or_gt k j with (hkj | hkj)
        · rwa [Fin.predAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.mpr hkj),
          Fin.castPred_castSucc]
        · rw [Fin.predAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.mpr hkj),
          Fin.le_pred_iff,
          Fin.succ_le_castSucc_iff]
          exact H.trans_lt hkj
      · simp_rw [Fin.predAbove_of_le_castSucc i.castSucc _ (Fin.castSucc_le_castSucc_iff.mpr
        (Fin.succ_le_castSucc_iff.mpr h)), Fin.castPred_castSucc, ← Fin.succ_castSucc,
        Fin.succ_predAbove_succ]
        rw [Fin.predAbove_of_le_castSucc _ k.castSucc
        (Fin.castSucc_le_castSucc_iff.mpr (h.le.trans H))]; rw [Fin.castPred_castSucc]; rw [Fin.predAbove_of_le_castSucc _ k.succ
        (Fin.succ_le_castSucc_iff.mpr (H.trans_lt' h))]; rw [Fin.predAbove_of_le_castSucc _ k.succ
        (Fin.succ_le_castSucc_iff.mpr h)]

/--
lemma `δ_zero_eq_const` / 引理 `δ_zero_eq_const`

English:
lemma δ_zero_eq_const
  statement: δ (0 : Fin 2) = const _ _ 1
  proof: by decide

中文:
引理 δ_zero_eq_const
  结论: δ (0 : Fin 2) = const _ _ 1
  证明: by decide
-/
lemma δ_zero_eq_const : δ (0 : Fin 2) = const _ _ 1 := by decide

/--
lemma `δ_one_eq_const` / 引理 `δ_one_eq_const`

English:
lemma δ_one_eq_const
  statement: δ (1 : Fin 2) = const _ _ 0
  proof: by decide

中文:
引理 δ_one_eq_const
  结论: δ (1 : Fin 2) = const _ _ 0
  证明: by decide
-/
lemma δ_one_eq_const : δ (1 : Fin 2) = const _ _ 0 := by decide

/--
Definition of `factor_δ` / `factor_δ` 的定义

English:
definition factor_δ
  signature: {m n : Nat} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
  body: f ≫ σ (Fin.predAbove 0 j)

中文:
定义 factor_δ
  签名: {m n : 自然数} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
  定义体: f ≫ σ (Fin.predAbove 0 j)

Depends on / 依赖: Fin.predAbove, predAbove
-/
def factor_δ {m n : Nat} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2)) : ⦋m⦌ ⟶ ⦋n⦌ :=
  f ≫ σ (Fin.predAbove 0 j)

/--
lemma `factor_δ_spec` / 引理 `factor_δ_spec`

English:
lemma factor_δ_spec
  statement: {m n : Nat} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
  proof: by
  ext k : 3
  cases j using Fin.cases <;> simp_all [factor_δ, δ, σ]

@[simp]

中文:
引理 factor_δ_spec
  结论: {m n : 自然数} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
  证明: by
  ext k : 3
  cases j using Fin.cases <;> simp_all [factor_δ, δ, σ]

@[simp]

Depends on / 依赖: Fin.cases
-/
lemma factor_δ_spec {m n : Nat} (f : ⦋m⦌ ⟶ ⦋n + 1⦌) (j : Fin (n + 2))
    (hj : forall (k : Fin (m + 1)), f.toOrderHom k != j) :
    factor_δ f j ≫ δ j = f := by
  ext k : 3
  cases j using Fin.cases <;> simp_all [factor_δ, δ, σ]

@[simp]
/--
lemma `δ_zero_mkOfSucc` / 引理 `δ_zero_mkOfSucc`

English:
lemma δ_zero_mkOfSucc
  given: {n : Nat} (i : Fin n)
  proof: by
  ext x
  fin_cases x
  rfl

@[simp]

中文:
引理 δ_zero_mkOfSucc
  条件: {n : 自然数} (i : Fin n)
  证明: by
  ext x
  fin_cases x
  rfl

@[simp]

Depends on / 依赖: fin_cases
-/
lemma δ_zero_mkOfSucc {n : Nat} (i : Fin n) :
    δ 0 ≫ mkOfSucc i = SimplexCategory.const _ ⦋n⦌ i.succ := by
  ext x
  fin_cases x
  rfl

@[simp]
/--
lemma `δ_one_mkOfSucc` / 引理 `δ_one_mkOfSucc`

English:
lemma δ_one_mkOfSucc
  given: {n : Nat} (i : Fin n)
  proof: by
  ext x
  fin_cases x
  rfl

中文:
引理 δ_one_mkOfSucc
  条件: {n : 自然数} (i : Fin n)
  证明: by
  ext x
  fin_cases x
  rfl

Depends on / 依赖: fin_cases
-/
lemma δ_one_mkOfSucc {n : Nat} (i : Fin n) :
    δ 1 ≫ mkOfSucc i = SimplexCategory.const _ ⦋n⦌ i.castSucc := by
  ext x
  fin_cases x
  rfl

/--
lemma `mkOfSucc_δ_lt` / 引理 `mkOfSucc_δ_lt`

English:
lemma mkOfSucc_δ_lt
  statement: {n : Nat} {i : Fin n} {j : Fin (n + 2)}
  proof: by
  ext x
  fin_cases x
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ (Nat.lt_trans _ h)]
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ h]

中文:
引理 mkOfSucc_δ_lt
  结论: {n : 自然数} {i : Fin n} {j : Fin (n + 2)}
  证明: by
  ext x
  fin_cases x
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ (Nat.lt_trans _ h)]
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ h]

Depends on / 依赖: Fin.succAbove_of_castSucc_lt, Nat.lt_trans, fin_cases, lt_trans, succAbove_of_castSucc_lt
-/
lemma mkOfSucc_δ_lt {n : Nat} {i : Fin n} {j : Fin (n + 2)}
    (h : i.succ.castSucc < j) :
    mkOfSucc i ≫ δ j = mkOfSucc i.castSucc := by
  ext x
  fin_cases x
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ (Nat.lt_trans _ h)]
  · simp [δ, Fin.succAbove_of_castSucc_lt _ _ h]

/--
lemma `mkOfSucc_δ_gt` / 引理 `mkOfSucc_δ_gt`

English:
lemma mkOfSucc_δ_gt
  statement: {n : Nat} {i : Fin n} {j : Fin (n + 2)}
  proof: by
  ext x
  simp only [δ, len_mk, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  fin_cases x <;> rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · exact Nat.le_of_lt_succ h
  · rfl
  · exact Nat.le_of_

中文:
引理 mkOfSucc_δ_gt
  结论: {n : 自然数} {i : Fin n} {j : Fin (n + 2)}
  证明: by
  ext x
  simp only [δ, len_mk, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  fin_cases x <;> rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · exact Nat.le_of_lt_succ h
  · rfl
  · exact Nat.le_of_

Depends on / 依赖: Fin.succAboveOrderEmb_apply, Fin.succAbove_of_le_castSucc, Function, Function.comp_apply, Hom.toOrderHom_mk, Nat.le_of_lt, Nat.le_of_lt_succ, OrderEmbedding, OrderEmbedding.toOrderHom_coe, OrderHom, OrderHom.comp_coe, comp_apply, comp_coe, comp_toOrderHom, fin_cases, le_of_lt, le_of_lt_succ, len_mk, succAboveOrderEmb_apply, succAbove_of_le_castSucc
-/
lemma mkOfSucc_δ_gt {n : Nat} {i : Fin n} {j : Fin (n + 2)}
    (h : j < i.succ.castSucc) :
    mkOfSucc i ≫ δ j = mkOfSucc i.succ := by
  ext x
  simp only [δ, len_mk, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    OrderEmbedding.toOrderHom_coe, Function.comp_apply, Fin.succAboveOrderEmb_apply]
  fin_cases x <;> rw [Fin.succAbove_of_le_castSucc]
  · rfl
  · exact Nat.le_of_lt_succ h
  · rfl
  · exact Nat.le_of_lt h

/--
lemma `mkOfSucc_δ_eq` / 引理 `mkOfSucc_δ_eq`

English:
lemma mkOfSucc_δ_eq
  statement: {n : Nat} {i : Fin n} {j : Fin (n + 2)}
  proof: by
  ext x
  fin_cases x
  · subst h
    simp only [δ, len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk,
      Fin.zero_eta, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      mkOfSucc_homToOrderHom_zero, Fin.succAboveOrderEmb_apply,
      Fin.castSucc_succA

中文:
引理 mkOfSucc_δ_eq
  结论: {n : 自然数} {i : Fin n} {j : Fin (n + 2)}
  证明: by
  ext x
  fin_cases x
  · subst h
    simp only [δ, len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk,
      Fin.zero_eta, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      mkOfSucc_homToOrderHom_zero, Fin.succAboveOrderEmb_apply,
      Fin.castSucc_succA

Depends on / 依赖: Fin.castSucc_succAbove_castSucc, Fin.mk_one, Fin.succAboveOrderEmb_apply, Fin.succAbove_succ_self, Fin.zero_eta, Function, Function.comp_apply, Hom.toOrderHom_mk, Nat.reduceAdd, OrderEmbedding, OrderEmbedding.toOrderHom_coe, OrderHom, OrderHom.comp_coe, castSucc_succAbove_castSucc, comp_apply, comp_coe, comp_toOrderHom, fin_cases, len_mk, mkOfSucc_homToOrder
-/
lemma mkOfSucc_δ_eq {n : Nat} {i : Fin n} {j : Fin (n + 2)}
    (h : j = i.succ.castSucc) :
    mkOfSucc i ≫ δ j = intervalEdge i 2 (by lia) := by
  ext x
  fin_cases x
  · subst h
    simp only [δ, len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk,
      Fin.zero_eta, OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      mkOfSucc_homToOrderHom_zero, Fin.succAboveOrderEmb_apply,
      Fin.castSucc_succAbove_castSucc, Fin.succAbove_succ_self]
    rfl
  · simp only [δ, len_mk, Nat.reduceAdd, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, Fin.mk_one,
      OrderHom.comp_coe, OrderEmbedding.toOrderHom_coe, Function.comp_apply,
      mkOfSucc_homToOrderHom_one, Fin.succAboveOrderEmb_apply]
    subst h
    rw [Fin.succAbove_castSucc_self]
    rfl

/--
lemma `mkOfSucc_one_eq_δ` / 引理 `mkOfSucc_one_eq_δ`

English:
lemma mkOfSucc_one_eq_δ
  statement: mkOfSucc (1 : Fin 2) = δ 0
  proof: by decide

中文:
引理 mkOfSucc_one_eq_δ
  结论: mkOfSucc (1 : Fin 2) = δ 0
  证明: by decide
-/
lemma mkOfSucc_one_eq_δ : mkOfSucc (1 : Fin 2) = δ 0 := by decide

/--
lemma `mkOfSucc_zero_eq_δ` / 引理 `mkOfSucc_zero_eq_δ`

English:
lemma mkOfSucc_zero_eq_δ
  statement: mkOfSucc (0 : Fin 2) = δ 2
  proof: by decide

中文:
引理 mkOfSucc_zero_eq_δ
  结论: mkOfSucc (0 : Fin 2) = δ 2
  证明: by decide
-/
lemma mkOfSucc_zero_eq_δ : mkOfSucc (0 : Fin 2) = δ 2 := by decide

/--
theorem `eq_of_one_to_two` / 定理 `eq_of_one_to_two`

English:
theorem eq_of_one_to_two
  given: (f : ⦋1⦌ ⟶ ⦋2⦌)
  proof: by
  have : f.toOrderHom 0 <= f.toOrderHom 1 := f.toOrderHom.monotone (by decide : (0 : Fin 2) <= 1)
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 1, 2 =>
    refine .inl ⟨0, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 2 =>
    refine .inl ⟨1, ?_⟩
  

中文:
定理 eq_of_one_to_two
  条件: (f : ⦋1⦌ ⟶ ⦋2⦌)
  证明: by
  have : f.toOrderHom 0 <= f.toOrderHom 1 := f.toOrderHom.monotone (by decide : (0 : Fin 2) <= 1)
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 1, 2 =>
    refine .inl ⟨0, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 2 =>
    refine .inl ⟨1, ?_⟩
  

Depends on / 依赖: SimplexCategory, SimplexCategory.const, f.toOrderHom, f.toOrderHom.monotone, monotone, toOrderHom
-/
theorem eq_of_one_to_two (f : ⦋1⦌ ⟶ ⦋2⦌) :
    (exists i, f = (δ (n := 1) i)) ∨ exists a, f = SimplexCategory.const _ _ a := by
  have : f.toOrderHom 0 <= f.toOrderHom 1 := f.toOrderHom.monotone (by decide : (0 : Fin 2) <= 1)
  match e0 : f.toOrderHom 0, e1 : f.toOrderHom 1 with
  | 1, 2 =>
    refine .inl ⟨0, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 2 =>
    refine .inl ⟨1, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 1 =>
    refine .inl ⟨2, ?_⟩
    ext i : 3
    match i with
    | 0 => exact e0
    | 1 => exact e1
  | 0, 0 | 1, 1 | 2, 2 =>
    refine .inr ⟨f.toOrderHom 0, ?_⟩
    ext i : 3
    match i with
    | 0 => rfl
    | 1 => exact e1.trans e0.symm
  | 1, 0 | 2, 0 | 2, 1 =>
    rw [e0]; rw [e1] at this
    exact Not.elim (by decide) this

/--
theorem `eq_of_one_to_two'` / 定理 `eq_of_one_to_two'`

English:
theorem eq_of_one_to_two'
  given: (f : ⦋1⦌ ⟶ ⦋2⦌)
  proof: match eq_of_one_to_two f with
  | .inl ⟨0, h⟩ => .inl h
  | .inl ⟨1, h⟩ => .inr (.inl h)
  | .inl ⟨2, h⟩ => .inr (.inr (.inl h))
  | .inr h => .inr (.inr (.inr h))

中文:
定理 eq_of_one_to_two'
  条件: (f : ⦋1⦌ ⟶ ⦋2⦌)
  证明: match eq_of_one_to_two f with
  | .inl ⟨0, h⟩ => .inl h
  | .inl ⟨1, h⟩ => .inr (.inl h)
  | .inl ⟨2, h⟩ => .inr (.inr (.inl h))
  | .inr h => .inr (.inr (.inr h))
-/
theorem eq_of_one_to_two' (f : ⦋1⦌ ⟶ ⦋2⦌) :
    f = (δ (n := 1) 0) ∨ f = (δ (n := 1) 1) ∨ f = (δ (n := 1) 2) ∨
      exists a, f = SimplexCategory.const _ _ a :=
  match eq_of_one_to_two f with
  | .inl ⟨0, h⟩ => .inl h
  | .inl ⟨1, h⟩ => .inr (.inl h)
  | .inl ⟨2, h⟩ => .inr (.inr (.inl h))
  | .inr h => .inr (.inr (.inr h))

end Generators

section Skeleton

/-- The functor that exhibits `SimplexCategory` as skeleton
of `NonemptyFinLinOrd` -/
@[simps obj map]
/--
Definition of `skeletalFunctor` / `skeletalFunctor` 的定义

English:
definition skeletalFunctor
  signature: : SimplexCategory ⥤ NonemptyFinLinOrd where
  body: NonemptyFinLinOrd.of (Fin (a.len + 1))
  map f := NonemptyFinLinOrd.ofHom f.toOrderHom

中文:
定义 skeletalFunctor
  签名: : SimplexCategory ⥤ NonemptyFinLinOrd where
  定义体: NonemptyFinLinOrd.of (Fin (a.len + 1))
  map f := NonemptyFinLinOrd.ofHom f.toOrderHom

Depends on / 依赖: NonemptyFinLinOrd, NonemptyFinLinOrd.of, a.len
-/
def skeletalFunctor : SimplexCategory ⥤ NonemptyFinLinOrd where
  obj a := NonemptyFinLinOrd.of (Fin (a.len + 1))
  map f := NonemptyFinLinOrd.ofHom f.toOrderHom

/--
theorem `skeletalFunctor.coe_map` / 定理 `skeletalFunctor.coe_map`

English:
theorem skeletalFunctor.coe_map
  given: {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂)
  proof: rfl

中文:
定理 skeletalFunctor.coe_map
  条件: {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂)
  证明: rfl
-/
theorem skeletalFunctor.coe_map {Δ₁ Δ₂ : SimplexCategory} (f : Δ₁ ⟶ Δ₂) :
    ↑(skeletalFunctor.map f).hom.hom = f.toOrderHom :=
  rfl

/--
theorem `skeletal` / 定理 `skeletal`

English:
theorem skeletal
  statement: Skeletal SimplexCategory
  proof: fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget NonemptyFinLinOrd).mapIso I).toEquiv

中文:
定理 skeletal
  结论: Skeletal SimplexCategory
  证明: fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget NonemptyFinLinOrd).mapIso I).toEquiv

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_congr, NonemptyFinLinOrd, X.len, Y.len, card_congr, forget, mapIso, skeletalFunctor, toEquiv
-/
theorem skeletal : Skeletal SimplexCategory := fun X Y ⟨I⟩ => by
  suffices Fintype.card (Fin (X.len + 1)) = Fintype.card (Fin (Y.len + 1)) by
    ext
    simpa
  apply Fintype.card_congr
  exact ((skeletalFunctor ⋙ forget NonemptyFinLinOrd).mapIso I).toEquiv

namespace SkeletalFunctor

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: skeletalFunctor.Full
  body: ⟨SimplexCategory.Hom.mk f.hom.hom, rfl⟩

中文:
实例 :
  签名: skeletalFunctor.Full
  定义体: ⟨SimplexCategory.Hom.mk f.hom.hom, rfl⟩

Depends on / 依赖: SimplexCategory, SimplexCategory.Hom.mk, f.hom.hom
-/
instance : skeletalFunctor.Full where
  map_surjective f := ⟨SimplexCategory.Hom.mk f.hom.hom, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: skeletalFunctor.Faithful
  body: by
    ext : 3
    exact CategoryTheory.congr_fun h _

中文:
实例 :
  签名: skeletalFunctor.Faithful
  定义体: by
    ext : 3
    exact CategoryTheory.congr_fun h _

Depends on / 依赖: CategoryTheory, CategoryTheory.congr_fun, congr_fun
-/
instance : skeletalFunctor.Faithful where
  map_injective {_ _ f g} h := by
    ext : 3
    exact CategoryTheory.congr_fun h _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: skeletalFunctor.EssSurj
  body: ⟨⦋(Fintype.card X - 1 : Nat)⦌,
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        refine
         

中文:
实例 :
  签名: skeletalFunctor.EssSurj
  定义体: ⟨⦋(Fintype.card X - 1 : Nat)⦌,
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        refine
         

Depends on / 依赖: Finset, Finset.univ.orderEmbOfFin, Fintype, Fintype.card, Fintype.card_pos_iff.mpr, InducedCategory, InducedCategory.homMk, LinOrd, LinOrd.ofHom, Nat.succ_pred_eq_of_pos, apply_symm_apply, card_pos_iff, f.apply_symm_apply, f.symm, f.symm_apply_apply, hf.monotone, hom_inv_id, inv_hom_id, monoEquivOfFin, monotone
-/
instance : skeletalFunctor.EssSurj where
  mem_essImage X :=
    ⟨⦋(Fintype.card X - 1 : Nat)⦌,
      ⟨by
        have aux : Fintype.card X = Fintype.card X - 1 + 1 :=
          (Nat.succ_pred_eq_of_pos <| Fintype.card_pos_iff.mpr ⟨⊥⟩).symm
        let f := monoEquivOfFin X aux
        have hf := (Finset.univ.orderEmbOfFin aux).strictMono
        refine
          { hom := InducedCategory.homMk (LinOrd.ofHom ⟨f, hf.monotone⟩)
            inv := InducedCategory.homMk (LinOrd.ofHom ⟨f.symm, ?_⟩)
            hom_inv_id := by ext; apply f.symm_apply_apply
            inv_hom_id := by ext; apply f.apply_symm_apply }
        intro i j h
        change f.symm i <= f.symm j
        rw [← hf.le_iff_le]
        change f (f.symm i) <= f (f.symm j)
        simpa only [OrderIso.apply_symm_apply]⟩⟩

/--
Instance `isEquivalence` / 实例 `isEquivalence`

English:
instance isEquivalence
  signature: : skeletalFunctor.IsEquivalence where

中文:
实例 isEquivalence
  签名: : skeletalFunctor.IsEquivalence where
-/
noncomputable instance isEquivalence : skeletalFunctor.IsEquivalence where

end SkeletalFunctor

/--
Definition of `skeletalEquivalence` / `skeletalEquivalence` 的定义

English:
definition skeletalEquivalence
  signature: : SimplexCategory ≌ NonemptyFinLinOrd
  body: Functor.asEquivalence skeletalFunctor

中文:
定义 skeletalEquivalence
  签名: : SimplexCategory ≌ NonemptyFinLinOrd
  定义体: Functor.asEquivalence skeletalFunctor

Depends on / 依赖: Functor, Functor.asEquivalence, asEquivalence, skeletalFunctor
-/
noncomputable def skeletalEquivalence : SimplexCategory ≌ NonemptyFinLinOrd :=
  Functor.asEquivalence skeletalFunctor

end Skeleton

/--
lemma `isSkeletonOf` / 引理 `isSkeletonOf`

English:
lemma isSkeletonOf
  proof: skeletal
  eqv := SkeletalFunctor.isEquivalence

中文:
引理 isSkeletonOf
  证明: skeletal
  eqv := SkeletalFunctor.isEquivalence

Depends on / 依赖: skeletal
-/
lemma isSkeletonOf :
    IsSkeletonOf NonemptyFinLinOrd SimplexCategory skeletalFunctor where
  skel := skeletal
  eqv := SkeletalFunctor.isEquivalence

section Concrete

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ConcreteCategory SimplexCategory (fun i j => Fin (i.len + 1) ->o Fin (j.len + 1))
  body: Hom.toOrderHom
  ofHom f := Hom.mk f

中文:
实例 :
  签名: ConcreteCategory SimplexCategory (fun i j => Fin (i.len + 1) ->o Fin (j.len + 1))
  定义体: Hom.toOrderHom
  ofHom f := Hom.mk f

Depends on / 依赖: Hom.toOrderHom, toOrderHom
-/
instance : ConcreteCategory SimplexCategory (fun i j => Fin (i.len + 1) ->o Fin (j.len + 1)) where
  hom := Hom.toOrderHom
  ofHom f := Hom.mk f

/--
lemma `toType_apply` / 引理 `toType_apply`

English:
lemma toType_apply
  given: (x : SimplexCategory)
  statement: ToType x = Fin (x.len + 1)
  proof: rfl

@[simp]

中文:
引理 toType_apply
  条件: (x : SimplexCategory)
  结论: ToType x = Fin (x.len + 1)
  证明: rfl

@[simp]
-/
lemma toType_apply (x : SimplexCategory) : ToType x = Fin (x.len + 1) := rfl

@[simp]
/--
lemma `concreteCategoryHom_id` / 引理 `concreteCategoryHom_id`

English:
lemma concreteCategoryHom_id
  given: (n : SimplexCategory)
  statement: ConcreteCategory.hom (𝟙 n) = .id
  proof: rfl

中文:
引理 concreteCategoryHom_id
  条件: (n : SimplexCategory)
  结论: ConcreteCategory.hom (𝟙 n) = .id
  证明: rfl
-/
lemma concreteCategoryHom_id (n : SimplexCategory) : ConcreteCategory.hom (𝟙 n) = .id := rfl

/--
lemma `coe_δ` / 引理 `coe_δ`

English:
lemma coe_δ
  given: {n : Nat} (i : Fin (n + 2))
  proof: rfl

中文:
引理 coe_δ
  条件: {n : 自然数} (i : Fin (n + 2))
  证明: rfl
-/
lemma coe_δ {n : Nat} (i : Fin (n + 2)) :
    dsimp% ⇑(δ i) = Fin.succAbove i := rfl

/--
lemma `coe_σ` / 引理 `coe_σ`

English:
lemma coe_σ
  given: {n : Nat} (i : Fin (n + 1))
  proof: rfl

中文:
引理 coe_σ
  条件: {n : 自然数} (i : Fin (n + 1))
  证明: rfl
-/
lemma coe_σ {n : Nat} (i : Fin (n + 1)) :
    dsimp% ⇑(σ i) = Fin.predAbove i := rfl

end Concrete

section EpiMono

set_option backward.defeqAttrib.useBackward true in
/--
theorem `mono_iff_injective` / 定理 `mono_iff_injective`

English:
theorem mono_iff_injective
  given: {n m : SimplexCategory} {f : n ⟶ m}
  proof: by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.mono_iff_injective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

中文:
定理 mono_iff_injective
  条件: {n m : SimplexCategory} {f : n ⟶ m}
  证明: by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.mono_iff_injective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.asEquivalence_functor, Functor.mono_map_iff_mono, NonemptyFinLinOrd, NonemptyFinLinOrd.coe_of, NonemptyFinLinOrd.mono_iff_injective, asEquivalence_functor, coe_of, functor, hom_ofHom, mono_iff_injective, mono_map_iff_mono, skeletalEquivalence, skeletalEquivalence.functor, skeletalFunctor_map, skeletalFunctor_obj
-/
theorem mono_iff_injective {n m : SimplexCategory} {f : n ⟶ m} :
    Mono f ↔ Function.Injective f.toOrderHom := by
  rw [← Functor.mono_map_iff_mono skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.mono_iff_injective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `epi_iff_surjective` / 定理 `epi_iff_surjective`

English:
theorem epi_iff_surjective
  given: {n m : SimplexCategory} {f : n ⟶ m}
  proof: by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.epi_iff_surjective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

中文:
定理 epi_iff_surjective
  条件: {n m : SimplexCategory} {f : n ⟶ m}
  证明: by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.epi_iff_surjective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.hom_ofHom, Functor, Functor.asEquivalence_functor, Functor.epi_map_iff_epi, NonemptyFinLinOrd, NonemptyFinLinOrd.coe_of, NonemptyFinLinOrd.epi_iff_surjective, asEquivalence_functor, coe_of, epi_iff_surjective, epi_map_iff_epi, functor, hom_ofHom, skeletalEquivalence, skeletalEquivalence.functor, skeletalFunctor_map, skeletalFunctor_obj
-/
theorem epi_iff_surjective {n m : SimplexCategory} {f : n ⟶ m} :
    Epi f ↔ Function.Surjective f.toOrderHom := by
  rw [← Functor.epi_map_iff_epi skeletalEquivalence.functor]
  dsimp only [skeletalEquivalence, Functor.asEquivalence_functor]
  simp only [skeletalFunctor_obj, skeletalFunctor_map,
    NonemptyFinLinOrd.epi_iff_surjective, NonemptyFinLinOrd.coe_of, ConcreteCategory.hom_ofHom]

/--
theorem `len_le_of_mono` / 定理 `len_le_of_mono`

English:
theorem len_le_of_mono
  given: {x y : SimplexCategory} (f : x ⟶ y) [Mono f]
  statement: x.len <= y.len
  proof: by
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun
    (by dsimp; rwa [← mono_iff_injective])

中文:
定理 len_le_of_mono
  条件: {x y : SimplexCategory} (f : x ⟶ y) [Mono f]
  结论: x.len <= y.len
  证明: by
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun
    (by dsimp; rwa [← mono_iff_injective])

Depends on / 依赖: Fintype, Fintype.card_le_of_injective, card_le_of_injective, f.toOrderHom.toFun, mono_iff_injective, toOrderHom
-/
theorem len_le_of_mono {x y : SimplexCategory} (f : x ⟶ y) [Mono f] : x.len <= y.len := by
  simpa using Fintype.card_le_of_injective f.toOrderHom.toFun
    (by dsimp; rwa [← mono_iff_injective])

/--
theorem `le_of_mono` / 定理 `le_of_mono`

English:
theorem le_of_mono
  given: {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Mono f]
  statement: n <= m
  proof: len_le_of_mono f

中文:
定理 le_of_mono
  条件: {n m : 自然数} (f : ⦋n⦌ ⟶ ⦋m⦌) [Mono f]
  结论: n <= m
  证明: len_le_of_mono f

Depends on / 依赖: len_le_of_mono
-/
theorem le_of_mono {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Mono f] : n <= m :=
  len_le_of_mono f

/--
theorem `len_le_of_epi` / 定理 `len_le_of_epi`

English:
theorem len_le_of_epi
  given: {x y : SimplexCategory} (f : x ⟶ y) [Epi f]
  statement: y.len <= x.len
  proof: by
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun
    (by dsimp; rwa [← epi_iff_surjective])

中文:
定理 len_le_of_epi
  条件: {x y : SimplexCategory} (f : x ⟶ y) [Epi f]
  结论: y.len <= x.len
  证明: by
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun
    (by dsimp; rwa [← epi_iff_surjective])

Depends on / 依赖: Fintype, Fintype.card_le_of_surjective, card_le_of_surjective, epi_iff_surjective, f.toOrderHom.toFun, toOrderHom
-/
theorem len_le_of_epi {x y : SimplexCategory} (f : x ⟶ y) [Epi f] : y.len <= x.len := by
  simpa using Fintype.card_le_of_surjective f.toOrderHom.toFun
    (by dsimp; rwa [← epi_iff_surjective])

/--
theorem `le_of_epi` / 定理 `le_of_epi`

English:
theorem le_of_epi
  given: {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
  statement: m <= n
  proof: len_le_of_epi f

中文:
定理 le_of_epi
  条件: {n m : 自然数} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f]
  结论: m <= n
  证明: len_le_of_epi f

Depends on / 依赖: len_le_of_epi
-/
theorem le_of_epi {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [Epi f] : m <= n := len_le_of_epi f

/--
lemma `len_eq_of_isIso` / 引理 `len_eq_of_isIso`

English:
lemma len_eq_of_isIso
  given: {x y : SimplexCategory} (f : x ⟶ y) [IsIso f]
  statement: x.len = y.len
  proof: le_antisymm (len_le_of_mono f) (len_le_of_epi f)

中文:
引理 len_eq_of_isIso
  条件: {x y : SimplexCategory} (f : x ⟶ y) [IsIso f]
  结论: x.len = y.len
  证明: le_antisymm (len_le_of_mono f) (len_le_of_epi f)

Depends on / 依赖: le_antisymm, len_le_of_epi, len_le_of_mono
-/
lemma len_eq_of_isIso {x y : SimplexCategory} (f : x ⟶ y) [IsIso f] : x.len = y.len :=
  le_antisymm (len_le_of_mono f) (len_le_of_epi f)

/--
lemma `eq_of_isIso` / 引理 `eq_of_isIso`

English:
lemma eq_of_isIso
  given: {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [IsIso f]
  statement: n = m
  proof: len_eq_of_isIso f

中文:
引理 eq_of_isIso
  条件: {n m : 自然数} (f : ⦋n⦌ ⟶ ⦋m⦌) [IsIso f]
  结论: n = m
  证明: len_eq_of_isIso f

Depends on / 依赖: len_eq_of_isIso
-/
lemma eq_of_isIso {n m : Nat} (f : ⦋n⦌ ⟶ ⦋m⦌) [IsIso f] : n = m :=
  len_eq_of_isIso f

instance {n : Nat} {i : Fin (n + 1)} : Epi (σ i) := by
  simpa only [epi_iff_surjective] using! Fin.predAbove_surjective i

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget SimplexCategory).ReflectsIsomorphisms
  body: ⟨fun f hf =>
    Iso.isIso_hom
      { hom := f
        inv := Hom.mk
            { toFun := inv ((forget SimplexCategory).map f)
              monotone' := fun y₁ y₂ h => by
                by_cases h' : y₁ < y₂
                · by_contra h''
                  apply not_le.mpr h'
                 

中文:
实例 :
  签名: (forget SimplexCategory).ReflectsIsomorphisms
  定义体: ⟨fun f hf =>
    Iso.isIso_hom
      { hom := f
        inv := Hom.mk
            { toFun := inv ((forget SimplexCategory).map f)
              monotone' := fun y₁ y₂ h => by
                by_cases h' : y₁ < y₂
                · by_contra h''
                  apply not_le.mpr h'
                 

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, Hom.mk, Iso.hom_inv_id_apply, Iso.inv_hom_id, Iso.isIso_hom, SimplexCategory, all_goals, congr_hom, convert, eq_of_le_of_not_lt, f.toOrderHom.monotone, forget, hom_inv_id, hom_inv_id_apply, inv_hom_id, isIso_hom, le_of_not_ge, monotone, not_le
-/
instance : (forget SimplexCategory).ReflectsIsomorphisms :=
  ⟨fun f hf =>
    Iso.isIso_hom
      { hom := f
        inv := Hom.mk
            { toFun := inv ((forget SimplexCategory).map f)
              monotone' := fun y₁ y₂ h => by
                by_cases h' : y₁ < y₂
                · by_contra h''
                  apply not_le.mpr h'
                  convert! f.toOrderHom.monotone (le_of_not_ge h'')
                  all_goals
                    exact (ConcreteCategory.congr_hom (Iso.inv_hom_id
                      (asIso ((forget SimplexCategory).map f))) _).symm
                · rw [eq_of_le_of_not_lt h h'] }
        hom_inv_id := by
          ext x : 3
          exact Iso.hom_inv_id_apply (asIso ((forget _).map f)) x
        inv_hom_id := by
          ext x : 3
          exact Iso.inv_hom_id_apply (asIso ((forget _).map f)) x }⟩

/--
theorem `isIso_of_bijective` / 定理 `isIso_of_bijective`

English:
theorem isIso_of_bijective
  statement: {x y : SimplexCategory} {f : x ⟶ y}
  proof: haveI : IsIso ((forget SimplexCategory).map f) := (isIso_iff_bijective _).mpr hf
  isIso_of_reflects_iso f (forget SimplexCategory)

中文:
定理 isIso_of_bijective
  结论: {x y : SimplexCategory} {f : x ⟶ y}
  证明: haveI : IsIso ((forget SimplexCategory).map f) := (isIso_iff_bijective _).mpr hf
  isIso_of_reflects_iso f (forget SimplexCategory)

Depends on / 依赖: SimplexCategory, forget, isIso_iff_bijective, isIso_of_reflects_iso
-/
theorem isIso_of_bijective {x y : SimplexCategory} {f : x ⟶ y}
    (hf : Function.Bijective f.toOrderHom.toFun) : IsIso f :=
  haveI : IsIso ((forget SimplexCategory).map f) := (isIso_iff_bijective _).mpr hf
  isIso_of_reflects_iso f (forget SimplexCategory)

/--
lemma `isIso_iff_of_mono` / 引理 `isIso_iff_of_mono`

English:
lemma isIso_iff_of_mono
  given: {n m : SimplexCategory} (f : n ⟶ m) [hf : Mono f]
  proof: by
  refine ⟨fun _ => len_eq_of_isIso f, fun h => ?_⟩
  obtain rfl : n = m := by aesop
  rw [mono_iff_injective] at hf
  exact isIso_of_bijective ⟨hf, by rwa [← Finite.injective_iff_surjective]⟩

中文:
引理 isIso_iff_of_mono
  条件: {n m : SimplexCategory} (f : n ⟶ m) [hf : Mono f]
  证明: by
  refine ⟨fun _ => len_eq_of_isIso f, fun h => ?_⟩
  obtain rfl : n = m := by aesop
  rw [mono_iff_injective] at hf
  exact isIso_of_bijective ⟨hf, by rwa [← Finite.injective_iff_surjective]⟩

Depends on / 依赖: Finite, Finite.injective_iff_surjective, injective_iff_surjective, isIso_of_bijective, len_eq_of_isIso, mono_iff_injective
-/
lemma isIso_iff_of_mono {n m : SimplexCategory} (f : n ⟶ m) [hf : Mono f] :
    IsIso f ↔ n.len = m.len := by
  refine ⟨fun _ => len_eq_of_isIso f, fun h => ?_⟩
  obtain rfl : n = m := by aesop
  rw [mono_iff_injective] at hf
  exact isIso_of_bijective ⟨hf, by rwa [← Finite.injective_iff_surjective]⟩

instance {n : Nat} {i : Fin (n + 2)} : Mono (δ i) := by
  rw [mono_iff_injective]
  exact Fin.succAbove_right_injective

/--
lemma `isIso_iff_of_epi` / 引理 `isIso_iff_of_epi`

English:
lemma isIso_iff_of_epi
  given: {n m : SimplexCategory} (f : n ⟶ m) [hf : Epi f]
  proof: by
  refine ⟨fun _ => len_eq_of_isIso f, fun h => ?_⟩
  obtain rfl : n = m := by aesop
  rw [epi_iff_surjective] at hf
  exact isIso_of_bijective ⟨by rwa [Finite.injective_iff_surjective], hf⟩

中文:
引理 isIso_iff_of_epi
  条件: {n m : SimplexCategory} (f : n ⟶ m) [hf : Epi f]
  证明: by
  refine ⟨fun _ => len_eq_of_isIso f, fun h => ?_⟩
  obtain rfl : n = m := by aesop
  rw [epi_iff_surjective] at hf
  exact isIso_of_bijective ⟨by rwa [Finite.injective_iff_surjective], hf⟩

Depends on / 依赖: Finite, Finite.injective_iff_surjective, epi_iff_surjective, injective_iff_surjective, isIso_of_bijective, len_eq_of_isIso
-/
lemma isIso_iff_of_epi {n m : SimplexCategory} (f : n ⟶ m) [hf : Epi f] :
    IsIso f ↔ n.len = m.len := by
  refine ⟨fun _ => len_eq_of_isIso f, fun h => ?_⟩
  obtain rfl : n = m := by aesop
  rw [epi_iff_surjective] at hf
  exact isIso_of_bijective ⟨by rwa [Finite.injective_iff_surjective], hf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Balanced SimplexCategory
  body: by
    rw [isIso_iff_of_epi]
    exact le_antisymm (len_le_of_mono f) (len_le_of_epi f)

中文:
实例 :
  签名: Balanced SimplexCategory
  定义体: by
    rw [isIso_iff_of_epi]
    exact le_antisymm (len_le_of_mono f) (len_le_of_epi f)

Depends on / 依赖: isIso_iff_of_epi, le_antisymm, len_le_of_epi, len_le_of_mono
-/
instance : Balanced SimplexCategory where
  isIso_of_mono_of_epi f _ _ := by
    rw [isIso_iff_of_epi]
    exact le_antisymm (len_le_of_mono f) (len_le_of_epi f)

/-- An isomorphism in `SimplexCategory` induces an `OrderIso`. -/
@[simp]
/--
Definition of `orderIsoOfIso` / `orderIsoOfIso` 的定义

English:
definition orderIsoOfIso
  signature: {x y : SimplexCategory} (e : x ≅ y)
  body: Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using! congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using! congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_ho

中文:
定义 orderIsoOfIso
  签名: {x y : SimplexCategory} (e : x ≅ y)
  定义体: Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using! congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using! congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_ho

Depends on / 依赖: Equiv.toOrderIso, Hom.toOrderHom, congr_arg, e.hom.toOrderHom, e.hom.toOrderHom.monotone, e.hom_inv_id, e.inv.toOrderHom, e.inv.toOrderHom.monotone, e.inv_hom_id, hom_inv_id, invFun, inv_hom_id, left_inv, monotone, right_inv, toOrderHom, toOrderIso
-/
def orderIsoOfIso {x y : SimplexCategory} (e : x ≅ y) : Fin (x.len + 1) ≃o Fin (y.len + 1) :=
  Equiv.toOrderIso
    { toFun := e.hom.toOrderHom
      invFun := e.inv.toOrderHom
      left_inv := fun i => by
        simpa only using! congr_arg (fun φ => (Hom.toOrderHom φ) i) e.hom_inv_id
      right_inv := fun i => by
        simpa only using! congr_arg (fun φ => (Hom.toOrderHom φ) i) e.inv_hom_id }
    e.hom.toOrderHom.monotone e.inv.toOrderHom.monotone

/--
theorem `iso_eq_iso_refl` / 定理 `iso_eq_iso_refl`

English:
theorem iso_eq_iso_refl
  given: {x : SimplexCategory} (e : x ≅ x)
  statement: e = Iso.refl x
  proof: by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i

中文:
定理 iso_eq_iso_refl
  条件: {x : SimplexCategory} (e : x ≅ x)
  结论: e = Iso.refl x
  证明: by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Finset, Finset.card_fin, Finset.mem_univ, Finset.orderEmbOfFin_unique, Finset.univ, Iso.refl, card_fin, congr_fun, mem_univ, orderEmbOfFin_unique, orderIsoOfIso, x.len
-/
theorem iso_eq_iso_refl {x : SimplexCategory} (e : x ≅ x) : e = Iso.refl x := by
  have h : (Finset.univ : Finset (Fin (x.len + 1))).card = x.len + 1 := Finset.card_fin (x.len + 1)
  have eq₁ := Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso e) i)
  have eq₂ :=
    Finset.orderEmbOfFin_unique' h fun i => Finset.mem_univ ((orderIsoOfIso (Iso.refl x)) i)
  ext : 4
  exact DFunLike.congr_fun (eq₁.trans eq₂.symm) _

/--
theorem `eq_id_of_isIso` / 定理 `eq_id_of_isIso`

English:
theorem eq_id_of_isIso
  given: {x : SimplexCategory} (f : x ⟶ x) [IsIso f]
  statement: f = 𝟙 _
  proof: congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))

中文:
定理 eq_id_of_isIso
  条件: {x : SimplexCategory} (f : x ⟶ x) [IsIso f]
  结论: f = 𝟙 _
  证明: congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))

Depends on / 依赖: congr_arg, iso_eq_iso_refl
-/
theorem eq_id_of_isIso {x : SimplexCategory} (f : x ⟶ x) [IsIso f] : f = 𝟙 _ :=
  congr_arg (fun φ : _ ≅ _ => φ.hom) (iso_eq_iso_refl (asIso f))

set_option backward.defeqAttrib.useBackward true in
/--
theorem `eq_σ_comp_of_not_injective'` / 定理 `eq_σ_comp_of_not_injective'`

English:
theorem eq_σ_comp_of_not_injective'
  statement: {n : Nat} {Δ' : SimplexCategory} (θ : ⦋n + 1⦌ ⟶ Δ')
  proof: by
  use δ i.succ ≫ θ
  ext x : 3
  simp only [len_mk, σ, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    Function.comp_apply, Fin.predAboveOrderHom_coe]
  by_cases h' : x <= Fin.castSucc i
  · rw [Fin.predAbove_of_le_castSucc i x h']
    dsimp [δ]
    rw [Fin.succAbove_of_castSucc

中文:
定理 eq_σ_comp_of_not_injective'
  结论: {n : 自然数} {Δ' : SimplexCategory} (θ : ⦋n + 1⦌ ⟶ Δ')
  证明: by
  use δ i.succ ≫ θ
  ext x : 3
  simp only [len_mk, σ, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    Function.comp_apply, Fin.predAboveOrderHom_coe]
  by_cases h' : x <= Fin.castSucc i
  · rw [Fin.predAbove_of_le_castSucc i x h']
    dsimp [δ]
    rw [Fin.succAbove_of_castSucc

Depends on / 依赖: Fin.castSucc, Fin.castSucc_castPred, Fin.castSucc_lt_succ_iff.mpr, Fin.predAboveOrderHom_coe, Fin.predAbove_of_le_castSucc, Fin.succAbove_of_castSucc_lt, Fin.succ_pred, Function, Function.comp_apply, Hom.toOrderHom_mk, OrderHom, OrderHom.comp_coe, castSucc, castSucc_castPred, castSucc_lt_succ_iff, comp_apply, comp_coe, comp_toOrderHom, i.succ, len_mk
-/
theorem eq_σ_comp_of_not_injective' {n : Nat} {Δ' : SimplexCategory} (θ : ⦋n + 1⦌ ⟶ Δ')
    (i : Fin (n + 1)) (hi : θ.toOrderHom (Fin.castSucc i) = θ.toOrderHom i.succ) :
    exists θ' : ⦋n⦌ ⟶ Δ', θ = σ i ≫ θ' := by
  use δ i.succ ≫ θ
  ext x : 3
  simp only [len_mk, σ, mkHom, comp_toOrderHom, Hom.toOrderHom_mk, OrderHom.comp_coe,
    Function.comp_apply, Fin.predAboveOrderHom_coe]
  by_cases h' : x <= Fin.castSucc i
  · rw [Fin.predAbove_of_le_castSucc i x h']
    dsimp [δ]
    rw [Fin.succAbove_of_castSucc_lt]
    · rw [Fin.castSucc_castPred]
    · exact (Fin.castSucc_lt_succ_iff.mpr h')
  · simp only [not_le] at h'
let y := x.pred by rintro (rfl : x = 0); simp at h'
    have hy : x = y.succ := (Fin.succ_pred x _).symm
    rw [hy] at h' ⊢
    rw [Fin.predAbove_of_castSucc_lt i y.succ h']; rw [Fin.pred_succ]
    by_cases h'' : y = i
    · rw [h'']
      refine hi.symm.trans ?_
      congr 1
      dsimp [δ]
      rw [Fin.succAbove_of_castSucc_lt i.succ]
      exact Fin.castSucc_lt_succ
    · dsimp [δ]
      rw [Fin.succAbove_of_le_castSucc i.succ _]
      simp only [Fin.lt_def, Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc,
        Nat.lt_succ_iff, Fin.ext_iff] at h' h'' ⊢
      lia

/--
theorem `eq_σ_comp_of_not_injective` / 定理 `eq_σ_comp_of_not_injective`

English:
theorem eq_σ_comp_of_not_injective
  statement: {n : Nat} {Δ' : SimplexCategory} (θ : ⦋n + 1⦌ ⟶ Δ')
  proof: by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : exists x y : Fin (n + 2), (Hom.toOrderHom θ) x = (Hom.toOrderHom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩


中文:
定理 eq_σ_comp_of_not_injective
  结论: {n : 自然数} {Δ' : SimplexCategory} (θ : ⦋n + 1⦌ ⟶ Δ')
  证明: by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : exists x y : Fin (n + 2), (Hom.toOrderHom θ) x = (Hom.toOrderHom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩


Depends on / 依赖: Function, Function.Injective, Injective, exists_prop, not_forall
-/
theorem eq_σ_comp_of_not_injective {n : Nat} {Δ' : SimplexCategory} (θ : ⦋n + 1⦌ ⟶ Δ')
    (hθ : ¬Function.Injective θ.toOrderHom) :
    exists (i : Fin (n + 1)) (θ' : ⦋n⦌ ⟶ Δ'), θ = σ i ≫ θ' := by
  simp only [Function.Injective, exists_prop, not_forall] at hθ
  -- as θ is not injective, there exists `x<y` such that `θ x = θ y`
  -- and then, `θ x = θ (x+1)`
  have hθ₂ : exists x y : Fin (n + 2), (Hom.toOrderHom θ) x = (Hom.toOrderHom θ) y ∧ x < y := by
    rcases hθ with ⟨x, y, ⟨h₁, h₂⟩⟩
    by_cases h : x < y
    · exact ⟨x, y, ⟨h₁, h⟩⟩
    · refine ⟨y, x, ⟨h₁.symm, ?_⟩⟩
      lia
  rcases hθ₂ with ⟨x, y, ⟨h₁, h₂⟩⟩
  use x.castPred ((Fin.le_last _).trans_lt' h₂).ne
  apply eq_σ_comp_of_not_injective'
  apply le_antisymm
  · exact θ.toOrderHom.monotone (le_of_lt Fin.castSucc_lt_succ)
  · rw [Fin.castSucc_castPred, h₁]
    exact θ.toOrderHom.monotone ((Fin.succ_castPred_le_iff _).mpr h₂)

/--
theorem `eq_comp_δ_of_not_surjective'` / 定理 `eq_comp_δ_of_not_surjective'`

English:
theorem eq_comp_δ_of_not_surjective'
  statement: {n : Nat} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌)
  proof: by
  use θ ≫ σ (.predAbove (.last n) i)
  ext x : 3
  suffices forall j != i, i.succAbove (((Fin.last n).predAbove i).predAbove j) = j by
    dsimp [δ, σ]
exact .symm this _ (hi _)
  intro j hj
  cases i using Fin.lastCases <;> simp [hj]

中文:
定理 eq_comp_δ_of_not_surjective'
  结论: {n : 自然数} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌)
  证明: by
  use θ ≫ σ (.predAbove (.last n) i)
  ext x : 3
  suffices forall j != i, i.succAbove (((Fin.last n).predAbove i).predAbove j) = j by
    dsimp [δ, σ]
exact .symm this _ (hi _)
  intro j hj
  cases i using Fin.lastCases <;> simp [hj]

Depends on / 依赖: Fin.last, Fin.lastCases, i.succAbove, lastCases, predAbove, succAbove
-/
theorem eq_comp_δ_of_not_surjective' {n : Nat} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌)
    (i : Fin (n + 2)) (hi : forall x, θ.toOrderHom x != i) : exists θ' : Δ ⟶ ⦋n⦌, θ = θ' ≫ δ i := by
  use θ ≫ σ (.predAbove (.last n) i)
  ext x : 3
  suffices forall j != i, i.succAbove (((Fin.last n).predAbove i).predAbove j) = j by
    dsimp [δ, σ]
exact .symm this _ (hi _)
  intro j hj
  cases i using Fin.lastCases <;> simp [hj]

/--
theorem `eq_comp_δ_of_not_surjective` / 定理 `eq_comp_δ_of_not_surjective`

English:
theorem eq_comp_δ_of_not_surjective
  statement: {n : Nat} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌)
  proof: by
  obtain ⟨i, hi⟩ := not_forall.mp hθ
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)

中文:
定理 eq_comp_δ_of_not_surjective
  结论: {n : 自然数} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌)
  证明: by
  obtain ⟨i, hi⟩ := not_forall.mp hθ
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)

Depends on / 依赖: not_exists, not_exists.mp, not_forall, not_forall.mp
-/
theorem eq_comp_δ_of_not_surjective {n : Nat} {Δ : SimplexCategory} (θ : Δ ⟶ ⦋n + 1⦌)
    (hθ : ¬Function.Surjective θ.toOrderHom) :
    exists (i : Fin (n + 2)) (θ' : Δ ⟶ ⦋n⦌), θ = θ' ≫ δ i := by
  obtain ⟨i, hi⟩ := not_forall.mp hθ
  use i
  exact eq_comp_δ_of_not_surjective' θ i (not_exists.mp hi)

/--
theorem `eq_id_of_mono` / 定理 `eq_id_of_mono`

English:
theorem eq_id_of_mono
  given: {x : SimplexCategory} (i : x ⟶ x) [Mono i]
  statement: i = 𝟙 _
  proof: have := (isIso_iff_of_mono i).mpr rfl
  eq_id_of_isIso _

中文:
定理 eq_id_of_mono
  条件: {x : SimplexCategory} (i : x ⟶ x) [Mono i]
  结论: i = 𝟙 _
  证明: have := (isIso_iff_of_mono i).mpr rfl
  eq_id_of_isIso _

Depends on / 依赖: eq_id_of_isIso, isIso_iff_of_mono
-/
theorem eq_id_of_mono {x : SimplexCategory} (i : x ⟶ x) [Mono i] : i = 𝟙 _ :=
  have := (isIso_iff_of_mono i).mpr rfl
  eq_id_of_isIso _

/--
theorem `eq_id_of_epi` / 定理 `eq_id_of_epi`

English:
theorem eq_id_of_epi
  given: {x : SimplexCategory} (i : x ⟶ x) [Epi i]
  statement: i = 𝟙 _
  proof: have := (isIso_iff_of_epi i).mpr rfl
  eq_id_of_isIso _

中文:
定理 eq_id_of_epi
  条件: {x : SimplexCategory} (i : x ⟶ x) [Epi i]
  结论: i = 𝟙 _
  证明: have := (isIso_iff_of_epi i).mpr rfl
  eq_id_of_isIso _

Depends on / 依赖: eq_id_of_isIso, isIso_iff_of_epi
-/
theorem eq_id_of_epi {x : SimplexCategory} (i : x ⟶ x) [Epi i] : i = 𝟙 _ :=
  have := (isIso_iff_of_epi i).mpr rfl
  eq_id_of_isIso _

/--
theorem `eq_σ_of_epi` / 定理 `eq_σ_of_epi`

English:
theorem eq_σ_of_epi
  given: {n : Nat} (θ : ⦋n + 1⦌ ⟶ ⦋n⦌) [Epi θ]
  statement: exists i : Fin (n + 1), θ = σ i
  proof: by
  obtain ⟨i, θ', h⟩ := eq_σ_comp_of_not_injective θ (by
    rw [← mono_iff_injective]
    grind [-> le_of_mono])
  use i
  have : Epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  have := CategoryTheory.epi_of_epi (σ i) θ'
  rw [h]; rw [eq_id_of_epi θ']; rw [Category.comp_id]

中文:
定理 eq_σ_of_epi
  条件: {n : 自然数} (θ : ⦋n + 1⦌ ⟶ ⦋n⦌) [Epi θ]
  结论: 存在 i : Fin (n + 1), θ = σ i
  证明: by
  obtain ⟨i, θ', h⟩ := eq_σ_comp_of_not_injective θ (by
    rw [← mono_iff_injective]
    grind [-> le_of_mono])
  use i
  have : Epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  have := CategoryTheory.epi_of_epi (σ i) θ'
  rw [h]; rw [eq_id_of_epi θ']; rw [Category.comp_id]

Depends on / 依赖: Category, Category.comp_id, CategoryTheory, CategoryTheory.epi_of_epi, comp_id, epi_of_epi, eq_id_of_epi, infer_instance, le_of_mono, mono_iff_injective
-/
theorem eq_σ_of_epi {n : Nat} (θ : ⦋n + 1⦌ ⟶ ⦋n⦌) [Epi θ] : exists i : Fin (n + 1), θ = σ i := by
  obtain ⟨i, θ', h⟩ := eq_σ_comp_of_not_injective θ (by
    rw [← mono_iff_injective]
    grind [-> le_of_mono])
  use i
  have : Epi (σ i ≫ θ') := by
    rw [← h]
    infer_instance
  have := CategoryTheory.epi_of_epi (σ i) θ'
  rw [h]; rw [eq_id_of_epi θ']; rw [Category.comp_id]

/--
theorem `eq_δ_of_mono` / 定理 `eq_δ_of_mono`

English:
theorem eq_δ_of_mono
  given: {n : Nat} (θ : ⦋n⦌ ⟶ ⦋n + 1⦌) [Mono θ]
  statement: exists i : Fin (n + 2), θ = δ i
  proof: by
  obtain ⟨i, θ', h⟩ := eq_comp_δ_of_not_surjective θ (by
    rw [← epi_iff_surjective]
    grind [-> le_of_epi])
  use i
  have : Mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  have := CategoryTheory.mono_of_mono θ' (δ i)
  rw [h]; rw [eq_id_of_mono θ']; rw [Category.id_comp]

中文:
定理 eq_δ_of_mono
  条件: {n : 自然数} (θ : ⦋n⦌ ⟶ ⦋n + 1⦌) [Mono θ]
  结论: 存在 i : Fin (n + 2), θ = δ i
  证明: by
  obtain ⟨i, θ', h⟩ := eq_comp_δ_of_not_surjective θ (by
    rw [← epi_iff_surjective]
    grind [-> le_of_epi])
  use i
  have : Mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  have := CategoryTheory.mono_of_mono θ' (δ i)
  rw [h]; rw [eq_id_of_mono θ']; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, CategoryTheory, CategoryTheory.mono_of_mono, epi_iff_surjective, eq_id_of_mono, id_comp, infer_instance, le_of_epi, mono_of_mono
-/
theorem eq_δ_of_mono {n : Nat} (θ : ⦋n⦌ ⟶ ⦋n + 1⦌) [Mono θ] : exists i : Fin (n + 2), θ = δ i := by
  obtain ⟨i, θ', h⟩ := eq_comp_δ_of_not_surjective θ (by
    rw [← epi_iff_surjective]
    grind [-> le_of_epi])
  use i
  have : Mono (θ' ≫ δ i) := by
    rw [← h]
    infer_instance
  have := CategoryTheory.mono_of_mono θ' (δ i)
  rw [h]; rw [eq_id_of_mono θ']; rw [Category.id_comp]

/--
theorem `len_lt_of_mono` / 定理 `len_lt_of_mono`

English:
theorem len_lt_of_mono
  given: {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] (hi' : Δ != Δ')
  proof: by
  grind [-> len_le_of_mono, SimplexCategory.ext]

中文:
定理 len_lt_of_mono
  条件: {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] (hi' : Δ != Δ')
  证明: by
  grind [-> len_le_of_mono, SimplexCategory.ext]

Depends on / 依赖: SimplexCategory, SimplexCategory.ext, len_le_of_mono
-/
theorem len_lt_of_mono {Δ' Δ : SimplexCategory} (i : Δ' ⟶ Δ) [Mono i] (hi' : Δ != Δ') :
    Δ'.len < Δ.len := by
  grind [-> len_le_of_mono, SimplexCategory.ext]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SplitEpiCategory SimplexCategory
  body: skeletalEquivalence.inverse.splitEpiCategoryImpOfIsEquivalence

中文:
实例 :
  签名: SplitEpiCategory SimplexCategory
  定义体: skeletalEquivalence.inverse.splitEpiCategoryImpOfIsEquivalence

Depends on / 依赖: inverse, skeletalEquivalence, skeletalEquivalence.inverse.splitEpiCategoryImpOfIsEquivalence, splitEpiCategoryImpOfIsEquivalence
-/
noncomputable instance : SplitEpiCategory SimplexCategory :=
  skeletalEquivalence.inverse.splitEpiCategoryImpOfIsEquivalence

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasStrongEpiMonoFactorisations SimplexCategory
  body: Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    SimplexCategory.skeletalEquivalence.inverse

中文:
实例 :
  签名: HasStrongEpiMonoFactorisations SimplexCategory
  定义体: Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    SimplexCategory.skeletalEquivalence.inverse

Depends on / 依赖: Functor, Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence, SimplexCategory, SimplexCategory.skeletalEquivalence.inverse, hasStrongEpiMonoFactorisations_imp_of_isEquivalence, inverse, skeletalEquivalence
-/
instance : HasStrongEpiMonoFactorisations SimplexCategory :=
  Functor.hasStrongEpiMonoFactorisations_imp_of_isEquivalence
    SimplexCategory.skeletalEquivalence.inverse

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasStrongEpiImages SimplexCategory
  body: Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations

中文:
实例 :
  签名: HasStrongEpiImages SimplexCategory
  定义体: Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations

Depends on / 依赖: Limits, Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations, hasStrongEpiImages_of_hasStrongEpiMonoFactorisations
-/
instance : HasStrongEpiImages SimplexCategory :=
  Limits.hasStrongEpiImages_of_hasStrongEpiMonoFactorisations

instance (Δ Δ' : SimplexCategory) (θ : Δ ⟶ Δ') : Epi (factorThruImage θ) :=
  StrongEpi.epi

/--
theorem `image_eq` / 定理 `image_eq`

English:
theorem image_eq
  statement: {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ Δ''}
  proof: by
  have := strongEpi_of_epi e
  let e := image.isoStrongEpiMono e i fac
  ext
  exact le_antisymm (len_le_of_epi e.hom) (len_le_of_mono e.hom)

中文:
定理 image_eq
  结论: {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ Δ''}
  证明: by
  have := strongEpi_of_epi e
  let e := image.isoStrongEpiMono e i fac
  ext
  exact le_antisymm (len_le_of_epi e.hom) (len_le_of_mono e.hom)

Depends on / 依赖: e.hom, image.isoStrongEpiMono, isoStrongEpiMono, le_antisymm, len_le_of_epi, len_le_of_mono, strongEpi_of_epi
-/
theorem image_eq {Δ Δ' Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ Δ'} [Epi e] {i : Δ' ⟶ Δ''}
    [Mono i] (fac : e ≫ i = φ) : image φ = Δ' := by
  have := strongEpi_of_epi e
  let e := image.isoStrongEpiMono e i fac
  ext
  exact le_antisymm (len_le_of_epi e.hom) (len_le_of_mono e.hom)

/--
theorem `image_ι_eq` / 定理 `image_ι_eq`

English:
theorem image_ι_eq
  statement: {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
  proof: by
  have := strongEpi_of_epi e
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac]; rw [SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom]; rw [Category.id_comp]

中文:
定理 image_ι_eq
  结论: {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
  证明: by
  have := strongEpi_of_epi e
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac]; rw [SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom]; rw [Category.id_comp]

Depends on / 依赖: Category, Category.id_comp, SimplexCategory, SimplexCategory.eq_id_of_isIso, eq_id_of_isIso, id_comp, image.isoStrongEpiMono, image.isoStrongEpiMono_hom_comp_, isoStrongEpiMono, strongEpi_of_epi
-/
theorem image_ι_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : image.ι φ = i := by
  have := strongEpi_of_epi e
  rw [← image.isoStrongEpiMono_hom_comp_ι e i fac]; rw [SimplexCategory.eq_id_of_isIso (image.isoStrongEpiMono e i fac).hom]; rw [Category.id_comp]

/--
theorem `factorThruImage_eq` / 定理 `factorThruImage_eq`

English:
theorem factorThruImage_eq
  statement: {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
  proof: by
  rw [← cancel_mono i]; rw [fac]; rw [← image_ι_eq fac]; rw [image.fac]

中文:
定理 factorThruImage_eq
  结论: {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
  证明: by
  rw [← cancel_mono i]; rw [fac]; rw [← image_ι_eq fac]; rw [image.fac]

Depends on / 依赖: cancel_mono, image.fac
-/
theorem factorThruImage_eq {Δ Δ'' : SimplexCategory} {φ : Δ ⟶ Δ''} {e : Δ ⟶ image φ} [Epi e]
    {i : image φ ⟶ Δ''} [Mono i] (fac : e ≫ i = φ) : factorThruImage φ = e := by
  rw [← cancel_mono i]; rw [fac]; rw [← image_ι_eq fac]; rw [image.fac]

end EpiMono

/--
Definition of `toPartOrd` / `toPartOrd` 的定义

English:
definition toPartOrd
  signature: : SimplexCategory ⥤ PartOrd.{u}
  body: skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ⋙
    forget₂ FinPartOrd PartOrd ⋙ PartOrd.uliftFunctor

@[simp]

中文:
定义 toPartOrd
  签名: : SimplexCategory ⥤ PartOrd.{u}
  定义体: skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ⋙
    forget₂ FinPartOrd PartOrd ⋙ PartOrd.uliftFunctor

@[simp]

Depends on / 依赖: FinPartOrd, NonemptyFinLinOrd, PartOrd, PartOrd.uliftFunctor, skeletalFunctor, uliftFunctor
-/
def toPartOrd : SimplexCategory ⥤ PartOrd.{u} :=
  skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd FinPartOrd ⋙
    forget₂ FinPartOrd PartOrd ⋙ PartOrd.uliftFunctor

@[simp]
/--
lemma `toPartOrd_obj` / 引理 `toPartOrd_obj`

English:
lemma toPartOrd_obj
  given: (n : SimplexCategory)
  proof: rfl

@[simp]

中文:
引理 toPartOrd_obj
  条件: (n : SimplexCategory)
  证明: rfl

@[simp]
-/
lemma toPartOrd_obj (n : SimplexCategory) :
    toPartOrd.{u}.obj n = .of (ULift.{u} (Fin (n.len + 1))) := rfl

@[simp]
/--
lemma `toPartOrd_map_apply` / 引理 `toPartOrd_map_apply`

English:
lemma toPartOrd_map_apply
  given: {n m : SimplexCategory} (f : n ⟶ m) (i : (Fin (n.len + 1)))
  proof: rfl

中文:
引理 toPartOrd_map_apply
  条件: {n m : SimplexCategory} (f : n ⟶ m) (i : (Fin (n.len + 1)))
  证明: rfl
-/
lemma toPartOrd_map_apply {n m : SimplexCategory} (f : n ⟶ m) (i : (Fin (n.len + 1))) :
    dsimp% toPartOrd.{u}.map f (ULift.up i) = ULift.up (f i) := rfl

/-- This functor `SimplexCategory ⥤ Cat` sends `⦋n⦌` (for `n : ℕ`)
to the category attached to the ordered set `{0, 1, ..., n}` -/
@[simps! obj map]
/--
Definition of `toCat` / `toCat` 的定义

English:
definition toCat
  signature: : SimplexCategory ⥤ Cat.{0}
  body: SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙
      forget₂ PartOrd Preord ⋙ preordToCat

中文:
定义 toCat
  签名: : SimplexCategory ⥤ Cat.{0}
  定义体: SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙
      forget₂ PartOrd Preord ⋙ preordToCat

Depends on / 依赖: LinOrd, NonemptyFinLinOrd, PartOrd, Preord, SimplexCategory, SimplexCategory.skeletalFunctor, preordToCat, skeletalFunctor
-/
def toCat : SimplexCategory ⥤ Cat.{0} :=
  SimplexCategory.skeletalFunctor ⋙ forget₂ NonemptyFinLinOrd LinOrd ⋙
      forget₂ LinOrd Lat ⋙ forget₂ Lat PartOrd ⋙
      forget₂ PartOrd Preord ⋙ preordToCat

/--
theorem `toCat.obj_eq_Fin` / 定理 `toCat.obj_eq_Fin`

English:
theorem toCat.obj_eq_Fin
  given: (n : Nat)
  statement: toCat.obj ⦋n⦌ = Fin (n + 1)
  proof: rfl

中文:
定理 toCat.obj_eq_Fin
  条件: (n : 自然数)
  结论: toCat.obj ⦋n⦌ = Fin (n + 1)
  证明: rfl
-/
theorem toCat.obj_eq_Fin (n : Nat) : toCat.obj ⦋n⦌ = Fin (n + 1) := rfl

/--
Instance `uniqueHomToZero` / 实例 `uniqueHomToZero`

English:
instance uniqueHomToZero
  signature: {Δ : SimplexCategory}
  body: Δ.const _ 0
  uniq := eq_const_to_zero

中文:
实例 uniqueHomToZero
  签名: {Δ : SimplexCategory}
  定义体: Δ.const _ 0
  uniq := eq_const_to_zero
-/
instance uniqueHomToZero {Δ : SimplexCategory} : Unique (Δ ⟶ ⦋0⦌) where
  default := Δ.const _ 0
  uniq := eq_const_to_zero

/--
Definition of `isTerminalZero` / `isTerminalZero` 的定义

English:
definition isTerminalZero
  signature: : IsTerminal (⦋0⦌ : SimplexCategory)
  body: IsTerminal.ofUnique ⦋0⦌

中文:
定义 isTerminalZero
  签名: : IsTerminal (⦋0⦌ : SimplexCategory)
  定义体: IsTerminal.ofUnique ⦋0⦌

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, ofUnique
-/
def isTerminalZero : IsTerminal (⦋0⦌ : SimplexCategory) :=
  IsTerminal.ofUnique ⦋0⦌

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: HasTerminal SimplexCategory
  body: IsTerminal.hasTerminal isTerminalZero

中文:
实例 :
  签名: HasTerminal SimplexCategory
  定义体: IsTerminal.hasTerminal isTerminalZero

Depends on / 依赖: IsTerminal, IsTerminal.hasTerminal, hasTerminal, isTerminalZero
-/
instance : HasTerminal SimplexCategory :=
  IsTerminal.hasTerminal isTerminalZero

/--
Definition of `topIsoZero` / `topIsoZero` 的定义

English:
definition topIsoZero
  signature: : ⊤_ SimplexCategory ≅ ⦋0⦌
  body: terminalIsoIsTerminal isTerminalZero

中文:
定义 topIsoZero
  签名: : ⊤_ SimplexCategory ≅ ⦋0⦌
  定义体: terminalIsoIsTerminal isTerminalZero

Depends on / 依赖: isTerminalZero, terminalIsoIsTerminal
-/
noncomputable def topIsoZero : ⊤_ SimplexCategory ≅ ⦋0⦌ :=
  terminalIsoIsTerminal isTerminalZero

/--
lemma `δ_injective` / 引理 `δ_injective`

English:
lemma δ_injective
  given: {n : Nat}
  statement: Function.Injective (δ (n := n))
  proof: by
  intro i j hij
  rw [← Fin.succAbove_left_inj]
  ext k : 1
  exact congr($hij k)

中文:
引理 δ_injective
  条件: {n : 自然数}
  结论: Function.Injective (δ (n := n))
  证明: by
  intro i j hij
  rw [← Fin.succAbove_left_inj]
  ext k : 1
  exact congr($hij k)

Depends on / 依赖: Fin.succAbove_left_inj, succAbove_left_inj
-/
lemma δ_injective {n : Nat} : Function.Injective (δ (n := n)) := by
  intro i j hij
  rw [← Fin.succAbove_left_inj]
  ext k : 1
  exact congr($hij k)

/--
lemma `σ_injective` / 引理 `σ_injective`

English:
lemma σ_injective
  given: {n : Nat}
  statement: Function.Injective (σ (n := n))
  proof: by
  intro i j hij
  rw [← Fin.predAbove_left_inj]
  ext k : 1
  exact congr($hij k)

中文:
引理 σ_injective
  条件: {n : 自然数}
  结论: Function.Injective (σ (n := n))
  证明: by
  intro i j hij
  rw [← Fin.predAbove_left_inj]
  ext k : 1
  exact congr($hij k)

Depends on / 依赖: Fin.predAbove_left_inj, predAbove_left_inj
-/
lemma σ_injective {n : Nat} : Function.Injective (σ (n := n)) := by
  intro i j hij
  rw [← Fin.predAbove_left_inj]
  ext k : 1
  exact congr($hij k)

end SimplexCategory
