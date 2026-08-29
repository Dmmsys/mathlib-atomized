/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Lua Viana Reis, Oliver Butterley
-/
module

public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Algebra.Module.Basic

/-!
# Birkhoff average

In this file we define `birkhoffAverage f g n x` to be
$$
\frac{1}{n}\sum_{k=0}^{n-1}g(f^{[k]}(x)),
$$
where `f : α → α` is a self-map on some type `α`,
`g : α → M` is a function from `α` to a module over a division semiring `R`,
and `R` is used to formalize division by `n` as `(n : R)⁻¹ • _`.

While we need an auxiliary division semiring `R` to define `birkhoffAverage`,
the definition does not depend on the choice of `R`,
see `birkhoffAverage_congr_ring`.

-/

@[expose] public section

open Finset

section birkhoffAverage

variable (R : Type*) {α M : Type*} [DivisionSemiring R] [AddCommMonoid M] [Module R M]

/--
Definition of `birkhoffAverage` / `birkhoffAverage` 的定义

English:
definition birkhoffAverage
  signature: (f : α -> α) (g : α -> M) (n : Nat) (x : α)
  body: (n : R)⁻¹ • birkhoffSum f g n x

中文:
定义 birkhoffAverage
  签名: (f : α -> α) (g : α -> M) (n : 自然数) (x : α)
  定义体: (n : R)⁻¹ • birkhoffSum f g n x

Depends on / 依赖: birkhoffSum
-/
def birkhoffAverage (f : α -> α) (g : α -> M) (n : Nat) (x : α) : M := (n : R)⁻¹ • birkhoffSum f g n x

/--
theorem `birkhoffAverage_zero` / 定理 `birkhoffAverage_zero`

English:
theorem birkhoffAverage_zero
  given: (f : α -> α) (g : α -> M) (x : α)
  proof: by simp [birkhoffAverage]

中文:
定理 birkhoffAverage_zero
  条件: (f : α -> α) (g : α -> M) (x : α)
  证明: by simp [birkhoffAverage]

Depends on / 依赖: birkhoffAverage
-/
theorem birkhoffAverage_zero (f : α -> α) (g : α -> M) (x : α) :
    birkhoffAverage R f g 0 x = 0 := by simp [birkhoffAverage]

/--
theorem `birkhoffAverage_zero'` / 定理 `birkhoffAverage_zero'`

English:
theorem birkhoffAverage_zero'
  given: (f : α -> α) (g : α -> M)
  statement: birkhoffAverage R f g 0 = 0
  proof: funext birkhoffAverage_zero _ _ _

中文:
定理 birkhoffAverage_zero'
  条件: (f : α -> α) (g : α -> M)
  结论: birkhoffAverage R f g 0 = 0
  证明: funext birkhoffAverage_zero _ _ _
-/
@[simp] theorem birkhoffAverage_zero' (f : α -> α) (g : α -> M) : birkhoffAverage R f g 0 = 0 :=
funext birkhoffAverage_zero _ _ _

/--
theorem `birkhoffAverage_one` / 定理 `birkhoffAverage_one`

English:
theorem birkhoffAverage_one
  given: (f : α -> α) (g : α -> M) (x : α)
  proof: by simp [birkhoffAverage]

@[simp]

中文:
定理 birkhoffAverage_one
  条件: (f : α -> α) (g : α -> M) (x : α)
  证明: by simp [birkhoffAverage]

@[simp]

Depends on / 依赖: birkhoffAverage
-/
theorem birkhoffAverage_one (f : α -> α) (g : α -> M) (x : α) :
    birkhoffAverage R f g 1 x = g x := by simp [birkhoffAverage]

@[simp]
/--
theorem `birkhoffAverage_one'` / 定理 `birkhoffAverage_one'`

English:
theorem birkhoffAverage_one'
  given: (f : α -> α) (g : α -> M)
  statement: birkhoffAverage R f g 1 = g
  proof: funext birkhoffAverage_one R f g

中文:
定理 birkhoffAverage_one'
  条件: (f : α -> α) (g : α -> M)
  结论: birkhoffAverage R f g 1 = g
  证明: funext birkhoffAverage_one R f g

Depends on / 依赖: birkhoffAverage_one
-/
theorem birkhoffAverage_one' (f : α -> α) (g : α -> M) : birkhoffAverage R f g 1 = g :=
funext birkhoffAverage_one R f g

/--
theorem `map_birkhoffAverage` / 定理 `map_birkhoffAverage`

English:
theorem map_birkhoffAverage
  statement: (S : Type*) {F N : Type*}
  proof: by
  simp only [birkhoffAverage, map_inv_natCast_smul g' R S, map_birkhoffSum]

中文:
定理 map_birkhoffAverage
  结论: (S : 类型) {F N : 类型}
  证明: by
  simp only [birkhoffAverage, map_inv_natCast_smul g' R S, map_birkhoffSum]

Depends on / 依赖: birkhoffAverage, map_birkhoffSum, map_inv_natCast_smul
-/
theorem map_birkhoffAverage (S : Type*) {F N : Type*}
    [DivisionSemiring S] [AddCommMonoid N] [Module S N] [FunLike F M N]
    [AddMonoidHomClass F M N] (g' : F) (f : α -> α) (g : α -> M) (n : Nat) (x : α) :
    g' (birkhoffAverage R f g n x) = birkhoffAverage S f (g' ∘ g) n x := by
  simp only [birkhoffAverage, map_inv_natCast_smul g' R S, map_birkhoffSum]

/--
theorem `birkhoffAverage_congr_ring` / 定理 `birkhoffAverage_congr_ring`

English:
theorem birkhoffAverage_congr_ring
  statement: (S : Type*) [DivisionSemiring S] [Module S M]
  proof: map_birkhoffAverage R S (AddMonoidHom.id M) f g n x

中文:
定理 birkhoffAverage_congr_ring
  结论: (S : 类型) [DivisionSemiring S] [Module S M]
  证明: map_birkhoffAverage R S (AddMonoidHom.id M) f g n x

Depends on / 依赖: AddMonoidHom, AddMonoidHom.id, map_birkhoffAverage
-/
theorem birkhoffAverage_congr_ring (S : Type*) [DivisionSemiring S] [Module S M]
    (f : α -> α) (g : α -> M) (n : Nat) (x : α) :
    birkhoffAverage R f g n x = birkhoffAverage S f g n x :=
  map_birkhoffAverage R S (AddMonoidHom.id M) f g n x

/--
theorem `birkhoffAverage_congr_ring'` / 定理 `birkhoffAverage_congr_ring'`

English:
theorem birkhoffAverage_congr_ring'
  given: (S : Type*) [DivisionSemiring S] [Module S M]
  proof: by
  ext; apply birkhoffAverage_congr_ring

中文:
定理 birkhoffAverage_congr_ring'
  条件: (S : 类型) [DivisionSemiring S] [Module S M]
  证明: by
  ext; apply birkhoffAverage_congr_ring

Depends on / 依赖: birkhoffAverage, birkhoffAverage_congr_ring
-/
theorem birkhoffAverage_congr_ring' (S : Type*) [DivisionSemiring S] [Module S M] :
    birkhoffAverage (α := α) (M := M) R = birkhoffAverage S := by
  ext; apply birkhoffAverage_congr_ring

/--
theorem `Function.IsFixedPt.birkhoffAverage_eq` / 定理 `Function.IsFixedPt.birkhoffAverage_eq`

English:
theorem Function.IsFixedPt.birkhoffAverage_eq
  statement: {f : α -> α} {x : α} (h : IsFixedPt f x)
  proof: by
  rw [birkhoffAverage]; rw [h.birkhoffSum_eq]; rw [← Nat.cast_smul_eq_nsmul R]; rw [inv_smul_smul₀ hn]

中文:
定理 Function.IsFixedPt.birkhoffAverage_eq
  结论: {f : α -> α} {x : α} (h : IsFixedPt f x)
  证明: by
  rw [birkhoffAverage]; rw [h.birkhoffSum_eq]; rw [← Nat.cast_smul_eq_nsmul R]; rw [inv_smul_smul₀ hn]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, birkhoffAverage, birkhoffSum_eq, cast_smul_eq_nsmul, h.birkhoffSum_eq
-/
theorem Function.IsFixedPt.birkhoffAverage_eq {f : α -> α} {x : α} (h : IsFixedPt f x)
    (g : α -> M) {n : Nat} (hn : (n : R) != 0) : birkhoffAverage R f g n x = g x := by
  rw [birkhoffAverage]; rw [h.birkhoffSum_eq]; rw [← Nat.cast_smul_eq_nsmul R]; rw [inv_smul_smul₀ hn]

/--
lemma `birkhoffAverage_add` / 引理 `birkhoffAverage_add`

English:
lemma birkhoffAverage_add
  given: {f : α -> α} {g g' : α -> M}
  proof: by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, sum_add_distrib, smul_add]

中文:
引理 birkhoffAverage_add
  条件: {f : α -> α} {g g' : α -> M}
  证明: by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, sum_add_distrib, smul_add]

Depends on / 依赖: birkhoffAverage, birkhoffSum, smul_add, sum_add_distrib
-/
lemma birkhoffAverage_add {f : α -> α} {g g' : α -> M} :
    birkhoffAverage R f (g + g') = birkhoffAverage R f g + birkhoffAverage R f g' := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, sum_add_distrib, smul_add]

/--
theorem `birkhoffAverage_of_comp_eq` / 定理 `birkhoffAverage_of_comp_eq`

English:
theorem birkhoffAverage_of_comp_eq
  statement: {f : α -> α} {g : α -> M} (h : g ∘ f = g)
  proof: by
  funext x
  suffices (n : R)⁻¹ • n • g x = g x by simpa [birkhoffAverage, birkhoffSum_of_comp_eq h]
  rw [← Nat.cast_smul_eq_nsmul (R := R)]; rw [← mul_smul]; rw [inv_mul_cancel₀ hn]; rw [one_smul]

中文:
定理 birkhoffAverage_of_comp_eq
  结论: {f : α -> α} {g : α -> M} (h : g ∘ f = g)
  证明: by
  funext x
  suffices (n : R)⁻¹ • n • g x = g x by simpa [birkhoffAverage, birkhoffSum_of_comp_eq h]
  rw [← Nat.cast_smul_eq_nsmul (R := R)]; rw [← mul_smul]; rw [inv_mul_cancel₀ hn]; rw [one_smul]

Depends on / 依赖: Nat.cast_smul_eq_nsmul, birkhoffAverage, birkhoffSum_of_comp_eq, cast_smul_eq_nsmul, mul_smul, one_smul
-/
theorem birkhoffAverage_of_comp_eq {f : α -> α} {g : α -> M} (h : g ∘ f = g)
    {n : Nat} (hn : (n : R) != 0) : birkhoffAverage R f g n = g := by
  funext x
  suffices (n : R)⁻¹ • n • g x = g x by simpa [birkhoffAverage, birkhoffSum_of_comp_eq h]
  rw [← Nat.cast_smul_eq_nsmul (R := R)]; rw [← mul_smul]; rw [inv_mul_cancel₀ hn]; rw [one_smul]

end birkhoffAverage

section AddCommGroup

variable {R : Type*} {α M : Type*} [DivisionSemiring R] [AddCommGroup M] [Module R M]

/--
lemma `birkhoffAverage_neg` / 引理 `birkhoffAverage_neg`

English:
lemma birkhoffAverage_neg
  given: {f : α -> α} {g : α -> M}
  proof: by
  funext _ x
  simp [birkhoffAverage, birkhoffSum]

中文:
引理 birkhoffAverage_neg
  条件: {f : α -> α} {g : α -> M}
  证明: by
  funext _ x
  simp [birkhoffAverage, birkhoffSum]

Depends on / 依赖: birkhoffAverage, birkhoffSum
-/
lemma birkhoffAverage_neg {f : α -> α} {g : α -> M} :
    birkhoffAverage R f (-g) = -birkhoffAverage R f g := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum]

/--
lemma `birkhoffAverage_sub` / 引理 `birkhoffAverage_sub`

English:
lemma birkhoffAverage_sub
  given: {f : α -> α} {g g' : α -> M}
  proof: by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, smul_sub]

中文:
引理 birkhoffAverage_sub
  条件: {f : α -> α} {g g' : α -> M}
  证明: by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, smul_sub]

Depends on / 依赖: birkhoffAverage, birkhoffSum, smul_sub
-/
lemma birkhoffAverage_sub {f : α -> α} {g g' : α -> M} :
    birkhoffAverage R f (g - g') = birkhoffAverage R f g - birkhoffAverage R f g' := by
  funext _ x
  simp [birkhoffAverage, birkhoffSum, smul_sub]

/--
theorem `birkhoffAverage_apply_sub_birkhoffAverage` / 定理 `birkhoffAverage_apply_sub_birkhoffAverage`

English:
theorem birkhoffAverage_apply_sub_birkhoffAverage
  given: (f : α -> α) (g : α -> M) (n : Nat) (x : α)
  proof: by
  simp only [birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, ← smul_sub]

中文:
定理 birkhoffAverage_apply_sub_birkhoffAverage
  条件: (f : α -> α) (g : α -> M) (n : 自然数) (x : α)
  证明: by
  simp only [birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, ← smul_sub]

Depends on / 依赖: birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, smul_sub
-/
theorem birkhoffAverage_apply_sub_birkhoffAverage (f : α -> α) (g : α -> M) (n : Nat) (x : α) :
    birkhoffAverage R f g n (f x) - birkhoffAverage R f g n x =
      (n : R)⁻¹ • (g (f^[n] x) - g x) := by
  simp only [birkhoffAverage, birkhoffSum_apply_sub_birkhoffSum, ← smul_sub]

end AddCommGroup
