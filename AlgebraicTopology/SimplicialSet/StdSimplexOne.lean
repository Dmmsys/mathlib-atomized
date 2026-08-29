/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex
public import Mathlib.AlgebraicTopology.SimplexCategory.ToMkOne

/-!
# Simplices in `Δ[1]`

We define a bijection `SSet.stdSimplex.objMk₁` between `Fin (n + 2)` and `Δ[1] _⦋n⦌`
for any `n : ℕ`.

-/

@[expose] public section

universe u

open CategoryTheory Simplicial

namespace SSet

namespace stdSimplex

/--
Definition of `objMk₁` / `objMk₁` 的定义

English:
definition objMk₁
  signature: {n : Nat} (i : Fin (n + 2))
  body: objMk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs <;> grind }

中文:
定义 objMk₁
  签名: {n : 自然数} (i : 有限集 (n + 2))
  定义体: objMk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs <;> grind }

Depends on / 依赖: castSucc, j.castSucc, monotone, split_ifs
-/
def objMk₁ {n : Nat} (i : Fin (n + 2)) : (Δ[1] _⦋n⦌ : Type u) :=
  objMk
    { toFun j := if j.castSucc < i then 0 else 1
      monotone' j₁ j₂ h := by
        dsimp
        split_ifs <;> grind }

/--
lemma `objMk₁_apply` / 引理 `objMk₁_apply`

English:
lemma objMk₁_apply
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1))
  proof: rfl

中文:
引理 objMk₁_apply
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 1))
  证明: rfl
-/
lemma objMk₁_apply {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% objMk₁ i j = if j.castSucc < i then 0 else 1 := rfl

/--
lemma `objMk₁_apply_eq_zero_iff` / 引理 `objMk₁_apply_eq_zero_iff`

English:
lemma objMk₁_apply_eq_zero_iff
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1))
  proof: SimplexCategory.toMk₁_apply_eq_zero_iff ..

中文:
引理 objMk₁_apply_eq_zero_iff
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 1))
  证明: SimplexCategory.toMk₁_apply_eq_zero_iff ..

Depends on / 依赖: SimplexCategory, SimplexCategory.toMk
-/
lemma objMk₁_apply_eq_zero_iff {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% objMk₁.{u} i j = 0 ↔ j.castSucc < i :=
  SimplexCategory.toMk₁_apply_eq_zero_iff ..

/--
lemma `objMk₁_of_castSucc_lt` / 引理 `objMk₁_of_castSucc_lt`

English:
lemma objMk₁_of_castSucc_lt
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i)
  proof: SimplexCategory.toMk₁_of_castSucc_lt _ _ h

中文:
引理 objMk₁_of_castSucc_lt
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 1)) (h : j.castSucc < i)
  证明: SimplexCategory.toMk₁_of_castSucc_lt _ _ h

Depends on / 依赖: SimplexCategory, SimplexCategory.toMk
-/
lemma objMk₁_of_castSucc_lt {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    dsimp% objMk₁.{u} i j = 0 :=
  SimplexCategory.toMk₁_of_castSucc_lt _ _ h

/--
lemma `objMk₁_apply_eq_one_iff` / 引理 `objMk₁_apply_eq_one_iff`

English:
lemma objMk₁_apply_eq_one_iff
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1))
  proof: SimplexCategory.toMk₁_apply_eq_one_iff ..

中文:
引理 objMk₁_apply_eq_one_iff
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 1))
  证明: SimplexCategory.toMk₁_apply_eq_one_iff ..

Depends on / 依赖: SimplexCategory, SimplexCategory.toMk
-/
lemma objMk₁_apply_eq_one_iff {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    dsimp% objMk₁.{u} i j = 1 ↔ i <= j.castSucc :=
  SimplexCategory.toMk₁_apply_eq_one_iff ..

/--
lemma `objMk₁_of_le_castSucc` / 引理 `objMk₁_of_le_castSucc`

English:
lemma objMk₁_of_le_castSucc
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc)
  proof: SimplexCategory.toMk₁_of_le_castSucc _ _ h

中文:
引理 objMk₁_of_le_castSucc
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 1)) (h : i <= j.castSucc)
  证明: SimplexCategory.toMk₁_of_le_castSucc _ _ h

Depends on / 依赖: SimplexCategory, SimplexCategory.toMk
-/
lemma objMk₁_of_le_castSucc {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc) :
    dsimp% objMk₁.{u} i j = 1 :=
  SimplexCategory.toMk₁_of_le_castSucc _ _ h

/--
lemma `δ_objMk₁_of_le` / 引理 `δ_objMk₁_of_le`

English:
lemma δ_objMk₁_of_le
  given: {n : Nat} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i <= j.castSucc)
  proof: by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.δ_comp_toMk₁_of_le _ _ h) k

中文:
引理 δ_objMk₁_of_le
  条件: {n : 自然数} (i : 有限集 (n + 3)) (j : 有限集 (n + 2)) (h : i <= j.castSucc)
  证明: by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.δ_comp_toMk₁_of_le _ _ h) k

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, SimplexCategory, congr_hom
-/
lemma δ_objMk₁_of_le {n : Nat} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : i <= j.castSucc) :
    Δ[1].δ j (objMk₁.{u} i) =
      objMk₁.{u} (i.castPred (Fin.ne_last_of_lt (lt_of_le_of_lt h j.castSucc_lt_succ))) := by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.δ_comp_toMk₁_of_le _ _ h) k

/--
lemma `δ_objMk₁_of_lt` / 引理 `δ_objMk₁_of_lt`

English:
lemma δ_objMk₁_of_lt
  given: {n : Nat} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i)
  proof: by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.δ_comp_toMk₁_of_lt _ _ h) k

中文:
引理 δ_objMk₁_of_lt
  条件: {n : 自然数} (i : 有限集 (n + 3)) (j : 有限集 (n + 2)) (h : j.castSucc < i)
  证明: by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.δ_comp_toMk₁_of_lt _ _ h) k

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, SimplexCategory, congr_hom
-/
lemma δ_objMk₁_of_lt {n : Nat} (i : Fin (n + 3)) (j : Fin (n + 2)) (h : j.castSucc < i) :
    Δ[1].δ j (objMk₁.{u} i) = objMk₁.{u} (i.pred (Fin.ne_zero_of_lt h)) := by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.δ_comp_toMk₁_of_lt _ _ h) k

/--
lemma `σ_objMk₁_of_le` / 引理 `σ_objMk₁_of_le`

English:
lemma σ_objMk₁_of_le
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc)
  proof: by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.σ_comp_toMk₁_of_le _ _ h) k

中文:
引理 σ_objMk₁_of_le
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 1)) (h : i <= j.castSucc)
  证明: by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.σ_comp_toMk₁_of_le _ _ h) k

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, SimplexCategory, congr_hom
-/
lemma σ_objMk₁_of_le {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i <= j.castSucc) :
    Δ[1].σ j (objMk₁.{u} i) = objMk₁ i.castSucc := by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.σ_comp_toMk₁_of_le _ _ h) k

/--
lemma `σ_objMk₁_of_lt` / 引理 `σ_objMk₁_of_lt`

English:
lemma σ_objMk₁_of_lt
  given: {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i)
  proof: by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.σ_comp_toMk₁_of_lt _ _ h) k

中文:
引理 σ_objMk₁_of_lt
  条件: {n : 自然数} (i : 有限集 (n + 2)) (j : 有限集 (n + 1)) (h : j.castSucc < i)
  证明: by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.σ_comp_toMk₁_of_lt _ _ h) k

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, SimplexCategory, congr_hom
-/
lemma σ_objMk₁_of_lt {n : Nat} (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    Δ[1].σ j (objMk₁.{u} i) = objMk₁ i.succ := by
  ext k : 1
  exact ConcreteCategory.congr_hom (SimplexCategory.σ_comp_toMk₁_of_lt _ _ h) k

/--
lemma `objMk₁_bijective` / 引理 `objMk₁_bijective`

English:
lemma objMk₁_bijective
  given: {n : Nat}
  statement: Function.Bijective (objMk₁.{u} (n := n))
  proof: ((SimplexCategory.toMk₁Equiv (n := n)).trans objEquiv.symm).bijective

中文:
引理 objMk₁_bijective
  条件: {n : 自然数}
  结论: 函数.双射 (objMk₁.{u} (n := n))
  证明: ((SimplexCategory.toMk₁Equiv (n := n)).trans objEquiv.symm).bijective
-/
lemma objMk₁_bijective {n : Nat} : Function.Bijective (objMk₁.{u} (n := n)) :=
  ((SimplexCategory.toMk₁Equiv (n := n)).trans objEquiv.symm).bijective

/--
lemma `objMk₁_injective` / 引理 `objMk₁_injective`

English:
lemma objMk₁_injective
  given: {n : Nat}
  statement: Function.Injective (objMk₁.{u} (n := n))
  proof: objMk₁_bijective.injective

中文:
引理 objMk₁_injective
  条件: {n : 自然数}
  结论: 函数.单射 (objMk₁.{u} (n := n))
  证明: objMk₁_bijective.injective
-/
lemma objMk₁_injective {n : Nat} : Function.Injective (objMk₁.{u} (n := n)) :=
  objMk₁_bijective.injective

/--
lemma `objMk₁_surjective` / 引理 `objMk₁_surjective`

English:
lemma objMk₁_surjective
  given: {n : Nat}
  statement: Function.Surjective (objMk₁.{u} (n := n))
  proof: objMk₁_bijective.surjective

中文:
引理 objMk₁_surjective
  条件: {n : 自然数}
  结论: 函数.满射 (objMk₁.{u} (n := n))
  证明: objMk₁_bijective.surjective
-/
lemma objMk₁_surjective {n : Nat} : Function.Surjective (objMk₁.{u} (n := n)) :=
  objMk₁_bijective.surjective

end stdSimplex

end SSet
