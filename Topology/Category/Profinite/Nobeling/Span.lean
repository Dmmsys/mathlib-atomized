/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Topology.Category.Profinite.CofilteredLimit
public import Mathlib.Topology.Category.Profinite.Nobeling.Basic

/-!
# The good products span

Most of the argument is developing an API for `π C (· ∈ s)` when `s : Finset I`; then the image
of `C` is finite with the discrete topology. In this case, there is a direct argument that the good
products span. The general result is deduced from this.

For the overall proof outline see `Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## Main theorems

* `GoodProducts.spanFin` : The good products span the locally constant functions on `π C (· ∈ s)`
  if `s` is finite.
* `GoodProducts.span` : The good products span `LocallyConstant C ℤ` for every closed subset `C`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I -> Bool)) [LinearOrder I]

section Fin

variable (s : Finset I)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → π C (· ∈ s)`. -/
noncomputable
/--
Definition of `πJ` / `πJ` 的定义

English:
definition πJ
  signature: : LocallyConstant (π C (· in s)) Int ->ₗ[Int] LocallyConstant C Int
  body: LocallyConstant.comapₗ Int ⟨_, (continuous_projRestrict C (· in s))⟩

中文:
定义 πJ
  签名: : 局部常数 (π C (· in s)) 整数 ->ₗ[整数] 局部常数 C 整数
  定义体: LocallyConstant.comapₗ Int ⟨_, (continuous_projRestrict C (· in s))⟩

Depends on / 依赖: LocallyConstant, LocallyConstant.comap, continuous_projRestrict
-/
def πJ : LocallyConstant (π C (· in s)) Int ->ₗ[Int] LocallyConstant C Int :=
  LocallyConstant.comapₗ Int ⟨_, (continuous_projRestrict C (· in s))⟩

/--
theorem `eval_eq_πJ` / 定理 `eval_eq_πJ`

English:
theorem eval_eq_πJ
  given: (l : Products I) (hl : l.isGood (π C (· in s)))
  proof: by
  ext f
  simp only [πJ, LocallyConstant.comapₗ]
  exact (congr_fun (Products.evalFacProp C (· in s) (Products.prop_of_isGood C (· in s) hl)) _).symm

中文:
定理 eval_eq_πJ
  条件: (l : Products I) (hl : l.isGood (π C (· in s)))
  证明: by
  ext f
  simp only [πJ, LocallyConstant.comapₗ]
  exact (congr_fun (Products.evalFacProp C (· in s) (Products.prop_of_isGood C (· in s) hl)) _).symm

Depends on / 依赖: LocallyConstant, LocallyConstant.comap, Products, Products.evalFacProp, Products.prop_of_isGood, congr_fun, evalFacProp, prop_of_isGood
-/
theorem eval_eq_πJ (l : Products I) (hl : l.isGood (π C (· in s))) :
    l.eval C = πJ C s (l.eval (π C (· in s))) := by
  ext f
  simp only [πJ, LocallyConstant.comapₗ]
  exact (congr_fun (Products.evalFacProp C (· in s) (Products.prop_of_isGood C (· in s) hl)) _).symm

/-- `π C (· ∈ s)` is finite for a finite set `s`. -/
noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (π C (· in s))
  body: by
  let f : π C (· in s) -> (s -> Bool) := fun x j => x.val j.val
  refine Fintype.ofInjective f ?_
  intro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ h
  ext i
  by_cases hi : i in s
  · exact congrFun h ⟨i, hi⟩
  · simp only [Proj, if_neg hi]

中文:
实例 :
  签名: 有限类型 (π C (· in s))
  定义体: by
  let f : π C (· in s) -> (s -> Bool) := fun x j => x.val j.val
  refine Fintype.ofInjective f ?_
  intro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ h
  ext i
  by_cases hi : i in s
  · exact congrFun h ⟨i, hi⟩
  · simp only [Proj, if_neg hi]

Depends on / 依赖: Fintype, Fintype.ofInjective, if_neg, j.val, ofInjective, x.val
-/
instance : Fintype (π C (· in s)) := by
  let f : π C (· in s) -> (s -> Bool) := fun x j => x.val j.val
  refine Fintype.ofInjective f ?_
  intro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ h
  ext i
  by_cases hi : i in s
  · exact congrFun h ⟨i, hi⟩
  · simp only [Proj, if_neg hi]

open scoped Classical in
/-- The Kronecker delta as a locally constant map from `π C (· ∈ s)` to `ℤ`. -/
noncomputable
/--
Definition of `spanFinBasis` / `spanFinBasis` 的定义

English:
definition spanFinBasis
  signature: (x : π C (· in s))
  body: fun y => if y = x then 1 else 0
  isLocallyConstant :=
    haveI : DiscreteTopology (π C (· in s)) := Finite.instDiscreteTopology
    IsLocallyConstant.of_discrete _

中文:
定义 spanFinBasis
  签名: (x : π C (· in s))
  定义体: fun y => if y = x then 1 else 0
  isLocallyConstant :=
    haveI : DiscreteTopology (π C (· in s)) := Finite.instDiscreteTopology
    IsLocallyConstant.of_discrete _
-/
def spanFinBasis (x : π C (· in s)) : LocallyConstant (π C (· in s)) Int where
  toFun := fun y => if y = x then 1 else 0
  isLocallyConstant :=
    haveI : DiscreteTopology (π C (· in s)) := Finite.instDiscreteTopology
    IsLocallyConstant.of_discrete _

/--
theorem `spanFinBasis.span` / 定理 `spanFinBasis.span`

English:
theorem spanFinBasis.span
  statement: ⊤ <= Submodule.span Int (Set.range (spanFinBasis C s))
  proof: by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ => Finset.mem_univ _)
  ext x
  change LocallyConstant.evalₗ Int x _ = _
  simp only [zsmul_eq_mul, map_finsuppSum, LocallyConstant.evalₗ_apply,
    LocallyConstant.coe_mul, Pi.mul_apply, spanFinBasis, LocallyConstant.coe_mk, mul_ite, mul_one,
    mul_zero, Finsupp.sum_ite_eq, Finsupp.mem_support_iff, ne_eq, ite_not]
  split_ifs with h <;> [exact h.symm; rfl]

中文:
定理 spanFinBasis.span
  结论: ⊤ <= 子模.span 整数 (集合.range (spanFinBasis C s))
  证明: by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ => Finset.mem_univ _)
  ext x
  change LocallyConstant.evalₗ Int x _ = _
  simp only [zsmul_eq_mul, map_finsuppSum, LocallyConstant.evalₗ_apply,
    LocallyConstant.coe_mul, Pi.mul_apply, spanFinBasis, LocallyConstant.coe_mk, mul_ite, mul_one,
    mul_zero, Finsupp.sum_ite_eq, Finsupp.mem_support_iff, ne_eq, ite_not]
  split_ifs with h <;> [exact h.symm; rfl]

Depends on / 依赖: Finset, Finset.mem_univ, Finset.univ, Finsupp, Finsupp.mem_span_range_iff_exists_finsupp, Finsupp.mem_support_iff, Finsupp.onFinset, Finsupp.sum_ite_eq, LocallyConstant, LocallyConstant.coe_mk, LocallyConstant.coe_mul, LocallyConstant.eval, Pi.mul_apply, coe_mk, coe_mul, f.toFun, h.symm, ite_not, map_finsuppSum, mem_span_range_iff_exists_finsupp
-/
theorem spanFinBasis.span : ⊤ <= Submodule.span Int (Set.range (spanFinBasis C s)) := by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ => Finset.mem_univ _)
  ext x
  change LocallyConstant.evalₗ Int x _ = _
  simp only [zsmul_eq_mul, map_finsuppSum, LocallyConstant.evalₗ_apply,
    LocallyConstant.coe_mul, Pi.mul_apply, spanFinBasis, LocallyConstant.coe_mk, mul_ite, mul_one,
    mul_zero, Finsupp.sum_ite_eq, Finsupp.mem_support_iff, ne_eq, ite_not]
  split_ifs with h <;> [exact h.symm; rfl]

/--
Definition of `factors` / `factors` 的定义

English:
definition factors
  signature: (x : π C (· in s))
  body: List.map (fun i => if x.val i = true then e (π C (· in s)) i else (1 - (e (π C (· in s)) i)))
    (s.sort (· >= ·))

中文:
定义 factors
  签名: (x : π C (· in s))
  定义体: List.map (fun i => if x.val i = true then e (π C (· in s)) i else (1 - (e (π C (· in s)) i)))
    (s.sort (· >= ·))

Depends on / 依赖: List.map, s.sort, x.val
-/
def factors (x : π C (· in s)) : List (LocallyConstant (π C (· in s)) Int) :=
  List.map (fun i => if x.val i = true then e (π C (· in s)) i else (1 - (e (π C (· in s)) i)))
    (s.sort (· >= ·))

/--
theorem `list_prod_apply` / 定理 `list_prod_apply`

English:
theorem list_prod_apply
  given: {I} (C : Set (I -> Bool)) (x : C) (l : List (LocallyConstant C Int))
  proof: by
  rw [← map_list_prod (LocallyConstant.evalMonoidHom x) l]; rw [LocallyConstant.evalMonoidHom_apply]

中文:
定理 list_prod_apply
  条件: {I} (C : 集合 (I -> 布尔值)) (x : C) (l : 列表 (局部常数 C 整数))
  证明: by
  rw [← map_list_prod (LocallyConstant.evalMonoidHom x) l]; rw [LocallyConstant.evalMonoidHom_apply]

Depends on / 依赖: LocallyConstant, LocallyConstant.evalMonoidHom, LocallyConstant.evalMonoidHom_apply, evalMonoidHom, evalMonoidHom_apply, map_list_prod
-/
theorem list_prod_apply {I} (C : Set (I -> Bool)) (x : C) (l : List (LocallyConstant C Int)) :
    l.prod x = (l.map (LocallyConstant.evalMonoidHom x)).prod := by
  rw [← map_list_prod (LocallyConstant.evalMonoidHom x) l]; rw [LocallyConstant.evalMonoidHom_apply]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `factors_prod_eq_basis_of_eq` / 定理 `factors_prod_eq_basis_of_eq`

English:
theorem factors_prod_eq_basis_of_eq
  given: {x y : (π C fun x => x in s)} (h : y = x)
  proof: by
  rw [list_prod_apply (π C (· in s)) y _]
  apply List.prod_eq_one
  simp only [h, List.mem_map, LocallyConstant.evalMonoidHom, factors]
  rintro _ ⟨a, ⟨b, _, rfl⟩, rfl⟩
  dsimp
  split_ifs with hh
  · rw [e, LocallyConstant.coe_mk, if_pos hh]
  · rw [LocallyConstant.sub_apply, e, LocallyConstant.coe_mk, LocallyConstant.coe_mk, if_neg hh]
    simp only [LocallyConstant.toFun_eq_coe, LocallyConstant.coe_one, Pi.one_apply, sub_zero]

中文:
定理 factors_prod_eq_basis_of_eq
  条件: {x y : (π C fun x => x in s)} (h : y = x)
  证明: by
  rw [list_prod_apply (π C (· in s)) y _]
  apply List.prod_eq_one
  simp only [h, List.mem_map, LocallyConstant.evalMonoidHom, factors]
  rintro _ ⟨a, ⟨b, _, rfl⟩, rfl⟩
  dsimp
  split_ifs with hh
  · rw [e, LocallyConstant.coe_mk, if_pos hh]
  · rw [LocallyConstant.sub_apply, e, LocallyConstant.coe_mk, LocallyConstant.coe_mk, if_neg hh]
    simp only [LocallyConstant.toFun_eq_coe, LocallyConstant.coe_one, Pi.one_apply, sub_zero]

Depends on / 依赖: List.mem_map, List.prod_eq_one, LocallyConstant, LocallyConstant.coe_mk, LocallyConstant.coe_one, LocallyConstant.evalMonoidHom, LocallyConstant.sub_apply, LocallyConstant.toFun_eq_coe, Pi.one_apply, coe_mk, coe_one, evalMonoidHom, factors, if_neg, if_pos, list_prod_apply, mem_map, one_apply, prod_eq_one, split_ifs
-/
theorem factors_prod_eq_basis_of_eq {x y : (π C fun x => x in s)} (h : y = x) :
    (factors C s x).prod y = 1 := by
  rw [list_prod_apply (π C (· in s)) y _]
  apply List.prod_eq_one
  simp only [h, List.mem_map, LocallyConstant.evalMonoidHom, factors]
  rintro _ ⟨a, ⟨b, _, rfl⟩, rfl⟩
  dsimp
  split_ifs with hh
  · rw [e, LocallyConstant.coe_mk, if_pos hh]
  · rw [LocallyConstant.sub_apply, e, LocallyConstant.coe_mk, LocallyConstant.coe_mk, if_neg hh]
    simp only [LocallyConstant.toFun_eq_coe, LocallyConstant.coe_one, Pi.one_apply, sub_zero]

/--
theorem `e_mem_of_eq_true` / 定理 `e_mem_of_eq_true`

English:
theorem e_mem_of_eq_true
  given: {x : (π C (· in s))} {a : I} (hx : x.val a = true)
  proof: by
  rcases x with ⟨_, z, hz, rfl⟩
  simp only [factors, List.mem_map, Finset.mem_sort]
  refine ⟨a, ?_, if_pos hx⟩
  aesop (add simp Proj)

中文:
定理 e_mem_of_eq_true
  条件: {x : (π C (· in s))} {a : I} (hx : x.val a = true)
  证明: by
  rcases x with ⟨_, z, hz, rfl⟩
  simp only [factors, List.mem_map, Finset.mem_sort]
  refine ⟨a, ?_, if_pos hx⟩
  aesop (add simp Proj)

Depends on / 依赖: Finset, Finset.mem_sort, List.mem_map, factors, if_pos, mem_map, mem_sort
-/
theorem e_mem_of_eq_true {x : (π C (· in s))} {a : I} (hx : x.val a = true) :
    e (π C (· in s)) a in factors C s x := by
  rcases x with ⟨_, z, hz, rfl⟩
  simp only [factors, List.mem_map, Finset.mem_sort]
  refine ⟨a, ?_, if_pos hx⟩
  aesop (add simp Proj)

/--
theorem `one_sub_e_mem_of_false` / 定理 `one_sub_e_mem_of_false`

English:
theorem one_sub_e_mem_of_false
  statement: {x y : (π C (· in s))} {a : I} (ha : y.val a = true)
  proof: by
  simp only [factors, List.mem_map, Finset.mem_sort]
  use a
  simp only [hx]
  rcases y with ⟨_, z, hz, rfl⟩
  aesop (add simp Proj)

中文:
定理 one_sub_e_mem_of_false
  结论: {x y : (π C (· in s))} {a : I} (ha : y.val a = true)
  证明: by
  simp only [factors, List.mem_map, Finset.mem_sort]
  use a
  simp only [hx]
  rcases y with ⟨_, z, hz, rfl⟩
  aesop (add simp Proj)

Depends on / 依赖: Finset, Finset.mem_sort, List.mem_map, factors, mem_map, mem_sort
-/
theorem one_sub_e_mem_of_false {x y : (π C (· in s))} {a : I} (ha : y.val a = true)
    (hx : x.val a = false) : 1 - e (π C (· in s)) a in factors C s x := by
  simp only [factors, List.mem_map, Finset.mem_sort]
  use a
  simp only [hx]
  rcases y with ⟨_, z, hz, rfl⟩
  aesop (add simp Proj)

/--
theorem `factors_prod_eq_basis_of_ne` / 定理 `factors_prod_eq_basis_of_ne`

English:
theorem factors_prod_eq_basis_of_ne
  given: {x y : (π C (· in s))} (h : y != x)
  proof: by
  rw [list_prod_apply (π C (· in s)) y _]
  apply List.prod_eq_zero
  simp only [List.mem_map]
  obtain ⟨a, ha⟩ : exists a, y.val a != x.val a := by contrapose! h; ext; apply h
  cases hx : x.val a
  · rw [hx, ne_eq, Bool.not_eq_false] at ha
    refine ⟨1 - (e (π C (· in s)) a), ⟨one_sub_e_mem_of_false _ _ ha hx, ?_⟩⟩
    rw [e]; rw [LocallyConstant.evalMonoidHom_apply]; rw [LocallyConstant.sub_apply]; rw [LocallyConstant.coe_one]; rw [Pi.one_apply]; rw [LocallyConstant.coe_mk]; rw [if_pos ha]; rw [sub_self]
  · refine ⟨e (π C (· in s)) a, ⟨e_mem_of_eq_true _ _ hx, ?_⟩⟩
    rw [hx] at ha
    rw [LocallyConstant.evalMonoidHom_apply]; rw [e]; rw [LocallyConstant.coe_mk]; rw [if_neg ha]

中文:
定理 factors_prod_eq_basis_of_ne
  条件: {x y : (π C (· in s))} (h : y != x)
  证明: by
  rw [list_prod_apply (π C (· in s)) y _]
  apply List.prod_eq_zero
  simp only [List.mem_map]
  obtain ⟨a, ha⟩ : exists a, y.val a != x.val a := by contrapose! h; ext; apply h
  cases hx : x.val a
  · rw [hx, ne_eq, Bool.not_eq_false] at ha
    refine ⟨1 - (e (π C (· in s)) a), ⟨one_sub_e_mem_of_false _ _ ha hx, ?_⟩⟩
    rw [e]; rw [LocallyConstant.evalMonoidHom_apply]; rw [LocallyConstant.sub_apply]; rw [LocallyConstant.coe_one]; rw [Pi.one_apply]; rw [LocallyConstant.coe_mk]; rw [if_pos ha]; rw [sub_self]
  · refine ⟨e (π C (· in s)) a, ⟨e_mem_of_eq_true _ _ hx, ?_⟩⟩
    rw [hx] at ha
    rw [LocallyConstant.evalMonoidHom_apply]; rw [e]; rw [LocallyConstant.coe_mk]; rw [if_neg ha]

Depends on / 依赖: Bool.not_eq_false, List.mem_map, List.prod_eq_zero, LocallyConstant, LocallyConstant.coe_mk, LocallyConstant.coe_one, LocallyConstant.evalMonoidHom_apply, LocallyConstant.sub_apply, Pi.one_apply, coe_mk, coe_one, contrapose, evalMonoidHom_apply, if_pos, list_prod_apply, mem_map, ne_eq, not_eq_false, one_apply, one_sub_e_mem_of_false
-/
theorem factors_prod_eq_basis_of_ne {x y : (π C (· in s))} (h : y != x) :
    (factors C s x).prod y = 0 := by
  rw [list_prod_apply (π C (· in s)) y _]
  apply List.prod_eq_zero
  simp only [List.mem_map]
  obtain ⟨a, ha⟩ : exists a, y.val a != x.val a := by contrapose! h; ext; apply h
  cases hx : x.val a
  · rw [hx, ne_eq, Bool.not_eq_false] at ha
    refine ⟨1 - (e (π C (· in s)) a), ⟨one_sub_e_mem_of_false _ _ ha hx, ?_⟩⟩
    rw [e]; rw [LocallyConstant.evalMonoidHom_apply]; rw [LocallyConstant.sub_apply]; rw [LocallyConstant.coe_one]; rw [Pi.one_apply]; rw [LocallyConstant.coe_mk]; rw [if_pos ha]; rw [sub_self]
  · refine ⟨e (π C (· in s)) a, ⟨e_mem_of_eq_true _ _ hx, ?_⟩⟩
    rw [hx] at ha
    rw [LocallyConstant.evalMonoidHom_apply]; rw [e]; rw [LocallyConstant.coe_mk]; rw [if_neg ha]

/--
theorem `factors_prod_eq_basis` / 定理 `factors_prod_eq_basis`

English:
theorem factors_prod_eq_basis
  given: (x : π C (· in s))
  proof: by
  ext y
  dsimp [spanFinBasis]
  split_ifs with h <;> [exact factors_prod_eq_basis_of_eq _ _ h;
    exact factors_prod_eq_basis_of_ne _ _ h]

中文:
定理 factors_prod_eq_basis
  条件: (x : π C (· in s))
  证明: by
  ext y
  dsimp [spanFinBasis]
  split_ifs with h <;> [exact factors_prod_eq_basis_of_eq _ _ h;
    exact factors_prod_eq_basis_of_ne _ _ h]

Depends on / 依赖: factors_prod_eq_basis_of_eq, factors_prod_eq_basis_of_ne, spanFinBasis, split_ifs
-/
theorem factors_prod_eq_basis (x : π C (· in s)) :
    (factors C s x).prod = spanFinBasis C s x := by
  ext y
  dsimp [spanFinBasis]
  split_ifs with h <;> [exact factors_prod_eq_basis_of_eq _ _ h;
    exact factors_prod_eq_basis_of_ne _ _ h]

/--
theorem `GoodProducts.finsuppSum_mem_span_eval` / 定理 `GoodProducts.finsuppSum_mem_span_eval`

English:
theorem GoodProducts.finsuppSum_mem_span_eval
  statement: {a : I} {as : List I}
  proof: by
  apply Submodule.finsuppSum_mem
  intro m hm
  have hsm := (LinearMap.mulLeft Int (e (π C (· in s)) a)).map_smul
  dsimp at hsm
  rw [hsm]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hmas : m.val <= as := by
    apply hc
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm
  refine ⟨⟨a :: m.val, ha.cons_of_le m.prop hmas⟩, ⟨List.cons_le_cons a hmas, ?_⟩⟩
  simp only [Products.eval, List.map, List.prod_cons]

中文:
定理 GoodProducts.finsuppSum_mem_span_eval
  结论: {a : I} {as : 列表 I}
  证明: by
  apply Submodule.finsuppSum_mem
  intro m hm
  have hsm := (LinearMap.mulLeft Int (e (π C (· in s)) a)).map_smul
  dsimp at hsm
  rw [hsm]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hmas : m.val <= as := by
    apply hc
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm
  refine ⟨⟨a :: m.val, ha.cons_of_le m.prop hmas⟩, ⟨List.cons_le_cons a hmas, ?_⟩⟩
  simp only [Products.eval, List.map, List.prod_cons]

Depends on / 依赖: Finset, Finset.mem_coe, Finsupp, Finsupp.mem_support_iff, LinearMap, LinearMap.mulLeft, List.cons_le_cons, List.map, List.prod_cons, Products, Products.eval, Submodule, Submodule.finsuppSum_mem, Submodule.smul_mem, Submodule.subset_span, cons_le_cons, cons_of_le, finsuppSum_mem, ha.cons_of_le, m.prop
-/
theorem GoodProducts.finsuppSum_mem_span_eval {a : I} {as : List I}
    (ha : List.IsChain (· > ·) (a :: as)) {c : Products I ->₀ Int}
    (hc : (c.support : Set (Products I)) subseteq {m | m.val <= as}) :
    (Finsupp.sum c fun a_1 b => e (π C (· in s)) a * b • Products.eval (π C (· in s)) a_1) in
      Submodule.span Int (Products.eval (π C (· in s)) '' {m | m.val <= a :: as}) := by
  apply Submodule.finsuppSum_mem
  intro m hm
  have hsm := (LinearMap.mulLeft Int (e (π C (· in s)) a)).map_smul
  dsimp at hsm
  rw [hsm]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hmas : m.val <= as := by
    apply hc
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm
  refine ⟨⟨a :: m.val, ha.cons_of_le m.prop hmas⟩, ⟨List.cons_le_cons a hmas, ?_⟩⟩
  simp only [Products.eval, List.map, List.prod_cons]

/--
theorem `GoodProducts.spanFin` / 定理 `GoodProducts.spanFin`

English:
theorem GoodProducts.spanFin
  given: [WellFoundedLT I]
  proof: by
  rw [span_iff_products]
  refine le_trans (spanFinBasis.span C s) ?_
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [← factors_prod_eq_basis]
  let l := s.sort (· >= ·)
  dsimp [factors]
  suffices l.SortedGT -> (l.map (fun i => if x.val i = true then e (π C (· in s)) i
      else (1 - (e (π C (· in s)) i)))).prod in
      Submodule.span Int ((Products.eval (π C (· in s))) '' {m | m.val <= l}) from
    Submodule.span_mono (Set.image_subset_range _ _)
      (this (Finset.sortedGT_sort _))
  rw [List.sortedGT_iff_isChain]
  induction l with
  | nil =>
    intro _
    apply Submodule.subset_span
    exact ⟨⟨[], List.isChain_nil⟩,⟨Or.inl rfl, rfl⟩⟩
  | cons a as ih =>
    rw [List.map_cons]; rw [List.prod_cons]
    intro ha
    specialize ih (by rw [List.isChain_cons] at ha; exact ha.2)
    rw [Finsupp.mem_span_image_iff_linearCombination] at ih
    simp only [Finsupp.mem_supported, Finsupp.linearCombination_apply] at ih
    obtain ⟨c, hc, hc'⟩ := ih
    rw [← hc']; clear hc'
    have hmap := fun g => map_finsuppSum (LinearMap.mulLeft Int (e (π C (· in s)) a)) c g
    dsimp at hmap ⊢
    split_ifs
    · rw [hmap]
      exact finsuppSum_mem_span_eval _ _ ha hc
    · noncomm_ring
      -- we use `noncomm_ring` even though this is a commutative ring, because we want a weaker
      -- normalization which preserves multiplication order (i.e. doesn't use commutativity rules)
      rw [hmap]
      apply Submodule.add_mem
      · apply Submodule.finsuppSum_mem
        intro m hm
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨m, ⟨?_, rfl⟩⟩
        simp only [Set.mem_ofPred_eq]
        have hmas : m.val <= as :=
          hc (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm)
        refine le_trans hmas ?_
        cases as with
        | nil => exact (List.nil_lt_cons a []).le
        | cons b bs =>
          apply le_of_lt
          rw [List.isChain_cons_cons] at ha
          exact (List.lt_iff_lex_lt _ _).mp (List.Lex.rel ha.1)
      · apply Submodule.smul_mem
        exact finsuppSum_mem_span_eval _ _ ha hc

中文:
定理 GoodProducts.spanFin
  条件: [WellFoundedLT I]
  证明: by
  rw [span_iff_products]
  refine le_trans (spanFinBasis.span C s) ?_
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [← factors_prod_eq_basis]
  let l := s.sort (· >= ·)
  dsimp [factors]
  suffices l.SortedGT -> (l.map (fun i => if x.val i = true then e (π C (· in s)) i
      else (1 - (e (π C (· in s)) i)))).prod in
      Submodule.span Int ((Products.eval (π C (· in s))) '' {m | m.val <= l}) from
    Submodule.span_mono (Set.image_subset_range _ _)
      (this (Finset.sortedGT_sort _))
  rw [List.sortedGT_iff_isChain]
  induction l with
  | nil =>
    intro _
    apply Submodule.subset_span
    exact ⟨⟨[], List.isChain_nil⟩,⟨Or.inl rfl, rfl⟩⟩
  | cons a as ih =>
    rw [List.map_cons]; rw [List.prod_cons]
    intro ha
    specialize ih (by rw [List.isChain_cons] at ha; exact ha.2)
    rw [Finsupp.mem_span_image_iff_linearCombination] at ih
    simp only [Finsupp.mem_supported, Finsupp.linearCombination_apply] at ih
    obtain ⟨c, hc, hc'⟩ := ih
    rw [← hc']; clear hc'
    have hmap := fun g => map_finsuppSum (LinearMap.mulLeft Int (e (π C (· in s)) a)) c g
    dsimp at hmap ⊢
    split_ifs
    · rw [hmap]
      exact finsuppSum_mem_span_eval _ _ ha hc
    · noncomm_ring
      -- we use `noncomm_ring` even though this is a commutative ring, because we want a weaker
      -- normalization which preserves multiplication order (i.e. doesn't use commutativity rules)
      rw [hmap]
      apply Submodule.add_mem
      · apply Submodule.finsuppSum_mem
        intro m hm
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨m, ⟨?_, rfl⟩⟩
        simp only [Set.mem_ofPred_eq]
        have hmas : m.val <= as :=
          hc (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm)
        refine le_trans hmas ?_
        cases as with
        | nil => exact (List.nil_lt_cons a []).le
        | cons b bs =>
          apply le_of_lt
          rw [List.isChain_cons_cons] at ha
          exact (List.lt_iff_lex_lt _ _).mp (List.Lex.rel ha.1)
      · apply Submodule.smul_mem
        exact finsuppSum_mem_span_eval _ _ ha hc

Depends on / 依赖: Finset, Finset.sortedGT_sort, List.sortedGT_iff_isChain, Products, Products.eval, Set.image_subset_range, SortedGT, Submodule, Submodule.span, Submodule.span_le, Submodule.span_mono, factors, factors_prod_eq_basis, image_subset_range, inducti, l.SortedGT, l.map, le_trans, m.val, s.sort
-/
theorem GoodProducts.spanFin [WellFoundedLT I] :
    ⊤ <= Submodule.span Int (Set.range (eval (π C (· in s)))) := by
  rw [span_iff_products]
  refine le_trans (spanFinBasis.span C s) ?_
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [← factors_prod_eq_basis]
  let l := s.sort (· >= ·)
  dsimp [factors]
  suffices l.SortedGT -> (l.map (fun i => if x.val i = true then e (π C (· in s)) i
      else (1 - (e (π C (· in s)) i)))).prod in
      Submodule.span Int ((Products.eval (π C (· in s))) '' {m | m.val <= l}) from
    Submodule.span_mono (Set.image_subset_range _ _)
      (this (Finset.sortedGT_sort _))
  rw [List.sortedGT_iff_isChain]
  induction l with
  | nil =>
    intro _
    apply Submodule.subset_span
    exact ⟨⟨[], List.isChain_nil⟩,⟨Or.inl rfl, rfl⟩⟩
  | cons a as ih =>
    rw [List.map_cons]; rw [List.prod_cons]
    intro ha
    specialize ih (by rw [List.isChain_cons] at ha; exact ha.2)
    rw [Finsupp.mem_span_image_iff_linearCombination] at ih
    simp only [Finsupp.mem_supported, Finsupp.linearCombination_apply] at ih
    obtain ⟨c, hc, hc'⟩ := ih
    rw [← hc']; clear hc'
    have hmap := fun g => map_finsuppSum (LinearMap.mulLeft Int (e (π C (· in s)) a)) c g
    dsimp at hmap ⊢
    split_ifs
    · rw [hmap]
      exact finsuppSum_mem_span_eval _ _ ha hc
    · noncomm_ring
      -- we use `noncomm_ring` even though this is a commutative ring, because we want a weaker
      -- normalization which preserves multiplication order (i.e. doesn't use commutativity rules)
      rw [hmap]
      apply Submodule.add_mem
      · apply Submodule.finsuppSum_mem
        intro m hm
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨m, ⟨?_, rfl⟩⟩
        simp only [Set.mem_ofPred_eq]
        have hmas : m.val <= as :=
          hc (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm)
        refine le_trans hmas ?_
        cases as with
        | nil => exact (List.nil_lt_cons a []).le
        | cons b bs =>
          apply le_of_lt
          rw [List.isChain_cons_cons] at ha
          exact (List.lt_iff_lex_lt _ _).mp (List.Lex.rel ha.1)
      · apply Submodule.smul_mem
        exact finsuppSum_mem_span_eval _ _ ha hc

end Fin

/--
theorem `fin_comap_jointlySurjective` / 定理 `fin_comap_jointlySurjective`

English:
theorem fin_comap_jointlySurjective
  proof: by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (spanCone hC.isCompact) Int
    (spanCone_isLimit hC.isCompact) f
  exact ⟨(Opposite.unop J), g, h⟩

中文:
定理 fin_comap_jointlySurjective
  证明: by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (spanCone hC.isCompact) Int
    (spanCone_isLimit hC.isCompact) f
  exact ⟨(Opposite.unop J), g, h⟩

Depends on / 依赖: Finset, Opposite, Opposite.unop, Profinite, Profinite.exists_locallyConstant, exists_locallyConstant, hC.isCompact, isCompact, spanCone, spanCone_isLimit
-/
theorem fin_comap_jointlySurjective
    (hC : IsClosed C)
    (f : LocallyConstant C Int) : exists (s : Finset I)
    (g : LocallyConstant (π C (· in s)) Int), f = g.comap ⟨(ProjRestrict C (· in s)),
      continuous_projRestrict _ _⟩ := by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (spanCone hC.isCompact) Int
    (spanCone_isLimit hC.isCompact) f
  exact ⟨(Opposite.unop J), g, h⟩

/--
theorem `GoodProducts.span` / 定理 `GoodProducts.span`

English:
theorem GoodProducts.span
  given: [WellFoundedLT I] (hC : IsClosed C)
  proof: by
  rw [span_iff_products]
  intro f _
  obtain ⟨K, f', rfl⟩ : exists K f', f = πJ C K f' := fin_comap_jointlySurjective C hC f
refine Submodule.span_mono ?_ Submodule.apply_mem_span_image_of_mem_span (πJ C K)
    spanFin C K (Submodule.mem_top : f' in ⊤)
  rintro l ⟨y, ⟨m, rfl⟩, rfl⟩
  exact ⟨m.val, eval_eq_πJ C K m.val m.prop⟩

中文:
定理 GoodProducts.span
  条件: [WellFoundedLT I] (hC : 是闭集 C)
  证明: by
  rw [span_iff_products]
  intro f _
  obtain ⟨K, f', rfl⟩ : exists K f', f = πJ C K f' := fin_comap_jointlySurjective C hC f
refine Submodule.span_mono ?_ Submodule.apply_mem_span_image_of_mem_span (πJ C K)
    spanFin C K (Submodule.mem_top : f' in ⊤)
  rintro l ⟨y, ⟨m, rfl⟩, rfl⟩
  exact ⟨m.val, eval_eq_πJ C K m.val m.prop⟩

Depends on / 依赖: Submodule, Submodule.apply_mem_span_image_of_mem_span, Submodule.mem_top, Submodule.span_mono, apply_mem_span_image_of_mem_span, fin_comap_jointlySurjective, m.prop, m.val, mem_top, spanFin, span_iff_products, span_mono
-/
theorem GoodProducts.span [WellFoundedLT I] (hC : IsClosed C) :
    ⊤ <= Submodule.span Int (Set.range (eval C)) := by
  rw [span_iff_products]
  intro f _
  obtain ⟨K, f', rfl⟩ : exists K f', f = πJ C K f' := fin_comap_jointlySurjective C hC f
refine Submodule.span_mono ?_ Submodule.apply_mem_span_image_of_mem_span (πJ C K)
    spanFin C K (Submodule.mem_top : f' in ⊤)
  rintro l ⟨y, ⟨m, rfl⟩, rfl⟩
  exact ⟨m.val, eval_eq_πJ C K m.val m.prop⟩

end Profinite.NobelingProof
