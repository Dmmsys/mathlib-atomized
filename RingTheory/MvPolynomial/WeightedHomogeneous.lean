/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Tactic.Order

/-!
# Weighted homogeneous polynomials

It is possible to assign weights (in a commutative additive monoid `M`) to the variables of a
multivariate polynomial ring, so that monomials of the ring then have a weighted degree with
respect to the weights of the variables. The weights are represented by a function `w : σ → M`,
where `σ` are the indeterminates.

A multivariate polynomial `φ` is weighted homogeneous of weighted degree `m : M` if all monomials
occurring in `φ` have the same weighted degree `m`.

## Main definitions/lemmas

* `weightedTotalDegree' w φ` : the weighted total degree of a multivariate polynomial with respect
  to the weights `w`, taking values in `WithBot M`.

* `weightedTotalDegree w φ` : When `M` has a `⊥` element, we can define the weighted total degree
  of a multivariate polynomial as a function taking values in `M`.

* `IsWeightedHomogeneous w φ m`: a predicate that asserts that `φ` is weighted homogeneous
  of weighted degree `m` with respect to the weights `w`.

* `weightedHomogeneousSubmodule R w m`: the submodule of homogeneous polynomials
  of weighted degree `m`.

* `weightedHomogeneousComponent w m`: the additive morphism that projects polynomials
  onto their summand that is weighted homogeneous of degree `n` with respect to `w`.

* `sum_weightedHomogeneousComponent`: every polynomial is the sum of its weighted homogeneous
  components.
-/

@[expose] public section


noncomputable section

open Set Function Finset Finsupp AddMonoidAlgebra

variable {R M : Type*} [CommSemiring R]

namespace MvPolynomial

variable {σ : Type*}

section AddCommMonoid

variable [AddCommMonoid M]

/-! ### `weight` -/


section SemilatticeSup

variable [SemilatticeSup M]

/--
Definition of `weightedTotalDegree'` / `weightedTotalDegree'` 的定义

English:
definition weightedTotalDegree'
  signature: (w : σ -> M) (p : MvPolynomial σ R)
  body: p.support.sup fun s => weight w s

中文:
定义 weightedTotalDegree'
  签名: (w : σ -> M) (p : 多元多项式 σ R)
  定义体: p.support.sup fun s => weight w s

Depends on / 依赖: p.support.sup, support, weight
-/
def weightedTotalDegree' (w : σ -> M) (p : MvPolynomial σ R) : WithBot M :=
  p.support.sup fun s => weight w s

/--
theorem `weightedTotalDegree'_eq_bot_iff` / 定理 `weightedTotalDegree'_eq_bot_iff`

English:
theorem weightedTotalDegree'_eq_bot_iff
  given: (w : σ -> M) (p : MvPolynomial σ R)
  proof: by
  simp only [weightedTotalDegree', Finset.sup_eq_bot_iff, mem_support_iff, WithBot.coe_ne_bot,
    MvPolynomial.eq_zero_iff]
  exact forall_congr' fun _ => Classical.not_not

中文:
定理 weightedTotalDegree'_eq_bot_iff
  条件: (w : σ -> M) (p : 多元多项式 σ R)
  证明: by
  simp only [weightedTotalDegree', Finset.sup_eq_bot_iff, mem_support_iff, WithBot.coe_ne_bot,
    MvPolynomial.eq_zero_iff]
  exact forall_congr' fun _ => Classical.not_not
-/
theorem weightedTotalDegree'_eq_bot_iff (w : σ -> M) (p : MvPolynomial σ R) :
    weightedTotalDegree' w p = ⊥ ↔ p = 0 := by
  simp only [weightedTotalDegree', Finset.sup_eq_bot_iff, mem_support_iff, WithBot.coe_ne_bot,
    MvPolynomial.eq_zero_iff]
  exact forall_congr' fun _ => Classical.not_not

/--
theorem `weightedTotalDegree'_zero` / 定理 `weightedTotalDegree'_zero`

English:
theorem weightedTotalDegree'_zero
  given: (w : σ -> M)
  proof: by
  simp only [weightedTotalDegree', support_zero, Finset.sup_empty]

中文:
定理 weightedTotalDegree'_zero
  条件: (w : σ -> M)
  证明: by
  simp only [weightedTotalDegree', support_zero, Finset.sup_empty]
-/
theorem weightedTotalDegree'_zero (w : σ -> M) :
    weightedTotalDegree' w (0 : MvPolynomial σ R) = ⊥ := by
  simp only [weightedTotalDegree', support_zero, Finset.sup_empty]

section OrderBot

variable [OrderBot M]

/--
Definition of `weightedTotalDegree` / `weightedTotalDegree` 的定义

English:
definition weightedTotalDegree
  signature: (w : σ -> M) (p : MvPolynomial σ R)
  body: p.support.sup fun s => weight w s

中文:
定义 weightedTotalDegree
  签名: (w : σ -> M) (p : 多元多项式 σ R)
  定义体: p.support.sup fun s => weight w s

Depends on / 依赖: p.support.sup, support, weight
-/
def weightedTotalDegree (w : σ -> M) (p : MvPolynomial σ R) : M :=
  p.support.sup fun s => weight w s

/--
theorem `weightedTotalDegree_coe` / 定理 `weightedTotalDegree_coe`

English:
theorem weightedTotalDegree_coe
  given: (w : σ -> M) (p : MvPolynomial σ R) (hp : p != 0)
  proof: by
  rw [Ne]; rw [← weightedTotalDegree'_eq_bot_iff w p]; rw [← Ne]; rw [WithBot.ne_bot_iff_exists] at hp
  obtain ⟨m, hm⟩ := hp
  apply le_antisymm
  · simp only [weightedTotalDegree, weightedTotalDegree', Finset.sup_le_iff, WithBot.coe_le_coe]
    intro b
    exact Finset.le_sup
  · simp only [wei

中文:
定理 weightedTotalDegree_coe
  条件: (w : σ -> M) (p : 多元多项式 σ R) (hp : p != 0)
  证明: by
  rw [Ne]; rw [← weightedTotalDegree'_eq_bot_iff w p]; rw [← Ne]; rw [WithBot.ne_bot_iff_exists] at hp
  obtain ⟨m, hm⟩ := hp
  apply le_antisymm
  · simp only [weightedTotalDegree, weightedTotalDegree', Finset.sup_le_iff, WithBot.coe_le_coe]
    intro b
    exact Finset.le_sup
  · simp only [wei

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_le_iff, WithBot, WithBot.coe_le_coe, WithBot.ne_bot_iff_exists, _eq_bot_iff, coe_le_coe, hm.symm, le_antisymm, le_of_eq, le_sup, ne_bot_iff_exists, sup_le_iff, weightedTotalDegree
-/
theorem weightedTotalDegree_coe (w : σ -> M) (p : MvPolynomial σ R) (hp : p != 0) :
    weightedTotalDegree' w p = ↑(weightedTotalDegree w p) := by
  rw [Ne]; rw [← weightedTotalDegree'_eq_bot_iff w p]; rw [← Ne]; rw [WithBot.ne_bot_iff_exists] at hp
  obtain ⟨m, hm⟩ := hp
  apply le_antisymm
  · simp only [weightedTotalDegree, weightedTotalDegree', Finset.sup_le_iff, WithBot.coe_le_coe]
    intro b
    exact Finset.le_sup
  · simp only [weightedTotalDegree]
    have hm' : weightedTotalDegree' w p <= m := le_of_eq hm.symm
    rw [← hm]
    simpa [weightedTotalDegree'] using hm'

/--
theorem `weightedTotalDegree_zero` / 定理 `weightedTotalDegree_zero`

English:
theorem weightedTotalDegree_zero
  given: (w : σ -> M)
  proof: by
  simp only [weightedTotalDegree, support_zero, Finset.sup_empty]

中文:
定理 weightedTotalDegree_zero
  条件: (w : σ -> M)
  证明: by
  simp only [weightedTotalDegree, support_zero, Finset.sup_empty]

Depends on / 依赖: Finset, Finset.sup_empty, sup_empty, support_zero, weightedTotalDegree
-/
theorem weightedTotalDegree_zero (w : σ -> M) :
    weightedTotalDegree w (0 : MvPolynomial σ R) = ⊥ := by
  simp only [weightedTotalDegree, support_zero, Finset.sup_empty]

/--
theorem `le_weightedTotalDegree` / 定理 `le_weightedTotalDegree`

English:
theorem le_weightedTotalDegree
  statement: (w : σ -> M) {φ : MvPolynomial σ R} {d : σ ->₀ Nat}
  proof: le_sup hd

中文:
定理 le_weightedTotalDegree
  结论: (w : σ -> M) {φ : 多元多项式 σ R} {d : σ ->₀ 自然数}
  证明: le_sup hd

Depends on / 依赖: le_sup
-/
theorem le_weightedTotalDegree (w : σ -> M) {φ : MvPolynomial σ R} {d : σ ->₀ Nat}
    (hd : d in φ.support) : weight w d <= φ.weightedTotalDegree w :=
  le_sup hd

end OrderBot

end SemilatticeSup

/--
Definition of `IsWeightedHomogeneous` / `IsWeightedHomogeneous` 的定义

English:
definition IsWeightedHomogeneous
  signature: (w : σ -> M) (φ : MvPolynomial σ R) (m : M)
  body: forall ⦃d⦄, coeff d φ != 0 -> weight w d = m

中文:
定义 IsWeightedHomogeneous
  签名: (w : σ -> M) (φ : 多元多项式 σ R) (m : M)
  定义体: forall ⦃d⦄, coeff d φ != 0 -> weight w d = m

Depends on / 依赖: weight
-/
def IsWeightedHomogeneous (w : σ -> M) (φ : MvPolynomial σ R) (m : M) : Prop :=
  forall ⦃d⦄, coeff d φ != 0 -> weight w d = m

variable (R)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `weightedHomogeneousSubmodule` / `weightedHomogeneousSubmodule` 的定义

English:
definition weightedHomogeneousSubmodule
  signature: (w : σ -> M) (m : M)
  body: { x | x.IsWeightedHomogeneous w m }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    exact ha (right_ne_zero_of_mul hc)
  zero_mem' _ hd := False.elim (hd <| coeff_zero _)
  add_mem' {a} {b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a != 0 ∨ coeff c b != 0 := by

中文:
定义 weightedHomogeneousSubmodule
  签名: (w : σ -> M) (m : M)
  定义体: { x | x.IsWeightedHomogeneous w m }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    exact ha (right_ne_zero_of_mul hc)
  zero_mem' _ hd := False.elim (hd <| coeff_zero _)
  add_mem' {a} {b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a != 0 ∨ coeff c b != 0 := by

Depends on / 依赖: IsWeightedHomogeneous, x.IsWeightedHomogeneous
-/
def weightedHomogeneousSubmodule (w : σ -> M) (m : M) : Submodule R (MvPolynomial σ R) where
  carrier := { x | x.IsWeightedHomogeneous w m }
  smul_mem' r a ha c hc := by
    rw [coeff_smul] at hc
    exact ha (right_ne_zero_of_mul hc)
  zero_mem' _ hd := False.elim (hd <| coeff_zero _)
  add_mem' {a} {b} ha hb c hc := by
    rw [coeff_add] at hc
    obtain h | h : coeff c a != 0 ∨ coeff c b != 0 := by
      contrapose! hc
      simp only [hc, add_zero]
    · exact ha h
    · exact hb h

@[simp]
/--
theorem `mem_weightedHomogeneousSubmodule` / 定理 `mem_weightedHomogeneousSubmodule`

English:
theorem mem_weightedHomogeneousSubmodule
  given: (w : σ -> M) (m : M) (p : MvPolynomial σ R)
  proof: Iff.rfl

中文:
定理 mem_weightedHomogeneousSubmodule
  条件: (w : σ -> M) (m : M) (p : 多元多项式 σ R)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_weightedHomogeneousSubmodule (w : σ -> M) (m : M) (p : MvPolynomial σ R) :
    p in weightedHomogeneousSubmodule R w m ↔ p.IsWeightedHomogeneous w m :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `weightedHomogeneousSubmodule_eq_finsupp_supported` / 定理 `weightedHomogeneousSubmodule_eq_finsupp_supported`

English:
theorem weightedHomogeneousSubmodule_eq_finsupp_supported
  given: (w : σ -> M) (m : M)
  proof: by
  ext x
  simp [IsWeightedHomogeneous]
  simp [AddMonoidAlgebra.mem_supported, Set.subset_def, MvPolynomial, coeff]

中文:
定理 weightedHomogeneousSubmodule_eq_finsupp_supported
  条件: (w : σ -> M) (m : M)
  证明: by
  ext x
  simp [IsWeightedHomogeneous]
  simp [AddMonoidAlgebra.mem_supported, Set.subset_def, MvPolynomial, coeff]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.mem_supported, IsWeightedHomogeneous, MvPolynomial, Set.subset_def, mem_supported, subset_def
-/
theorem weightedHomogeneousSubmodule_eq_finsupp_supported (w : σ -> M) (m : M) :
    weightedHomogeneousSubmodule R w m = AddMonoidAlgebra.supported R R {d | weight w d = m} := by
  ext x
  simp [IsWeightedHomogeneous]
  simp [AddMonoidAlgebra.mem_supported, Set.subset_def, MvPolynomial, coeff]

/--
lemma `weightedHomogeneousSubmodule_fg` / 引理 `weightedHomogeneousSubmodule_fg`

English:
lemma weightedHomogeneousSubmodule_fg
  given: [Finite σ] (w : σ -> Nat) (hw : forall (x : σ), w x != 0) (n : Nat)
  proof: by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [← Module.Finite.iff_fg]
  have := (Finsupp.finite_of_nat_weight_eq w hw n).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport R {d | Finsupp.weight w d = n})

中文:
引理 weightedHomogeneousSubmodule_fg
  条件: [有限 σ] (w : σ -> 自然数) (hw : 对任意 (x : σ), w x != 0) (n : 自然数)
  证明: by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [← Module.Finite.iff_fg]
  have := (Finsupp.finite_of_nat_weight_eq w hw n).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport R {d | Finsupp.weight w d = n})

Depends on / 依赖: Finite, Finsupp, Finsupp.finite_of_nat_weight_eq, Finsupp.weight, IsTopologicalGroup, IsTopologicalGroup.regularSpace, Module, Module.Finite.iff_fg, Module.Finite.of_basis, RegularSpace, Tendsto, basisRestrictSupport, closure, continuous_mul, continuous_mul.tendsto, finite_of_nat_weight_eq, iff_fg, image_prod, image_subset_iff, interior
-/
lemma weightedHomogeneousSubmodule_fg [Finite σ] (w : σ -> Nat) (hw : forall (x : σ), w x != 0) (n : Nat) :
    (weightedHomogeneousSubmodule R w n).FG := by
  rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [← Module.Finite.iff_fg]
  have := (Finsupp.finite_of_nat_weight_eq w hw n).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport R {d | Finsupp.weight w d = n})

variable {R}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `weightedHomogeneousSubmodule_mul` / 定理 `weightedHomogeneousSubmodule_mul`

English:
theorem weightedHomogeneousSubmodule_mul
  given: (w : σ -> M) (m n : M)
  proof: by
  classical
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ != 0 ∧ coeff e ψ != 0 := by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne, not_false_iff, ze

中文:
定理 weightedHomogeneousSubmodule_mul
  条件: (w : σ -> M) (m n : M)
  证明: by
  classical
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ != 0 ∧ coeff e ψ != 0 := by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne, not_false_iff, ze

Depends on / 依赖: Finset, Finset.exists_ne_zero_of_sum_ne_zero, Submodule, Submodule.mul_le, classical, coeff_mul, contrapose, exists_ne_zero_of_sum_ne_zero, map_add, mem_antidiagonal, mem_antidiagonal.mp, mul_le, mul_zero, not_false_iff, zero_mul
-/
theorem weightedHomogeneousSubmodule_mul (w : σ -> M) (m n : M) :
    weightedHomogeneousSubmodule R w m * weightedHomogeneousSubmodule R w n <=
      weightedHomogeneousSubmodule R w (m + n) := by
  classical
  rw [Submodule.mul_le]
  intro φ hφ ψ hψ c hc
  rw [coeff_mul] at hc
  obtain ⟨⟨d, e⟩, hde, H⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have aux : coeff d φ != 0 ∧ coeff e ψ != 0 := by
    contrapose! H
    by_cases h : coeff d φ = 0 <;>
      simp_all only [Ne, not_false_iff, zero_mul, mul_zero]
  rw [← mem_antidiagonal.mp hde]; rw [← hφ aux.1]; rw [← hψ aux.2]; rw [map_add]

/--
theorem `isWeightedHomogeneous_monomial` / 定理 `isWeightedHomogeneous_monomial`

English:
theorem isWeightedHomogeneous_monomial
  statement: (w : σ -> M) (d : σ ->₀ Nat) (r : R) {m : M}
  proof: by
  classical
  intro c hc
  rw [coeff_monomial] at hc
  split_ifs at hc with h
  · subst c
    exact hm
  · contradiction

中文:
定理 isWeightedHomogeneous_monomial
  结论: (w : σ -> M) (d : σ ->₀ 自然数) (r : R) {m : M}
  证明: by
  classical
  intro c hc
  rw [coeff_monomial] at hc
  split_ifs at hc with h
  · subst c
    exact hm
  · contradiction

Depends on / 依赖: classical, coeff_monomial, split_ifs
-/
theorem isWeightedHomogeneous_monomial (w : σ -> M) (d : σ ->₀ Nat) (r : R) {m : M}
    (hm : weight w d = m) : IsWeightedHomogeneous w (monomial d r) m := by
  classical
  intro c hc
  rw [coeff_monomial] at hc
  split_ifs at hc with h
  · subst c
    exact hm
  · contradiction

/--
theorem `isWeightedHomogeneous_of_total_degree_zero` / 定理 `isWeightedHomogeneous_of_total_degree_zero`

English:
theorem isWeightedHomogeneous_of_total_degree_zero
  statement: [SemilatticeSup M] [OrderBot M] (w : σ -> M)
  proof: by
  intro d hd
  have h := weightedTotalDegree_coe w p (MvPolynomial.ne_zero_iff.mpr ⟨d, hd⟩)
  simp only [weightedTotalDegree', hp] at h
  rw [eq_bot_iff]; rw [← WithBot.coe_le_coe]; rw [← h]
  apply Finset.le_sup (mem_support_iff.mpr hd)

中文:
定理 isWeightedHomogeneous_of_total_degree_zero
  结论: [SemilatticeSup M] [有底序 M] (w : σ -> M)
  证明: by
  intro d hd
  have h := weightedTotalDegree_coe w p (MvPolynomial.ne_zero_iff.mpr ⟨d, hd⟩)
  simp only [weightedTotalDegree', hp] at h
  rw [eq_bot_iff]; rw [← WithBot.coe_le_coe]; rw [← h]
  apply Finset.le_sup (mem_support_iff.mpr hd)

Depends on / 依赖: Finset, Finset.le_sup, MvPolynomial, MvPolynomial.ne_zero_iff.mpr, WithBot, WithBot.coe_le_coe, coe_le_coe, eq_bot_iff, le_sup, mem_support_iff, mem_support_iff.mpr, ne_zero_iff, weightedTotalDegree, weightedTotalDegree_coe
-/
theorem isWeightedHomogeneous_of_total_degree_zero [SemilatticeSup M] [OrderBot M] (w : σ -> M)
    {p : MvPolynomial σ R} (hp : weightedTotalDegree w p = (⊥ : M)) :
    IsWeightedHomogeneous w p (⊥ : M) := by
  intro d hd
  have h := weightedTotalDegree_coe w p (MvPolynomial.ne_zero_iff.mpr ⟨d, hd⟩)
  simp only [weightedTotalDegree', hp] at h
  rw [eq_bot_iff]; rw [← WithBot.coe_le_coe]; rw [← h]
  apply Finset.le_sup (mem_support_iff.mpr hd)

/--
theorem `isWeightedHomogeneous_C` / 定理 `isWeightedHomogeneous_C`

English:
theorem isWeightedHomogeneous_C
  given: (w : σ -> M) (r : R)
  proof: isWeightedHomogeneous_monomial _ _ _ (map_zero _)

中文:
定理 isWeightedHomogeneous_C
  条件: (w : σ -> M) (r : R)
  证明: isWeightedHomogeneous_monomial _ _ _ (map_zero _)

Depends on / 依赖: isWeightedHomogeneous_monomial, map_zero
-/
theorem isWeightedHomogeneous_C (w : σ -> M) (r : R) :
    IsWeightedHomogeneous w (C r : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_monomial _ _ _ (map_zero _)

variable (R)

/--
theorem `isWeightedHomogeneous_zero` / 定理 `isWeightedHomogeneous_zero`

English:
theorem isWeightedHomogeneous_zero
  given: (w : σ -> M) (m : M)
  proof: (weightedHomogeneousSubmodule R w m).zero_mem

中文:
定理 isWeightedHomogeneous_zero
  条件: (w : σ -> M) (m : M)
  证明: (weightedHomogeneousSubmodule R w m).zero_mem

Depends on / 依赖: weightedHomogeneousSubmodule, zero_mem
-/
theorem isWeightedHomogeneous_zero (w : σ -> M) (m : M) :
    IsWeightedHomogeneous w (0 : MvPolynomial σ R) m :=
  (weightedHomogeneousSubmodule R w m).zero_mem

/--
theorem `isWeightedHomogeneous_one` / 定理 `isWeightedHomogeneous_one`

English:
theorem isWeightedHomogeneous_one
  given: (w : σ -> M)
  statement: IsWeightedHomogeneous w (1 : MvPolynomial σ R) 0
  proof: isWeightedHomogeneous_C _ _

中文:
定理 isWeightedHomogeneous_one
  条件: (w : σ -> M)
  结论: IsWeightedHomogeneous w (1 : 多元多项式 σ R) 0
  证明: isWeightedHomogeneous_C _ _

Depends on / 依赖: isWeightedHomogeneous_C
-/
theorem isWeightedHomogeneous_one (w : σ -> M) : IsWeightedHomogeneous w (1 : MvPolynomial σ R) 0 :=
  isWeightedHomogeneous_C _ _

/--
lemma `isWeightedHomogeneous_of_isEmpty` / 引理 `isWeightedHomogeneous_of_isEmpty`

English:
lemma isWeightedHomogeneous_of_isEmpty
  given: [IsEmpty σ] (w : σ -> M) (f : MvPolynomial σ R)
  proof: by
  rw [eq_C_of_isEmpty f]
  exact isWeightedHomogeneous_C _ _

中文:
引理 isWeightedHomogeneous_of_isEmpty
  条件: [是空 σ] (w : σ -> M) (f : 多元多项式 σ R)
  证明: by
  rw [eq_C_of_isEmpty f]
  exact isWeightedHomogeneous_C _ _

Depends on / 依赖: eq_C_of_isEmpty, isWeightedHomogeneous_C
-/
lemma isWeightedHomogeneous_of_isEmpty [IsEmpty σ] (w : σ -> M) (f : MvPolynomial σ R) :
    IsWeightedHomogeneous w f 0 := by
  rw [eq_C_of_isEmpty f]
  exact isWeightedHomogeneous_C _ _

/--
theorem `isWeightedHomogeneous_X` / 定理 `isWeightedHomogeneous_X`

English:
theorem isWeightedHomogeneous_X
  given: (w : σ -> M) (i : σ)
  proof: by
  apply isWeightedHomogeneous_monomial
  simp only [weight, LinearMap.toAddMonoidHom_coe, linearCombination_single, one_nsmul]

中文:
定理 isWeightedHomogeneous_X
  条件: (w : σ -> M) (i : σ)
  证明: by
  apply isWeightedHomogeneous_monomial
  simp only [weight, LinearMap.toAddMonoidHom_coe, linearCombination_single, one_nsmul]

Depends on / 依赖: LinearMap, LinearMap.toAddMonoidHom_coe, isWeightedHomogeneous_monomial, linearCombination_single, one_nsmul, toAddMonoidHom_coe, weight
-/
theorem isWeightedHomogeneous_X (w : σ -> M) (i : σ) :
    IsWeightedHomogeneous w (X i : MvPolynomial σ R) (w i) := by
  apply isWeightedHomogeneous_monomial
  simp only [weight, LinearMap.toAddMonoidHom_coe, linearCombination_single, one_nsmul]

namespace IsWeightedHomogeneous

variable {R}
variable {φ ψ : MvPolynomial σ R} {m n : M}

/--
theorem `coeff_eq_zero` / 定理 `coeff_eq_zero`

English:
theorem coeff_eq_zero
  statement: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (d : σ ->₀ Nat)
  proof: by
  have aux := mt (@hφ d) hd
  rwa [Classical.not_not] at aux

中文:
定理 coeff_eq_zero
  结论: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (d : σ ->₀ 自然数)
  证明: by
  have aux := mt (@hφ d) hd
  rwa [Classical.not_not] at aux

Depends on / 依赖: Classical, Classical.not_not, not_not
-/
theorem coeff_eq_zero {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (d : σ ->₀ Nat)
    (hd : weight w d != n) : coeff d φ = 0 := by
  have aux := mt (@hφ d) hd
  rwa [Classical.not_not] at aux

/--
theorem `inj_right` / 定理 `inj_right`

English:
theorem inj_right
  statement: {w : σ -> M} (hφ : φ != 0) (hm : IsWeightedHomogeneous w φ m)
  proof: by
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero hφ
  rw [← hm hd]; rw [← hn hd]

中文:
定理 inj_right
  结论: {w : σ -> M} (hφ : φ != 0) (hm : IsWeightedHomogeneous w φ m)
  证明: by
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero hφ
  rw [← hm hd]; rw [← hn hd]

Depends on / 依赖: exists_coeff_ne_zero
-/
theorem inj_right {w : σ -> M} (hφ : φ != 0) (hm : IsWeightedHomogeneous w φ m)
    (hn : IsWeightedHomogeneous w φ n) : m = n := by
  obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero hφ
  rw [← hm hd]; rw [← hn hd]

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n)
  proof: (weightedHomogeneousSubmodule R w n).add_mem hφ hψ

中文:
定理 add
  条件: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n)
  证明: (weightedHomogeneousSubmodule R w n).add_mem hφ hψ

Depends on / 依赖: add_mem, weightedHomogeneousSubmodule
-/
theorem add {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ + ψ) n :=
  (weightedHomogeneousSubmodule R w n).add_mem hφ hψ

section CommRing

-- In this section we shadow the semiring `R` with a ring `R`.
variable {R : Type*} [CommRing R] {w : σ -> M} {φ ψ : MvPolynomial σ R}

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  given: (hφ : IsWeightedHomogeneous w φ n)
  statement: IsWeightedHomogeneous w (-φ) n
  proof: (weightedHomogeneousSubmodule R w n).neg_mem hφ

中文:
定理 neg
  条件: (hφ : IsWeightedHomogeneous w φ n)
  结论: IsWeightedHomogeneous w (-φ) n
  证明: (weightedHomogeneousSubmodule R w n).neg_mem hφ

Depends on / 依赖: neg_mem, weightedHomogeneousSubmodule
-/
theorem neg (hφ : IsWeightedHomogeneous w φ n) : IsWeightedHomogeneous w (-φ) n :=
  (weightedHomogeneousSubmodule R w n).neg_mem hφ

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  given: (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n)
  proof: (weightedHomogeneousSubmodule R w n).sub_mem hφ hψ

中文:
定理 sub
  条件: (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n)
  证明: (weightedHomogeneousSubmodule R w n).sub_mem hφ hψ

Depends on / 依赖: sub_mem, weightedHomogeneousSubmodule
-/
theorem sub (hφ : IsWeightedHomogeneous w φ n) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ - ψ) n :=
  (weightedHomogeneousSubmodule R w n).sub_mem hφ hψ

end CommRing

/--
theorem `eq_zero_of_no_monomials` / 定理 `eq_zero_of_no_monomials`

English:
theorem eq_zero_of_no_monomials
  statement: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n)
  proof: support_eq_empty.mp Finset.eq_empty_of_forall_notMem
    fun _ hd => hno _ (hφ (mem_support_iff.mp hd))

中文:
定理 eq_zero_of_no_monomials
  结论: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n)
  证明: support_eq_empty.mp Finset.eq_empty_of_forall_notMem
    fun _ hd => hno _ (hφ (mem_support_iff.mp hd))

Depends on / 依赖: Finset, Finset.eq_empty_of_forall_notMem, eq_empty_of_forall_notMem, mem_support_iff, mem_support_iff.mp, support_eq_empty, support_eq_empty.mp
-/
theorem eq_zero_of_no_monomials {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n)
    (hno : forall d : σ ->₀ Nat, weight w d != n) : φ = 0 :=
support_eq_empty.mp Finset.eq_empty_of_forall_notMem
    fun _ hd => hno _ (hφ (mem_support_iff.mp hd))

/--
theorem `eq_monomial_of_unique_weight` / 定理 `eq_monomial_of_unique_weight`

English:
theorem eq_monomial_of_unique_weight
  statement: {w : σ -> M} {d₀ : σ ->₀ Nat} (hφ : IsWeightedHomogeneous w φ n)
  proof: eq_monomial_of_support_subset_singleton fun d hd => huniq d (hφ (mem_support_iff.mp hd))

中文:
定理 eq_monomial_of_unique_weight
  结论: {w : σ -> M} {d₀ : σ ->₀ 自然数} (hφ : IsWeightedHomogeneous w φ n)
  证明: eq_monomial_of_support_subset_singleton fun d hd => huniq d (hφ (mem_support_iff.mp hd))

Depends on / 依赖: eq_monomial_of_support_subset_singleton, mem_support_iff, mem_support_iff.mp
-/
theorem eq_monomial_of_unique_weight {w : σ -> M} {d₀ : σ ->₀ Nat} (hφ : IsWeightedHomogeneous w φ n)
    (huniq : forall d, weight w d = n -> d = d₀) : φ = monomial d₀ (coeff d₀ φ) :=
  eq_monomial_of_support_subset_singleton fun d hd => huniq d (hφ (mem_support_iff.mp hd))

/--
theorem `sum` / 定理 `sum`

English:
theorem sum
  statement: {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : M) {w : σ -> M}
  proof: (weightedHomogeneousSubmodule R w n).sum_mem h

中文:
定理 求和
  结论: {ι : 类型} (s : 有限集 ι) (φ : ι -> 多元多项式 σ R) (n : M) {w : σ -> M}
  证明: (weightedHomogeneousSubmodule R w n).sum_mem h

Depends on / 依赖: sum_mem, weightedHomogeneousSubmodule
-/
theorem sum {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : M) {w : σ -> M}
    (h : forall i in s, IsWeightedHomogeneous w (φ i) n) : IsWeightedHomogeneous w (∑ i in s, φ i) n :=
  (weightedHomogeneousSubmodule R w n).sum_mem h

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n)
  proof: weightedHomogeneousSubmodule_mul w m n Submodule.mul_mem_mul hφ hψ

中文:
定理 mul
  条件: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n)
  证明: weightedHomogeneousSubmodule_mul w m n Submodule.mul_mem_mul hφ hψ

Depends on / 依赖: Submodule, Submodule.mul_mem_mul, mul_mem_mul, weightedHomogeneousSubmodule_mul
-/
theorem mul {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (hψ : IsWeightedHomogeneous w ψ n) :
    IsWeightedHomogeneous w (φ * ψ) (m + n) :=
weightedHomogeneousSubmodule_mul w m n Submodule.mul_mem_mul hφ hψ

/--
lemma `C_mul` / 引理 `C_mul`

English:
lemma C_mul
  given: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (r : R)
  proof: by
  rw [← zero_add m]
  exact (isWeightedHomogeneous_C w r).mul hφ

中文:
引理 C_mul
  条件: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (r : R)
  证明: by
  rw [← zero_add m]
  exact (isWeightedHomogeneous_C w r).mul hφ

Depends on / 依赖: isWeightedHomogeneous_C, zero_add
-/
lemma C_mul {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (r : R) :
    IsWeightedHomogeneous w (C r * φ) m := by
  rw [← zero_add m]
  exact (isWeightedHomogeneous_C w r).mul hφ

/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (n : Nat)
  proof: by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact isWeightedHomogeneous_one R w
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hφ

中文:
定理 pow
  条件: {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (n : 自然数)
  证明: by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact isWeightedHomogeneous_one R w
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hφ

Depends on / 依赖: ih.mul, isWeightedHomogeneous_one, pow_succ, pow_zero, succ_nsmul, zero_smul
-/
theorem pow {w : σ -> M} (hφ : IsWeightedHomogeneous w φ m) (n : Nat) :
    IsWeightedHomogeneous w (φ ^ n) (n • m) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact isWeightedHomogeneous_one R w
  | succ n ih => rw [pow_succ, succ_nsmul]; exact ih.mul hφ

/--
theorem `prod` / 定理 `prod`

English:
theorem prod
  given: {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : ι -> M) {w : σ -> M}
  proof: by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isWeightedHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    in

中文:
定理 乘积
  条件: {ι : 类型} (s : 有限集 ι) (φ : ι -> 多元多项式 σ R) (n : ι -> M) {w : σ -> M}
  证明: by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isWeightedHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    in

Depends on / 依赖: Finset, Finset.induction_on, Finset.mem_insert_of_mem, Finset.mem_insert_self, Finset.prod_empty, Finset.prod_insert, Finset.sum_empty, Finset.sum_insert, classical, induction_on, isWeightedHomogeneous_one, mem_insert_of_mem, mem_insert_self, not_false_iff, prod_empty, prod_insert, sum_empty, sum_insert
-/
theorem prod {ι : Type*} (s : Finset ι) (φ : ι -> MvPolynomial σ R) (n : ι -> M) {w : σ -> M} :
    (forall i in s, IsWeightedHomogeneous w (φ i) (n i)) ->
      IsWeightedHomogeneous w (∏ i in s, φ i) (∑ i in s, n i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro
    simp only [isWeightedHomogeneous_one, Finset.sum_empty, Finset.prod_empty]
  · intro i s his IH h
    simp only [his, Finset.prod_insert, Finset.sum_insert, not_false_iff]
    apply (h i (Finset.mem_insert_self _ _)).mul (IH _)
    intro j hjs
    exact h j (Finset.mem_insert_of_mem hjs)

/--
theorem `weighted_total_degree` / 定理 `weighted_total_degree`

English:
theorem weighted_total_degree
  statement: [SemilatticeSup M] {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n)
  proof: by
  simp only [weightedTotalDegree']
  apply le_antisymm
  · simp only [Finset.sup_le_iff, mem_support_iff, WithBot.coe_le_coe]
    exact fun d hd => le_of_eq (hφ hd)
  · obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero h
    simp only [← hφ hd]
    replace hd := Finsupp.mem_suppor

中文:
定理 weighted_total_degree
  结论: [SemilatticeSup M] {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n)
  证明: by
  simp only [weightedTotalDegree']
  apply le_antisymm
  · simp only [Finset.sup_le_iff, mem_support_iff, WithBot.coe_le_coe]
    exact fun d hd => le_of_eq (hφ hd)
  · obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero h
    simp only [← hφ hd]
    replace hd := Finsupp.mem_suppor

Depends on / 依赖: Finset, Finset.le_sup, Finset.sup_le_iff, Finsupp, Finsupp.mem_support_iff.mpr, WithBot, WithBot.coe_le_coe, coe_le_coe, exists_coeff_ne_zero, le_antisymm, le_of_eq, le_sup, mem_support_iff, replace, sup_le_iff, weightedTotalDegree
-/
theorem weighted_total_degree [SemilatticeSup M] {w : σ -> M} (hφ : IsWeightedHomogeneous w φ n)
    (h : φ != 0) : weightedTotalDegree' w φ = n := by
  simp only [weightedTotalDegree']
  apply le_antisymm
  · simp only [Finset.sup_le_iff, mem_support_iff, WithBot.coe_le_coe]
    exact fun d hd => le_of_eq (hφ hd)
  · obtain ⟨d, hd⟩ : exists d, coeff d φ != 0 := exists_coeff_ne_zero h
    simp only [← hφ hd]
    replace hd := Finsupp.mem_support_iff.mpr hd
    apply Finset.le_sup hd

set_option backward.isDefEq.respectTransparency false in
/--
lemma `induction_on` / 引理 `induction_on`

English:
lemma induction_on
  statement: {w : σ -> M} {m : M}
  proof: by
  suffices h : forall a, motive (C a * p) (.C_mul hp _) by simpa using h 1
  let A : Submodule R (MvPolynomial σ R) :=
    { carrier := { p | exists hp, forall a, motive (C a * p) (.C_mul hp _) }
      add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ =>
        ⟨.add ‹_› ‹_›, fun a => by simp [mul_add, add _ _ _ 

中文:
引理 induction_on
  结论: {w : σ -> M} {m : M}
  证明: by
  suffices h : forall a, motive (C a * p) (.C_mul hp _) by simpa using h 1
  let A : Submodule R (MvPolynomial σ R) :=
    { carrier := { p | exists hp, forall a, motive (C a * p) (.C_mul hp _) }
      add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ =>
        ⟨.add ‹_› ‹_›, fun a => by simp [mul_add, add _ _ _ 

Depends on / 依赖: Algebra, Algebra.smul_def, C_mul, MvPolynomial, Submodule, add_mem, algebraMap_eq, carrier, isWeightedHomogeneous_zero, motive, mul_add, mul_assoc, simp_rw, smul_def, smul_mem, zero_mem
-/
lemma induction_on {w : σ -> M} {m : M}
    {motive : (p : MvPolynomial σ R) -> p.IsWeightedHomogeneous w m -> Prop}
    (zero : motive 0 (isWeightedHomogeneous_zero R w m))
    (add : forall p q hp hq, motive p hp -> motive q hq -> motive (p + q) (hp.add hq))
    (monomial : forall (d : σ ->₀ Nat) (r : R) (hr : Finsupp.weight w d = m),
      motive ((monomial d) r) (isWeightedHomogeneous_monomial w d r hr))
    {p : MvPolynomial σ R} (hp : p.IsWeightedHomogeneous w m) :
    motive p hp := by
  suffices h : forall a, motive (C a * p) (.C_mul hp _) by simpa using h 1
  let A : Submodule R (MvPolynomial σ R) :=
    { carrier := { p | exists hp, forall a, motive (C a * p) (.C_mul hp _) }
      add_mem' := fun ⟨_, hx⟩ ⟨_, hy⟩ =>
        ⟨.add ‹_› ‹_›, fun a => by simp [mul_add, add _ _ _ _ (hx a) (hy a)]⟩
      zero_mem' := ⟨isWeightedHomogeneous_zero R w m, by simp [zero]⟩
      smul_mem' := fun a x ⟨_, hx⟩ => ⟨by simp [Algebra.smul_def, C_mul ‹_› a], fun a => by
        simp_rw [Algebra.smul_def, algebraMap_eq, ← mul_assoc, ← map_mul]
        apply hx⟩ }
  rw [← mem_weightedHomogeneousSubmodule]; rw [weightedHomogeneousSubmodule_eq_finsupp_supported]; rw [AddMonoidAlgebra.supported_eq_span_single] at hp
  refine (Submodule.span_le (p := A) |>.mpr ?_ hp).2
  rw [Set.image_subset_iff]
  intro d hd
  simp only [MvPolynomial, Submodule.coe_set_mk, AddSubmonoid.coe_set_mk,
    AddSubsemigroup.coe_set_mk, preimage_ofPred_eq, mem_ofPred_eq, A]
  refine ⟨isWeightedHomogeneous_monomial w d 1 hd, fun a => ?_⟩
  simpa only [single_eq_monomial, ← MvPolynomial.C_mul_monomial] using monomial _ (a * 1) hd

end IsWeightedHomogeneous

variable {R}

/--
lemma `WeightedHomogeneousSubmodule.gradedMonoid` / 引理 `WeightedHomogeneousSubmodule.gradedMonoid`

English:
lemma WeightedHomogeneousSubmodule.gradedMonoid
  given: {w : σ -> M}
  proof: isWeightedHomogeneous_one R w
  mul_mem _ _ _ _ := IsWeightedHomogeneous.mul

中文:
引理 WeightedHomogeneousSubmodule.gradedMonoid
  条件: {w : σ -> M}
  证明: isWeightedHomogeneous_one R w
  mul_mem _ _ _ _ := IsWeightedHomogeneous.mul

Depends on / 依赖: isWeightedHomogeneous_one
-/
lemma WeightedHomogeneousSubmodule.gradedMonoid {w : σ -> M} :
    SetLike.GradedMonoid (weightedHomogeneousSubmodule R w) where
  one_mem := isWeightedHomogeneous_one R w
  mul_mem _ _ _ _ := IsWeightedHomogeneous.mul

/--
Definition of `weightedHomogeneousComponent` / `weightedHomogeneousComponent` 的定义

English:
definition weightedHomogeneousComponent
  signature: (w : σ -> M) (n : M)
  body: letI := Classical.decEq M
  (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Submodule.subtype _ ∘ₗ
    Finsupp.restrictDom _ _ {d | weight w d = n} ∘ₗ (coeffLinearEquiv _).toLinearMap

中文:
定义 weightedHomogeneousComponent
  签名: (w : σ -> M) (n : M)
  定义体: letI := Classical.decEq M
  (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Submodule.subtype _ ∘ₗ
    Finsupp.restrictDom _ _ {d | weight w d = n} ∘ₗ (coeffLinearEquiv _).toLinearMap

Depends on / 依赖: Classical, Classical.decEq, Finsupp, Finsupp.restrictDom, Submodule, Submodule.subtype, coeffLinearEquiv, restrictDom, subtype, symm.toLinearMap, toLinearMap, weight
-/
def weightedHomogeneousComponent (w : σ -> M) (n : M) : MvPolynomial σ R ->ₗ[R] MvPolynomial σ R :=
  letI := Classical.decEq M
  (coeffLinearEquiv _).symm.toLinearMap ∘ₗ Submodule.subtype _ ∘ₗ
    Finsupp.restrictDom _ _ {d | weight w d = n} ∘ₗ (coeffLinearEquiv _).toLinearMap

section WeightedHomogeneousComponent

variable {w : σ -> M} (n : M) (φ ψ : MvPolynomial σ R)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `coeff_weightedHomogeneousComponent` / 定理 `coeff_weightedHomogeneousComponent`

English:
theorem coeff_weightedHomogeneousComponent
  given: [DecidableEq M] (d : σ ->₀ Nat)
  proof: by
  simp [weightedHomogeneousComponent, MvPolynomial, coeff, Finsupp.filter_apply]

中文:
定理 coeff_weightedHomogeneousComponent
  条件: [DecidableEq M] (d : σ ->₀ 自然数)
  证明: by
  simp [weightedHomogeneousComponent, MvPolynomial, coeff, Finsupp.filter_apply]

Depends on / 依赖: Finsupp, Finsupp.filter_apply, MvPolynomial, filter_apply, weightedHomogeneousComponent
-/
theorem coeff_weightedHomogeneousComponent [DecidableEq M] (d : σ ->₀ Nat) :
    coeff d (weightedHomogeneousComponent w n φ) =
      if weight w d = n then coeff d φ else 0 := by
  simp [weightedHomogeneousComponent, MvPolynomial, coeff, Finsupp.filter_apply]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `weightedHomogeneousComponent_apply` / 定理 `weightedHomogeneousComponent_apply`

English:
theorem weightedHomogeneousComponent_apply
  given: [DecidableEq M]
  proof: by
  simp [weightedHomogeneousComponent, MvPolynomial, coeff, Finsupp.filter_eq_sum, support, monomial]
  congr

中文:
定理 weightedHomogeneousComponent_apply
  条件: [DecidableEq M]
  证明: by
  simp [weightedHomogeneousComponent, MvPolynomial, coeff, Finsupp.filter_eq_sum, support, monomial]
  congr

Depends on / 依赖: Finsupp, Finsupp.filter_eq_sum, MvPolynomial, filter_eq_sum, monomial, support, weightedHomogeneousComponent
-/
theorem weightedHomogeneousComponent_apply [DecidableEq M] :
    weightedHomogeneousComponent w n φ =
      ∑ d in φ.support with weight w d = n, monomial d (coeff d φ) := by
  simp [weightedHomogeneousComponent, MvPolynomial, coeff, Finsupp.filter_eq_sum, support, monomial]
  congr

/--
theorem `weightedHomogeneousComponent_isWeightedHomogeneous` / 定理 `weightedHomogeneousComponent_isWeightedHomogeneous`

English:
theorem weightedHomogeneousComponent_isWeightedHomogeneous
  proof: by
  classical
  intro d hd
  contrapose! hd
  rw [coeff_weightedHomogeneousComponent]; rw [if_neg hd]

中文:
定理 weightedHomogeneousComponent_isWeightedHomogeneous
  证明: by
  classical
  intro d hd
  contrapose! hd
  rw [coeff_weightedHomogeneousComponent]; rw [if_neg hd]

Depends on / 依赖: classical, coeff_weightedHomogeneousComponent, contrapose, if_neg
-/
theorem weightedHomogeneousComponent_isWeightedHomogeneous :
    (weightedHomogeneousComponent w n φ).IsWeightedHomogeneous w n := by
  classical
  intro d hd
  contrapose! hd
  rw [coeff_weightedHomogeneousComponent]; rw [if_neg hd]

/--
theorem `weightedHomogeneousComponent_mem` / 定理 `weightedHomogeneousComponent_mem`

English:
theorem weightedHomogeneousComponent_mem
  given: (w : σ -> M) (φ : MvPolynomial σ R) (m : M)
  proof: by
  rw [mem_weightedHomogeneousSubmodule]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ

@[simp]

中文:
定理 weightedHomogeneousComponent_mem
  条件: (w : σ -> M) (φ : 多元多项式 σ R) (m : M)
  证明: by
  rw [mem_weightedHomogeneousSubmodule]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ

@[simp]

Depends on / 依赖: mem_weightedHomogeneousSubmodule, weightedHomogeneousComponent_isWeightedHomogeneous
-/
theorem weightedHomogeneousComponent_mem (w : σ -> M) (φ : MvPolynomial σ R) (m : M) :
    weightedHomogeneousComponent w m φ in weightedHomogeneousSubmodule R w m := by
  rw [mem_weightedHomogeneousSubmodule]
  exact weightedHomogeneousComponent_isWeightedHomogeneous m φ

@[simp]
/--
theorem `weightedHomogeneousComponent_C_mul` / 定理 `weightedHomogeneousComponent_C_mul`

English:
theorem weightedHomogeneousComponent_C_mul
  given: (n : M) (r : R)
  proof: by
  simp only [C_mul', map_smul]

中文:
定理 weightedHomogeneousComponent_C_mul
  条件: (n : M) (r : R)
  证明: by
  simp only [C_mul', map_smul]

Depends on / 依赖: C_mul, map_smul
-/
theorem weightedHomogeneousComponent_C_mul (n : M) (r : R) :
    weightedHomogeneousComponent w n (C r * φ) = C r * weightedHomogeneousComponent w n φ := by
  simp only [C_mul', map_smul]

/--
theorem `weightedHomogeneousComponent_eq_zero'` / 定理 `weightedHomogeneousComponent_eq_zero'`

English:
theorem weightedHomogeneousComponent_eq_zero'
  proof: by
  classical
  rw [weightedHomogeneousComponent_apply]; rw [sum_eq_zero]
  intro d hd; rw [mem_filter] at hd
  exfalso; exact h _ hd.1 hd.2

中文:
定理 weightedHomogeneousComponent_eq_zero'
  证明: by
  classical
  rw [weightedHomogeneousComponent_apply]; rw [sum_eq_zero]
  intro d hd; rw [mem_filter] at hd
  exfalso; exact h _ hd.1 hd.2

Depends on / 依赖: classical, mem_filter, sum_eq_zero, weightedHomogeneousComponent_apply
-/
theorem weightedHomogeneousComponent_eq_zero'
    (h : forall d : σ ->₀ Nat, d in φ.support -> weight w d != n) :
    weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply]; rw [sum_eq_zero]
  intro d hd; rw [mem_filter] at hd
  exfalso; exact h _ hd.1 hd.2

/--
theorem `weightedHomogeneousComponent_eq_zero` / 定理 `weightedHomogeneousComponent_eq_zero`

English:
theorem weightedHomogeneousComponent_eq_zero
  statement: [SemilatticeSup M] [OrderBot M]
  proof: by
  classical
  rw [weightedHomogeneousComponent_apply]; rw [sum_eq_zero]
  intro d hd
  rw [Finset.mem_filter] at hd
  exfalso
  apply lt_irrefl n
  nth_rw 1 [← hd.2]
  exact lt_of_le_of_lt (le_weightedTotalDegree w hd.1) h

中文:
定理 weightedHomogeneousComponent_eq_zero
  结论: [SemilatticeSup M] [有底序 M]
  证明: by
  classical
  rw [weightedHomogeneousComponent_apply]; rw [sum_eq_zero]
  intro d hd
  rw [Finset.mem_filter] at hd
  exfalso
  apply lt_irrefl n
  nth_rw 1 [← hd.2]
  exact lt_of_le_of_lt (le_weightedTotalDegree w hd.1) h

Depends on / 依赖: Finset, Finset.mem_filter, classical, le_weightedTotalDegree, lt_irrefl, lt_of_le_of_lt, mem_filter, nth_rw, sum_eq_zero, weightedHomogeneousComponent_apply
-/
theorem weightedHomogeneousComponent_eq_zero [SemilatticeSup M] [OrderBot M]
    (h : weightedTotalDegree w φ < n) : weightedHomogeneousComponent w n φ = 0 := by
  classical
  rw [weightedHomogeneousComponent_apply]; rw [sum_eq_zero]
  intro d hd
  rw [Finset.mem_filter] at hd
  exfalso
  apply lt_irrefl n
  nth_rw 1 [← hd.2]
  exact lt_of_le_of_lt (le_weightedTotalDegree w hd.1) h

/--
theorem `weightedHomogeneousComponent_finsupp` / 定理 `weightedHomogeneousComponent_finsupp`

English:
theorem weightedHomogeneousComponent_finsupp
  proof: by
  apply ((fun d : σ ->₀ Nat => (weight w) d) '' (φ.support : Set (σ ->₀ Nat))).toFinite.subset
  intro m hm
  by_contra hm'
  apply hm (weightedHomogeneousComponent_eq_zero' m φ _)
  simpa only [Set.mem_image, not_exists, not_and] using! hm'

中文:
定理 weightedHomogeneousComponent_finsupp
  证明: by
  apply ((fun d : σ ->₀ Nat => (weight w) d) '' (φ.support : Set (σ ->₀ Nat))).toFinite.subset
  intro m hm
  by_contra hm'
  apply hm (weightedHomogeneousComponent_eq_zero' m φ _)
  simpa only [Set.mem_image, not_exists, not_and] using! hm'

Depends on / 依赖: Set.mem_image, mem_image, not_and, not_exists, subset, support, toFinite, toFinite.subset, weight, weightedHomogeneousComponent_eq_zero
-/
theorem weightedHomogeneousComponent_finsupp :
    (fun m => weightedHomogeneousComponent w m φ).HasFiniteSupport := by
  apply ((fun d : σ ->₀ Nat => (weight w) d) '' (φ.support : Set (σ ->₀ Nat))).toFinite.subset
  intro m hm
  by_contra hm'
  apply hm (weightedHomogeneousComponent_eq_zero' m φ _)
  simpa only [Set.mem_image, not_exists, not_and] using! hm'

variable (w)

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `sum_weightedHomogeneousComponent` / 定理 `sum_weightedHomogeneousComponent`

English:
theorem sum_weightedHomogeneousComponent
  proof: by
  classical
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
  ext1 d
  simp only [coeff_sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (weight w d)]
  · rw [if_pos rfl]
  · intro m _ hm'
    rw [if_neg hm'.symm]
  · intro hm
    rw [if_pos rfl]
    simp only [

中文:
定理 sum_weightedHomogeneousComponent
  证明: by
  classical
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
  ext1 d
  simp only [coeff_sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (weight w d)]
  · rw [if_pos rfl]
  · intro m _ hm'
    rw [if_neg hm'.symm]
  · intro hm
    rw [if_pos rfl]
    simp only [

Depends on / 依赖: Classical, Classical.not_not, Finite, Finite.mem_toFinset, Finset, Finset.sum_eq_single, classical, coeff_sum, coeff_weightedHomogeneousComponent, coeff_zero, finsum_eq_sum, if_neg, if_pos, mem_support, mem_toFinset, not_not, sum_eq_single, this.symm, weight, weightedHomogeneousComponent_finsupp
-/
theorem sum_weightedHomogeneousComponent :
    (finsum fun m => weightedHomogeneousComponent w m φ) = φ := by
  classical
  rw [finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
  ext1 d
  simp only [coeff_sum, coeff_weightedHomogeneousComponent]
  rw [Finset.sum_eq_single (weight w d)]
  · rw [if_pos rfl]
  · intro m _ hm'
    rw [if_neg hm'.symm]
  · intro hm
    rw [if_pos rfl]
    simp only [Finite.mem_toFinset, mem_support, Ne, Classical.not_not] at hm
    have := coeff_weightedHomogeneousComponent (w := w) (weight w d) φ d
    rw [hm]; rw [if_pos rfl]; rw [coeff_zero] at this
    exact this.symm

/--
theorem `finsum_weightedHomogeneousComponent` / 定理 `finsum_weightedHomogeneousComponent`

English:
theorem finsum_weightedHomogeneousComponent
  proof: by
  rw [sum_weightedHomogeneousComponent]

中文:
定理 finsum_weightedHomogeneousComponent
  证明: by
  rw [sum_weightedHomogeneousComponent]

Depends on / 依赖: sum_weightedHomogeneousComponent
-/
theorem finsum_weightedHomogeneousComponent :
    (finsum fun m => weightedHomogeneousComponent w m φ) = φ := by
  rw [sum_weightedHomogeneousComponent]

variable {w}

/--
theorem `IsWeightedHomogeneous.weightedHomogeneousComponent_same` / 定理 `IsWeightedHomogeneous.weightedHomogeneousComponent_same`

English:
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_same
  statement: {m : M} {p : MvPolynomial σ R}
  proof: by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    · rfl
    rw [zero_coeff]
  · rw [hp zero_coeff, if_pos rfl]

中文:
定理 IsWeightedHomogeneous.weightedHomogeneousComponent_same
  结论: {m : M} {p : 多元多项式 σ R}
  证明: by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    · rfl
    rw [zero_coeff]
  · rw [hp zero_coeff, if_pos rfl]

Depends on / 依赖: classical, coeff_weightedHomogeneousComponent, if_pos, split_ifs, zero_coeff
-/
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_same {m : M} {p : MvPolynomial σ R}
    (hp : IsWeightedHomogeneous w p m) :
    weightedHomogeneousComponent w m p = p := by
  classical
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs
    · rfl
    rw [zero_coeff]
  · rw [hp zero_coeff, if_pos rfl]

/--
theorem `IsWeightedHomogeneous.weightedHomogeneousComponent_ne` / 定理 `IsWeightedHomogeneous.weightedHomogeneousComponent_ne`

English:
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_ne
  statement: {m : M} (n : M)
  proof: by
  classical
  intro hn
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · simp [zero_coeff]
  · rw [if_neg]
    · rw [coeff_zero]
    · rw [hp zero_coeff]; exact Ne.symm hn

中文:
定理 IsWeightedHomogeneous.weightedHomogeneousComponent_ne
  结论: {m : M} (n : M)
  证明: by
  classical
  intro hn
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · simp [zero_coeff]
  · rw [if_neg]
    · rw [coeff_zero]
    · rw [hp zero_coeff]; exact Ne.symm hn

Depends on / 依赖: Ne.symm, classical, coeff_weightedHomogeneousComponent, coeff_zero, if_neg, zero_coeff
-/
theorem IsWeightedHomogeneous.weightedHomogeneousComponent_ne {m : M} (n : M)
    {p : MvPolynomial σ R} (hp : IsWeightedHomogeneous w p m) :
    n != m -> weightedHomogeneousComponent w n p = 0 := by
  classical
  intro hn
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · simp [zero_coeff]
  · rw [if_neg]
    · rw [coeff_zero]
    · rw [hp zero_coeff]; exact Ne.symm hn

/--
theorem `weightedHomogeneousComponent_of_mem` / 定理 `weightedHomogeneousComponent_of_mem`

English:
theorem weightedHomogeneousComponent_of_mem
  statement: [DecidableEq M] {m n : M}
  proof: by
  simp only [mem_weightedHomogeneousSubmodule] at h
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs <;>
    simp only [zero_coeff, coeff_zero]
  · rw [h zero_coeff]
    simp only [show n = m ↔ m = n from eq_comm]
    split_ifs with h1
    · rf

中文:
定理 weightedHomogeneousComponent_of_mem
  结论: [DecidableEq M] {m n : M}
  证明: by
  simp only [mem_weightedHomogeneousSubmodule] at h
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs <;>
    simp only [zero_coeff, coeff_zero]
  · rw [h zero_coeff]
    simp only [show n = m ↔ m = n from eq_comm]
    split_ifs with h1
    · rf

Depends on / 依赖: coeff_weightedHomogeneousComponent, coeff_zero, eq_comm, mem_weightedHomogeneousSubmodule, split_ifs, zero_coeff
-/
theorem weightedHomogeneousComponent_of_mem [DecidableEq M] {m n : M}
    {p : MvPolynomial σ R} (h : p in weightedHomogeneousSubmodule R w n) :
    weightedHomogeneousComponent w m p = if m = n then p else 0 := by
  simp only [mem_weightedHomogeneousSubmodule] at h
  ext x
  rw [coeff_weightedHomogeneousComponent]
  by_cases zero_coeff : coeff x p = 0
  · split_ifs <;>
    simp only [zero_coeff, coeff_zero]
  · rw [h zero_coeff]
    simp only [show n = m ↔ m = n from eq_comm]
    split_ifs with h1
    · rfl
    · simp only [coeff_zero]

/--
lemma `weightedHomogeneousComponent_eq_self` / 引理 `weightedHomogeneousComponent_eq_self`

English:
lemma weightedHomogeneousComponent_eq_self
  statement: {n : M} {p : MvPolynomial σ R}
  proof: by
  classical simp [weightedHomogeneousComponent_of_mem hp]

中文:
引理 weightedHomogeneousComponent_eq_self
  结论: {n : M} {p : 多元多项式 σ R}
  证明: by
  classical simp [weightedHomogeneousComponent_of_mem hp]

Depends on / 依赖: classical, weightedHomogeneousComponent_of_mem
-/
lemma weightedHomogeneousComponent_eq_self {n : M} {p : MvPolynomial σ R}
    (hp : p.IsWeightedHomogeneous w n) : weightedHomogeneousComponent w n p = p := by
  classical simp [weightedHomogeneousComponent_of_mem hp]

/--
lemma `support_weightedHomogeneousComponent` / 引理 `support_weightedHomogeneousComponent`

English:
lemma support_weightedHomogeneousComponent
  given: [DecidableEq M] (n : M) (p : MvPolynomial σ R)
  proof: by
  ext c
  simp [coeff_weightedHomogeneousComponent, And.comm]

中文:
引理 support_weightedHomogeneousComponent
  条件: [DecidableEq M] (n : M) (p : 多元多项式 σ R)
  证明: by
  ext c
  simp [coeff_weightedHomogeneousComponent, And.comm]

Depends on / 依赖: And.comm, coeff_weightedHomogeneousComponent
-/
lemma support_weightedHomogeneousComponent [DecidableEq M] (n : M) (p : MvPolynomial σ R) :
    (weightedHomogeneousComponent w n p).support = {c in p.support | (weight w) c = n} := by
  ext c
  simp [coeff_weightedHomogeneousComponent, And.comm]

variable (R w)

open DirectSum

/--
theorem `DirectSum.coeLinearMap_eq_dfinsuppSum` / 定理 `DirectSum.coeLinearMap_eq_dfinsuppSum`

English:
theorem DirectSum.coeLinearMap_eq_dfinsuppSum
  statement: [DecidableEq σ] [DecidableEq R] [DecidableEq M]
  proof: by
  rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum]

中文:
定理 直和.coeLinearMap_eq_dfinsuppSum
  结论: [DecidableEq σ] [DecidableEq R] [DecidableEq M]
  证明: by
  rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum]
-/
theorem DirectSum.coeLinearMap_eq_dfinsuppSum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) := by
  rw [_root_.DirectSum.coeLinearMap_eq_dfinsuppSum]

/--
theorem `DirectSum.coeAddMonoidHom_eq_support_sum` / 定理 `DirectSum.coeAddMonoidHom_eq_support_sum`

English:
theorem DirectSum.coeAddMonoidHom_eq_support_sum
  statement: [DecidableEq σ] [DecidableEq R] [DecidableEq M]
  proof: DirectSum.coeLinearMap_eq_dfinsuppSum R w x

中文:
定理 直和.coeAddMonoidHom_eq_support_sum
  结论: [DecidableEq σ] [DecidableEq R] [DecidableEq M]
  证明: DirectSum.coeLinearMap_eq_dfinsuppSum R w x

Depends on / 依赖: DirectSum, DirectSum.coeLinearMap_eq_dfinsuppSum, coeLinearMap_eq_dfinsuppSum
-/
theorem DirectSum.coeAddMonoidHom_eq_support_sum [DecidableEq σ] [DecidableEq R] [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeAddMonoidHom fun i : M => weightedHomogeneousSubmodule R w i) x =
      DFinsupp.sum x (fun _ x => ↑x) :=
  DirectSum.coeLinearMap_eq_dfinsuppSum R w x

set_option backward.isDefEq.respectTransparency false in
/--
theorem `DirectSum.coeLinearMap_eq_finsum` / 定理 `DirectSum.coeLinearMap_eq_finsum`

English:
theorem DirectSum.coeLinearMap_eq_finsum
  statement: [DecidableEq M]
  proof: by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum]; rw [DFinsupp.sum]; rw [finsum_eq_sum_of_support_subset]
  apply DirectSum.support_subset

中文:
定理 直和.coeLinearMap_eq_finsum
  结论: [DecidableEq M]
  证明: by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum]; rw [DFinsupp.sum]; rw [finsum_eq_sum_of_support_subset]
  apply DirectSum.support_subset

Depends on / 依赖: DFinsupp, DFinsupp.sum, DirectSum, DirectSum.coeLinearMap_eq_dfinsuppSum, DirectSum.support_subset, classical, coeLinearMap_eq_dfinsuppSum, finsum_eq_sum_of_support_subset, support_subset
-/
theorem DirectSum.coeLinearMap_eq_finsum [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) :
    (DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x =
      finsum fun m => x m := by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum]; rw [DFinsupp.sum]; rw [finsum_eq_sum_of_support_subset]
  apply DirectSum.support_subset

set_option backward.isDefEq.respectTransparency false in
/--
theorem `weightedHomogeneousComponent_directSum` / 定理 `weightedHomogeneousComponent_directSum`

English:
theorem weightedHomogeneousComponent_directSum
  statement: [DecidableEq M]
  proof: by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum]; rw [DFinsupp.sum]; rw [map_sum]
  convert! @Finset.sum_eq_single M (MvPolynomial σ R) _ (DFinsupp.support x) _ m _ _
  · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same (x m).prop]
  · intro n _ hmn
    exact IsWeightedHomogene

中文:
定理 weightedHomogeneousComponent_directSum
  结论: [DecidableEq M]
  证明: by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum]; rw [DFinsupp.sum]; rw [map_sum]
  convert! @Finset.sum_eq_single M (MvPolynomial σ R) _ (DFinsupp.support x) _ m _ _
  · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same (x m).prop]
  · intro n _ hmn
    exact IsWeightedHomogene

Depends on / 依赖: DFinsupp, DFinsupp.notMem_support_iff, DFinsupp.sum, DFinsupp.support, DirectSum, DirectSum.coeLinearMap_eq_dfinsuppSum, Finset, Finset.sum_eq_single, IsWeightedHomogeneous, IsWeightedHomogeneous.weightedHomogeneousComponent_ne, IsWeightedHomogeneous.weightedHomogeneousComponent_same, MvPolynomial, Submodule, Submodule.coe_zero, classical, coeLinearMap_eq_dfinsuppSum, coe_zero, convert, hmn.symm, map_sum
-/
theorem weightedHomogeneousComponent_directSum [DecidableEq M]
    (x : DirectSum M fun i : M => ↥(weightedHomogeneousSubmodule R w i)) (m : M) :
    (weightedHomogeneousComponent w m)
      ((DirectSum.coeLinearMap fun i : M => weightedHomogeneousSubmodule R w i) x) = x m := by
  classical
  rw [DirectSum.coeLinearMap_eq_dfinsuppSum]; rw [DFinsupp.sum]; rw [map_sum]
  convert! @Finset.sum_eq_single M (MvPolynomial σ R) _ (DFinsupp.support x) _ m _ _
  · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same (x m).prop]
  · intro n _ hmn
    exact IsWeightedHomogeneous.weightedHomogeneousComponent_ne m (x n).prop hmn.symm
  · rw [DFinsupp.notMem_support_iff]
    intro hm; rw [hm, Submodule.coe_zero, map_zero]

end WeightedHomogeneousComponent

end AddCommMonoid

section OrderedAddCommMonoid

variable [AddCommMonoid M] [PartialOrder M]
  {w : σ -> M} (φ : MvPolynomial σ R)

/-- If `M` is canonically ordered, then the `weightedHomogeneousComponent` of weighted degree `0`
of a polynomial is its constant coefficient. -/
@[simp]
/--
theorem `weightedHomogeneousComponent_zero` / 定理 `weightedHomogeneousComponent_zero`

English:
theorem weightedHomogeneousComponent_zero
  statement: [CanonicallyOrderedAdd M] [IsAddTorsionFree M]
  proof: by
  classical
  ext1 d
  rcases Classical.em (d = 0) with (rfl | hd)
  · simp only [coeff_weightedHomogeneousComponent, if_pos, map_zero, coeff_zero_C]
  · rw [coeff_weightedHomogeneousComponent, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [weight, LinearMap.toAddMonoidHom_coe, Finsupp.line

中文:
定理 weightedHomogeneousComponent_zero
  结论: [典范有序加法 M] [是加法无挠 M]
  证明: by
  classical
  ext1 d
  rcases Classical.em (d = 0) with (rfl | hd)
  · simp only [coeff_weightedHomogeneousComponent, if_pos, map_zero, coeff_zero_C]
  · rw [coeff_weightedHomogeneousComponent, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [weight, LinearMap.toAddMonoidHom_coe, Finsupp.line

Depends on / 依赖: Classical, Classical.em, DFunLike, DFunLike.ext_iff, Finsupp, Finsupp.coe_zero, Finsupp.linearCombination_apply, Finsupp.mem_support_iff, Finsupp.sum, LinearMap, LinearMap.toAddMonoidHom_coe, Ne.symm, Pi.zero_apply, and_self_left, classical, coe_zero, coeff_C, coeff_weightedHomogeneousComponent, coeff_zero_C, exists_prop
-/
theorem weightedHomogeneousComponent_zero [CanonicallyOrderedAdd M] [IsAddTorsionFree M]
    (hw : forall i : σ, w i != 0) :
    weightedHomogeneousComponent w 0 φ = C (coeff 0 φ) := by
  classical
  ext1 d
  rcases Classical.em (d = 0) with (rfl | hd)
  · simp only [coeff_weightedHomogeneousComponent, if_pos, map_zero, coeff_zero_C]
  · rw [coeff_weightedHomogeneousComponent, if_neg, coeff_C, if_neg (Ne.symm hd)]
    simp only [weight, LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply, Finsupp.sum,
      sum_eq_zero_iff, Finsupp.mem_support_iff, Ne, smul_eq_zero, not_forall, not_or,
      and_self_left, exists_prop]
    simp only [DFunLike.ext_iff, Finsupp.coe_zero, Pi.zero_apply, not_forall] at hd
    obtain ⟨i, hi⟩ := hd
    exact ⟨i, hi, hw i⟩

/--
Definition of `NonTorsionWeight` / `NonTorsionWeight` 的定义

English:
definition NonTorsionWeight
  signature: (w : σ -> M)
  body: forall n x, n • w x = (0 : M) -> n = 0

omit [PartialOrder M] in

中文:
定义 NonTorsionWeight
  签名: (w : σ -> M)
  定义体: forall n x, n • w x = (0 : M) -> n = 0

omit [PartialOrder M] in
-/
def NonTorsionWeight (w : σ -> M) :=
  forall n x, n • w x = (0 : M) -> n = 0

omit [PartialOrder M] in
/--
theorem `nonTorsionWeight_of` / 定理 `nonTorsionWeight_of`

English:
theorem nonTorsionWeight_of
  given: [IsAddTorsionFree M] (hw : forall i : σ, w i != 0)
  proof: fun _ x hnx => (smul_eq_zero_iff_left (hw x)).mp hnx

中文:
定理 nonTorsionWeight_of
  条件: [是加法无挠 M] (hw : 对任意 i : σ, w i != 0)
  证明: fun _ x hnx => (smul_eq_zero_iff_left (hw x)).mp hnx

Depends on / 依赖: smul_eq_zero_iff_left
-/
theorem nonTorsionWeight_of [IsAddTorsionFree M] (hw : forall i : σ, w i != 0) :
    NonTorsionWeight w :=
  fun _ x hnx => (smul_eq_zero_iff_left (hw x)).mp hnx

/--
theorem `weightedDegree_eq_zero_iff` / 定理 `weightedDegree_eq_zero_iff`

English:
theorem weightedDegree_eq_zero_iff
  statement: [CanonicallyOrderedAdd M]
  proof: by
  simp only [weight, Finsupp.linearCombination, LinearMap.toAddMonoidHom_coe, coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  rw [Finsupp.sum]; rw [Finset.sum_eq_zero_iff]
  apply forall_congr'
  intro x
  rw [Finsupp.mem_support_iff]
  constructor
  · intro hx
    by_contra hx'

中文:
定理 weightedDegree_eq_zero_iff
  结论: [典范有序加法 M]
  证明: by
  simp only [weight, Finsupp.linearCombination, LinearMap.toAddMonoidHom_coe, coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  rw [Finsupp.sum]; rw [Finset.sum_eq_zero_iff]
  apply forall_congr'
  intro x
  rw [Finsupp.mem_support_iff]
  constructor
  · intro hx
    by_contra hx'

Depends on / 依赖: Finset, Finset.sum_eq_zero_iff, Finsupp, Finsupp.linearCombination, Finsupp.mem_support_iff, Finsupp.sum, LinearMap, LinearMap.coe_smulRight, LinearMap.id_coe, LinearMap.toAddMonoidHom_coe, absurd, coe_lsum, coe_smulRight, forall_congr, id_coe, id_eq, linearCombination, mem_support_iff, sum_eq_zero_iff, toAddMonoidHom_coe
-/
theorem weightedDegree_eq_zero_iff [CanonicallyOrderedAdd M]
    (hw : NonTorsionWeight w) {m : σ ->₀ Nat} :
    weight w m = 0 ↔ forall x : σ, m x = 0 := by
  simp only [weight, Finsupp.linearCombination, LinearMap.toAddMonoidHom_coe, coe_lsum,
    LinearMap.coe_smulRight, LinearMap.id_coe, id_eq]
  rw [Finsupp.sum]; rw [Finset.sum_eq_zero_iff]
  apply forall_congr'
  intro x
  rw [Finsupp.mem_support_iff]
  constructor
  · intro hx
    by_contra hx'
    exact absurd (hw _ _ (hx hx')) hx'
  · order

end OrderedAddCommMonoid

section LinearOrderedAddCommMonoid

variable [AddCommMonoid M] [LinearOrder M] [OrderBot M] [CanonicallyOrderedAdd M]
  {w : σ -> M} (φ : MvPolynomial σ R)

/--
theorem `isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero` / 定理 `isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero`

English:
theorem isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero
  given: {p : MvPolynomial σ R}
  proof: by
  rw [weightedTotalDegree]; rw [← bot_eq_zero]; rw [Finset.sup_eq_bot_iff]; rw [bot_eq_zero]; rw [IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]

中文:
定理 isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero
  条件: {p : 多元多项式 σ R}
  证明: by
  rw [weightedTotalDegree]; rw [← bot_eq_zero]; rw [Finset.sup_eq_bot_iff]; rw [bot_eq_zero]; rw [IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]

Depends on / 依赖: Finset, Finset.sup_eq_bot_iff, IsWeightedHomogeneous, bot_eq_zero, forall_congr, mem_support_iff, sup_eq_bot_iff, weightedTotalDegree
-/
theorem isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero {p : MvPolynomial σ R} :
    IsWeightedHomogeneous w p 0 ↔ p.weightedTotalDegree w = 0 := by
  rw [weightedTotalDegree]; rw [← bot_eq_zero]; rw [Finset.sup_eq_bot_iff]; rw [bot_eq_zero]; rw [IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]

/--
theorem `weightedTotalDegree_eq_zero_iff` / 定理 `weightedTotalDegree_eq_zero_iff`

English:
theorem weightedTotalDegree_eq_zero_iff
  given: (hw : NonTorsionWeight w) (p : MvPolynomial σ R)
  proof: by
  rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero]; rw [IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]
  apply forall_congr'
  intro _
  exact weightedDegree_eq_zero_iff hw

中文:
定理 weightedTotalDegree_eq_zero_iff
  条件: (hw : NonTorsionWeight w) (p : 多元多项式 σ R)
  证明: by
  rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero]; rw [IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]
  apply forall_congr'
  intro _
  exact weightedDegree_eq_zero_iff hw

Depends on / 依赖: IsWeightedHomogeneous, forall_congr, isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero, mem_support_iff, weightedDegree_eq_zero_iff
-/
theorem weightedTotalDegree_eq_zero_iff (hw : NonTorsionWeight w) (p : MvPolynomial σ R) :
    p.weightedTotalDegree w = 0 ↔ forall (m : σ ->₀ Nat) (_ : m in p.support) (x : σ), m x = 0 := by
  rw [← isWeightedHomogeneous_zero_iff_weightedTotalDegree_eq_zero]; rw [IsWeightedHomogeneous]
  apply forall_congr'
  intro m
  rw [mem_support_iff]
  apply forall_congr'
  intro _
  exact weightedDegree_eq_zero_iff hw

end LinearOrderedAddCommMonoid

section GradedAlgebra

/- Here, given a weight `w : σ → M`, where `M` is an additive and commutative monoid, we endow the
  ring of multivariate polynomials `MvPolynomial σ R` with the structure of a graded algebra -/
variable (w : σ -> M) [AddCommMonoid M]

/--
theorem `weightedHomogeneousComponent_eq_zero_of_notMem` / 定理 `weightedHomogeneousComponent_eq_zero_of_notMem`

English:
theorem weightedHomogeneousComponent_eq_zero_of_notMem
  statement: [DecidableEq M]
  proof: by
  apply weightedHomogeneousComponent_eq_zero'
  simp only [Finset.mem_image, mem_support_iff, ne_eq, not_exists, not_and] at hi
  exact fun m hm => hi m (mem_support_iff.mp hm)

中文:
定理 weightedHomogeneousComponent_eq_zero_of_notMem
  结论: [DecidableEq M]
  证明: by
  apply weightedHomogeneousComponent_eq_zero'
  simp only [Finset.mem_image, mem_support_iff, ne_eq, not_exists, not_and] at hi
  exact fun m hm => hi m (mem_support_iff.mp hm)

Depends on / 依赖: Finset, Finset.mem_image, mem_image, mem_support_iff, mem_support_iff.mp, ne_eq, not_and, not_exists, weightedHomogeneousComponent_eq_zero
-/
theorem weightedHomogeneousComponent_eq_zero_of_notMem [DecidableEq M]
    (φ : MvPolynomial σ R) (i : M) (hi : i ∉ Finset.image (weight w) φ.support) :
    weightedHomogeneousComponent w i φ = 0 := by
  apply weightedHomogeneousComponent_eq_zero'
  simp only [Finset.mem_image, mem_support_iff, ne_eq, not_exists, not_and] at hi
  exact fun m hm => hi m (mem_support_iff.mp hm)

variable (R)

/--
Definition of `decompose'` / `decompose'` 的定义

English:
definition decompose'
  signature: [DecidableEq M]
  body: fun φ : MvPolynomial σ R =>
  DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
    (Finset.image (weight w) φ.support) fun m =>
      ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩

中文:
定义 decompose'
  签名: [DecidableEq M]
  定义体: fun φ : MvPolynomial σ R =>
  DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
    (Finset.image (weight w) φ.support) fun m =>
      ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩

Depends on / 依赖: MvPolynomial
-/
def decompose' [DecidableEq M] := fun φ : MvPolynomial σ R =>
  DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
    (Finset.image (weight w) φ.support) fun m =>
      ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩

/--
theorem `decompose'_apply` / 定理 `decompose'_apply`

English:
theorem decompose'_apply
  given: [DecidableEq M] (φ : MvPolynomial σ R) (m : M)
  proof: by
  rw [decompose']
  by_cases hm : m in Finset.image (weight w) φ.support
  · simp only [DirectSum.mk_apply_of_mem hm, Subtype.coe_mk]
  · rw [DirectSum.mk_apply_of_notMem hm, Submodule.coe_zero,
      weightedHomogeneousComponent_eq_zero_of_notMem w φ m hm]

中文:
定理 decompose'_apply
  条件: [DecidableEq M] (φ : 多元多项式 σ R) (m : M)
  证明: by
  rw [decompose']
  by_cases hm : m in Finset.image (weight w) φ.support
  · simp only [DirectSum.mk_apply_of_mem hm, Subtype.coe_mk]
  · rw [DirectSum.mk_apply_of_notMem hm, Submodule.coe_zero,
      weightedHomogeneousComponent_eq_zero_of_notMem w φ m hm]
-/
theorem decompose'_apply [DecidableEq M] (φ : MvPolynomial σ R) (m : M) :
    (decompose' R w φ m : MvPolynomial σ R) = weightedHomogeneousComponent w m φ := by
  rw [decompose']
  by_cases hm : m in Finset.image (weight w) φ.support
  · simp only [DirectSum.mk_apply_of_mem hm, Subtype.coe_mk]
  · rw [DirectSum.mk_apply_of_notMem hm, Submodule.coe_zero,
      weightedHomogeneousComponent_eq_zero_of_notMem w φ m hm]

set_option backward.isDefEq.respectTransparency false in
/-- Given a weight `w`, the decomposition of `MvPolynomial σ R` into weighted homogeneous
submodules -/
@[instance_reducible]
/--
Definition of `weightedDecomposition` / `weightedDecomposition` 的定义

English:
definition weightedDecomposition
  signature: [DecidableEq M]
  body: decompose' R w
  left_inv φ := by
    classical
    conv_rhs => rw [← sum_weightedHomogeneousComponent w φ]
    rw [← DirectSum.sum_support_of (decompose' R w φ)]
    simp only [DirectSum.coeAddMonoidHom_of, map_sum,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
    apply Finset.su

中文:
定义 weightedDecomposition
  签名: [DecidableEq M]
  定义体: decompose' R w
  left_inv φ := by
    classical
    conv_rhs => rw [← sum_weightedHomogeneousComponent w φ]
    rw [← DirectSum.sum_support_of (decompose' R w φ)]
    simp only [DirectSum.coeAddMonoidHom_of, map_sum,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
    apply Finset.su

Depends on / 依赖: decompose
-/
def weightedDecomposition [DecidableEq M] :
    DirectSum.Decomposition (weightedHomogeneousSubmodule R w) where
  decompose' := decompose' R w
  left_inv φ := by
    classical
    conv_rhs => rw [← sum_weightedHomogeneousComponent w φ]
    rw [← DirectSum.sum_support_of (decompose' R w φ)]
    simp only [DirectSum.coeAddMonoidHom_of, map_sum,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp φ)]
    apply Finset.sum_congr _ (fun m _ => by rw [decompose'_apply])
    ext m
    simp only [DFinsupp.mem_support_toFun, ne_eq, Set.Finite.mem_toFinset, Function.mem_support,
      not_iff_not]
    conv_lhs => rw [← Subtype.coe_inj]
    rw [decompose'_apply]; rw [Submodule.coe_zero]
  right_inv x := by
    apply DFinsupp.ext
    intro m
    rw [← Subtype.coe_inj]; rw [decompose'_apply]
    exact weightedHomogeneousComponent_directSum R w x m


set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given a weight, `MvPolynomial` as a graded algebra -/
@[instance_reducible]
/--
Definition of `weightedGradedAlgebra` / `weightedGradedAlgebra` 的定义

English:
definition weightedGradedAlgebra
  signature: [DecidableEq M]
  body: weightedDecomposition R w
  toGradedMonoid := WeightedHomogeneousSubmodule.gradedMonoid

中文:
定义 weightedGradedAlgebra
  签名: [DecidableEq M]
  定义体: weightedDecomposition R w
  toGradedMonoid := WeightedHomogeneousSubmodule.gradedMonoid

Depends on / 依赖: weightedDecomposition
-/
def weightedGradedAlgebra [DecidableEq M] :
    GradedAlgebra (weightedHomogeneousSubmodule R w) where
  toDecomposition := weightedDecomposition R w
  toGradedMonoid := WeightedHomogeneousSubmodule.gradedMonoid

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `weightedDecomposition.decompose'_eq` / 定理 `weightedDecomposition.decompose'_eq`

English:
theorem weightedDecomposition.decompose'_eq
  given: [DecidableEq M]
  proof: rfl

中文:
定理 weightedDecomposition.decompose'_eq
  条件: [DecidableEq M]
  证明: rfl
-/
theorem weightedDecomposition.decompose'_eq [DecidableEq M] :
    (weightedDecomposition R w).decompose' = fun φ : MvPolynomial σ R =>
      DirectSum.mk (fun i : M => ↥(weightedHomogeneousSubmodule R w i))
        (Finset.image (weight w) φ.support) fun m =>
          ⟨weightedHomogeneousComponent w m φ, weightedHomogeneousComponent_mem w φ m⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `weightedDecomposition.decompose'_apply` / 定理 `weightedDecomposition.decompose'_apply`

English:
theorem weightedDecomposition.decompose'_apply
  statement: [DecidableEq M]
  proof: MvPolynomial.decompose'_apply R w φ m

中文:
定理 weightedDecomposition.decompose'_apply
  结论: [DecidableEq M]
  证明: MvPolynomial.decompose'_apply R w φ m
-/
theorem weightedDecomposition.decompose'_apply [DecidableEq M]
    (φ : MvPolynomial σ R) (m : M) :
    ((weightedDecomposition R w).decompose' φ m : MvPolynomial σ R) =
      weightedHomogeneousComponent w m φ :=
  MvPolynomial.decompose'_apply R w φ m

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/--
lemma `mem_iff_weightedHomogeneousComponent_mem` / 引理 `mem_iff_weightedHomogeneousComponent_mem`

English:
lemma mem_iff_weightedHomogeneousComponent_mem
  statement: [DecidableEq M] {I : Ideal (MvPolynomial σ R)}
  proof: by
  simp_rw [← weightedDecomposition.decompose'_apply]
  exact h.mem_iff

中文:
引理 mem_iff_weightedHomogeneousComponent_mem
  结论: [DecidableEq M] {I : 理想 (多元多项式 σ R)}
  证明: by
  simp_rw [← weightedDecomposition.decompose'_apply]
  exact h.mem_iff

Depends on / 依赖: _apply, decompose, h.mem_iff, mem_iff, simp_rw, weightedDecomposition, weightedDecomposition.decompose
-/
lemma mem_iff_weightedHomogeneousComponent_mem [DecidableEq M] {I : Ideal (MvPolynomial σ R)}
    (h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) (p : MvPolynomial σ R) :
    p in I ↔ forall m : M, (weightedHomogeneousComponent w m p) in I := by
  simp_rw [← weightedDecomposition.decompose'_apply]
  exact h.mem_iff

/--
lemma `weightedHomogeneousComponent_mem_of_mem` / 引理 `weightedHomogeneousComponent_mem_of_mem`

English:
lemma weightedHomogeneousComponent_mem_of_mem
  statement: [DecidableEq M] {I : Ideal (MvPolynomial σ R)}
  proof: (mem_iff_weightedHomogeneousComponent_mem R w h p).mp hp m

中文:
引理 weightedHomogeneousComponent_mem_of_mem
  结论: [DecidableEq M] {I : 理想 (多元多项式 σ R)}
  证明: (mem_iff_weightedHomogeneousComponent_mem R w h p).mp hp m

Depends on / 依赖: mem_iff_weightedHomogeneousComponent_mem
-/
lemma weightedHomogeneousComponent_mem_of_mem [DecidableEq M] {I : Ideal (MvPolynomial σ R)}
    (h : I.IsHomogeneous (weightedHomogeneousSubmodule R w)) {p : MvPolynomial σ R} (hp : p in I)
    (m : M) : (weightedHomogeneousComponent w m p) in I :=
  (mem_iff_weightedHomogeneousComponent_mem R w h p).mp hp m

end GradedAlgebra

end MvPolynomial
