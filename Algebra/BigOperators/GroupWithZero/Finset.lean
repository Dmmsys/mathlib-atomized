/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Set.Lattice

/-!
# Big operators on a finset in groups with zero

This file contains the results concerning the interaction of finset big operators with groups with
zero.
-/

public section

open Function

variable {ι κ G₀ M₀ : Type*} {α : ι -> Type*}

namespace Finset
variable [CommMonoidWithZero M₀] {p : ι -> Prop} [DecidablePred p] {f : ι -> M₀} {s : Finset ι}
  {i : ι}

/--
lemma `prod_eq_zero` / 引理 `prod_eq_zero`

English:
lemma prod_eq_zero
  given: (hi : i in s) (h : f i = 0)
  statement: ∏ j in s, f j = 0
  proof: by
  classical rw [← prod_erase_mul _ _ hi, h, mul_zero]

中文:
引理 prod_eq_zero
  条件: (hi : i in s) (h : f i = 0)
  结论: ∏ j in s, f j = 0
  证明: by
  classical rw [← prod_erase_mul _ _ hi, h, mul_zero]

Depends on / 依赖: classical, mul_zero, prod_erase_mul
-/
lemma prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s, f j = 0 := by
  classical rw [← prod_erase_mul _ _ hi, h, mul_zero]

/--
lemma `prod_ite_zero` / 引理 `prod_ite_zero`

English:
lemma prod_ite_zero
  proof: by
  split_ifs with h
  · exact prod_congr rfl fun i hi => by simp [h i hi]
  · push Not at h
    rcases h with ⟨i, hi, hq⟩
    exact prod_eq_zero hi (by simp [hq])

中文:
引理 prod_ite_zero
  证明: by
  split_ifs with h
  · exact prod_congr rfl fun i hi => by simp [h i hi]
  · push Not at h
    rcases h with ⟨i, hi, hq⟩
    exact prod_eq_zero hi (by simp [hq])

Depends on / 依赖: prod_congr, prod_eq_zero, split_ifs
-/
lemma prod_ite_zero :
    (∏ i in s, if p i then f i else 0) = if forall i in s, p i then ∏ i in s, f i else 0 := by
  split_ifs with h
  · exact prod_congr rfl fun i hi => by simp [h i hi]
  · push Not at h
    rcases h with ⟨i, hi, hq⟩
    exact prod_eq_zero hi (by simp [hq])

/--
lemma `prod_boole` / 引理 `prod_boole`

English:
lemma prod_boole
  statement: ∏ i in s, (ite (p i) 1 0 : M₀) = ite (forall i in s, p i) 1 0
  proof: by
  rw [prod_ite_zero]; rw [prod_const_one]

中文:
引理 prod_boole
  结论: ∏ i in s, (ite (p i) 1 0 : M₀) = ite (对任意 i in s, p i) 1 0
  证明: by
  rw [prod_ite_zero]; rw [prod_const_one]

Depends on / 依赖: prod_const_one, prod_ite_zero
-/
lemma prod_boole : ∏ i in s, (ite (p i) 1 0 : M₀) = ite (forall i in s, p i) 1 0 := by
  rw [prod_ite_zero]; rw [prod_const_one]

/--
lemma `support_prod_subset` / 引理 `support_prod_subset`

English:
lemma support_prod_subset
  given: (s : Finset ι) (f : ι -> κ -> M₀)
  proof: fun _ hx => Set.mem_iInter₂.2 fun _ hi H => hx prod_eq_zero hi H

中文:
引理 support_prod_subset
  条件: (s : 有限集 ι) (f : ι -> κ -> M₀)
  证明: fun _ hx => Set.mem_iInter₂.2 fun _ hi H => hx prod_eq_zero hi H

Depends on / 依赖: Set.mem_iInter, prod_eq_zero
-/
lemma support_prod_subset (s : Finset ι) (f : ι -> κ -> M₀) :
    support (fun x => ∏ i in s, f i x) subseteq ⋂ i in s, support (f i) :=
fun _ hx => Set.mem_iInter₂.2 fun _ hi H => hx prod_eq_zero hi H

/--
lemma `_root_.Set.indicator_pi_one_apply` / 引理 `_root_.Set.indicator_pi_one_apply`

English:
lemma _root_.Set.indicator_pi_one_apply
  given: (s : Finset ι) (t : forall i, Set (α i)) (f : forall i, α i)
  proof: by
  classical simp [Set.indicator, prod_boole]

中文:
引理 _root_.集合.indicator_pi_one_apply
  条件: (s : 有限集 ι) (t : 对任意 i, 集合 (α i)) (f : 对任意 i, α i)
  证明: by
  classical simp [Set.indicator, prod_boole]
-/
@[simp] lemma _root_.Set.indicator_pi_one_apply (s : Finset ι) (t : forall i, Set (α i)) (f : forall i, α i) :
    ((s : Set ι).pi t).indicator 1 f = ∏ i in s, (t i).indicator (M := M₀) 1 (f i) := by
  classical simp [Set.indicator, prod_boole]

variable [Nontrivial M₀] [NoZeroDivisors M₀]

/--
lemma `prod_eq_zero_iff` / 引理 `prod_eq_zero_iff`

English:
lemma prod_eq_zero_iff
  statement: ∏ x in s, f x = 0 ↔ exists a in s, f a = 0
  proof: by
  classical
    induction s using Finset.induction_on with
    | empty => exact ⟨Not.elim one_ne_zero, fun ⟨_, H, _⟩ => by simp at H⟩
    | insert _ _ ha ih => rw [prod_insert ha, mul_eq_zero, exists_mem_insert, ih]

中文:
引理 prod_eq_zero_iff
  结论: ∏ x in s, f x = 0 ↔ 存在 a in s, f a = 0
  证明: by
  classical
    induction s using Finset.induction_on with
    | empty => exact ⟨Not.elim one_ne_zero, fun ⟨_, H, _⟩ => by simp at H⟩
    | insert _ _ ha ih => rw [prod_insert ha, mul_eq_zero, exists_mem_insert, ih]

Depends on / 依赖: Finset, Finset.induction_on, Not.elim, classical, exists_mem_insert, induction_on, insert, mul_eq_zero, one_ne_zero, prod_insert
-/
lemma prod_eq_zero_iff : ∏ x in s, f x = 0 ↔ exists a in s, f a = 0 := by
  classical
    induction s using Finset.induction_on with
    | empty => exact ⟨Not.elim one_ne_zero, fun ⟨_, H, _⟩ => by simp at H⟩
    | insert _ _ ha ih => rw [prod_insert ha, mul_eq_zero, exists_mem_insert, ih]

/--
lemma `prod_ne_zero_iff` / 引理 `prod_ne_zero_iff`

English:
lemma prod_ne_zero_iff
  statement: ∏ x in s, f x != 0 ↔ forall a in s, f a != 0
  proof: by
  rw [Ne]; rw [prod_eq_zero_iff]
  push Not; rfl

中文:
引理 prod_ne_zero_iff
  结论: ∏ x in s, f x != 0 ↔ 对任意 a in s, f a != 0
  证明: by
  rw [Ne]; rw [prod_eq_zero_iff]
  push Not; rfl

Depends on / 依赖: prod_eq_zero_iff
-/
lemma prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall a in s, f a != 0 := by
  rw [Ne]; rw [prod_eq_zero_iff]
  push Not; rfl

/--
lemma `support_prod` / 引理 `support_prod`

English:
lemma support_prod
  given: (s : Finset ι) (f : ι -> κ -> M₀)
  proof: Set.ext fun x => by simp [support, prod_eq_zero_iff]

中文:
引理 support_prod
  条件: (s : 有限集 ι) (f : ι -> κ -> M₀)
  证明: Set.ext fun x => by simp [support, prod_eq_zero_iff]

Depends on / 依赖: Set.ext, prod_eq_zero_iff, support
-/
lemma support_prod (s : Finset ι) (f : ι -> κ -> M₀) :
    support (fun j => ∏ i in s, f i j) = ⋂ i in s, support (f i) :=
  Set.ext fun x => by simp [support, prod_eq_zero_iff]

end Finset

namespace Fintype
variable [Fintype ι] [CommMonoidWithZero M₀] {p : ι -> Prop} [DecidablePred p] {f : ι -> M₀}

/--
lemma `prod_ite_zero` / 引理 `prod_ite_zero`

English:
lemma prod_ite_zero
  statement: (∏ i, if p i then f i else 0) = if forall i, p i then ∏ i, f i else 0
  proof: by
  simp [Finset.prod_ite_zero]

中文:
引理 prod_ite_zero
  结论: (∏ i, if p i then f i else 0) = if 对任意 i, p i then ∏ i, f i else 0
  证明: by
  simp [Finset.prod_ite_zero]

Depends on / 依赖: Finset, Finset.prod_ite_zero, prod_ite_zero
-/
lemma prod_ite_zero : (∏ i, if p i then f i else 0) = if forall i, p i then ∏ i, f i else 0 := by
  simp [Finset.prod_ite_zero]

/--
lemma `prod_boole` / 引理 `prod_boole`

English:
lemma prod_boole
  statement: ∏ i, (ite (p i) 1 0 : M₀) = ite (forall i, p i) 1 0
  proof: by simp [Finset.prod_boole]

中文:
引理 prod_boole
  结论: ∏ i, (ite (p i) 1 0 : M₀) = ite (对任意 i, p i) 1 0
  证明: by simp [Finset.prod_boole]

Depends on / 依赖: Finset, Finset.prod_boole, prod_boole
-/
lemma prod_boole : ∏ i, (ite (p i) 1 0 : M₀) = ite (forall i, p i) 1 0 := by simp [Finset.prod_boole]

end Fintype

set_option backward.isDefEq.respectTransparency false in
/--
lemma `Units.mk0_prod` / 引理 `Units.mk0_prod`

English:
lemma Units.mk0_prod
  given: [CommGroupWithZero G₀] (s : Finset ι) (f : ι -> G₀) (h)
  proof: by
  induction s using Finset.cons_induction_on <;> simp [*]

中文:
引理 单位群.mk0_prod
  条件: [带零交换群 G₀] (s : 有限集 ι) (f : ι -> G₀) (h)
  证明: by
  induction s using Finset.cons_induction_on <;> simp [*]

Depends on / 依赖: Finset, Finset.cons_induction_on, cons_induction_on
-/
lemma Units.mk0_prod [CommGroupWithZero G₀] (s : Finset ι) (f : ι -> G₀) (h) :
    Units.mk0 (∏ i in s, f i) h =
      ∏ i in s.attach, Units.mk0 (f i) fun hh => h (Finset.prod_eq_zero i.2 hh) := by
  induction s using Finset.cons_induction_on <;> simp [*]
