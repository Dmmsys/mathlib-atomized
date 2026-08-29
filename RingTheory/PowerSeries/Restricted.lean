/-
Copyright (c) 2025 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Order.Filter.Cofinite

/-!
# Univariate restricted power series

`IsRestricted` : We say a univariate power series over a normed ring `R` is restricted for a
real number `c` if `‖coeff t f‖ * c i ^ t i → 0` under the cofinite filter.

-/

@[expose] public section
namespace PowerSeries

open Filter
open scoped Topology Pointwise

variable {R : Type*} [NormedRing R] (c : Real) (f : PowerSeries R)

/--
Definition of `IsRestricted` / `IsRestricted` 的定义

English:
abbreviation IsRestricted
  body: MvPowerSeries.IsRestricted (σ := Unit) (fun _ => c) f

中文:
缩写 IsRestricted
  定义体: MvPowerSeries.IsRestricted (σ := Unit) (fun _ => c) f

Depends on / 依赖: ConcreteCategory, ConcreteCategory.ofHom, IsRestricted, MvPowerSeries, MvPowerSeries.IsRestricted, apply_fun, continuous_toFun, fun_prop
-/
abbrev IsRestricted :=
  MvPowerSeries.IsRestricted (σ := Unit) (fun _ => c) f

/--
lemma `isRestricted_comp_uniqueEquiv` / 引理 `isRestricted_comp_uniqueEquiv`

English:
lemma isRestricted_comp_uniqueEquiv
  proof: by
  funext t
  simp only [Function.comp_apply, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit,
    Finsupp.prod_pow, Finset.univ_unique, Finset.prod_singleton, coeff,
    show (Finsupp.single () (t ())) = t by grind]

中文:
引理 isRestricted_comp_uniqueEquiv
  证明: by
  funext t
  simp only [Function.comp_apply, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit,
    Finsupp.prod_pow, Finset.univ_unique, Finset.prod_singleton, coeff,
    show (Finsupp.single () (t ())) = t by grind]
-/
private lemma isRestricted_comp_uniqueEquiv :
    (fun (t : Unit ->₀ Nat) => ‖MvPowerSeries.coeff t f‖ * t.prod (fun _ x => c ^ x)) =
    (fun (n : Nat) => ‖coeff n f‖ * c ^ n) ∘ Finsupp.uniqueEquiv () := by
  funext t
  simp only [Function.comp_apply, Finsupp.uniqueEquiv_apply, PUnit.default_eq_unit,
    Finsupp.prod_pow, Finset.univ_unique, Finset.prod_singleton, coeff,
    show (Finsupp.single () (t ())) = t by grind]

/--
lemma `isRestricted_iff` / 引理 `isRestricted_iff`

English:
lemma isRestricted_iff
  statement: IsRestricted c f ↔
  proof: by
  rw [IsRestricted]; rw [MvPowerSeries.IsRestricted]; rw [isRestricted_comp_uniqueEquiv]
  exact ⟨fun H => (H.comp (Finsupp.uniqueEquiv ()).symm.injective.tendsto_cofinite).congr fun n =>
    by simp, fun H => H.comp (Finsupp.uniqueEquiv ()).injective.tendsto_cofinite⟩

中文:
引理 isRestricted_iff
  结论: IsRestricted c f ↔
  证明: by
  rw [IsRestricted]; rw [MvPowerSeries.IsRestricted]; rw [isRestricted_comp_uniqueEquiv]
  exact ⟨fun H => (H.comp (Finsupp.uniqueEquiv ()).symm.injective.tendsto_cofinite).congr fun n =>
    by simp, fun H => H.comp (Finsupp.uniqueEquiv ()).injective.tendsto_cofinite⟩

Depends on / 依赖: Finsupp, Finsupp.uniqueEquiv, H.comp, IsRestricted, MvPowerSeries, MvPowerSeries.IsRestricted, injective, injective.tendsto_cofinite, isRestricted_comp_uniqueEquiv, symm.injective.tendsto_cofinite, tendsto_cofinite, uniqueEquiv
-/
lemma isRestricted_iff : IsRestricted c f ↔
    Tendsto (fun (t : Nat) => ‖coeff t f‖ * c ^ t) cofinite (𝓝 0) := by
  rw [IsRestricted]; rw [MvPowerSeries.IsRestricted]; rw [isRestricted_comp_uniqueEquiv]
  exact ⟨fun H => (H.comp (Finsupp.uniqueEquiv ()).symm.injective.tendsto_cofinite).congr fun n =>
    by simp, fun H => H.comp (Finsupp.uniqueEquiv ()).injective.tendsto_cofinite⟩

/--
lemma `isRestricted_iff'` / 引理 `isRestricted_iff'`

English:
lemma isRestricted_iff'
  statement: IsRestricted c f ↔
  proof: by
  simp_rw [isRestricted_iff, Nat.cofinite_eq_atTop]

@[simp]

中文:
引理 isRestricted_iff'
  结论: IsRestricted c f ↔
  证明: by
  simp_rw [isRestricted_iff, Nat.cofinite_eq_atTop]

@[simp]

Depends on / 依赖: Nat.cofinite_eq_atTop, Prod.ext, Subtype, Subtype.ext, apply_fun, cofinite_eq_atTop, isRestricted_iff, simp_rw
-/
lemma isRestricted_iff' : IsRestricted c f ↔
    Tendsto (fun (t : Nat) => ‖coeff t f‖ * c ^ t) atTop (𝓝 0) := by
  simp_rw [isRestricted_iff, Nat.cofinite_eq_atTop]

@[simp]
/--
lemma `isRestricted_abs_iff` / 引理 `isRestricted_abs_iff`

English:
lemma isRestricted_abs_iff
  statement: IsRestricted |c| f ↔ IsRestricted c f
  proof: MvPowerSeries.isRestricted_abs_iff (fun _ => c) f

中文:
引理 isRestricted_abs_iff
  结论: IsRestricted |c| f ↔ IsRestricted c f
  证明: MvPowerSeries.isRestricted_abs_iff (fun _ => c) f

Depends on / 依赖: Limits, Limits.PullbackCone.mk, MvPowerSeries, MvPowerSeries.isRestricted_abs_iff, PullbackCone, condition, isRestricted_abs_iff, pullback, pullback.condition, pullback.fst, pullback.snd
-/
lemma isRestricted_abs_iff : IsRestricted |c| f ↔ IsRestricted c f :=
  MvPowerSeries.isRestricted_abs_iff (fun _ => c) f

/--
lemma `isRestricted_zero` / 引理 `isRestricted_zero`

English:
lemma isRestricted_zero
  statement: IsRestricted c (0 : PowerSeries R)
  proof: MvPowerSeries.isRestricted_zero (fun _ => c)

中文:
引理 isRestricted_zero
  结论: IsRestricted c (0 : PowerSeries R)
  证明: MvPowerSeries.isRestricted_zero (fun _ => c)

Depends on / 依赖: Limits, Limits.PullbackCone.isLimitAux, MvPowerSeries, MvPowerSeries.isRestricted_zero, PullbackCone, condition, hom_ext, isLimitAux, isRestricted_zero, lift_fst, lift_snd, pullback, pullback.hom_ext, pullback.lift, pullback.lift_fst, pullback.lift_snd, s.condition, s.fst, s.snd
-/
lemma isRestricted_zero : IsRestricted c (0 : PowerSeries R) :=
 MvPowerSeries.isRestricted_zero (fun _ => c)

/--
lemma `isRestricted_monomial` / 引理 `isRestricted_monomial`

English:
lemma isRestricted_monomial
  given: (n : Nat) (a : R)
  statement: IsRestricted c (monomial n a)
  proof: MvPowerSeries.isRestricted_monomial (fun _ => c) ((Finsupp.single () n)) a

中文:
引理 isRestricted_monomial
  条件: (n : 自然数) (a : R)
  结论: IsRestricted c (monomial n a)
  证明: MvPowerSeries.isRestricted_monomial (fun _ => c) ((Finsupp.single () n)) a

Depends on / 依赖: Finsupp, Finsupp.single, MvPowerSeries, MvPowerSeries.isRestricted_monomial, isRestricted_monomial, single
-/
lemma isRestricted_monomial (n : Nat) (a : R) : IsRestricted c (monomial n a) :=
  MvPowerSeries.isRestricted_monomial (fun _ => c) ((Finsupp.single () n)) a

/--
lemma `isRestricted_one` / 引理 `isRestricted_one`

English:
lemma isRestricted_one
  statement: IsRestricted c (1 : PowerSeries R)
  proof: MvPowerSeries.isRestricted_monomial (fun _ => c) 0 1

中文:
引理 isRestricted_one
  结论: IsRestricted c (1 : PowerSeries R)
  证明: MvPowerSeries.isRestricted_monomial (fun _ => c) 0 1

Depends on / 依赖: MvPowerSeries, MvPowerSeries.isRestricted_monomial, isRestricted_monomial
-/
lemma isRestricted_one : IsRestricted c (1 : PowerSeries R) :=
  MvPowerSeries.isRestricted_monomial (fun _ => c) 0 1

/--
lemma `isRestricted_C` / 引理 `isRestricted_C`

English:
lemma isRestricted_C
  given: (a : R)
  statement: IsRestricted c (C a)
  proof: MvPowerSeries.isRestricted_C (fun _ => c) a

中文:
引理 isRestricted_C
  条件: (a : R)
  结论: IsRestricted c (C a)
  证明: MvPowerSeries.isRestricted_C (fun _ => c) a

Depends on / 依赖: MvPowerSeries, MvPowerSeries.isRestricted_C, isRestricted_C
-/
lemma isRestricted_C (a : R) : IsRestricted c (C a) :=
  MvPowerSeries.isRestricted_C (fun _ => c) a

variable {f} in
/--
lemma `isRestricted.add` / 引理 `isRestricted.add`

English:
lemma isRestricted.add
  given: {g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g)
  proof: MvPowerSeries.isRestricted.add (fun _ => c) hf hg

中文:
引理 isRestricted.add
  条件: {g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g)
  证明: MvPowerSeries.isRestricted.add (fun _ => c) hf hg

Depends on / 依赖: PreservesLimit, compHausLikeToTop, cospan, preservesLimit_of_reflects_of_preserves, toCompHausLike
-/
lemma isRestricted.add {g : PowerSeries R} (hf : IsRestricted c f) (hg : IsRestricted c g) :
    IsRestricted c (f + g) :=
  MvPowerSeries.isRestricted.add (fun _ => c) hf hg

variable {f} in
/--
lemma `isRestricted.neg` / 引理 `isRestricted.neg`

English:
lemma isRestricted.neg
  given: (hf : IsRestricted c f)
  statement: IsRestricted c (-f)
  proof: MvPowerSeries.isRestricted.neg (fun _ => c) hf

中文:
引理 isRestricted.neg
  条件: (hf : IsRestricted c f)
  结论: IsRestricted c (-f)
  证明: MvPowerSeries.isRestricted.neg (fun _ => c) hf
-/
lemma isRestricted.neg (hf : IsRestricted c f) : IsRestricted c (-f) :=
  MvPowerSeries.isRestricted.neg (fun _ => c) hf

/--
lemma `isRestricted.mul` / 引理 `isRestricted.mul`

English:
lemma isRestricted.mul
  statement: [IsUltrametricDist R] (c : Real) {f g : PowerSeries R}
  proof: MvPowerSeries.isRestricted.mul (fun _ => c) hf hg

中文:
引理 isRestricted.mul
  结论: [IsUltrametricDist R] (c : 实数) {f g : PowerSeries R}
  证明: MvPowerSeries.isRestricted.mul (fun _ => c) hf hg
-/
lemma isRestricted.mul [IsUltrametricDist R] (c : Real) {f g : PowerSeries R}
    (hf : IsRestricted c f) (hg : IsRestricted c g) : IsRestricted c (f * g) :=
  MvPowerSeries.isRestricted.mul (fun _ => c) hf hg

namespace IsRestricted

/--
Definition of `addSubgroup` / `addSubgroup` 的定义

English:
definition addSubgroup
  signature: (c : Real)
  body: MvPowerSeries.IsRestricted.addSubgroup (fun _ => c)

中文:
定义 addSubgroup
  签名: (c : 实数)
  定义体: MvPowerSeries.IsRestricted.addSubgroup (fun _ => c)

Depends on / 依赖: IsRestricted, MvPowerSeries, MvPowerSeries.IsRestricted.addSubgroup, addSubgroup
-/
def addSubgroup (c : Real) : AddSubgroup (PowerSeries R) :=
  MvPowerSeries.IsRestricted.addSubgroup (fun _ => c)

variable [IsUltrametricDist R]

/--
Definition of `subring` / `subring` 的定义

English:
definition subring
  signature: (c : Real)
  body: MvPowerSeries.IsRestricted.subring (fun _ => c)

中文:
定义 subring
  签名: (c : 实数)
  定义体: MvPowerSeries.IsRestricted.subring (fun _ => c)

Depends on / 依赖: IsRestricted, MvPowerSeries, MvPowerSeries.IsRestricted.subring, subring
-/
def subring (c : Real) : Subring (PowerSeries R) :=
  MvPowerSeries.IsRestricted.subring (fun _ => c)

end PowerSeries.IsRestricted
