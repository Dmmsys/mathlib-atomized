/-
Copyright (c) 2022 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
module

public import Mathlib.FieldTheory.Minpoly.IsConjRoot

/-!
# Conjugate root classes

In this file, we define the `ConjRootClass` of a field extension `L / K` as the quotient of `L` by
the relation `IsConjRoot K`.
-/

@[expose] public section

variable (K L S : Type*) [Field K] [Field L] [Field S]
variable [Algebra K L] [Algebra K S] [Algebra L S] [IsScalarTower K L S]

/--
Definition of `ConjRootClass` / `ConjRootClass` 的定义

English:
definition ConjRootClass
  body: Quotient (α := L) (IsConjRoot.setoid K L)

中文:
定义 ConjRootClass
  定义体: Quotient (α := L) (IsConjRoot.setoid K L)

Depends on / 依赖: IsConjRoot, IsConjRoot.setoid, Quotient, setoid
-/
def ConjRootClass := Quotient (α := L) (IsConjRoot.setoid K L)

namespace ConjRootClass

variable {L}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (x : L)
  body: ⟦x⟧

@[simp]

中文:
定义 mk
  签名: (x : L)
  定义体: ⟦x⟧

@[simp]
-/
def mk (x : L) : ConjRootClass K L :=
  ⟦x⟧

@[simp]
/--
theorem `mk_def` / 定理 `mk_def`

English:
theorem mk_def
  given: {x : L}
  statement: ⟦x⟧ = mk K x
  proof: rfl

中文:
定理 mk_def
  条件: {x : L}
  结论: ⟦x⟧ = mk K x
  证明: rfl
-/
theorem mk_def {x : L} : ⟦x⟧ = mk K x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (ConjRootClass K L)
  body: ⟨mk K 0⟩

@[elab_as_elim, cases_eliminator, induction_eliminator]

中文:
实例 :
  签名: 零 (ConjRootClass K L)
  定义体: ⟨mk K 0⟩

@[elab_as_elim, cases_eliminator, induction_eliminator]
-/
instance : Zero (ConjRootClass K L) :=
  ⟨mk K 0⟩

@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
lemma `ind` / 引理 `ind`

English:
lemma ind
  statement: {motive : ConjRootClass K L -> Prop} (h : forall x : L, motive (mk K x))
  proof: Quotient.ind h c

中文:
引理 ind
  结论: {motive : ConjRootClass K L -> 命题} (h : 对任意 x : L, motive (mk K x))
  证明: Quotient.ind h c

Depends on / 依赖: Quotient, Quotient.ind
-/
lemma ind {motive : ConjRootClass K L -> Prop} (h : forall x : L, motive (mk K x))
    (c : ConjRootClass K L) : motive c :=
  Quotient.ind h c

variable {K}

@[simp]
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {x y : L}
  statement: mk K x = mk K y ↔ IsConjRoot K x y
  proof: Quotient.eq

@[simp]

中文:
定理 mk_eq_mk
  条件: {x y : L}
  结论: mk K x = mk K y ↔ IsConjRoot K x y
  证明: Quotient.eq

@[simp]

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem mk_eq_mk {x y : L} : mk K x = mk K y ↔ IsConjRoot K x y := Quotient.eq

@[simp]
/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  statement: mk K (0 : L) = 0
  proof: rfl

@[simp]

中文:
定理 mk_zero
  结论: mk K (0 : L) = 0
  证明: rfl

@[simp]
-/
theorem mk_zero : mk K (0 : L) = 0 :=
  rfl

@[simp]
/--
theorem `mk_eq_zero_iff` / 定理 `mk_eq_zero_iff`

English:
theorem mk_eq_zero_iff
  given: (x : L)
  statement: mk K x = 0 ↔ x = 0
  proof: by
  rw [eq_comm (b := 0)]; rw [← mk_zero]; rw [mk_eq_mk]; rw [isConjRoot_zero_iff_eq_zero]

中文:
定理 mk_eq_zero_iff
  条件: (x : L)
  结论: mk K x = 0 ↔ x = 0
  证明: by
  rw [eq_comm (b := 0)]; rw [← mk_zero]; rw [mk_eq_mk]; rw [isConjRoot_zero_iff_eq_zero]

Depends on / 依赖: eq_comm, isConjRoot_zero_iff_eq_zero, mk_eq_mk, mk_zero
-/
theorem mk_eq_zero_iff (x : L) : mk K x = 0 ↔ x = 0 := by
  rw [eq_comm (b := 0)]; rw [← mk_zero]; rw [mk_eq_mk]; rw [isConjRoot_zero_iff_eq_zero]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Normal
  signature: K L] [DecidableEq L] [Fintype Gal(L/K)] : DecidableEq (ConjRootClass K L)
  body: Quotient.decidableEq (d := IsConjRoot.decidable)

中文:
实例 [正规
  签名: K L] [DecidableEq L] [有限类型 Gal(L/K)] : DecidableEq (ConjRootClass K L)
  定义体: Quotient.decidableEq (d := IsConjRoot.decidable)

Depends on / 依赖: IsConjRoot, IsConjRoot.decidable, Quotient, Quotient.decidableEq, decidable, decidableEq
-/
instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] : DecidableEq (ConjRootClass K L) :=
  Quotient.decidableEq (d := IsConjRoot.decidable)

/--
Definition of `carrier` / `carrier` 的定义

English:
definition carrier
  signature: (c : ConjRootClass K L)
  body: mk K ⁻¹' {c}

@[simp]

中文:
定义 carrier
  签名: (c : ConjRootClass K L)
  定义体: mk K ⁻¹' {c}

@[simp]
-/
def carrier (c : ConjRootClass K L) : Set L :=
  mk K ⁻¹' {c}

@[simp]
/--
theorem `mem_carrier` / 定理 `mem_carrier`

English:
theorem mem_carrier
  given: {x : L} {c : ConjRootClass K L}
  statement: x in c.carrier ↔ mk K x = c
  proof: Iff.rfl

@[simp]

中文:
定理 mem_carrier
  条件: {x : L} {c : ConjRootClass K L}
  结论: x in c.carrier ↔ mk K x = c
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_carrier {x : L} {c : ConjRootClass K L} : x in c.carrier ↔ mk K x = c :=
  Iff.rfl

@[simp]
/--
theorem `carrier_zero` / 定理 `carrier_zero`

English:
theorem carrier_zero
  statement: (0 : ConjRootClass K L).carrier = {0}
  proof: by
  ext; rw [mem_carrier, mk_eq_zero_iff, Set.mem_singleton_iff]

中文:
定理 carrier_zero
  结论: (0 : ConjRootClass K L).carrier = {0}
  证明: by
  ext; rw [mem_carrier, mk_eq_zero_iff, Set.mem_singleton_iff]

Depends on / 依赖: Set.mem_singleton_iff, mem_carrier, mem_singleton_iff, mk_eq_zero_iff
-/
theorem carrier_zero : (0 : ConjRootClass K L).carrier = {0} := by
  ext; rw [mem_carrier, mk_eq_zero_iff, Set.mem_singleton_iff]

/--
theorem `carrier_inj` / 定理 `carrier_inj`

English:
theorem carrier_inj
  statement: Function.Injective (carrier (K := K) (L := L))
  proof: by
  intro x y H
  induction x with | h x => ?_
  induction y with | h y => ?_
  simp_rw [Set.ext_iff, mem_carrier] at H
  rw [← H]

中文:
定理 carrier_inj
  结论: 函数.单射 (carrier (K := K) (L := L))
  证明: by
  intro x y H
  induction x with | h x => ?_
  induction y with | h y => ?_
  simp_rw [Set.ext_iff, mem_carrier] at H
  rw [← H]

Depends on / 依赖: Set.ext_iff, ext_iff, mem_carrier, simp_rw
-/
theorem carrier_inj : Function.Injective (carrier (K := K) (L := L)) := by
  intro x y H
  induction x with | h x => ?_
  induction y with | h y => ?_
  simp_rw [Set.ext_iff, mem_carrier] at H
  rw [← H]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (ConjRootClass K L)
  body: Quotient.map (fun x => -x) (fun _ _ => IsConjRoot.neg)

中文:
实例 :
  签名: 取负 (ConjRootClass K L)
  定义体: Quotient.map (fun x => -x) (fun _ _ => IsConjRoot.neg)

Depends on / 依赖: IsConjRoot, IsConjRoot.neg, Quotient, Quotient.map
-/
instance : Neg (ConjRootClass K L) where
  neg := Quotient.map (fun x => -x) (fun _ _ => IsConjRoot.neg)

/--
theorem `mk_neg` / 定理 `mk_neg`

English:
theorem mk_neg
  given: (x : L)
  statement: - mk K x = mk K (-x)
  proof: rfl

中文:
定理 mk_neg
  条件: (x : L)
  结论: - mk K x = mk K (-x)
  证明: rfl
-/
theorem mk_neg (x : L) : - mk K x = mk K (-x) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InvolutiveNeg (ConjRootClass K L)
  body: by induction c; rw [mk_neg, mk_neg, neg_neg]

@[simp]

中文:
实例 :
  签名: InvolutiveNeg (ConjRootClass K L)
  定义体: by induction c; rw [mk_neg, mk_neg, neg_neg]

@[simp]

Depends on / 依赖: mk_neg, neg_neg
-/
instance : InvolutiveNeg (ConjRootClass K L) where
  neg_neg c := by induction c; rw [mk_neg, mk_neg, neg_neg]

@[simp]
/--
theorem `carrier_neg` / 定理 `carrier_neg`

English:
theorem carrier_neg
  given: (c : ConjRootClass K L)
  statement: carrier (-c) = - carrier c
  proof: by
  ext
  simp [mem_carrier, ← mk_neg, neg_eq_iff_eq_neg]

中文:
定理 carrier_neg
  条件: (c : ConjRootClass K L)
  结论: carrier (-c) = - carrier c
  证明: by
  ext
  simp [mem_carrier, ← mk_neg, neg_eq_iff_eq_neg]

Depends on / 依赖: mem_carrier, mk_neg, neg_eq_iff_eq_neg
-/
theorem carrier_neg (c : ConjRootClass K L) : carrier (-c) = - carrier c := by
  ext
  simp [mem_carrier, ← mk_neg, neg_eq_iff_eq_neg]

/--
theorem `exists_mem_carrier_add_eq_zero` / 定理 `exists_mem_carrier_add_eq_zero`

English:
theorem exists_mem_carrier_add_eq_zero
  given: (x y : ConjRootClass K L)
  proof: by
  simp_rw [mem_carrier]
  constructor
  · rintro ⟨a, rfl, b, rfl, h⟩
    rw [mk_neg]; rw [mk_eq_mk]; rw [add_eq_zero_iff_eq_neg.mp h]
  · rintro rfl
    induction y with
    | h y => exact ⟨-y, mk_neg y, y, rfl, neg_add_cancel _⟩

中文:
定理 存在_mem_carrier_add_eq_zero
  条件: (x y : ConjRootClass K L)
  证明: by
  simp_rw [mem_carrier]
  constructor
  · rintro ⟨a, rfl, b, rfl, h⟩
    rw [mk_neg]; rw [mk_eq_mk]; rw [add_eq_zero_iff_eq_neg.mp h]
  · rintro rfl
    induction y with
    | h y => exact ⟨-y, mk_neg y, y, rfl, neg_add_cancel _⟩

Depends on / 依赖: add_eq_zero_iff_eq_neg, add_eq_zero_iff_eq_neg.mp, mem_carrier, mk_eq_mk, mk_neg, neg_add_cancel, simp_rw
-/
theorem exists_mem_carrier_add_eq_zero (x y : ConjRootClass K L) :
    (existsᵉ (a in x.carrier) (b in y.carrier), a + b = 0) ↔ x = -y := by
  simp_rw [mem_carrier]
  constructor
  · rintro ⟨a, rfl, b, rfl, h⟩
    rw [mk_neg]; rw [mk_eq_mk]; rw [add_eq_zero_iff_eq_neg.mp h]
  · rintro rfl
    induction y with
    | h y => exact ⟨-y, mk_neg y, y, rfl, neg_add_cancel _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Normal
  signature: K L] [DecidableEq L] [Fintype Gal(L/K)] (c
  body: fun x =>
  decidable_of_iff (mk K x = c) (by simp)

中文:
实例 [正规
  签名: K L] [DecidableEq L] [有限类型 Gal(L/K)] (c
  定义体: fun x =>
  decidable_of_iff (mk K x = c) (by simp)
-/
instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (c : ConjRootClass K L) :
    DecidablePred (· in c.carrier) := fun x =>
  decidable_of_iff (mk K x = c) (by simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Normal
  signature: K L] [DecidableEq L] [Fintype Gal(L/K)] (c
  body: Quotient.recOnSubsingleton c fun x =>
    .ofFinset
      ((Finset.univ (α := Gal(L/K))).image (· x))
      (fun _ => by simp [← isConjRoot_iff_exists_algEquiv, ← mk_eq_mk])

中文:
实例 [正规
  签名: K L] [DecidableEq L] [有限类型 Gal(L/K)] (c
  定义体: Quotient.recOnSubsingleton c fun x =>
    .ofFinset
      ((Finset.univ (α := Gal(L/K))).image (· x))
      (fun _ => by simp [← isConjRoot_iff_exists_algEquiv, ← mk_eq_mk])

Depends on / 依赖: Finset, Finset.univ, Quotient, Quotient.recOnSubsingleton, isConjRoot_iff_exists_algEquiv, mk_eq_mk, ofFinset, recOnSubsingleton
-/
instance [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (c : ConjRootClass K L) :
    Fintype c.carrier :=
  Quotient.recOnSubsingleton c fun x =>
    .ofFinset
      ((Finset.univ (α := Gal(L/K))).image (· x))
      (fun _ => by simp [← isConjRoot_iff_exists_algEquiv, ← mk_eq_mk])

open Polynomial

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def minpoly
  body: Quotient.lift (minpoly K) fun _ _ => id

@[simp]

中文:
定义 noncomputable
  签名: def minpoly
  定义体: Quotient.lift (minpoly K) fun _ _ => id

@[simp]
-/
protected noncomputable def minpoly : ConjRootClass K L -> K[X] :=
  Quotient.lift (minpoly K) fun _ _ => id

@[simp]
/--
theorem `minpoly_mk` / 定理 `minpoly_mk`

English:
theorem minpoly_mk
  given: (x : L)
  statement: (mk K x).minpoly = minpoly K x
  proof: rfl

@[simp]

中文:
定理 minpoly_mk
  条件: (x : L)
  结论: (mk K x).minpoly = minpoly K x
  证明: rfl

@[simp]
-/
theorem minpoly_mk (x : L) : (mk K x).minpoly = minpoly K x :=
  rfl

@[simp]
/--
theorem `minpoly_inj` / 定理 `minpoly_inj`

English:
theorem minpoly_inj
  given: {c d : ConjRootClass K L}
  statement: c.minpoly = d.minpoly ↔ c = d
  proof: by
  induction c
  induction d
  simp [isConjRoot_def]

中文:
定理 minpoly_inj
  条件: {c d : ConjRootClass K L}
  结论: c.minpoly = d.minpoly ↔ c = d
  证明: by
  induction c
  induction d
  simp [isConjRoot_def]

Depends on / 依赖: isConjRoot_def
-/
theorem minpoly_inj {c d : ConjRootClass K L} : c.minpoly = d.minpoly ↔ c = d := by
  induction c
  induction d
  simp [isConjRoot_def]

/--
theorem `minpoly_injective` / 定理 `minpoly_injective`

English:
theorem minpoly_injective
  statement: Function.Injective (ConjRootClass.minpoly (K := K) (L := L))
  proof: fun _ _ => minpoly_inj.mp

中文:
定理 minpoly_injective
  结论: 函数.单射 (ConjRootClass.minpoly (K := K) (L := L))
  证明: fun _ _ => minpoly_inj.mp
-/
theorem minpoly_injective : Function.Injective (ConjRootClass.minpoly (K := K) (L := L)) :=
  fun _ _ => minpoly_inj.mp

/--
theorem `splits_minpoly` / 定理 `splits_minpoly`

English:
theorem splits_minpoly
  given: [n : Normal K L] (c : ConjRootClass K L)
  proof: by
  induction c
  rw [minpoly_mk]
  exact n.splits _

中文:
定理 splits_minpoly
  条件: [n : 正规 K L] (c : ConjRootClass K L)
  证明: by
  induction c
  rw [minpoly_mk]
  exact n.splits _

Depends on / 依赖: minpoly_mk, n.splits, splits
-/
theorem splits_minpoly [n : Normal K L] (c : ConjRootClass K L) :
    Splits (c.minpoly.map (algebraMap K L)) := by
  induction c
  rw [minpoly_mk]
  exact n.splits _

section IsAlgebraic

variable [Algebra.IsAlgebraic K L]

/--
theorem `monic_minpoly` / 定理 `monic_minpoly`

English:
theorem monic_minpoly
  given: (c : ConjRootClass K L)
  statement: c.minpoly.Monic
  proof: by
  induction c
  rw [minpoly_mk]
  exact minpoly.monic (Algebra.IsIntegral.isIntegral _)

中文:
定理 monic_minpoly
  条件: (c : ConjRootClass K L)
  结论: c.minpoly.Monic
  证明: by
  induction c
  rw [minpoly_mk]
  exact minpoly.monic (Algebra.IsIntegral.isIntegral _)

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, isIntegral, minpoly, minpoly.monic, minpoly_mk
-/
theorem monic_minpoly (c : ConjRootClass K L) : c.minpoly.Monic := by
  induction c
  rw [minpoly_mk]
  exact minpoly.monic (Algebra.IsIntegral.isIntegral _)

/--
theorem `minpoly_ne_zero` / 定理 `minpoly_ne_zero`

English:
theorem minpoly_ne_zero
  given: (c : ConjRootClass K L)
  statement: c.minpoly != 0
  proof: c.monic_minpoly.ne_zero

中文:
定理 minpoly_ne_zero
  条件: (c : ConjRootClass K L)
  结论: c.minpoly != 0
  证明: c.monic_minpoly.ne_zero

Depends on / 依赖: c.monic_minpoly.ne_zero, monic_minpoly, ne_zero
-/
theorem minpoly_ne_zero (c : ConjRootClass K L) : c.minpoly != 0 :=
  c.monic_minpoly.ne_zero

/--
theorem `irreducible_minpoly` / 定理 `irreducible_minpoly`

English:
theorem irreducible_minpoly
  given: (c : ConjRootClass K L)
  statement: Irreducible c.minpoly
  proof: by
  induction c
  rw [minpoly_mk]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)

中文:
定理 irreducible_minpoly
  条件: (c : ConjRootClass K L)
  结论: 不可约 c.minpoly
  证明: by
  induction c
  rw [minpoly_mk]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, irreducible, isIntegral, minpoly, minpoly.irreducible, minpoly_mk
-/
theorem irreducible_minpoly (c : ConjRootClass K L) : Irreducible c.minpoly := by
  induction c
  rw [minpoly_mk]
  exact minpoly.irreducible (Algebra.IsIntegral.isIntegral _)

/--
theorem `aeval_minpoly_iff` / 定理 `aeval_minpoly_iff`

English:
theorem aeval_minpoly_iff
  given: (x : L) (c : ConjRootClass K L)
  proof: by
  induction c
  simpa [← isConjRoot_iff_aeval_eq_zero (Algebra.IsIntegral.isIntegral _)] using comm

中文:
定理 aeval_minpoly_iff
  条件: (x : L) (c : ConjRootClass K L)
  证明: by
  induction c
  simpa [← isConjRoot_iff_aeval_eq_zero (Algebra.IsIntegral.isIntegral _)] using comm

Depends on / 依赖: Algebra, Algebra.IsIntegral.isIntegral, IsIntegral, isConjRoot_iff_aeval_eq_zero, isIntegral
-/
theorem aeval_minpoly_iff (x : L) (c : ConjRootClass K L) :
    aeval x c.minpoly = 0 ↔ mk K x = c := by
  induction c
  simpa [← isConjRoot_iff_aeval_eq_zero (Algebra.IsIntegral.isIntegral _)] using comm

/--
theorem `rootSet_minpoly_eq_carrier` / 定理 `rootSet_minpoly_eq_carrier`

English:
theorem rootSet_minpoly_eq_carrier
  given: (c : ConjRootClass K L)
  proof: by
  ext x
  rw [mem_carrier]; rw [mem_rootSet]; rw [aeval_minpoly_iff x c]
  simp [c.minpoly_ne_zero]

中文:
定理 rootSet_minpoly_eq_carrier
  条件: (c : ConjRootClass K L)
  证明: by
  ext x
  rw [mem_carrier]; rw [mem_rootSet]; rw [aeval_minpoly_iff x c]
  simp [c.minpoly_ne_zero]

Depends on / 依赖: aeval_minpoly_iff, c.minpoly_ne_zero, mem_carrier, mem_rootSet, minpoly_ne_zero
-/
theorem rootSet_minpoly_eq_carrier (c : ConjRootClass K L) :
    c.minpoly.rootSet L = c.carrier := by
  ext x
  rw [mem_carrier]; rw [mem_rootSet]; rw [aeval_minpoly_iff x c]
  simp [c.minpoly_ne_zero]

end IsAlgebraic

section IsSeparable

variable [Algebra.IsSeparable K L]

/--
theorem `separable_minpoly` / 定理 `separable_minpoly`

English:
theorem separable_minpoly
  given: (c : ConjRootClass K L)
  statement: Separable c.minpoly
  proof: by
  induction c
  exact Algebra.IsSeparable.isSeparable K _

中文:
定理 separable_minpoly
  条件: (c : ConjRootClass K L)
  结论: 可分 c.minpoly
  证明: by
  induction c
  exact Algebra.IsSeparable.isSeparable K _

Depends on / 依赖: Algebra, Algebra.IsSeparable.isSeparable, IsSeparable, isSeparable
-/
theorem separable_minpoly (c : ConjRootClass K L) : Separable c.minpoly := by
  induction c
  exact Algebra.IsSeparable.isSeparable K _

/--
theorem `nodup_aroots_minpoly` / 定理 `nodup_aroots_minpoly`

English:
theorem nodup_aroots_minpoly
  given: (c : ConjRootClass K L)
  statement: (c.minpoly.aroots L).Nodup
  proof: nodup_roots c.separable_minpoly.map

中文:
定理 nodup_aroots_minpoly
  条件: (c : ConjRootClass K L)
  结论: (c.minpoly.aroots L).Nodup
  证明: nodup_roots c.separable_minpoly.map

Depends on / 依赖: c.separable_minpoly.map, nodup_roots, separable_minpoly
-/
theorem nodup_aroots_minpoly (c : ConjRootClass K L) : (c.minpoly.aroots L).Nodup :=
  nodup_roots c.separable_minpoly.map

/--
theorem `aroots_minpoly_eq_carrier_val` / 定理 `aroots_minpoly_eq_carrier_val`

English:
theorem aroots_minpoly_eq_carrier_val
  given: (c : ConjRootClass K L) [Fintype c.carrier]
  proof: by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, rootSet_def, Finset.toFinset_coe, Multiset.toFinset_val,
    c.nodup_aroots_minpoly.dedup]

中文:
定理 aroots_minpoly_eq_carrier_val
  条件: (c : ConjRootClass K L) [有限类型 c.carrier]
  证明: by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, rootSet_def, Finset.toFinset_coe, Multiset.toFinset_val,
    c.nodup_aroots_minpoly.dedup]

Depends on / 依赖: Finset, Finset.toFinset_coe, Multiset, Multiset.toFinset_val, c.nodup_aroots_minpoly.dedup, classical, nodup_aroots_minpoly, rootSet_def, rootSet_minpoly_eq_carrier, simp_rw, toFinset_coe, toFinset_val
-/
theorem aroots_minpoly_eq_carrier_val (c : ConjRootClass K L) [Fintype c.carrier] :
    c.minpoly.aroots L = c.carrier.toFinset.1 := by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, rootSet_def, Finset.toFinset_coe, Multiset.toFinset_val,
    c.nodup_aroots_minpoly.dedup]

/--
theorem `carrier_eq_mk_aroots_minpoly` / 定理 `carrier_eq_mk_aroots_minpoly`

English:
theorem carrier_eq_mk_aroots_minpoly
  given: (c : ConjRootClass K L) [Fintype c.carrier]
  proof: by
  simp only [aroots_minpoly_eq_carrier_val]

中文:
定理 carrier_eq_mk_aroots_minpoly
  条件: (c : ConjRootClass K L) [有限类型 c.carrier]
  证明: by
  simp only [aroots_minpoly_eq_carrier_val]

Depends on / 依赖: aroots_minpoly_eq_carrier_val
-/
theorem carrier_eq_mk_aroots_minpoly (c : ConjRootClass K L) [Fintype c.carrier] :
    c.carrier.toFinset = ⟨c.minpoly.aroots L, c.nodup_aroots_minpoly⟩ := by
  simp only [aroots_minpoly_eq_carrier_val]

/--
theorem `minpoly.map_eq_prod` / 定理 `minpoly.map_eq_prod`

English:
theorem minpoly.map_eq_prod
  given: [Normal K L] (c : ConjRootClass K L) [Fintype c.carrier]
  proof: by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, Finset.prod_eq_multiset_prod, rootSet_def,
    Finset.toFinset_coe, Multiset.toFinset_val]
  rw [Multiset.dedup_eq_self.mpr (nodup_roots c.separable_minpoly.map)]; rw [prod_multiset_X_sub_C_of_monic_of_roots_card_eq (c.monic_minpoly.map _)]
  r

中文:
定理 minpoly.map_eq_prod
  条件: [正规 K L] (c : ConjRootClass K L) [有限类型 c.carrier]
  证明: by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, Finset.prod_eq_multiset_prod, rootSet_def,
    Finset.toFinset_coe, Multiset.toFinset_val]
  rw [Multiset.dedup_eq_self.mpr (nodup_roots c.separable_minpoly.map)]; rw [prod_multiset_X_sub_C_of_monic_of_roots_card_eq (c.monic_minpoly.map _)]
  r

Depends on / 依赖: Finset, Finset.prod_eq_multiset_prod, Finset.toFinset_coe, Multiset, Multiset.dedup_eq_self.mpr, Multiset.toFinset_val, c.monic_minpoly.map, c.separable_minpoly.map, c.splits_minpoly, classical, dedup_eq_self, monic_minpoly, nodup_roots, prod_eq_multiset_prod, prod_multiset_X_sub_C_of_monic_of_roots_card_eq, rootSet_def, rootSet_minpoly_eq_carrier, separable_minpoly, simp_rw, splits_iff_card_roots
-/
theorem minpoly.map_eq_prod [Normal K L] (c : ConjRootClass K L) [Fintype c.carrier] :
    c.minpoly.map (algebraMap K L) = ∏ x in c.carrier.toFinset, (X - C x) := by
  classical
  simp_rw [← rootSet_minpoly_eq_carrier, Finset.prod_eq_multiset_prod, rootSet_def,
    Finset.toFinset_coe, Multiset.toFinset_val]
  rw [Multiset.dedup_eq_self.mpr (nodup_roots c.separable_minpoly.map)]; rw [prod_multiset_X_sub_C_of_monic_of_roots_card_eq (c.monic_minpoly.map _)]
  rw [← splits_iff_card_roots]
  exact c.splits_minpoly

end IsSeparable

end ConjRootClass
