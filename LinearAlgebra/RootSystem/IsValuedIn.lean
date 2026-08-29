/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan, Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.PerfectPairing.Restrict
public import Mathlib.LinearAlgebra.RootSystem.Defs

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Span.TensorProduct
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Root pairings taking values in a subring

This file lays out the basic theory of root pairings over a commutative ring `R`, where `R` is an
`S`-algebra, and the pairing between roots and coroots takes values in `S`. The main application
of this theory is the theory of crystallographic root systems, where `S = ℤ`.

## Main definitions:

* `RootPairing.IsValuedIn`: Given a commutative ring `S` and an `S`-algebra `R`, a root pairing
  over `R` is valued in `S` if all root-coroot pairings lie in the image of `algebraMap S R`.
* `RootPairing.IsCrystallographic`: A root pairing is said to be crystallographic if the pairing
  between a root and coroot is always an integer.
* `RootPairing.pairingIn`: The `S`-valued pairing between roots and coroots.
* `RootPairing.coxeterWeightIn`: The product of `pairingIn i j` and `pairingIn j i`.

-/

@[expose] public section

open Set Function
open Submodule (span)
open Module

noncomputable section

namespace RootPairing

variable {ι R S M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (i j : ι)

/-- If `R` is an `S`-algebra, a root pairing over `R` is said to be valued in `S` if the pairing
between a root and coroot always belongs to `S`.

Of particular interest is the case `S = ℤ`. See `RootPairing.IsCrystallographic`. -/
@[mk_iff]
/--
Definition of `IsValuedIn` / `IsValuedIn` 的定义

English:
class IsValuedIn
  parameters: (S : Type*) [CommRing S] [Algebra S R]
  axioms and operations (1):
    - exists_value : forall i j, exists s, algebraMap S R s = P.pairing i j

中文:
类 IsValuedIn
  参数: (S : 类型) [CommRing S] [Algebra S R]
  公理与运算 (1 个):
    - exists_value : 对任意 i j, 存在 s, algebraMap S R s = P.pairing i j

Depends on / 依赖: IsValuedIn, IsValuedIn.exists_value, MeasurableSup, OrderDual, OrderDual.instMeasurableInf, exists_value, instMeasurableInf
-/
class IsValuedIn (S : Type*) [CommRing S] [Algebra S R] : Prop where
  exists_value : forall i j, exists s, algebraMap S R s = P.pairing i j

protected alias exists_value := IsValuedIn.exists_value

/--
Definition of `IsCrystallographic` / `IsCrystallographic` 的定义

English:
abbreviation IsCrystallographic
  body: P.IsValuedIn Int

中文:
缩写 IsCrystallographic
  定义体: P.IsValuedIn Int

Depends on / 依赖: IsValuedIn, OrderDual, OrderDual.instMeasurableSup, P.IsValuedIn
-/
abbrev IsCrystallographic := P.IsValuedIn Int

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.IsValuedIn R
  body: by simp

中文:
实例 :
  签名: P.IsValuedIn R
  定义体: by simp

Depends on / 依赖: OrderDual, OrderDual.instMeasurableInf
-/
instance : P.IsValuedIn R where
  exists_value i j := by simp

variable (S : Type*) [CommRing S] [Algebra S R]

variable {S} in
/--
lemma `isValuedIn_iff_mem_range` / 引理 `isValuedIn_iff_mem_range`

English:
lemma isValuedIn_iff_mem_range
  proof: by
  simp only [isValuedIn_iff, mem_range]

中文:
引理 isValuedIn_iff_mem_range
  证明: by
  simp only [isValuedIn_iff, mem_range]

Depends on / 依赖: isValuedIn_iff, mem_range
-/
lemma isValuedIn_iff_mem_range :
    P.IsValuedIn S ↔ forall i j, P.pairing i j in range (algebraMap S R) := by
  simp only [isValuedIn_iff, mem_range]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsValuedIn
  signature: S] : P.flip.IsValuedIn S
  body: by
  rw [isValuedIn_iff]; rw [forall_comm]
  exact P.exists_value

中文:
实例 [P.IsValuedIn
  签名: S] : P.flip.IsValuedIn S
  定义体: by
  rw [isValuedIn_iff]; rw [forall_comm]
  exact P.exists_value

Depends on / 依赖: P.exists_value, exists_value, forall_comm, isValuedIn_iff
-/
instance [P.IsValuedIn S] : P.flip.IsValuedIn S := by
  rw [isValuedIn_iff]; rw [forall_comm]
  exact P.exists_value

/--
Definition of `pairingIn` / `pairingIn` 的定义

English:
definition pairingIn
  signature: [P.IsValuedIn S] (i j : ι)
  body: (P.exists_value i j).choose

@[simp]

中文:
定义 pairingIn
  签名: [P.IsValuedIn S] (i j : ι)
  定义体: (P.exists_value i j).choose

@[simp]

Depends on / 依赖: P.exists_value, exists_value
-/
def pairingIn [P.IsValuedIn S] (i j : ι) : S :=
  (P.exists_value i j).choose

@[simp]
/--
lemma `algebraMap_pairingIn` / 引理 `algebraMap_pairingIn`

English:
lemma algebraMap_pairingIn
  given: [P.IsValuedIn S] (i j : ι)
  proof: (P.exists_value i j).choose_spec

@[simp]

中文:
引理 algebraMap_pairingIn
  条件: [P.IsValuedIn S] (i j : ι)
  证明: (P.exists_value i j).choose_spec

@[simp]

Depends on / 依赖: P.exists_value, choose_spec, exists_value
-/
lemma algebraMap_pairingIn [P.IsValuedIn S] (i j : ι) :
    algebraMap S R (P.pairingIn S i j) = P.pairing i j :=
  (P.exists_value i j).choose_spec

@[simp]
/--
lemma `pairingIn_same` / 引理 `pairingIn_same`

English:
lemma pairingIn_same
  given: [FaithfulSMul S R] [P.IsValuedIn S] (i : ι)
  proof: FaithfulSMul.algebraMap_injective S R by simp [map_ofNat]

中文:
引理 pairingIn_same
  条件: [FaithfulSMul S R] [P.IsValuedIn S] (i : ι)
  证明: FaithfulSMul.algebraMap_injective S R by simp [map_ofNat]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, map_ofNat
-/
lemma pairingIn_same [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    P.pairingIn S i i = 2 :=
FaithfulSMul.algebraMap_injective S R by simp [map_ofNat]

variable {P S} in
/--
lemma `pairingIn_eq_add_of_root_eq_add` / 引理 `pairingIn_eq_add_of_root_eq_add`

English:
lemma pairingIn_eq_add_of_root_eq_add
  statement: [FaithfulSMul S R] [P.IsValuedIn S]
  proof: by
  apply FaithfulSMul.algebraMap_injective S R
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using pairing_eq_add_of_root_eq_add h

中文:
引理 pairingIn_eq_add_of_root_eq_add
  结论: [FaithfulSMul S R] [P.IsValuedIn S]
  证明: by
  apply FaithfulSMul.algebraMap_injective S R
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using pairing_eq_add_of_root_eq_add h

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, P.algebraMap_pairingIn, algebraMap_injective, algebraMap_pairingIn, pairing_eq_add_of_root_eq_add
-/
lemma pairingIn_eq_add_of_root_eq_add [FaithfulSMul S R] [P.IsValuedIn S]
    {i j k l : ι} (h : P.root k = P.root i + P.root l) :
    P.pairingIn S k j = P.pairingIn S i j + P.pairingIn S l j := by
  apply FaithfulSMul.algebraMap_injective S R
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using pairing_eq_add_of_root_eq_add h

variable {P S} in
/--
lemma `pairingIn_eq_add_of_root_eq_smul_add_smul` / 引理 `pairingIn_eq_add_of_root_eq_smul_add_smul`

English:
lemma pairingIn_eq_add_of_root_eq_smul_add_smul
  proof: by
  apply FaithfulSMul.algebraMap_injective S R
  replace h : P.root k = (algebraMap S R x) • P.root i + (algebraMap S R y) • P.root l := by simpa
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using
    pairing_eq_add_of_root_eq_smul_add_smul h

中文:
引理 pairingIn_eq_add_of_root_eq_smul_add_smul
  证明: by
  apply FaithfulSMul.algebraMap_injective S R
  replace h : P.root k = (algebraMap S R x) • P.root i + (algebraMap S R y) • P.root l := by simpa
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using
    pairing_eq_add_of_root_eq_smul_add_smul h

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, MeasurableSup, P.algebraMap_pairingIn, P.root, algebraMap, algebraMap_injective, algebraMap_pairingIn, pairing_eq_add_of_root_eq_smul_add_smul, replace, toMeasurableSup
-/
lemma pairingIn_eq_add_of_root_eq_smul_add_smul
    [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsScalarTower S R M]
    {i j k l : ι} {x y : S} (h : P.root k = x • P.root i + y • P.root l) :
    P.pairingIn S k j = x • P.pairingIn S i j + y • P.pairingIn S l j := by
  apply FaithfulSMul.algebraMap_injective S R
  replace h : P.root k = (algebraMap S R x) • P.root i + (algebraMap S R y) • P.root l := by simpa
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using
    pairing_eq_add_of_root_eq_smul_add_smul h

/--
lemma `pairingIn_reflectionPerm` / 引理 `pairingIn_reflectionPerm`

English:
lemma pairingIn_reflectionPerm
  given: [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι)
  proof: by
  simp only [← (FaithfulSMul.algebraMap_injective S R).eq_iff, algebraMap_pairingIn]
  exact pairing_reflectionPerm P i j k

@[simp]

中文:
引理 pairingIn_reflectionPerm
  条件: [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι)
  证明: by
  simp only [← (FaithfulSMul.algebraMap_injective S R).eq_iff, algebraMap_pairingIn]
  exact pairing_reflectionPerm P i j k

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, algebraMap_pairingIn, eq_iff, pairing_reflectionPerm
-/
lemma pairingIn_reflectionPerm [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι) :
    P.pairingIn S j (P.reflectionPerm i k) = P.pairingIn S (P.reflectionPerm i j) k := by
  simp only [← (FaithfulSMul.algebraMap_injective S R).eq_iff, algebraMap_pairingIn]
  exact pairing_reflectionPerm P i j k

@[simp]
/--
lemma `pairingIn_reflectionPerm_self_left` / 引理 `pairingIn_reflectionPerm_self_left`

English:
lemma pairingIn_reflectionPerm_self_left
  given: [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι)
  proof: by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

@[simp]

中文:
引理 pairingIn_reflectionPerm_self_left
  条件: [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι)
  证明: by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, eq_iff
-/
lemma pairingIn_reflectionPerm_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) :
    P.pairingIn S (P.reflectionPerm i i) j = - P.pairingIn S i j := by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

@[simp]
/--
lemma `pairingIn_reflectionPerm_self_right` / 引理 `pairingIn_reflectionPerm_self_right`

English:
lemma pairingIn_reflectionPerm_self_right
  given: [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι)
  proof: by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

中文:
引理 pairingIn_reflectionPerm_self_right
  条件: [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι)
  证明: by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap_injective, eq_iff
-/
lemma pairingIn_reflectionPerm_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) :
    P.pairingIn S i (P.reflectionPerm j j) = - P.pairingIn S i j := by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

/--
lemma `IsValuedIn.trans` / 引理 `IsValuedIn.trans`

English:
lemma IsValuedIn.trans
  statement: (T : Type*) [CommRing T] [Algebra T S] [Algebra T R] [IsScalarTower T S R]
  proof: by
    use algebraMap T S (P.pairingIn T i j)
    simp [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq T S R]

中文:
引理 IsValuedIn.trans
  结论: (T : 类型) [CommRing T] [Algebra T S] [Algebra T R] [IsScalarTower T S R]
  证明: by
    use algebraMap T S (P.pairingIn T i j)
    simp [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq T S R]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, P.pairingIn, RingHom, RingHom.comp_apply, algebraMap, algebraMap_eq, comp_apply, pairingIn
-/
lemma IsValuedIn.trans (T : Type*) [CommRing T] [Algebra T S] [Algebra T R] [IsScalarTower T S R]
    [P.IsValuedIn T] :
    P.IsValuedIn S where
  exists_value i j := by
    use algebraMap T S (P.pairingIn T i j)
    simp [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq T S R]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsCrystallographic]
  signature: [Algebra Rat R]
  body: IsValuedIn.trans P (T := Int) (S := Rat)

中文:
实例 [P.IsCrystallographic]
  签名: [Algebra Rat R]
  定义体: IsValuedIn.trans P (T := Int) (S := Rat)

Depends on / 依赖: IsValuedIn, IsValuedIn.trans
-/
instance [P.IsCrystallographic] [Algebra Rat R] : P.IsValuedIn Rat :=
  IsValuedIn.trans P (T := Int) (S := Rat)

/--
lemma `algebraMap_pairingIn'` / 引理 `algebraMap_pairingIn'`

English:
lemma algebraMap_pairingIn'
  statement: (T : Type*)
  proof: by
  apply FaithfulSMul.algebraMap_injective S R
  rw [← RingHom.comp_apply]; rw [← IsScalarTower.algebraMap_eq]
  simp

中文:
引理 algebraMap_pairingIn'
  结论: (T : 类型)
  证明: by
  apply FaithfulSMul.algebraMap_injective S R
  rw [← RingHom.comp_apply]; rw [← IsScalarTower.algebraMap_eq]
  simp
-/
@[simp] lemma algebraMap_pairingIn' (T : Type*)
    [CommRing T] [Algebra T S] [Algebra T R] [IsScalarTower T S R] [P.IsValuedIn T] [P.IsValuedIn S]
    [FaithfulSMul S R] (i j : ι) :
    algebraMap T S (P.pairingIn T i j) = P.pairingIn S i j := by
  apply FaithfulSMul.algebraMap_injective S R
  rw [← RingHom.comp_apply]; rw [← IsScalarTower.algebraMap_eq]
  simp

/--
lemma `pairingIn_rat` / 引理 `pairingIn_rat`

English:
lemma pairingIn_rat
  given: [Nontrivial R] [P.IsCrystallographic] [Algebra Rat R] (i j : ι)
  proof: by
  simp [← P.algebraMap_pairingIn' Rat Int]

中文:
引理 pairingIn_rat
  条件: [Nontrivial R] [P.IsCrystallographic] [Algebra Rat R] (i j : ι)
  证明: by
  simp [← P.algebraMap_pairingIn' Rat Int]

Depends on / 依赖: MeasurableInf, to_hasMeasurableInf
-/
@[simp] lemma pairingIn_rat [Nontrivial R] [P.IsCrystallographic] [Algebra Rat R] (i j : ι) :
    P.pairingIn Rat i j = P.pairingIn Int i j := by
  simp [← P.algebraMap_pairingIn' Rat Int]

/--
lemma `coroot'_apply_apply_mem_of_mem_span` / 引理 `coroot'_apply_apply_mem_of_mem_span`

English:
lemma coroot'_apply_apply_mem_of_mem_span
  statement: [Module S M] [IsScalarTower S R M] [P.IsValuedIn S]
  proof: by
  rw [show range (algebraMap S R) = LinearMap.range (Algebra.linearMap S R) by ext; simp]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    simpa using! RootPairing.exists_value k i
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using

中文:
引理 coroot'_apply_apply_mem_of_mem_span
  结论: [Module S M] [IsScalarTower S R M] [P.IsValuedIn S]
  证明: by
  rw [show range (algebraMap S R) = LinearMap.range (Algebra.linearMap S R) by ext; simp]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    simpa using! RootPairing.exists_value k i
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using
-/
lemma coroot'_apply_apply_mem_of_mem_span [Module S M] [IsScalarTower S R M] [P.IsValuedIn S]
    {x : M} (hx : x in span S (range P.root)) (i : ι) :
    P.coroot' i x in range (algebraMap S R) := by
  rw [show range (algebraMap S R) = LinearMap.range (Algebra.linearMap S R) by ext; simp]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    simpa using! RootPairing.exists_value k i
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using! add_mem hx hy
  | smul t x _ hx => simpa only [LinearMap.map_smul_of_tower] using! Submodule.smul_mem _ t hx

/--
lemma `root'_apply_apply_mem_of_mem_span` / 引理 `root'_apply_apply_mem_of_mem_span`

English:
lemma root'_apply_apply_mem_of_mem_span
  statement: [Module S N] [IsScalarTower S R N] [P.IsValuedIn S]
  proof: P.flip.coroot'_apply_apply_mem_of_mem_span S hx i

中文:
引理 root'_apply_apply_mem_of_mem_span
  结论: [Module S N] [IsScalarTower S R N] [P.IsValuedIn S]
  证明: P.flip.coroot'_apply_apply_mem_of_mem_span S hx i
-/
lemma root'_apply_apply_mem_of_mem_span [Module S N] [IsScalarTower S R N] [P.IsValuedIn S]
    {x : N} (hx : x in span S (range P.coroot)) (i : ι) :
    P.root' i x in LinearMap.range (Algebra.linearMap S R) :=
  P.flip.coroot'_apply_apply_mem_of_mem_span S hx i

/--
Definition of `rootSpan` / `rootSpan` 的定义

English:
abbreviation rootSpan
  signature: [Module S M]
  body: span S (range P.root)

中文:
缩写 rootSpan
  签名: [Module S M]
  定义体: span S (range P.root)

Depends on / 依赖: P.root
-/
abbrev rootSpan [Module S M] := span S (range P.root)

/--
Definition of `corootSpan` / `corootSpan` 的定义

English:
abbreviation corootSpan
  signature: [Module S N]
  body: span S (range P.coroot)

中文:
缩写 corootSpan
  签名: [Module S N]
  定义体: span S (range P.coroot)

Depends on / 依赖: P.coroot, coroot
-/
abbrev corootSpan [Module S N] := span S (range P.coroot)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module
  signature: S M] [Finite ι] :
  body: Finite.span_of_finite S finite_range _

中文:
实例 [Module
  签名: S M] [Finite ι] :
  定义体: Finite.span_of_finite S finite_range _

Depends on / 依赖: Finite, Finite.span_of_finite, finite_range, span_of_finite
-/
instance [Module S M] [Finite ι] :
Module.Finite S P.rootSpan S :=
Finite.span_of_finite S finite_range _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module
  signature: S N] [Finite ι] :
  body: Finite.span_of_finite S finite_range _

中文:
实例 [Module
  签名: S N] [Finite ι] :
  定义体: Finite.span_of_finite S finite_range _

Depends on / 依赖: Finite, Finite.span_of_finite, finite_range, span_of_finite
-/
instance [Module S N] [Finite ι] :
Module.Finite S P.corootSpan S :=
Finite.span_of_finite S finite_range _

/--
Definition of `rootSpanMem` / `rootSpanMem` 的定义

English:
abbreviation rootSpanMem
  signature: [Module S M] (i : ι)
  body: ⟨P.root i, Submodule.subset_span (mem_range_self i)⟩

中文:
缩写 rootSpanMem
  签名: [Module S M] (i : ι)
  定义体: ⟨P.root i, Submodule.subset_span (mem_range_self i)⟩

Depends on / 依赖: P.root, Submodule, Submodule.subset_span, mem_range_self, subset_span
-/
abbrev rootSpanMem [Module S M] (i : ι) : P.rootSpan S :=
  ⟨P.root i, Submodule.subset_span (mem_range_self i)⟩

/--
Definition of `corootSpanMem` / `corootSpanMem` 的定义

English:
abbreviation corootSpanMem
  signature: [Module S N] (i : ι)
  body: ⟨P.coroot i, Submodule.subset_span (mem_range_self i)⟩

omit [Algebra S R] in

中文:
缩写 corootSpanMem
  签名: [Module S N] (i : ι)
  定义体: ⟨P.coroot i, Submodule.subset_span (mem_range_self i)⟩

omit [Algebra S R] in

Depends on / 依赖: P.coroot, Submodule, Submodule.subset_span, coroot, mem_range_self, subset_span
-/
abbrev corootSpanMem [Module S N] (i : ι) : P.corootSpan S :=
  ⟨P.coroot i, Submodule.subset_span (mem_range_self i)⟩

omit [Algebra S R] in
/--
lemma `rootSpanMem_reflectionPerm_self` / 引理 `rootSpanMem_reflectionPerm_self`

English:
lemma rootSpanMem_reflectionPerm_self
  given: [Module S M] (i : ι)
  proof: by
  ext; simp

omit [Algebra S R] in

中文:
引理 rootSpanMem_reflectionPerm_self
  条件: [Module S M] (i : ι)
  证明: by
  ext; simp

omit [Algebra S R] in
-/
lemma rootSpanMem_reflectionPerm_self [Module S M] (i : ι) :
    P.rootSpanMem S (P.reflectionPerm i i) = - P.rootSpanMem S i := by
  ext; simp

omit [Algebra S R] in
/--
lemma `corootSpanMem_reflectionPerm_self` / 引理 `corootSpanMem_reflectionPerm_self`

English:
lemma corootSpanMem_reflectionPerm_self
  given: [Module S N] (i : ι)
  proof: by
  ext; simp

中文:
引理 corootSpanMem_reflectionPerm_self
  条件: [Module S N] (i : ι)
  证明: by
  ext; simp
-/
lemma corootSpanMem_reflectionPerm_self [Module S N] (i : ι) :
    P.corootSpanMem S (P.reflectionPerm i i) = - P.corootSpanMem S i := by
  ext; simp

/--
Definition of `root'In` / `root'In` 的定义

English:
definition root'In
  signature: [Module S N] [IsScalarTower S R N] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι)
  body: LinearMap.restrictScalarsRange (P.corootSpan S).subtype (Algebra.linearMap S R)
    (FaithfulSMul.algebraMap_injective S R) (P.root' i)
    (fun m => P.root'_apply_apply_mem_of_mem_span S m.2 i)

中文:
定义 root'In
  签名: [Module S N] [IsScalarTower S R N] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι)
  定义体: LinearMap.restrictScalarsRange (P.corootSpan S).subtype (Algebra.linearMap S R)
    (FaithfulSMul.algebraMap_injective S R) (P.root' i)
    (fun m => P.root'_apply_apply_mem_of_mem_span S m.2 i)
-/
def root'In [Module S N] [IsScalarTower S R N] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    Dual S (P.corootSpan S) :=
  LinearMap.restrictScalarsRange (P.corootSpan S).subtype (Algebra.linearMap S R)
    (FaithfulSMul.algebraMap_injective S R) (P.root' i)
    (fun m => P.root'_apply_apply_mem_of_mem_span S m.2 i)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `algebraMap_root'In_apply` / 引理 `algebraMap_root'In_apply`

English:
lemma algebraMap_root'In_apply
  statement: [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
  proof: by
  rw [root'In]; rw [← Algebra.linearMap_apply]; rw [LinearMap.restrictScalarsRange_apply]; rw [Submodule.subtype_apply]

@[simp]

中文:
引理 algebraMap_root'In_apply
  结论: [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
  证明: by
  rw [root'In]; rw [← Algebra.linearMap_apply]; rw [LinearMap.restrictScalarsRange_apply]; rw [Submodule.subtype_apply]

@[simp]

Depends on / 依赖: Algebra, Algebra.linearMap_apply, LinearMap, LinearMap.restrictScalarsRange_apply, Submodule, Submodule.subtype_apply, linearMap_apply, restrictScalarsRange_apply, subtype_apply
-/
lemma algebraMap_root'In_apply [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
    [P.IsValuedIn S] (i : ι) (x : P.corootSpan S) :
    algebraMap S R (P.root'In S i x) = P.root' i x := by
  rw [root'In]; rw [← Algebra.linearMap_apply]; rw [LinearMap.restrictScalarsRange_apply]; rw [Submodule.subtype_apply]

@[simp]
/--
lemma `root'In_corootSpanMem_eq_pairingIn` / 引理 `root'In_corootSpanMem_eq_pairingIn`

English:
lemma root'In_corootSpanMem_eq_pairingIn
  statement: [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
  proof: rfl

中文:
引理 root'In_corootSpanMem_eq_pairingIn
  结论: [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
  证明: rfl
-/
lemma root'In_corootSpanMem_eq_pairingIn [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
    [P.IsValuedIn S] :
    P.root'In S i (P.corootSpanMem S j) = P.pairingIn S i j :=
  rfl

/--
Definition of `coroot'In` / `coroot'In` 的定义

English:
definition coroot'In
  signature: [Module S M] [IsScalarTower S R M] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι)
  body: P.flip.root'In S i

@[simp]

中文:
定义 coroot'In
  签名: [Module S M] [IsScalarTower S R M] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι)
  定义体: P.flip.root'In S i

@[simp]
-/
def coroot'In [Module S M] [IsScalarTower S R M] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    Dual S (P.rootSpan S) :=
  P.flip.root'In S i

@[simp]
/--
lemma `algebraMap_coroot'In_apply` / 引理 `algebraMap_coroot'In_apply`

English:
lemma algebraMap_coroot'In_apply
  statement: [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
  proof: P.flip.algebraMap_root'In_apply S i x

@[simp]

中文:
引理 algebraMap_coroot'In_apply
  结论: [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
  证明: P.flip.algebraMap_root'In_apply S i x

@[simp]

Depends on / 依赖: In_apply, P.flip.algebraMap_root, algebraMap_root
-/
lemma algebraMap_coroot'In_apply [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
    [P.IsValuedIn S] (i : ι) (x : P.rootSpan S) :
    algebraMap S R (P.coroot'In S i x) = P.coroot' i x :=
  P.flip.algebraMap_root'In_apply S i x

@[simp]
/--
lemma `coroot'In_rootSpanMem_eq_pairingIn` / 引理 `coroot'In_rootSpanMem_eq_pairingIn`

English:
lemma coroot'In_rootSpanMem_eq_pairingIn
  statement: [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
  proof: rfl

omit [Algebra S R] in

中文:
引理 coroot'In_rootSpanMem_eq_pairingIn
  结论: [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
  证明: rfl

omit [Algebra S R] in
-/
lemma coroot'In_rootSpanMem_eq_pairingIn [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
    [P.IsValuedIn S] :
    P.coroot'In S i (P.rootSpanMem S j) = P.pairingIn S j i :=
  rfl

omit [Algebra S R] in
/--
lemma `rootSpan_ne_bot` / 引理 `rootSpan_ne_bot`

English:
lemma rootSpan_ne_bot
  given: [Module S M] [Nonempty ι] [NeZero (2 : R)]
  statement: P.rootSpan S != ⊥
  proof: by
  simpa [rootSpan] using P.exists_ne_zero

omit [Algebra S R] in

中文:
引理 rootSpan_ne_bot
  条件: [Module S M] [Nonempty ι] [NeZero (2 : R)]
  结论: P.rootSpan S != ⊥
  证明: by
  simpa [rootSpan] using P.exists_ne_zero

omit [Algebra S R] in

Depends on / 依赖: P.exists_ne_zero, exists_ne_zero, rootSpan
-/
lemma rootSpan_ne_bot [Module S M] [Nonempty ι] [NeZero (2 : R)] : P.rootSpan S != ⊥ := by
  simpa [rootSpan] using P.exists_ne_zero

omit [Algebra S R] in
/--
lemma `corootSpan_ne_bot` / 引理 `corootSpan_ne_bot`

English:
lemma corootSpan_ne_bot
  given: [Module S N] [Nonempty ι] [NeZero (2 : R)]
  statement: P.corootSpan S != ⊥
  proof: P.flip.rootSpan_ne_bot S

中文:
引理 corootSpan_ne_bot
  条件: [Module S N] [Nonempty ι] [NeZero (2 : R)]
  结论: P.corootSpan S != ⊥
  证明: P.flip.rootSpan_ne_bot S

Depends on / 依赖: P.flip.rootSpan_ne_bot, rootSpan_ne_bot
-/
lemma corootSpan_ne_bot [Module S N] [Nonempty ι] [NeZero (2 : R)] : P.corootSpan S != ⊥ :=
  P.flip.rootSpan_ne_bot S

/--
lemma `rootSpan_mem_invtSubmodule_reflection` / 引理 `rootSpan_mem_invtSubmodule_reflection`

English:
lemma rootSpan_mem_invtSubmodule_reflection
  given: (i : ι)
  proof: by
  rw [Module.End.mem_invtSubmodule]; rw [rootSpan]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [Submodule.mem_comap]; rw [LinearEquiv.coe_coe]; rw [reflection_apply_root]
    apply Submodule.sub_mem
· exact Submodule.subset_span

中文:
引理 rootSpan_mem_invtSubmodule_reflection
  条件: (i : ι)
  证明: by
  rw [Module.End.mem_invtSubmodule]; rw [rootSpan]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [Submodule.mem_comap]; rw [LinearEquiv.coe_coe]; rw [reflection_apply_root]
    apply Submodule.sub_mem
· exact Submodule.subset_span

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, Module, Module.End.mem_invtSubmodule, Submodule, Submodule.add_mem, Submodule.mem_comap, Submodule.smul_me, Submodule.smul_mem, Submodule.span_induction, Submodule.sub_mem, Submodule.subset_span, add_mem, coe_coe, mem_comap, mem_invtSubmodule, mem_range_self, reflection_apply_root, rootSpan, smul_me
-/
lemma rootSpan_mem_invtSubmodule_reflection (i : ι) :
    P.rootSpan R in Module.End.invtSubmodule (P.reflection i) := by
  rw [Module.End.mem_invtSubmodule]; rw [rootSpan]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [Submodule.mem_comap]; rw [LinearEquiv.coe_coe]; rw [reflection_apply_root]
    apply Submodule.sub_mem
· exact Submodule.subset_span mem_range_self j
· exact Submodule.smul_mem _ _ Submodule.subset_span mem_range_self i
  | zero => simp
  | add y z hy hz hy' hz' => simpa using Submodule.add_mem _ hy' hz'
  | smul y t hy hy' => simpa using Submodule.smul_mem _ _ hy'

/--
lemma `corootSpan_mem_invtSubmodule_coreflection` / 引理 `corootSpan_mem_invtSubmodule_coreflection`

English:
lemma corootSpan_mem_invtSubmodule_coreflection
  given: (i : ι)
  proof: P.flip.rootSpan_mem_invtSubmodule_reflection i

中文:
引理 corootSpan_mem_invtSubmodule_coreflection
  条件: (i : ι)
  证明: P.flip.rootSpan_mem_invtSubmodule_reflection i

Depends on / 依赖: P.flip.rootSpan_mem_invtSubmodule_reflection, rootSpan_mem_invtSubmodule_reflection
-/
lemma corootSpan_mem_invtSubmodule_coreflection (i : ι) :
    P.corootSpan R in Module.End.invtSubmodule (P.coreflection i) :=
  P.flip.rootSpan_mem_invtSubmodule_reflection i

/--
lemma `rootSpan_dualAnnihilator_map_eq_iInf_ker_root'` / 引理 `rootSpan_dualAnnihilator_map_eq_iInf_ker_root'`

English:
lemma rootSpan_dualAnnihilator_map_eq_iInf_ker_root'
  proof: SetLike.coe_injective by ext; simp [LinearEquiv.symm_apply_eq, subset_def]

中文:
引理 rootSpan_dualAnnihilator_map_eq_iInf_ker_root'
  证明: SetLike.coe_injective by ext; simp [LinearEquiv.symm_apply_eq, subset_def]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, SetLike, SetLike.coe_injective, coe_injective, subset_def, symm_apply_eq
-/
lemma rootSpan_dualAnnihilator_map_eq_iInf_ker_root' :
    (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M ->ₗ[R] N) =
      ⨅ i, (P.root' i).ker :=
SetLike.coe_injective by ext; simp [LinearEquiv.symm_apply_eq, subset_def]

/--
lemma `corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'` / 引理 `corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'`

English:
lemma corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'
  proof: P.flip.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'

中文:
引理 corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'
  证明: P.flip.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'

Depends on / 依赖: P.flip.rootSpan_dualAnnihilator_map_eq_iInf_ker_root, rootSpan_dualAnnihilator_map_eq_iInf_ker_root
-/
lemma corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot' :
    (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm : Dual R N ->ₗ[R] M) =
      ⨅ i, (P.coroot' i).ker :=
  P.flip.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'

/--
lemma `rootSpan_dualAnnihilator_map_eq` / 引理 `rootSpan_dualAnnihilator_map_eq`

English:
lemma rootSpan_dualAnnihilator_map_eq
  proof: SetLike.coe_injective by ext; simp [LinearEquiv.symm_apply_eq, subset_def]

中文:
引理 rootSpan_dualAnnihilator_map_eq
  证明: SetLike.coe_injective by ext; simp [LinearEquiv.symm_apply_eq, subset_def]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, SetLike, SetLike.coe_injective, coe_injective, subset_def, symm_apply_eq
-/
lemma rootSpan_dualAnnihilator_map_eq :
    (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M ->ₗ[R] N) =
      (span R (range P.root')).dualCoannihilator :=
SetLike.coe_injective by ext; simp [LinearEquiv.symm_apply_eq, subset_def]

/--
lemma `corootSpan_dualAnnihilator_map_eq` / 引理 `corootSpan_dualAnnihilator_map_eq`

English:
lemma corootSpan_dualAnnihilator_map_eq
  proof: P.flip.rootSpan_dualAnnihilator_map_eq

中文:
引理 corootSpan_dualAnnihilator_map_eq
  证明: P.flip.rootSpan_dualAnnihilator_map_eq

Depends on / 依赖: P.flip.rootSpan_dualAnnihilator_map_eq, rootSpan_dualAnnihilator_map_eq
-/
lemma corootSpan_dualAnnihilator_map_eq :
    (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm : Dual R N ->ₗ[R] M) =
      (span R (range P.coroot')).dualCoannihilator :=
  P.flip.rootSpan_dualAnnihilator_map_eq

/--
lemma `iInf_ker_root'_eq` / 引理 `iInf_ker_root'_eq`

English:
lemma iInf_ker_root'_eq
  proof: by
  rw [← rootSpan_dualAnnihilator_map_eq]; rw [rootSpan_dualAnnihilator_map_eq_iInf_ker_root']

中文:
引理 iInf_ker_root'_eq
  证明: by
  rw [← rootSpan_dualAnnihilator_map_eq]; rw [rootSpan_dualAnnihilator_map_eq_iInf_ker_root']

Depends on / 依赖: rootSpan_dualAnnihilator_map_eq, rootSpan_dualAnnihilator_map_eq_iInf_ker_root
-/
lemma iInf_ker_root'_eq :
    ⨅ i, LinearMap.ker (P.root' i) = (span R (range P.root')).dualCoannihilator := by
  rw [← rootSpan_dualAnnihilator_map_eq]; rw [rootSpan_dualAnnihilator_map_eq_iInf_ker_root']

/--
lemma `iInf_ker_coroot'_eq` / 引理 `iInf_ker_coroot'_eq`

English:
lemma iInf_ker_coroot'_eq
  proof: P.flip.iInf_ker_root'_eq

中文:
引理 iInf_ker_coroot'_eq
  证明: P.flip.iInf_ker_root'_eq

Depends on / 依赖: P.flip.iInf_ker_root, iInf_ker_root
-/
lemma iInf_ker_coroot'_eq :
    ⨅ i, LinearMap.ker (P.coroot' i) = (span R (range P.coroot')).dualCoannihilator :=
  P.flip.iInf_ker_root'_eq

/--
lemma `rootSpan_map_toPerfPair` / 引理 `rootSpan_map_toPerfPair`

English:
lemma rootSpan_map_toPerfPair
  proof: by
  rw [rootSpan]; rw [Submodule.map_span]; rw [← image_univ]; rw [← image_comp]; rw [image_univ]; rw [LinearEquiv.coe_coe]; rw [toPerfPair_comp_root]

中文:
引理 rootSpan_map_toPerfPair
  证明: by
  rw [rootSpan]; rw [Submodule.map_span]; rw [← image_univ]; rw [← image_comp]; rw [image_univ]; rw [LinearEquiv.coe_coe]; rw [toPerfPair_comp_root]
-/
@[simp] lemma rootSpan_map_toPerfPair :
    (P.rootSpan R).map (P.toPerfPair : M ->ₗ[R] Dual R N) = span R (range P.root') := by
  rw [rootSpan]; rw [Submodule.map_span]; rw [← image_univ]; rw [← image_comp]; rw [image_univ]; rw [LinearEquiv.coe_coe]; rw [toPerfPair_comp_root]

/--
lemma `corootSpan_map_flip_toPerfPair` / 引理 `corootSpan_map_flip_toPerfPair`

English:
lemma corootSpan_map_flip_toPerfPair
  proof: P.flip.rootSpan_map_toPerfPair

中文:
引理 corootSpan_map_flip_toPerfPair
  证明: P.flip.rootSpan_map_toPerfPair
-/
@[simp] lemma corootSpan_map_flip_toPerfPair :
    (P.corootSpan R).map (P.toLinearMap.flip.toPerfPair : N ->ₗ[R] Dual R M) =
      span R (range P.coroot') :=
  P.flip.rootSpan_map_toPerfPair

/--
lemma `span_root'_eq_top` / 引理 `span_root'_eq_top`

English:
lemma span_root'_eq_top
  given: [P.IsRootSystem]
  proof: by
  simp [← rootSpan_map_toPerfPair]

中文:
引理 span_root'_eq_top
  条件: [P.IsRootSystem]
  证明: by
  simp [← rootSpan_map_toPerfPair]
-/
@[simp] lemma span_root'_eq_top [P.IsRootSystem] :
    span R (range P.root') = ⊤ := by
  simp [← rootSpan_map_toPerfPair]

/--
lemma `span_coroot'_eq_top` / 引理 `span_coroot'_eq_top`

English:
lemma span_coroot'_eq_top
  given: [P.IsRootSystem]
  proof: span_root'_eq_top P.flip

中文:
引理 span_coroot'_eq_top
  条件: [P.IsRootSystem]
  证明: span_root'_eq_top P.flip
-/
@[simp] lemma span_coroot'_eq_top [P.IsRootSystem] :
    span R (range P.coroot') = ⊤ :=
  span_root'_eq_top P.flip

/--
lemma `pairingIn_eq_zero_iff` / 引理 `pairingIn_eq_zero_iff`

English:
lemma pairingIn_eq_zero_iff
  statement: {S : Type*} [CommRing S] [Algebra S R] [FaithfulSMul S R]
  proof: by
  simpa only [← FaithfulSMul.algebraMap_eq_zero_iff S R, algebraMap_pairingIn] using
    P.pairing_eq_zero_iff

中文:
引理 pairingIn_eq_zero_iff
  结论: {S : 类型} [CommRing S] [Algebra S R] [FaithfulSMul S R]
  证明: by
  simpa only [← FaithfulSMul.algebraMap_eq_zero_iff S R, algebraMap_pairingIn] using
    P.pairing_eq_zero_iff

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_eq_zero_iff, P.pairing_eq_zero_iff, algebraMap_eq_zero_iff, algebraMap_pairingIn, pairing_eq_zero_iff
-/
lemma pairingIn_eq_zero_iff {S : Type*} [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [P.IsValuedIn S] [IsDomain R] [Module.IsTorsionFree R M] [NeZero (2 : R)] {i j : ι} :
    P.pairingIn S i j = 0 ↔ P.pairingIn S j i = 0 := by
  simpa only [← FaithfulSMul.algebraMap_eq_zero_iff S R, algebraMap_pairingIn] using
    P.pairing_eq_zero_iff

variable {P i j} in
/--
lemma `reflection_apply_root'` / 引理 `reflection_apply_root'`

English:
lemma reflection_apply_root'
  statement: (S : Type*) [CommRing S] [Algebra S R]
  proof: by
  rw [reflection_apply_root]; rw [← P.algebraMap_pairingIn S]; rw [algebraMap_smul]

中文:
引理 reflection_apply_root'
  结论: (S : 类型) [CommRing S] [Algebra S R]
  证明: by
  rw [reflection_apply_root]; rw [← P.algebraMap_pairingIn S]; rw [algebraMap_smul]

Depends on / 依赖: P.algebraMap_pairingIn, algebraMap_pairingIn, algebraMap_smul, reflection_apply_root
-/
lemma reflection_apply_root' (S : Type*) [CommRing S] [Algebra S R]
    [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] :
    P.reflection i (P.root j) = P.root j - (P.pairingIn S j i) • P.root i := by
  rw [reflection_apply_root]; rw [← P.algebraMap_pairingIn S]; rw [algebraMap_smul]

/--
Definition of `coxeterWeightIn` / `coxeterWeightIn` 的定义

English:
definition coxeterWeightIn
  signature: (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] (i j : ι)
  body: P.pairingIn S i j * P.pairingIn S j i

中文:
定义 coxeterWeightIn
  签名: (S : 类型) [CommRing S] [Algebra S R] [P.IsValuedIn S] (i j : ι)
  定义体: P.pairingIn S i j * P.pairingIn S j i

Depends on / 依赖: P.pairingIn, pairingIn
-/
def coxeterWeightIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] (i j : ι) : S :=
  P.pairingIn S i j * P.pairingIn S j i

/--
lemma `algebraMap_coxeterWeightIn` / 引理 `algebraMap_coxeterWeightIn`

English:
lemma algebraMap_coxeterWeightIn
  statement: (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S]
  proof: by
  simp [coxeterWeightIn, coxeterWeight]

中文:
引理 algebraMap_coxeterWeightIn
  结论: (S : 类型) [CommRing S] [Algebra S R] [P.IsValuedIn S]
  证明: by
  simp [coxeterWeightIn, coxeterWeight]
-/
@[simp] lemma algebraMap_coxeterWeightIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S]
    (i j : ι) :
    algebraMap S R (P.coxeterWeightIn S i j) = P.coxeterWeight i j := by
  simp [coxeterWeightIn, coxeterWeight]

/--
lemma `toLinearMap_apply_apply_mem_range_algebraMap` / 引理 `toLinearMap_apply_apply_mem_range_algebraMap`

English:
lemma toLinearMap_apply_apply_mem_range_algebraMap
  statement: [P.IsValuedIn S]
  proof: LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (LinearMap.range (Algebra.linearMap S R)) (range P.root) (range P.coroot)
    (LinearMap.restrictScalarsₗ S R _ _ _ ∘ₗ P.toLinearMap.restrictScalars S)
    (by simpa using RootPairing.exists_value) x y hx hy

中文:
引理 toLinearMap_apply_apply_mem_range_algebraMap
  结论: [P.IsValuedIn S]
  证明: LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (LinearMap.range (Algebra.linearMap S R)) (range P.root) (range P.coroot)
    (LinearMap.restrictScalarsₗ S R _ _ _ ∘ₗ P.toLinearMap.restrictScalars S)
    (by simpa using RootPairing.exists_value) x y hx hy

Depends on / 依赖: Algebra, Algebra.linearMap, BilinMap, LinearMap, LinearMap.BilinMap.apply_apply_mem_of_mem_span, LinearMap.range, LinearMap.restrictScalars, P.coroot, P.root, P.toLinearMap.restrictScalars, RootPairing, RootPairing.exists_value, apply_apply_mem_of_mem_span, coroot, exists_value, linearMap, restrictScalars, toLinearMap
-/
lemma toLinearMap_apply_apply_mem_range_algebraMap [P.IsValuedIn S]
    [Module S M] [Module S N] [IsScalarTower S R M] [IsScalarTower S R N]
    (x : M) (hx : x in P.rootSpan S) (y : N) (hy : y in P.corootSpan S) :
    P.toLinearMap x y in (algebraMap S R).range :=
  LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (LinearMap.range (Algebra.linearMap S R)) (range P.root) (range P.coroot)
    (LinearMap.restrictScalarsₗ S R _ _ _ ∘ₗ P.toLinearMap.restrictScalars S)
    (by simpa using RootPairing.exists_value) x y hx hy

section Field

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
  [Module L M] [Module L N] [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  (Q : RootPairing ι L M N) [Q.IsRootSystem]

@[simp]
/--
lemma `finrank_rootSpanIn` / 引理 `finrank_rootSpanIn`

English:
lemma finrank_rootSpanIn
  given: [Q.IsValuedIn K]
  proof: by
  rw [LinearMap.finrank_eq_of_isPerfPair Q.toLinearMap (Q.rootSpan K) (Q.corootSpan K)]
  · simp
  · simp
  · exact Q.toLinearMap_apply_apply_mem_range_algebraMap K

@[simp]

中文:
引理 finrank_rootSpanIn
  条件: [Q.IsValuedIn K]
  证明: by
  rw [LinearMap.finrank_eq_of_isPerfPair Q.toLinearMap (Q.rootSpan K) (Q.corootSpan K)]
  · simp
  · simp
  · exact Q.toLinearMap_apply_apply_mem_range_algebraMap K

@[simp]

Depends on / 依赖: LinearMap, LinearMap.finrank_eq_of_isPerfPair, Q.corootSpan, Q.rootSpan, Q.toLinearMap, Q.toLinearMap_apply_apply_mem_range_algebraMap, corootSpan, finrank_eq_of_isPerfPair, rootSpan, toLinearMap, toLinearMap_apply_apply_mem_range_algebraMap
-/
lemma finrank_rootSpanIn [Q.IsValuedIn K] :
    finrank K (Q.rootSpan K) = finrank L M := by
  rw [LinearMap.finrank_eq_of_isPerfPair Q.toLinearMap (Q.rootSpan K) (Q.corootSpan K)]
  · simp
  · simp
  · exact Q.toLinearMap_apply_apply_mem_range_algebraMap K

@[simp]
/--
lemma `finrank_corootSpanIn` / 引理 `finrank_corootSpanIn`

English:
lemma finrank_corootSpanIn
  given: [Q.IsValuedIn K]
  proof: finrank_rootSpanIn K Q.flip

@[simp]

中文:
引理 finrank_corootSpanIn
  条件: [Q.IsValuedIn K]
  证明: finrank_rootSpanIn K Q.flip

@[simp]

Depends on / 依赖: Q.flip, finrank_rootSpanIn
-/
lemma finrank_corootSpanIn [Q.IsValuedIn K] :
    finrank K (Q.corootSpan K) = finrank L N :=
  finrank_rootSpanIn K Q.flip

@[simp]
/--
lemma `finrank_rootSpanIn_int` / 引理 `finrank_rootSpanIn_int`

English:
lemma finrank_rootSpanIn_int
  given: [Finite ι] [CharZero L] [Q.IsCrystallographic]
  proof: by
  let _i : Module Rat M := .compHom M (algebraMap Rat L)
  let _i : Module Rat N := .compHom N (algebraMap Rat L)
  have _i : IsAddTorsionFree M := .of_isTorsionFree L M
  rw [← Submodule.finrank_span_eq_finrank_span Int Rat]; rw [← Q.finrank_rootSpanIn Rat]

@[simp]

中文:
引理 finrank_rootSpanIn_int
  条件: [Finite ι] [CharZero L] [Q.IsCrystallographic]
  证明: by
  let _i : Module Rat M := .compHom M (algebraMap Rat L)
  let _i : Module Rat N := .compHom N (algebraMap Rat L)
  have _i : IsAddTorsionFree M := .of_isTorsionFree L M
  rw [← Submodule.finrank_span_eq_finrank_span Int Rat]; rw [← Q.finrank_rootSpanIn Rat]

@[simp]

Depends on / 依赖: IsAddTorsionFree, Module, Q.finrank_rootSpanIn, Submodule, Submodule.finrank_span_eq_finrank_span, algebraMap, compHom, finrank_rootSpanIn, finrank_span_eq_finrank_span, of_isTorsionFree
-/
lemma finrank_rootSpanIn_int [Finite ι] [CharZero L] [Q.IsCrystallographic] :
    finrank Int (Q.rootSpan Int) = finrank L M := by
  let _i : Module Rat M := .compHom M (algebraMap Rat L)
  let _i : Module Rat N := .compHom N (algebraMap Rat L)
  have _i : IsAddTorsionFree M := .of_isTorsionFree L M
  rw [← Submodule.finrank_span_eq_finrank_span Int Rat]; rw [← Q.finrank_rootSpanIn Rat]

@[simp]
/--
lemma `finrank_corootSpanIn_int` / 引理 `finrank_corootSpanIn_int`

English:
lemma finrank_corootSpanIn_int
  given: [Finite ι] [CharZero L] [Q.IsCrystallographic]
  proof: Q.flip.finrank_rootSpanIn_int

中文:
引理 finrank_corootSpanIn_int
  条件: [Finite ι] [CharZero L] [Q.IsCrystallographic]
  证明: Q.flip.finrank_rootSpanIn_int

Depends on / 依赖: Q.flip.finrank_rootSpanIn_int, finrank_rootSpanIn_int
-/
lemma finrank_corootSpanIn_int [Finite ι] [CharZero L] [Q.IsCrystallographic] :
    finrank Int (Q.corootSpan Int) = finrank L N :=
  Q.flip.finrank_rootSpanIn_int

end Field

end RootPairing
