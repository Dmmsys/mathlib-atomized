/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.LinearAlgebra.PerfectPairing.Restrict
public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Base change for root pairings

When the coefficients are a field, root pairings behave well with respect to restriction and
extension of scalars.

## Main results:
* `RootPairing.restrict`: if `RootPairing.pairing` takes values in a subfield, we may restrict to
  get a root _system_ with coefficients in the subfield. Of particular interest is the case when
  the pairing takes values in its prime subfield (which happens for crystallographic pairings).

## TODO

* Extension of scalars
* Crystallographic root systems are isomorphic to base changes of root systems over `ℤ`: Take
  `M₀` and `N₀` to be the `ℤ`-span of roots and coroots.

-/

@[expose] public section

noncomputable section

open Set Function
open Submodule (span injective_subtype span subset_span span_setOfPred_mem_eq_top)

namespace RootPairing

/--
Definition of `IsBalanced` / `IsBalanced` 的定义

English:
class IsBalanced
  parameters: {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]
  axioms and operations (1):
    - isPerfectCompl : P.toLinearMap.IsPerfectCompl (P.rootSpan R) (P.corootSpan R)

中文:
类 IsBalanced
  参数: {ι R M N : 类型} [AddCommGroup M] [AddCommGroup N]
  公理与运算 (1 个):
    - isPerfectCompl : P.toLinearMap.IsPerfectCompl (P.rootSpan R) (P.corootSpan R)
-/
class IsBalanced {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N) : Prop where
  isPerfectCompl : P.toLinearMap.IsPerfectCompl (P.rootSpan R) (P.corootSpan R)

instance {ι R M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [CommRing R] [Module R M] [Module R N] (P : RootPairing ι R M N) [P.IsRootSystem] :
    P.IsBalanced where
  isPerfectCompl := by simp

variable {ι L M N : Type*}
  [Field L] [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  (P : RootPairing ι L M N)

section restrictScalars

variable (K : Type*) [Field K] [Algebra K L]
  [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  [P.IsBalanced]

section SubfieldValued

variable [P.IsValuedIn K]

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `restrictScalars'` / `restrictScalars'` 的定义

English:
definition restrictScalars'
  signature: :
  body: .restrictScalarsRange₂ (R := L)
    (span K (range P.root)).subtype (span K (range P.coroot)).subtype (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) P.toLinearMap fun x y =>
      P.toLinearMap_apply_apply_mem_range_algebraMap K x x.property y y.property
  isPerfPair_toLinearMap

中文:
定义 restrictScalars'
  签名: :
  定义体: .restrictScalarsRange₂ (R := L)
    (span K (range P.root)).subtype (span K (range P.coroot)).subtype (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) P.toLinearMap fun x y =>
      P.toLinearMap_apply_apply_mem_range_algebraMap K x x.property y y.property
  isPerfPair_toLinearMap
-/
def restrictScalars' :
    RootPairing ι K (span K (range P.root)) (span K (range P.coroot)) where
  toLinearMap := .restrictScalarsRange₂ (R := L)
    (span K (range P.root)).subtype (span K (range P.coroot)).subtype (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) P.toLinearMap fun x y =>
      P.toLinearMap_apply_apply_mem_range_algebraMap K x x.property y y.property
  isPerfPair_toLinearMap := .restrictScalars_of_field P.toLinearMap _ _
    (injective_subtype _) (injective_subtype _) (by simpa using IsBalanced.isPerfectCompl) _
  root := ⟨fun i => ⟨_, subset_span (mem_range_self i)⟩, fun i j h => by simpa using h⟩
  coroot := ⟨fun i => ⟨_, subset_span (mem_range_self i)⟩, fun i j h => by simpa using h⟩
  root_coroot_two i := by
    have : algebraMap K L 2 = 2 := by
      rw [← Int.cast_two (R := K)]; rw [← Int.cast_two (R := L)]; rw [map_intCast]
exact FaithfulSMul.algebraMap_injective K L by simp [this]
  reflectionPerm := P.reflectionPerm
  reflectionPerm_root i j := by
    ext; simpa [algebra_compatible_smul L] using P.reflectionPerm_root i j
  reflectionPerm_coroot i j := by
    ext; simpa [algebra_compatible_smul L] using P.reflectionPerm_coroot i j

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (P.restrictScalars' K).IsRootSystem
  body: by
    rw [← span_setOfPred_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp [restrictScalars']
  span_coroot_eq_top := by
    rw [← span_setOfPred_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp [restrictScalars']

中文:
实例 :
  签名: (P.restrictScalars' K).IsRootSystem
  定义体: by
    rw [← span_setOfPred_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp [restrictScalars']
  span_coroot_eq_top := by
    rw [← span_setOfPred_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp [restrictScalars']

Depends on / 依赖: restrictScalars, span_coroot_eq_top, span_setOfPred_mem_eq_top
-/
instance : (P.restrictScalars' K).IsRootSystem where
  span_root_eq_top := by
    rw [← span_setOfPred_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp [restrictScalars']
  span_coroot_eq_top := by
    rw [← span_setOfPred_mem_eq_top]
    congr
    ext ⟨x, hx⟩
    simp [restrictScalars']

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `restrictScalars_toLinearMap_apply_apply` / 引理 `restrictScalars_toLinearMap_apply_apply`

English:
lemma restrictScalars_toLinearMap_apply_apply
  proof: by
  simp [restrictScalars']

中文:
引理 restrictScalars_toLinearMap_apply_apply
  证明: by
  simp [restrictScalars']
-/
@[simp] lemma restrictScalars_toLinearMap_apply_apply
    (x : span K (range P.root)) (y : span K (range P.coroot)) :
    algebraMap K L ((P.restrictScalars' K).toLinearMap x y) = P.toLinearMap x y := by
  simp [restrictScalars']

/--
lemma `restrictScalars_coe_root` / 引理 `restrictScalars_coe_root`

English:
lemma restrictScalars_coe_root
  given: (i : ι)
  proof: rfl

中文:
引理 restrictScalars_coe_root
  条件: (i : ι)
  证明: rfl
-/
@[simp] lemma restrictScalars_coe_root (i : ι) :
    (P.restrictScalars' K).root i = P.root i :=
  rfl

/--
lemma `restrictScalars_coe_coroot` / 引理 `restrictScalars_coe_coroot`

English:
lemma restrictScalars_coe_coroot
  given: (i : ι)
  proof: rfl

中文:
引理 restrictScalars_coe_coroot
  条件: (i : ι)
  证明: rfl
-/
@[simp] lemma restrictScalars_coe_coroot (i : ι) :
    (P.restrictScalars' K).coroot i = P.coroot i :=
  rfl

/--
lemma `restrictScalars_pairing` / 引理 `restrictScalars_pairing`

English:
lemma restrictScalars_pairing
  given: (i j : ι)
  proof: by
  simp only [pairing, restrictScalars_toLinearMap_apply_apply, restrictScalars_coe_root,
    restrictScalars_coe_coroot]

中文:
引理 restrictScalars_pairing
  条件: (i j : ι)
  证明: by
  simp only [pairing, restrictScalars_toLinearMap_apply_apply, restrictScalars_coe_root,
    restrictScalars_coe_coroot]
-/
@[simp] lemma restrictScalars_pairing (i j : ι) :
    algebraMap K L ((P.restrictScalars' K).pairing i j) = P.pairing i j := by
  simp only [pairing, restrictScalars_toLinearMap_apply_apply, restrictScalars_coe_root,
    restrictScalars_coe_coroot]

end SubfieldValued

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
abbreviation restrictScalars
  signature: [P.IsCrystallographic]
  body: have := IsValuedIn.trans P K Int
  P.restrictScalars' K

中文:
缩写 restrictScalars
  签名: [P.IsCrystallographic]
  定义体: have := IsValuedIn.trans P K Int
  P.restrictScalars' K

Depends on / 依赖: IsValuedIn, IsValuedIn.trans, P.restrictScalars, restrictScalars
-/
abbrev restrictScalars [P.IsCrystallographic] :
    RootPairing ι K (span K (range P.root)) (span K (range P.coroot)) :=
  have := IsValuedIn.trans P K Int
  P.restrictScalars' K

/--
Definition of `restrictScalarsRat` / `restrictScalarsRat` 的定义

English:
abbreviation restrictScalarsRat
  signature: [CharZero L] [P.IsCrystallographic]
  body: let _i : Module Rat M := Module.compHom M (algebraMap Rat L)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat L)
  P.restrictScalars Rat

中文:
缩写 restrictScalarsRat
  签名: [CharZero L] [P.IsCrystallographic]
  定义体: let _i : Module Rat M := Module.compHom M (algebraMap Rat L)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat L)
  P.restrictScalars Rat

Depends on / 依赖: Module, Module.compHom, P.restrictScalars, algebraMap, compHom, restrictScalars
-/
abbrev restrictScalarsRat [CharZero L] [P.IsCrystallographic] :=
  let _i : Module Rat M := Module.compHom M (algebraMap Rat L)
  let _i : Module Rat N := Module.compHom N (algebraMap Rat L)
  P.restrictScalars Rat

end restrictScalars

end RootPairing
