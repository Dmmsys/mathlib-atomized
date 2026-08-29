/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.Topology.Category.Profinite.Nobeling.Basic

/-!
# The zero and limit cases in the induction for Nöbeling's theorem

This file proves the zero and limit cases of the ordinal induction used in the proof of
Nöbeling's theorem. See the section docstrings for more information.

For the overall proof outline see `Mathlib/Topology/Category/Profinite/Nobeling/Basic.lean`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

@[expose] public section

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I -> Bool)) [LinearOrder I]

section Zero

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (LocallyConstant (∅ : Set (I -> Bool)) Int)
  body: subsingleton_iff.mpr (fun _ _ => LocallyConstant.ext isEmptyElim)

中文:
实例 :
  签名: 子单例 (局部常数 (∅ : 集合 (I -> 布尔值)) 整数)
  定义体: subsingleton_iff.mpr (fun _ _ => LocallyConstant.ext isEmptyElim)

Depends on / 依赖: LocallyConstant, LocallyConstant.ext, isEmptyElim, subsingleton_iff, subsingleton_iff.mpr
-/
instance : Subsingleton (LocallyConstant (∅ : Set (I -> Bool)) Int) :=
  subsingleton_iff.mpr (fun _ _ => LocallyConstant.ext isEmptyElim)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsEmpty { l // Products.isGood (∅ : Set (I -> Bool)) l }
  body: isEmpty_iff.mpr fun ⟨l, hl⟩ => hl by
    rw [subsingleton_iff.mp inferInstance (Products.eval ∅ l) 0]
    exact Submodule.zero_mem _

中文:
实例 :
  签名: 是空 { l // Products.isGood (∅ : 集合 (I -> 布尔值)) l }
  定义体: isEmpty_iff.mpr fun ⟨l, hl⟩ => hl by
    rw [subsingleton_iff.mp inferInstance (Products.eval ∅ l) 0]
    exact Submodule.zero_mem _

Depends on / 依赖: Products, Products.eval, Submodule, Submodule.zero_mem, isEmpty_iff, isEmpty_iff.mpr, subsingleton_iff, subsingleton_iff.mp, zero_mem
-/
instance : IsEmpty { l // Products.isGood (∅ : Set (I -> Bool)) l } :=
isEmpty_iff.mpr fun ⟨l, hl⟩ => hl by
    rw [subsingleton_iff.mp inferInstance (Products.eval ∅ l) 0]
    exact Submodule.zero_mem _

/--
theorem `GoodProducts.linearIndependentEmpty` / 定理 `GoodProducts.linearIndependentEmpty`

English:
theorem GoodProducts.linearIndependentEmpty
  given: {I} [LinearOrder I]
  proof: linearIndependent_empty_type

中文:
定理 GoodProducts.linearIndependentEmpty
  条件: {I} [线性序 I]
  证明: linearIndependent_empty_type

Depends on / 依赖: linearIndependent_empty_type
-/
theorem GoodProducts.linearIndependentEmpty {I} [LinearOrder I] :
    LinearIndependent Int (eval (∅ : Set (I -> Bool))) := linearIndependent_empty_type

/--
Definition of `Products.nil` / `Products.nil` 的定义

English:
definition Products.nil
  signature: : Products I
  body: ⟨[], by simp only [List.isChain_nil]⟩

中文:
定义 Products.nil
  签名: : Products I
  定义体: ⟨[], by simp only [List.isChain_nil]⟩

Depends on / 依赖: List.isChain_nil, isChain_nil
-/
def Products.nil : Products I := ⟨[], by simp only [List.isChain_nil]⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Products.lt_nil_empty` / 定理 `Products.lt_nil_empty`

English:
theorem Products.lt_nil_empty
  given: {I} [LinearOrder I]
  statement: { m : Products I | m < Products.nil } = ∅
  proof: by
  ext ⟨m, hm⟩
  refine ⟨fun h => ?_, by tauto⟩
  simp only [Set.mem_ofPred_eq, lt_iff_lex_lt, nil, List.not_lex_nil] at h

中文:
定理 Products.lt_nil_empty
  条件: {I} [线性序 I]
  结论: { m : Products I | m < Products.nil } = ∅
  证明: by
  ext ⟨m, hm⟩
  refine ⟨fun h => ?_, by tauto⟩
  simp only [Set.mem_ofPred_eq, lt_iff_lex_lt, nil, List.not_lex_nil] at h

Depends on / 依赖: List.not_lex_nil, Set.mem_ofPred_eq, lt_iff_lex_lt, mem_ofPred_eq, not_lex_nil
-/
theorem Products.lt_nil_empty {I} [LinearOrder I] : { m : Products I | m < Products.nil } = ∅ := by
  ext ⟨m, hm⟩
  refine ⟨fun h => ?_, by tauto⟩
  simp only [Set.mem_ofPred_eq, lt_iff_lex_lt, nil, List.not_lex_nil] at h

instance {α : Type*} [TopologicalSpace α] [Nonempty α] : Nontrivial (LocallyConstant α Int) :=
⟨0, 1, ne_of_apply_ne DFunLike.coe (Function.const_injective (β := Int)).ne zero_ne_one⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `Products.isGood_nil` / 定理 `Products.isGood_nil`

English:
theorem Products.isGood_nil
  given: {I} [LinearOrder I]
  proof: by
  intro h
  simp [Products.eval, Products.nil] at h

中文:
定理 Products.isGood_nil
  条件: {I} [线性序 I]
  证明: by
  intro h
  simp [Products.eval, Products.nil] at h

Depends on / 依赖: Products, Products.eval, Products.nil
-/
theorem Products.isGood_nil {I} [LinearOrder I] :
    Products.isGood ({fun _ => false} : Set (I -> Bool)) Products.nil := by
  intro h
  simp [Products.eval, Products.nil] at h

/--
theorem `Products.span_nil_eq_top` / 定理 `Products.span_nil_eq_top`

English:
theorem Products.span_nil_eq_top
  given: {I} [LinearOrder I]
  proof: by
  rw [Set.image_singleton]; rw [eq_top_iff]
  intro f _
  rw [Submodule.mem_span_singleton]
  refine ⟨f default, ?_⟩
  simp only [eval, List.map, List.prod_nil, zsmul_eq_mul, mul_one, Products.nil]
  ext x
  obtain rfl : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
  rfl

中文:
定理 Products.span_nil_eq_top
  条件: {I} [线性序 I]
  证明: by
  rw [Set.image_singleton]; rw [eq_top_iff]
  intro f _
  rw [Submodule.mem_span_singleton]
  refine ⟨f default, ?_⟩
  simp only [eval, List.map, List.prod_nil, zsmul_eq_mul, mul_one, Products.nil]
  ext x
  obtain rfl : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
  rfl

Depends on / 依赖: List.map, List.prod_nil, Products, Products.nil, Set.default_coe_singleton, Set.image_singleton, Submodule, Submodule.mem_span_singleton, default_coe_singleton, eq_iff_true_of_subsingleton, eq_top_iff, image_singleton, mem_span_singleton, mul_one, prod_nil, zsmul_eq_mul
-/
theorem Products.span_nil_eq_top {I} [LinearOrder I] :
    Submodule.span Int (eval ({fun _ => false} : Set (I -> Bool)) '' {nil}) = ⊤ := by
  rw [Set.image_singleton]; rw [eq_top_iff]
  intro f _
  rw [Submodule.mem_span_singleton]
  refine ⟨f default, ?_⟩
  simp only [eval, List.map, List.prod_nil, zsmul_eq_mul, mul_one, Products.nil]
  ext x
  obtain rfl : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- There is a unique `GoodProducts` for the singleton `{fun _ ↦ false}`. -/
noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique { l // Products.isGood ({fun _ => false} : Set (I -> Bool)) l }
  body: ⟨Products.nil, Products.isGood_nil⟩
  uniq := by
    intro ⟨⟨l, hl⟩, hll⟩
    ext
    apply Subtype.ext
    apply (List.lex_nil_or_eq_nil l (r := (· < ·))).resolve_left
    intro _
    apply hll
    have he : {Products.nil} subseteq {m | m < ⟨l,hl⟩} := by
      simpa only [Products.nil, Products.lt_iff_lex_lt, Set.singleton_subset_iff, Set.mem_ofPred_eq]
    grw [← he]
    rw [Products.span_nil_eq_top]
    exact Submodule.mem_top

中文:
实例 :
  签名: 唯一 { l // Products.isGood ({fun _ => false} : 集合 (I -> 布尔值)) l }
  定义体: ⟨Products.nil, Products.isGood_nil⟩
  uniq := by
    intro ⟨⟨l, hl⟩, hll⟩
    ext
    apply Subtype.ext
    apply (List.lex_nil_or_eq_nil l (r := (· < ·))).resolve_left
    intro _
    apply hll
    have he : {Products.nil} subseteq {m | m < ⟨l,hl⟩} := by
      simpa only [Products.nil, Products.lt_iff_lex_lt, Set.singleton_subset_iff, Set.mem_ofPred_eq]
    grw [← he]
    rw [Products.span_nil_eq_top]
    exact Submodule.mem_top

Depends on / 依赖: Products, Products.isGood_nil, Products.nil, isGood_nil
-/
instance : Unique { l // Products.isGood ({fun _ => false} : Set (I -> Bool)) l } where
  default := ⟨Products.nil, Products.isGood_nil⟩
  uniq := by
    intro ⟨⟨l, hl⟩, hll⟩
    ext
    apply Subtype.ext
    apply (List.lex_nil_or_eq_nil l (r := (· < ·))).resolve_left
    intro _
    apply hll
    have he : {Products.nil} subseteq {m | m < ⟨l,hl⟩} := by
      simpa only [Products.nil, Products.lt_iff_lex_lt, Set.singleton_subset_iff, Set.mem_ofPred_eq]
    grw [← he]
    rw [Products.span_nil_eq_top]
    exact Submodule.mem_top

instance (α : Type*) [TopologicalSpace α] : IsAddTorsionFree (LocallyConstant α Int) :=
  LocallyConstant.coe_injective.isAddTorsionFree LocallyConstant.coeFnAddMonoidHom

/--
theorem `GoodProducts.linearIndependentSingleton` / 定理 `GoodProducts.linearIndependentSingleton`

English:
theorem GoodProducts.linearIndependentSingleton
  given: {I} [LinearOrder I]
  proof: .of_subsingleton default by simp [eval, Products.eval, Products.nil, default]

中文:
定理 GoodProducts.linearIndependentSingleton
  条件: {I} [线性序 I]
  证明: .of_subsingleton default by simp [eval, Products.eval, Products.nil, default]

Depends on / 依赖: Products, Products.eval, Products.nil, of_subsingleton
-/
theorem GoodProducts.linearIndependentSingleton {I} [LinearOrder I] :
    LinearIndependent Int (eval ({fun _ => false} : Set (I -> Bool))) :=
.of_subsingleton default by simp [eval, Products.eval, Products.nil, default]

end Zero

variable [WellFoundedLT I]

section Limit
/-!
## The limit case of the induction

We relate linear independence in `LocallyConstant (π C (ord I · < o')) ℤ` with linear independence
in `LocallyConstant C ℤ`, where `contained C o` and `o' < o`.

When `o` is a limit ordinal, we prove that the good products in `LocallyConstant C ℤ` are linearly
independent if and only if a certain directed union is linearly independent. Each term in this
directed union is in bijection with the good products w.r.t. `π C (ord I · < o')` for an ordinal
`o' < o`, and these are linearly independent by the inductive hypothesis.

### Main definitions

* `GoodProducts.smaller` is the image of good products coming from a smaller ordinal.

* `GoodProducts.range_equiv`: The image of the `GoodProducts` in `C` is equivalent to the union of
  `smaller C o'` over all ordinals `o' < o`.

### Main results

* `Products.limitOrdinal`: for `o` a limit ordinal such that `contained C o`, a product `l` is good
  w.r.t. `C` iff it there exists an ordinal `o' < o` such that `l` is good w.r.t.
  `π C (ord I · < o')`.

* `GoodProducts.linearIndependent_iff_union_smaller` is the result mentioned above, that the good
  products are linearly independent iff a directed union is.
-/

namespace GoodProducts

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `smaller` / `smaller` 的定义

English:
definition smaller
  signature: (o : Ordinal)
  body: (πs C o) '' (range (π C (ord I · < o)))

中文:
定义 smaller
  签名: (o : 序数)
  定义体: (πs C o) '' (range (π C (ord I · < o)))
-/
noncomputable def smaller (o : Ordinal) : Set (LocallyConstant C Int) :=
  (πs C o) '' (range (π C (ord I · < o)))

/--
The map from the image of the `GoodProducts` in `LocallyConstant (π C (ord I · < o)) ℤ` to
`smaller C o`
-/
noncomputable
/--
Definition of `range_equiv_smaller_toFun` / `range_equiv_smaller_toFun` 的定义

English:
definition range_equiv_smaller_toFun
  signature: (o : Ordinal) (x : range (π C (ord I · < o)))
  body: ⟨πs C o ↑x, x.val, x.property, rfl⟩

中文:
定义 range_equiv_smaller_toFun
  签名: (o : 序数) (x : range (π C (ord I · < o)))
  定义体: ⟨πs C o ↑x, x.val, x.property, rfl⟩

Depends on / 依赖: property, x.property, x.val
-/
def range_equiv_smaller_toFun (o : Ordinal) (x : range (π C (ord I · < o))) : smaller C o :=
  ⟨πs C o ↑x, x.val, x.property, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `range_equiv_smaller_toFun_bijective` / 定理 `range_equiv_smaller_toFun_bijective`

English:
theorem range_equiv_smaller_toFun_bijective
  given: (o : Ordinal)
  proof: by
  dsimp +unfoldPartialApp [range_equiv_smaller_toFun]
  refine ⟨fun a b hab => ?_, fun ⟨a, b, hb⟩ => ?_⟩
  · ext1
    simp only [Subtype.mk.injEq] at hab
    exact injective_πs C o hab
  · use ⟨b, hb.1⟩
    simpa only [Subtype.mk.injEq] using hb.2

中文:
定理 range_equiv_smaller_toFun_bijective
  条件: (o : 序数)
  证明: by
  dsimp +unfoldPartialApp [range_equiv_smaller_toFun]
  refine ⟨fun a b hab => ?_, fun ⟨a, b, hb⟩ => ?_⟩
  · ext1
    simp only [Subtype.mk.injEq] at hab
    exact injective_πs C o hab
  · use ⟨b, hb.1⟩
    simpa only [Subtype.mk.injEq] using hb.2

Depends on / 依赖: Subtype, Subtype.mk.injEq, range_equiv_smaller_toFun, unfoldPartialApp
-/
theorem range_equiv_smaller_toFun_bijective (o : Ordinal) :
    Function.Bijective (range_equiv_smaller_toFun C o) := by
  dsimp +unfoldPartialApp [range_equiv_smaller_toFun]
  refine ⟨fun a b hab => ?_, fun ⟨a, b, hb⟩ => ?_⟩
  · ext1
    simp only [Subtype.mk.injEq] at hab
    exact injective_πs C o hab
  · use ⟨b, hb.1⟩
    simpa only [Subtype.mk.injEq] using hb.2

/--
The equivalence from the image of the `GoodProducts` in `LocallyConstant (π C (ord I · < o)) ℤ` to
`smaller C o`
-/
noncomputable
/--
Definition of `range_equiv_smaller` / `range_equiv_smaller` 的定义

English:
definition range_equiv_smaller
  signature: (o : Ordinal)
  body: Equiv.ofBijective (range_equiv_smaller_toFun C o) (range_equiv_smaller_toFun_bijective C o)

中文:
定义 range_equiv_smaller
  签名: (o : 序数)
  定义体: Equiv.ofBijective (range_equiv_smaller_toFun C o) (range_equiv_smaller_toFun_bijective C o)

Depends on / 依赖: Equiv.ofBijective, ofBijective, range_equiv_smaller_toFun, range_equiv_smaller_toFun_bijective
-/
def range_equiv_smaller (o : Ordinal) : range (π C (ord I · < o)) ≃ smaller C o :=
  Equiv.ofBijective (range_equiv_smaller_toFun C o) (range_equiv_smaller_toFun_bijective C o)

/--
theorem `smaller_factorization` / 定理 `smaller_factorization`

English:
theorem smaller_factorization
  given: (o : Ordinal)
  proof: by rfl

中文:
定理 smaller_factorization
  条件: (o : 序数)
  证明: by rfl
-/
theorem smaller_factorization (o : Ordinal) :
    (fun (p : smaller C o) => p.1) ∘ (range_equiv_smaller C o).toFun =
    (πs C o) ∘ (fun (p : range (π C (ord I · < o))) => p.1) := by rfl

/--
theorem `linearIndependent_iff_smaller` / 定理 `linearIndependent_iff_smaller`

English:
theorem linearIndependent_iff_smaller
  given: (o : Ordinal)
  proof: by
  rw [GoodProducts.linearIndependent_iff_range]; rw [← LinearMap.linearIndependent_iff (πs C o)
    (LinearMap.ker_eq_bot_of_injective (injective_πs _ _))]; rw [← smaller_factorization C o]
  exact linearIndependent_equiv _

中文:
定理 linearIndependent_iff_smaller
  条件: (o : 序数)
  证明: by
  rw [GoodProducts.linearIndependent_iff_range]; rw [← LinearMap.linearIndependent_iff (πs C o)
    (LinearMap.ker_eq_bot_of_injective (injective_πs _ _))]; rw [← smaller_factorization C o]
  exact linearIndependent_equiv _

Depends on / 依赖: GoodProducts, GoodProducts.linearIndependent_iff_range, LinearMap, LinearMap.ker_eq_bot_of_injective, LinearMap.linearIndependent_iff, ker_eq_bot_of_injective, linearIndependent_equiv, linearIndependent_iff, linearIndependent_iff_range, smaller_factorization
-/
theorem linearIndependent_iff_smaller (o : Ordinal) :
    LinearIndependent Int (GoodProducts.eval (π C (ord I · < o))) ↔
    LinearIndependent Int (fun (p : smaller C o) => p.1) := by
  rw [GoodProducts.linearIndependent_iff_range]; rw [← LinearMap.linearIndependent_iff (πs C o)
    (LinearMap.ker_eq_bot_of_injective (injective_πs _ _))]; rw [← smaller_factorization C o]
  exact linearIndependent_equiv _

/--
theorem `smaller_mono` / 定理 `smaller_mono`

English:
theorem smaller_mono
  given: {o₁ o₂ : Ordinal} (h : o₁ <= o₂)
  statement: smaller C o₁ subseteq smaller C o₂
  proof: by
  rintro f ⟨g, hg, rfl⟩
  simp only [smaller, Set.mem_image]
  use πs' C h g
  obtain ⟨⟨l, gl⟩, rfl⟩ := hg
  refine ⟨?_, ?_⟩
  · use ⟨l, Products.isGood_mono C h gl⟩
    ext x
    rw [eval]; rw [← Products.eval_πs' _ h (Products.prop_of_isGood C _ gl)]; rw [eval]
  · rw [← LocallyConstant.coe_inj, coe_πs C o₂, ← LocallyConstant.toFun_eq_coe, coe_πs',
      Function.comp_assoc, projRestricts_comp_projRestrict C _, coe_πs]
    rfl

中文:
定理 smaller_mono
  条件: {o₁ o₂ : 序数} (h : o₁ <= o₂)
  结论: smaller C o₁ subseteq smaller C o₂
  证明: by
  rintro f ⟨g, hg, rfl⟩
  simp only [smaller, Set.mem_image]
  use πs' C h g
  obtain ⟨⟨l, gl⟩, rfl⟩ := hg
  refine ⟨?_, ?_⟩
  · use ⟨l, Products.isGood_mono C h gl⟩
    ext x
    rw [eval]; rw [← Products.eval_πs' _ h (Products.prop_of_isGood C _ gl)]; rw [eval]
  · rw [← LocallyConstant.coe_inj, coe_πs C o₂, ← LocallyConstant.toFun_eq_coe, coe_πs',
      Function.comp_assoc, projRestricts_comp_projRestrict C _, coe_πs]
    rfl

Depends on / 依赖: Function, Function.comp_assoc, LocallyConstant, LocallyConstant.coe_inj, LocallyConstant.toFun_eq_coe, Products, Products.eval_, Products.isGood_mono, Products.prop_of_isGood, Set.mem_image, coe_inj, comp_assoc, isGood_mono, mem_image, projRestricts_comp_projRestrict, prop_of_isGood, smaller, toFun_eq_coe
-/
theorem smaller_mono {o₁ o₂ : Ordinal} (h : o₁ <= o₂) : smaller C o₁ subseteq smaller C o₂ := by
  rintro f ⟨g, hg, rfl⟩
  simp only [smaller, Set.mem_image]
  use πs' C h g
  obtain ⟨⟨l, gl⟩, rfl⟩ := hg
  refine ⟨?_, ?_⟩
  · use ⟨l, Products.isGood_mono C h gl⟩
    ext x
    rw [eval]; rw [← Products.eval_πs' _ h (Products.prop_of_isGood C _ gl)]; rw [eval]
  · rw [← LocallyConstant.coe_inj, coe_πs C o₂, ← LocallyConstant.toFun_eq_coe, coe_πs',
      Function.comp_assoc, projRestricts_comp_projRestrict C _, coe_πs]
    rfl

end GoodProducts

variable {o : Ordinal} (ho : Order.IsSuccLimit o)
include ho

/--
theorem `Products.limitOrdinal` / 定理 `Products.limitOrdinal`

English:
theorem Products.limitOrdinal
  given: (l : Products I)
  statement: l.isGood (π C (ord I · < o)) ↔
  proof: by
  refine ⟨fun h => ?_, fun ⟨o', ⟨ho', hl⟩⟩ => isGood_mono C (le_of_lt ho') hl⟩
  use Finset.sup l.val.toFinset (fun a => Order.succ (ord I a))
  have hslt : Finset.sup l.val.toFinset (fun a => Order.succ (ord I a)) < o := by
    simp only [Finset.sup_lt_iff ho.bot_lt, List.mem_toFinset]
    exact fun b hb => ho.succ_lt (prop_of_isGood C (ord I · < o) h b hb)
  refine ⟨hslt, fun he => h ?_⟩
  have hlt : forall i in l.val, ord I i < Finset.sup l.val.toFinset (fun a => Order.succ (ord I a)) := by
    intro i hi
    simp only [Finset.lt_sup_iff, List.mem_toFinset, Order.lt_succ_iff]
    exact ⟨i, hi, le_rfl⟩
  rwa [eval_πs_image' C (le_of_lt hslt) hlt, ← eval_πs' C (le_of_lt hslt) hlt,
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C _)]

中文:
定理 Products.limitOrdinal
  条件: (l : Products I)
  结论: l.isGood (π C (ord I · < o)) ↔
  证明: by
  refine ⟨fun h => ?_, fun ⟨o', ⟨ho', hl⟩⟩ => isGood_mono C (le_of_lt ho') hl⟩
  use Finset.sup l.val.toFinset (fun a => Order.succ (ord I a))
  have hslt : Finset.sup l.val.toFinset (fun a => Order.succ (ord I a)) < o := by
    simp only [Finset.sup_lt_iff ho.bot_lt, List.mem_toFinset]
    exact fun b hb => ho.succ_lt (prop_of_isGood C (ord I · < o) h b hb)
  refine ⟨hslt, fun he => h ?_⟩
  have hlt : forall i in l.val, ord I i < Finset.sup l.val.toFinset (fun a => Order.succ (ord I a)) := by
    intro i hi
    simp only [Finset.lt_sup_iff, List.mem_toFinset, Order.lt_succ_iff]
    exact ⟨i, hi, le_rfl⟩
  rwa [eval_πs_image' C (le_of_lt hslt) hlt, ← eval_πs' C (le_of_lt hslt) hlt,
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C _)]

Depends on / 依赖: Finset, Finset.sup, Finset.sup_lt_iff, List.mem_toFinset, Order.succ, bot_lt, ho.bot_lt, ho.succ_lt, isGood_mono, l.val, l.val.toFinset, le_of_lt, mem_toFinset, prop_of_isGood, succ_lt, sup_lt_iff, toFinset
-/
theorem Products.limitOrdinal (l : Products I) : l.isGood (π C (ord I · < o)) ↔
    exists (o' : Ordinal), o' < o ∧ l.isGood (π C (ord I · < o')) := by
  refine ⟨fun h => ?_, fun ⟨o', ⟨ho', hl⟩⟩ => isGood_mono C (le_of_lt ho') hl⟩
  use Finset.sup l.val.toFinset (fun a => Order.succ (ord I a))
  have hslt : Finset.sup l.val.toFinset (fun a => Order.succ (ord I a)) < o := by
    simp only [Finset.sup_lt_iff ho.bot_lt, List.mem_toFinset]
    exact fun b hb => ho.succ_lt (prop_of_isGood C (ord I · < o) h b hb)
  refine ⟨hslt, fun he => h ?_⟩
  have hlt : forall i in l.val, ord I i < Finset.sup l.val.toFinset (fun a => Order.succ (ord I a)) := by
    intro i hi
    simp only [Finset.lt_sup_iff, List.mem_toFinset, Order.lt_succ_iff]
    exact ⟨i, hi, le_rfl⟩
  rwa [eval_πs_image' C (le_of_lt hslt) hlt, ← eval_πs' C (le_of_lt hslt) hlt,
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C _)]

variable (hsC : contained C o)
include hsC

/--
theorem `GoodProducts.union` / 定理 `GoodProducts.union`

English:
theorem GoodProducts.union
  statement: range C = ⋃ (e : {o' // o' < o}), (smaller C e.val)
  proof: by
  ext p
  simp only [smaller, range, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := hp
    rw [contained_eq_proj C o hsC]; rw [Products.limitOrdinal C ho] at hl
    obtain ⟨o', ho'⟩ := hl
    refine ⟨o', ho'.1, eval (π C (ord I · < o')) ⟨l, ho'.2⟩, ⟨l, ho'.2, rfl⟩, ?_⟩
    exact Products.eval_πs C (Products.prop_of_isGood C _ ho'.2)
  · obtain ⟨o', h, _, ⟨l, hl, rfl⟩, rfl⟩ := hp
    refine ⟨l, ?_, (Products.eval_πs C (Products.prop_of_isGood C _ hl)).symm⟩
    rw [contained_eq_proj C o hsC]
    exact Products.isGood_mono C (le_of_lt h) hl

中文:
定理 GoodProducts.union
  结论: range C = ⋃ (e : {o' // o' < o}), (smaller C e.val)
  证明: by
  ext p
  simp only [smaller, range, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := hp
    rw [contained_eq_proj C o hsC]; rw [Products.limitOrdinal C ho] at hl
    obtain ⟨o', ho'⟩ := hl
    refine ⟨o', ho'.1, eval (π C (ord I · < o')) ⟨l, ho'.2⟩, ⟨l, ho'.2, rfl⟩, ?_⟩
    exact Products.eval_πs C (Products.prop_of_isGood C _ ho'.2)
  · obtain ⟨o', h, _, ⟨l, hl, rfl⟩, rfl⟩ := hp
    refine ⟨l, ?_, (Products.eval_πs C (Products.prop_of_isGood C _ hl)).symm⟩
    rw [contained_eq_proj C o hsC]
    exact Products.isGood_mono C (le_of_lt h) hl

Depends on / 依赖: Products, Products.eval_, Products.limitOrdinal, Products.prop_of_isGood, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype, Subtype.exists, contained_eq_proj, limitOrdinal, mem_iUnion, mem_image, mem_range, prop_of_isGood, smaller
-/
theorem GoodProducts.union : range C = ⋃ (e : {o' // o' < o}), (smaller C e.val) := by
  ext p
  simp only [smaller, range, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · obtain ⟨l, hl, rfl⟩ := hp
    rw [contained_eq_proj C o hsC]; rw [Products.limitOrdinal C ho] at hl
    obtain ⟨o', ho'⟩ := hl
    refine ⟨o', ho'.1, eval (π C (ord I · < o')) ⟨l, ho'.2⟩, ⟨l, ho'.2, rfl⟩, ?_⟩
    exact Products.eval_πs C (Products.prop_of_isGood C _ ho'.2)
  · obtain ⟨o', h, _, ⟨l, hl, rfl⟩, rfl⟩ := hp
    refine ⟨l, ?_, (Products.eval_πs C (Products.prop_of_isGood C _ hl)).symm⟩
    rw [contained_eq_proj C o hsC]
    exact Products.isGood_mono C (le_of_lt h) hl

-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Definition of `GoodProducts.range_equiv` / `GoodProducts.range_equiv` 的定义

English:
definition GoodProducts.range_equiv
  signature: : range C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val)
  body: Equiv.setCongr (union C ho hsC)

中文:
定义 GoodProducts.range_equiv
  签名: : range C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val)
  定义体: Equiv.setCongr (union C ho hsC)

Depends on / 依赖: Equiv.setCongr, setCongr
-/
noncomputable def GoodProducts.range_equiv : range C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val) :=
  Equiv.setCongr (union C ho hsC)

/--
theorem `GoodProducts.range_equiv_factorization` / 定理 `GoodProducts.range_equiv_factorization`

English:
theorem GoodProducts.range_equiv_factorization
  proof: rfl

中文:
定理 GoodProducts.range_equiv_factorization
  证明: rfl
-/
theorem GoodProducts.range_equiv_factorization :
    (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) => p.1) ∘ (range_equiv C ho hsC).toFun =
    (fun (p : range C) => (p.1 : LocallyConstant C Int)) := rfl

/--
theorem `GoodProducts.linearIndependent_iff_union_smaller` / 定理 `GoodProducts.linearIndependent_iff_union_smaller`

English:
theorem GoodProducts.linearIndependent_iff_union_smaller
  proof: by
  rw [GoodProducts.linearIndependent_iff_range]; rw [← range_equiv_factorization C ho hsC]
  exact linearIndependent_equiv (range_equiv C ho hsC)

中文:
定理 GoodProducts.linearIndependent_iff_union_smaller
  证明: by
  rw [GoodProducts.linearIndependent_iff_range]; rw [← range_equiv_factorization C ho hsC]
  exact linearIndependent_equiv (range_equiv C ho hsC)

Depends on / 依赖: GoodProducts, GoodProducts.linearIndependent_iff_range, linearIndependent_equiv, linearIndependent_iff_range, range_equiv, range_equiv_factorization
-/
theorem GoodProducts.linearIndependent_iff_union_smaller :
    LinearIndependent Int (GoodProducts.eval C) ↔
      LinearIndependent Int (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) => p.1) := by
  rw [GoodProducts.linearIndependent_iff_range]; rw [← range_equiv_factorization C ho hsC]
  exact linearIndependent_equiv (range_equiv C ho hsC)

end Limit

end Profinite.NobelingProof
