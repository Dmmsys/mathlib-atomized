/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau
-/
module

public import Mathlib.Algebra.Group.Submonoid.BigOperators
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# `DFinsupp` and submonoids

This file mainly concerns the interaction between submonoids and products/sums of `DFinsupp`s.

## Main results

* `AddSubmonoid.mem_iSup_iff_exists_dfinsupp`: elements of the supremum of additive commutative
  monoids can be given by taking finite sums of elements of each monoid.
* `AddSubmonoid.mem_bsupr_iff_exists_dfinsupp`: elements of the supremum of additive commutative
  monoids can be given by taking finite sums of elements of each monoid.
-/

public section


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

variable {ι : Type u} {γ : Type w} {β : ι -> Type v} {β₁ : ι -> Type v₁} {β₂ : ι -> Type v₂}

open DFinsupp

variable [DecidableEq ι]

@[to_additive]
/--
theorem `dfinsuppProd_mem` / 定理 `dfinsuppProd_mem`

English:
theorem dfinsuppProd_mem
  statement: [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
  proof: prod_mem fun _ hi => h _ mem_support_iff.1 hi

中文:
定理 dfinsuppProd_mem
  结论: [对任意 i, Zero (β i)] [对任意 (i) (x : β i), Decidable (x != 0)]
  证明: prod_mem fun _ hi => h _ mem_support_iff.1 hi

Depends on / 依赖: mem_support_iff, prod_mem
-/
theorem dfinsuppProd_mem [forall i, Zero (β i)] [forall (i) (x : β i), Decidable (x != 0)]
    [CommMonoid γ] {S : Type*} [SetLike S γ] [SubmonoidClass S γ]
    (s : S) (f : Π₀ i, β i) (g : forall i, β i -> γ)
    (h : forall c, f c != 0 -> g c (f c) in s) : f.prod g in s :=
prod_mem fun _ hi => h _ mem_support_iff.1 hi

/--
theorem `dfinsuppSumAddHom_mem` / 定理 `dfinsuppSumAddHom_mem`

English:
theorem dfinsuppSumAddHom_mem
  statement: [forall i, AddZeroClass (β i)] [AddCommMonoid γ] {S : Type*}
  proof: by
  classical
    rw [DFinsupp.sumAddHom_apply]
    exact dfinsuppSum_mem s f (g ·) h

中文:
定理 dfinsuppSumAddHom_mem
  结论: [对任意 i, AddZeroClass (β i)] [AddCommMonoid γ] {S : 类型}
  证明: by
  classical
    rw [DFinsupp.sumAddHom_apply]
    exact dfinsuppSum_mem s f (g ·) h

Depends on / 依赖: DFinsupp, DFinsupp.sumAddHom_apply, classical, dfinsuppSum_mem, sumAddHom_apply
-/
theorem dfinsuppSumAddHom_mem [forall i, AddZeroClass (β i)] [AddCommMonoid γ] {S : Type*}
    [SetLike S γ] [AddSubmonoidClass S γ] (s : S) (f : Π₀ i, β i) (g : forall i, β i ->+ γ)
    (h : forall c, f c != 0 -> g c (f c) in s) : DFinsupp.sumAddHom g f in s := by
  classical
    rw [DFinsupp.sumAddHom_apply]
    exact dfinsuppSum_mem s f (g ·) h

/--
theorem `AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom` / 定理 `AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom`

English:
theorem AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom
  proof: by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup S i : S i <= _) (v i).prop

中文:
定理 AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom
  证明: by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup S i : S i <= _) (v i).prop

Depends on / 依赖: DFinsupp, DFinsupp.single, DFinsupp.sumAddHom_single, dfinsuppSumAddHom_mem, iSup_le, le_antisymm, le_iSup, single, sumAddHom_single
-/
theorem AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom
    [AddCommMonoid γ] (S : ι -> AddSubmonoid γ) :
    iSup S = AddMonoidHom.mrange (DFinsupp.sumAddHom fun i => (S i).subtype) := by
  apply le_antisymm
  · apply iSup_le _
    intro i y hy
    exact ⟨DFinsupp.single i ⟨y, hy⟩, DFinsupp.sumAddHom_single _ _ _⟩
  · rintro x ⟨v, rfl⟩
    exact dfinsuppSumAddHom_mem _ v _ fun i _ => (le_iSup S i : S i <= _) (v i).prop

/--
theorem `AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom` / 定理 `AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom`

English:
theorem AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom
  statement: (p : ι -> Prop) [DecidablePred p]
  proof: by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [AddMonoidHom.comp_apply]; rw [filterAddMonoidHom_apply]; rw [filter_single_pos _ _ hi]
    exact sumAddHom_single _ _ _
  · rintro x ⟨v, rfl⟩
    refine dfinsuppSumAddHom_mem _ _ _ fun i _ => ?_
    r

中文:
定理 AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom
  结论: (p : ι -> 命题) [DecidablePred p]
  证明: by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [AddMonoidHom.comp_apply]; rw [filterAddMonoidHom_apply]; rw [filter_single_pos _ _ hi]
    exact sumAddHom_single _ _ _
  · rintro x ⟨v, rfl⟩
    refine dfinsuppSumAddHom_mem _ _ _ fun i _ => ?_
    r

Depends on / 依赖: AddMonoidHom, AddMonoidHom.comp_apply, AddSubmonoid, AddSubmonoid.mem_iSup_of_mem, DFinsupp, DFinsupp.single, comp_apply, dfinsuppSumAddHom_mem, filterAddMonoidHom_apply, filter_single_pos, le_antisymm, mem_iSup_of_mem, single, sumAddHom_single
-/
theorem AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom (p : ι -> Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι -> AddSubmonoid γ) :
    ⨆ (i) (_ : p i), S i =
      AddMonoidHom.mrange ((sumAddHom fun i => (S i).subtype).comp (filterAddMonoidHom _ p)) := by
  apply le_antisymm
  · refine iSup₂_le fun i hi y hy => ⟨DFinsupp.single i ⟨y, hy⟩, ?_⟩
    rw [AddMonoidHom.comp_apply]; rw [filterAddMonoidHom_apply]; rw [filter_single_pos _ _ hi]
    exact sumAddHom_single _ _ _
  · rintro x ⟨v, rfl⟩
    refine dfinsuppSumAddHom_mem _ _ _ fun i _ => ?_
    refine AddSubmonoid.mem_iSup_of_mem i ?_
    by_cases hp : p i
    · simp [hp]
    · simp [hp]

/--
theorem `AddSubmonoid.mem_iSup_iff_exists_dfinsupp` / 定理 `AddSubmonoid.mem_iSup_iff_exists_dfinsupp`

English:
theorem AddSubmonoid.mem_iSup_iff_exists_dfinsupp
  statement: [AddCommMonoid γ] (S : ι -> AddSubmonoid γ)
  proof: SetLike.ext_iff.mp (AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom S) x

中文:
定理 AddSubmonoid.mem_iSup_iff_exists_dfinsupp
  结论: [AddCommMonoid γ] (S : ι -> AddSubmonoid γ)
  证明: SetLike.ext_iff.mp (AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom S) x

Depends on / 依赖: AddSubmonoid, AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom, SetLike, SetLike.ext_iff.mp, ext_iff, iSup_eq_mrange_dfinsuppSumAddHom
-/
theorem AddSubmonoid.mem_iSup_iff_exists_dfinsupp [AddCommMonoid γ] (S : ι -> AddSubmonoid γ)
    (x : γ) : x in iSup S ↔ exists f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) f = x :=
  SetLike.ext_iff.mp (AddSubmonoid.iSup_eq_mrange_dfinsuppSumAddHom S) x

/--
theorem `AddSubmonoid.mem_iSup_iff_exists_dfinsupp'` / 定理 `AddSubmonoid.mem_iSup_iff_exists_dfinsupp'`

English:
theorem AddSubmonoid.mem_iSup_iff_exists_dfinsupp'
  statement: [AddCommMonoid γ] (S : ι -> AddSubmonoid γ)
  proof: by
  rw [AddSubmonoid.mem_iSup_iff_exists_dfinsupp]
  simp_rw [sumAddHom_apply]
  rfl

中文:
定理 AddSubmonoid.mem_iSup_iff_exists_dfinsupp'
  结论: [AddCommMonoid γ] (S : ι -> AddSubmonoid γ)
  证明: by
  rw [AddSubmonoid.mem_iSup_iff_exists_dfinsupp]
  simp_rw [sumAddHom_apply]
  rfl

Depends on / 依赖: AddSubmonoid, AddSubmonoid.mem_iSup_iff_exists_dfinsupp, mem_iSup_iff_exists_dfinsupp, simp_rw, sumAddHom_apply
-/
theorem AddSubmonoid.mem_iSup_iff_exists_dfinsupp' [AddCommMonoid γ] (S : ι -> AddSubmonoid γ)
    [forall (i) (x : S i), Decidable (x != 0)] (x : γ) :
    x in iSup S ↔ exists f : Π₀ i, S i, (f.sum fun _ xi => ↑xi) = x := by
  rw [AddSubmonoid.mem_iSup_iff_exists_dfinsupp]
  simp_rw [sumAddHom_apply]
  rfl

/--
theorem `AddSubmonoid.mem_bsupr_iff_exists_dfinsupp` / 定理 `AddSubmonoid.mem_bsupr_iff_exists_dfinsupp`

English:
theorem AddSubmonoid.mem_bsupr_iff_exists_dfinsupp
  statement: (p : ι -> Prop) [DecidablePred p]
  proof: SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom p S) x

中文:
定理 AddSubmonoid.mem_bsupr_iff_exists_dfinsupp
  结论: (p : ι -> 命题) [DecidablePred p]
  证明: SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom p S) x

Depends on / 依赖: AddSubmonoid, AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom, SetLike, SetLike.ext_iff.mp, bsupr_eq_mrange_dfinsuppSumAddHom, ext_iff
-/
theorem AddSubmonoid.mem_bsupr_iff_exists_dfinsupp (p : ι -> Prop) [DecidablePred p]
    [AddCommMonoid γ] (S : ι -> AddSubmonoid γ) (x : γ) :
    (x in ⨆ (i) (_ : p i), S i) ↔
      exists f : Π₀ i, S i, DFinsupp.sumAddHom (fun i => (S i).subtype) (f.filter p) = x :=
  SetLike.ext_iff.mp (AddSubmonoid.bsupr_eq_mrange_dfinsuppSumAddHom p S) x
