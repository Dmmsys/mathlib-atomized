/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Data.DFinsupp.BigOperators
public import Mathlib.Data.DFinsupp.Order

/-!
# Equivalence between `Multiset` and `ℕ`-valued finitely supported functions

This defines `DFinsupp.toMultiset` the equivalence between `Π₀ a : α, ℕ` and `Multiset α`, along
with `Multiset.toDFinsupp` the reverse equivalence.
-/

@[expose] public section

open Function

variable {α : Type*}

namespace DFinsupp

/--
Instance `addZeroClass'` / 实例 `addZeroClass'`

English:
instance addZeroClass'
  signature: {β} [AddZeroClass β]
  body: @DFinsupp.addZeroClass α (fun _ => β) _

中文:
实例 addZeroClass'
  签名: {β} [AddZeroClass β]
  定义体: @DFinsupp.addZeroClass α (fun _ => β) _

Depends on / 依赖: DFinsupp, DFinsupp.addZeroClass, addZeroClass
-/
instance addZeroClass' {β} [AddZeroClass β] : AddZeroClass (Π₀ _ : α, β) :=
  @DFinsupp.addZeroClass α (fun _ => β) _

variable [DecidableEq α]

/--
Definition of `toMultiset` / `toMultiset` 的定义

English:
definition toMultiset
  signature: : (Π₀ _ : α, Nat) ->+ Multiset α
  body: DFinsupp.sumAddHom fun a : α => Multiset.replicateAddMonoidHom a

@[simp]

中文:
定义 toMultiset
  签名: : (Π₀ _ : α, 自然数) ->+ Multiset α
  定义体: DFinsupp.sumAddHom fun a : α => Multiset.replicateAddMonoidHom a

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.sumAddHom, Multiset, Multiset.replicateAddMonoidHom, replicateAddMonoidHom, sumAddHom
-/
def toMultiset : (Π₀ _ : α, Nat) ->+ Multiset α :=
  DFinsupp.sumAddHom fun a : α => Multiset.replicateAddMonoidHom a

@[simp]
/--
theorem `toMultiset_single` / 定理 `toMultiset_single`

English:
theorem toMultiset_single
  given: (a : α) (n : Nat)
  proof: DFinsupp.sumAddHom_single _ _ _

中文:
定理 toMultiset_single
  条件: (a : α) (n : 自然数)
  证明: DFinsupp.sumAddHom_single _ _ _

Depends on / 依赖: DFinsupp, DFinsupp.sumAddHom_single, sumAddHom_single
-/
theorem toMultiset_single (a : α) (n : Nat) :
    toMultiset (DFinsupp.single a n) = Multiset.replicate n a :=
  DFinsupp.sumAddHom_single _ _ _

end DFinsupp

namespace Multiset

variable [DecidableEq α] {s t : Multiset α}

/--
Definition of `toDFinsupp` / `toDFinsupp` 的定义

English:
definition toDFinsupp
  signature: : Multiset α ->+ Π₀ _ : α, Nat where
  body: { toFun := fun n => s.count n
      support' := Trunc.mk ⟨s, fun i => (em (i in s)).imp_right Multiset.count_eq_zero_of_notMem⟩ }
  map_zero' := rfl
  map_add' _ _ := DFinsupp.ext fun _ => Multiset.count_add _ _ _

@[simp]

中文:
定义 toDFinsupp
  签名: : Multiset α ->+ Π₀ _ : α, 自然数 where
  定义体: { toFun := fun n => s.count n
      support' := Trunc.mk ⟨s, fun i => (em (i in s)).imp_right Multiset.count_eq_zero_of_notMem⟩ }
  map_zero' := rfl
  map_add' _ _ := DFinsupp.ext fun _ => Multiset.count_add _ _ _

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.ext, Multiset, Multiset.count_add, Multiset.count_eq_zero_of_notMem, Trunc.mk, count_add, count_eq_zero_of_notMem, imp_right, map_add, map_zero, s.count, support
-/
def toDFinsupp : Multiset α ->+ Π₀ _ : α, Nat where
  toFun s :=
    { toFun := fun n => s.count n
      support' := Trunc.mk ⟨s, fun i => (em (i in s)).imp_right Multiset.count_eq_zero_of_notMem⟩ }
  map_zero' := rfl
  map_add' _ _ := DFinsupp.ext fun _ => Multiset.count_add _ _ _

@[simp]
/--
theorem `toDFinsupp_apply` / 定理 `toDFinsupp_apply`

English:
theorem toDFinsupp_apply
  given: (s : Multiset α) (a : α)
  statement: Multiset.toDFinsupp s a = s.count a
  proof: rfl

@[simp]

中文:
定理 toDFinsupp_apply
  条件: (s : Multiset α) (a : α)
  结论: Multiset.toDFinsupp s a = s.count a
  证明: rfl

@[simp]
-/
theorem toDFinsupp_apply (s : Multiset α) (a : α) : Multiset.toDFinsupp s a = s.count a :=
  rfl

@[simp]
/--
theorem `toDFinsupp_support` / 定理 `toDFinsupp_support`

English:
theorem toDFinsupp_support
  given: (s : Multiset α)
  statement: s.toDFinsupp.support = s.toFinset
  proof: Finset.filter_true_of_mem fun _ hx => count_ne_zero.mpr Multiset.mem_toFinset.1 hx

中文:
定理 toDFinsupp_support
  条件: (s : Multiset α)
  结论: s.toDFinsupp.support = s.toFinset
  证明: Finset.filter_true_of_mem fun _ hx => count_ne_zero.mpr Multiset.mem_toFinset.1 hx

Depends on / 依赖: Finset, Finset.filter_true_of_mem, Multiset, Multiset.mem_toFinset, count_ne_zero, count_ne_zero.mpr, filter_true_of_mem, mem_toFinset
-/
theorem toDFinsupp_support (s : Multiset α) : s.toDFinsupp.support = s.toFinset :=
Finset.filter_true_of_mem fun _ hx => count_ne_zero.mpr Multiset.mem_toFinset.1 hx

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toDFinsupp_replicate` / 定理 `toDFinsupp_replicate`

English:
theorem toDFinsupp_replicate
  given: (a : α) (n : Nat)
  proof: by
  ext i
  dsimp [toDFinsupp]
  simp [count_replicate]

@[simp]

中文:
定理 toDFinsupp_replicate
  条件: (a : α) (n : 自然数)
  证明: by
  ext i
  dsimp [toDFinsupp]
  simp [count_replicate]

@[simp]

Depends on / 依赖: count_replicate, toDFinsupp
-/
theorem toDFinsupp_replicate (a : α) (n : Nat) :
    toDFinsupp (Multiset.replicate n a) = DFinsupp.single a n := by
  ext i
  dsimp [toDFinsupp]
  simp [count_replicate]

@[simp]
/--
theorem `toDFinsupp_singleton` / 定理 `toDFinsupp_singleton`

English:
theorem toDFinsupp_singleton
  given: (a : α)
  statement: toDFinsupp {a} = DFinsupp.single a 1
  proof: by
  rw [← replicate_one]; rw [toDFinsupp_replicate]

中文:
定理 toDFinsupp_singleton
  条件: (a : α)
  结论: toDFinsupp {a} = DFinsupp.single a 1
  证明: by
  rw [← replicate_one]; rw [toDFinsupp_replicate]

Depends on / 依赖: replicate_one, toDFinsupp_replicate
-/
theorem toDFinsupp_singleton (a : α) : toDFinsupp {a} = DFinsupp.single a 1 := by
  rw [← replicate_one]; rw [toDFinsupp_replicate]

/-- `Multiset.toDFinsupp` as an `AddEquiv`. -/
@[simps! apply symm_apply]
/--
Definition of `equivDFinsupp` / `equivDFinsupp` 的定义

English:
definition equivDFinsupp
  signature: : Multiset α ≃+ Π₀ _ : α, Nat
  body: AddMonoidHom.toAddEquiv Multiset.toDFinsupp DFinsupp.toMultiset (by ext; simp) (by ext; simp)

@[simp]

中文:
定义 equivDFinsupp
  签名: : Multiset α ≃+ Π₀ _ : α, 自然数
  定义体: AddMonoidHom.toAddEquiv Multiset.toDFinsupp DFinsupp.toMultiset (by ext; simp) (by ext; simp)

@[simp]

Depends on / 依赖: AddMonoidHom, AddMonoidHom.toAddEquiv, DFinsupp, DFinsupp.toMultiset, Multiset, Multiset.toDFinsupp, toAddEquiv, toDFinsupp, toMultiset
-/
def equivDFinsupp : Multiset α ≃+ Π₀ _ : α, Nat :=
  AddMonoidHom.toAddEquiv Multiset.toDFinsupp DFinsupp.toMultiset (by ext; simp) (by ext; simp)

@[simp]
/--
theorem `toDFinsupp_toMultiset` / 定理 `toDFinsupp_toMultiset`

English:
theorem toDFinsupp_toMultiset
  given: (s : Multiset α)
  statement: DFinsupp.toMultiset (Multiset.toDFinsupp s) = s
  proof: equivDFinsupp.symm_apply_apply s

中文:
定理 toDFinsupp_toMultiset
  条件: (s : Multiset α)
  结论: DFinsupp.toMultiset (Multiset.toDFinsupp s) = s
  证明: equivDFinsupp.symm_apply_apply s

Depends on / 依赖: equivDFinsupp, equivDFinsupp.symm_apply_apply, symm_apply_apply
-/
theorem toDFinsupp_toMultiset (s : Multiset α) : DFinsupp.toMultiset (Multiset.toDFinsupp s) = s :=
  equivDFinsupp.symm_apply_apply s

/--
theorem `toDFinsupp_injective` / 定理 `toDFinsupp_injective`

English:
theorem toDFinsupp_injective
  statement: Injective (toDFinsupp : Multiset α -> Π₀ _a, Nat)
  proof: equivDFinsupp.injective

@[simp]

中文:
定理 toDFinsupp_injective
  结论: Injective (toDFinsupp : Multiset α -> Π₀ _a, 自然数)
  证明: equivDFinsupp.injective

@[simp]

Depends on / 依赖: equivDFinsupp, equivDFinsupp.injective, injective
-/
theorem toDFinsupp_injective : Injective (toDFinsupp : Multiset α -> Π₀ _a, Nat) :=
  equivDFinsupp.injective

@[simp]
/--
theorem `toDFinsupp_inj` / 定理 `toDFinsupp_inj`

English:
theorem toDFinsupp_inj
  statement: toDFinsupp s = toDFinsupp t ↔ s = t
  proof: toDFinsupp_injective.eq_iff

@[simp]

中文:
定理 toDFinsupp_inj
  结论: toDFinsupp s = toDFinsupp t ↔ s = t
  证明: toDFinsupp_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toDFinsupp_injective, toDFinsupp_injective.eq_iff
-/
theorem toDFinsupp_inj : toDFinsupp s = toDFinsupp t ↔ s = t :=
  toDFinsupp_injective.eq_iff

@[simp]
/--
theorem `toDFinsupp_le_toDFinsupp` / 定理 `toDFinsupp_le_toDFinsupp`

English:
theorem toDFinsupp_le_toDFinsupp
  statement: toDFinsupp s <= toDFinsupp t ↔ s <= t
  proof: by
  simp [Multiset.le_iff_count, DFinsupp.le_def]

@[simp]

中文:
定理 toDFinsupp_le_toDFinsupp
  结论: toDFinsupp s <= toDFinsupp t ↔ s <= t
  证明: by
  simp [Multiset.le_iff_count, DFinsupp.le_def]

@[simp]

Depends on / 依赖: DFinsupp, DFinsupp.le_def, Multiset, Multiset.le_iff_count, le_def, le_iff_count
-/
theorem toDFinsupp_le_toDFinsupp : toDFinsupp s <= toDFinsupp t ↔ s <= t := by
  simp [Multiset.le_iff_count, DFinsupp.le_def]

@[simp]
/--
theorem `toDFinsupp_lt_toDFinsupp` / 定理 `toDFinsupp_lt_toDFinsupp`

English:
theorem toDFinsupp_lt_toDFinsupp
  statement: toDFinsupp s < toDFinsupp t ↔ s < t
  proof: lt_iff_lt_of_le_iff_le' toDFinsupp_le_toDFinsupp toDFinsupp_le_toDFinsupp

@[simp]

中文:
定理 toDFinsupp_lt_toDFinsupp
  结论: toDFinsupp s < toDFinsupp t ↔ s < t
  证明: lt_iff_lt_of_le_iff_le' toDFinsupp_le_toDFinsupp toDFinsupp_le_toDFinsupp

@[simp]

Depends on / 依赖: lt_iff_lt_of_le_iff_le, toDFinsupp_le_toDFinsupp
-/
theorem toDFinsupp_lt_toDFinsupp : toDFinsupp s < toDFinsupp t ↔ s < t :=
  lt_iff_lt_of_le_iff_le' toDFinsupp_le_toDFinsupp toDFinsupp_le_toDFinsupp

@[simp]
/--
theorem `toDFinsupp_inter` / 定理 `toDFinsupp_inter`

English:
theorem toDFinsupp_inter
  given: (s t : Multiset α)
  statement: toDFinsupp (s inter t) = toDFinsupp s ⊓ toDFinsupp t
  proof: by
  ext i; simp

@[simp]

中文:
定理 toDFinsupp_inter
  条件: (s t : Multiset α)
  结论: toDFinsupp (s inter t) = toDFinsupp s ⊓ toDFinsupp t
  证明: by
  ext i; simp

@[simp]
-/
theorem toDFinsupp_inter (s t : Multiset α) : toDFinsupp (s inter t) = toDFinsupp s ⊓ toDFinsupp t := by
  ext i; simp

@[simp]
/--
theorem `toDFinsupp_union` / 定理 `toDFinsupp_union`

English:
theorem toDFinsupp_union
  given: (s t : Multiset α)
  statement: toDFinsupp (s union t) = toDFinsupp s ⊔ toDFinsupp t
  proof: by
  ext i; simp

中文:
定理 toDFinsupp_union
  条件: (s t : Multiset α)
  结论: toDFinsupp (s union t) = toDFinsupp s ⊔ toDFinsupp t
  证明: by
  ext i; simp
-/
theorem toDFinsupp_union (s t : Multiset α) : toDFinsupp (s union t) = toDFinsupp s ⊔ toDFinsupp t := by
  ext i; simp

end Multiset


namespace DFinsupp

variable [DecidableEq α] {f g : Π₀ _a : α, Nat}

@[simp]
/--
theorem `toMultiset_toDFinsupp` / 定理 `toMultiset_toDFinsupp`

English:
theorem toMultiset_toDFinsupp
  given: (f : Π₀ _ : α, Nat)
  proof: Multiset.equivDFinsupp.apply_symm_apply f

中文:
定理 toMultiset_toDFinsupp
  条件: (f : Π₀ _ : α, 自然数)
  证明: Multiset.equivDFinsupp.apply_symm_apply f

Depends on / 依赖: Multiset, Multiset.equivDFinsupp.apply_symm_apply, apply_symm_apply, equivDFinsupp
-/
theorem toMultiset_toDFinsupp (f : Π₀ _ : α, Nat) :
    Multiset.toDFinsupp (DFinsupp.toMultiset f) = f :=
  Multiset.equivDFinsupp.apply_symm_apply f

/--
theorem `toMultiset_injective` / 定理 `toMultiset_injective`

English:
theorem toMultiset_injective
  statement: Injective (toMultiset : (Π₀ _a, Nat) -> Multiset α)
  proof: Multiset.equivDFinsupp.symm.injective

@[simp]

中文:
定理 toMultiset_injective
  结论: Injective (toMultiset : (Π₀ _a, 自然数) -> Multiset α)
  证明: Multiset.equivDFinsupp.symm.injective

@[simp]

Depends on / 依赖: Multiset, Multiset.equivDFinsupp.symm.injective, equivDFinsupp, injective
-/
theorem toMultiset_injective : Injective (toMultiset : (Π₀ _a, Nat) -> Multiset α) :=
  Multiset.equivDFinsupp.symm.injective

@[simp]
/--
theorem `toMultiset_inj` / 定理 `toMultiset_inj`

English:
theorem toMultiset_inj
  statement: toMultiset f = toMultiset g ↔ f = g
  proof: toMultiset_injective.eq_iff

@[simp]

中文:
定理 toMultiset_inj
  结论: toMultiset f = toMultiset g ↔ f = g
  证明: toMultiset_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, toMultiset_injective, toMultiset_injective.eq_iff
-/
theorem toMultiset_inj : toMultiset f = toMultiset g ↔ f = g :=
  toMultiset_injective.eq_iff

@[simp]
/--
theorem `toMultiset_le_toMultiset` / 定理 `toMultiset_le_toMultiset`

English:
theorem toMultiset_le_toMultiset
  statement: toMultiset f <= toMultiset g ↔ f <= g
  proof: by
  simp_rw [← Multiset.toDFinsupp_le_toDFinsupp, toMultiset_toDFinsupp]

@[simp]

中文:
定理 toMultiset_le_toMultiset
  结论: toMultiset f <= toMultiset g ↔ f <= g
  证明: by
  simp_rw [← Multiset.toDFinsupp_le_toDFinsupp, toMultiset_toDFinsupp]

@[simp]

Depends on / 依赖: Multiset, Multiset.toDFinsupp_le_toDFinsupp, simp_rw, toDFinsupp_le_toDFinsupp, toMultiset_toDFinsupp
-/
theorem toMultiset_le_toMultiset : toMultiset f <= toMultiset g ↔ f <= g := by
  simp_rw [← Multiset.toDFinsupp_le_toDFinsupp, toMultiset_toDFinsupp]

@[simp]
/--
theorem `toMultiset_lt_toMultiset` / 定理 `toMultiset_lt_toMultiset`

English:
theorem toMultiset_lt_toMultiset
  statement: toMultiset f < toMultiset g ↔ f < g
  proof: by
  simp_rw [← Multiset.toDFinsupp_lt_toDFinsupp, toMultiset_toDFinsupp]

中文:
定理 toMultiset_lt_toMultiset
  结论: toMultiset f < toMultiset g ↔ f < g
  证明: by
  simp_rw [← Multiset.toDFinsupp_lt_toDFinsupp, toMultiset_toDFinsupp]

Depends on / 依赖: Multiset, Multiset.toDFinsupp_lt_toDFinsupp, simp_rw, toDFinsupp_lt_toDFinsupp, toMultiset_toDFinsupp
-/
theorem toMultiset_lt_toMultiset : toMultiset f < toMultiset g ↔ f < g := by
  simp_rw [← Multiset.toDFinsupp_lt_toDFinsupp, toMultiset_toDFinsupp]

variable (f g)

@[simp]
/--
theorem `toMultiset_inf` / 定理 `toMultiset_inf`

English:
theorem toMultiset_inf
  statement: toMultiset (f ⊓ g) = toMultiset f inter toMultiset g
  proof: Multiset.toDFinsupp_injective by simp

@[simp]

中文:
定理 toMultiset_inf
  结论: toMultiset (f ⊓ g) = toMultiset f inter toMultiset g
  证明: Multiset.toDFinsupp_injective by simp

@[simp]

Depends on / 依赖: Multiset, Multiset.toDFinsupp_injective, toDFinsupp_injective
-/
theorem toMultiset_inf : toMultiset (f ⊓ g) = toMultiset f inter toMultiset g :=
Multiset.toDFinsupp_injective by simp

@[simp]
/--
theorem `toMultiset_sup` / 定理 `toMultiset_sup`

English:
theorem toMultiset_sup
  statement: toMultiset (f ⊔ g) = toMultiset f union toMultiset g
  proof: Multiset.toDFinsupp_injective by simp

中文:
定理 toMultiset_sup
  结论: toMultiset (f ⊔ g) = toMultiset f union toMultiset g
  证明: Multiset.toDFinsupp_injective by simp

Depends on / 依赖: Multiset, Multiset.toDFinsupp_injective, toDFinsupp_injective
-/
theorem toMultiset_sup : toMultiset (f ⊔ g) = toMultiset f union toMultiset g :=
Multiset.toDFinsupp_injective by simp

end DFinsupp
