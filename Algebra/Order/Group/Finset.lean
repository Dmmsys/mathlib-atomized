/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Finset.Lattice.Prod

/-!
# `Finset.sup` in a group
-/

public section

open scoped Finset

assert_not_exists MonoidWithZero

namespace Multiset
variable {α : Type*} [DecidableEq α]

/--
lemma `toFinset_nsmul` / 引理 `toFinset_nsmul`

English:
lemma toFinset_nsmul
  given: (s : Multiset α)
  statement: forall n != 0, (n • s).toFinset = s.toFinset

中文:
引理 toFinset_nsmul
  条件: (s : Multiset α)
  结论: 对任意 n != 0, (n • s).toFinset = s.toFinset
-/
@[simp] lemma toFinset_nsmul (s : Multiset α) : forall n != 0, (n • s).toFinset = s.toFinset
  | 0, h => by contradiction
  | n + 1, _ => by
    by_cases h : n = 0
    · rw [h, zero_add, one_nsmul]
    · rw [add_nsmul, toFinset_add, one_nsmul, toFinset_nsmul s n h, Finset.union_idempotent]

/--
lemma `toFinset_eq_singleton_iff` / 引理 `toFinset_eq_singleton_iff`

English:
lemma toFinset_eq_singleton_iff
  given: (s : Multiset α) (a : α)
  proof: by
  refine ⟨fun H => ⟨fun h => ?_, ext' fun x => ?_⟩, fun H => ?_⟩
  · rw [card_eq_zero.1 h, toFinset_zero] at H
    exact Finset.empty_ne_singleton _ H
  · rw [count_nsmul, count_singleton]
    by_cases hx : x = a
    · simp_rw [hx, ite_true, mul_one, count_eq_card]
      intro y hy
      rw [← mem_toFinset]; rw [H]; rw [Finset.mem_singleton] at hy
      exact hy.symm
have hx' : x ∉ s := fun h' => hx by rwa [← mem_toFinset, H, Finset.mem_singleton] at h'
    simp_rw [count_eq_zero_of_notMem hx', hx, ite_false, Nat.mul_zero]
  simpa only [toFinset_nsmul _ _ H.1, toFinset_singleton] using congr($(H.2).toFinset)

中文:
引理 toFinset_eq_singleton_iff
  条件: (s : Multiset α) (a : α)
  证明: by
  refine ⟨fun H => ⟨fun h => ?_, ext' fun x => ?_⟩, fun H => ?_⟩
  · rw [card_eq_zero.1 h, toFinset_zero] at H
    exact Finset.empty_ne_singleton _ H
  · rw [count_nsmul, count_singleton]
    by_cases hx : x = a
    · simp_rw [hx, ite_true, mul_one, count_eq_card]
      intro y hy
      rw [← mem_toFinset]; rw [H]; rw [Finset.mem_singleton] at hy
      exact hy.symm
have hx' : x ∉ s := fun h' => hx by rwa [← mem_toFinset, H, Finset.mem_singleton] at h'
    simp_rw [count_eq_zero_of_notMem hx', hx, ite_false, Nat.mul_zero]
  simpa only [toFinset_nsmul _ _ H.1, toFinset_singleton] using congr($(H.2).toFinset)

Depends on / 依赖: Finset, Finset.empty_ne_singleton, Finset.mem_singleton, Nat.mul_zero, card_eq_zero, count_eq_card, count_eq_zero_of_notMem, count_nsmul, count_singleton, empty_ne_singleton, hy.symm, ite_false, ite_true, mem_singleton, mem_toFinset, mul_one, mul_zero, simp_rw, toFinset_zero
-/
lemma toFinset_eq_singleton_iff (s : Multiset α) (a : α) :
    s.toFinset = {a} ↔ card s != 0 ∧ s = card s • {a} := by
  refine ⟨fun H => ⟨fun h => ?_, ext' fun x => ?_⟩, fun H => ?_⟩
  · rw [card_eq_zero.1 h, toFinset_zero] at H
    exact Finset.empty_ne_singleton _ H
  · rw [count_nsmul, count_singleton]
    by_cases hx : x = a
    · simp_rw [hx, ite_true, mul_one, count_eq_card]
      intro y hy
      rw [← mem_toFinset]; rw [H]; rw [Finset.mem_singleton] at hy
      exact hy.symm
have hx' : x ∉ s := fun h' => hx by rwa [← mem_toFinset, H, Finset.mem_singleton] at h'
    simp_rw [count_eq_zero_of_notMem hx', hx, ite_false, Nat.mul_zero]
  simpa only [toFinset_nsmul _ _ H.1, toFinset_singleton] using congr($(H.2).toFinset)

/--
lemma `toFinset_card_eq_one_iff` / 引理 `toFinset_card_eq_one_iff`

English:
lemma toFinset_card_eq_one_iff
  given: (s : Multiset α)
  proof: by
  simp_rw [Finset.card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

中文:
引理 toFinset_card_eq_one_iff
  条件: (s : Multiset α)
  证明: by
  simp_rw [Finset.card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

Depends on / 依赖: Finset, Finset.card_eq_one, Multiset, Multiset.toFinset_eq_singleton_iff, card_eq_one, exists_and_left, simp_rw, toFinset_eq_singleton_iff
-/
lemma toFinset_card_eq_one_iff (s : Multiset α) :
    #s.toFinset = 1 ↔ Multiset.card s != 0 ∧ exists a : α, s = Multiset.card s • {a} := by
  simp_rw [Finset.card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

end Multiset

namespace Finset
variable {ι κ M G : Type*}

/--
lemma `fold_max_add` / 引理 `fold_max_add`

English:
lemma fold_max_add
  statement: [LinearOrder M] [Add M] [AddRightMono M] (s : Finset ι) (a : WithBot M)
  proof: by
  classical induction s using Finset.induction_on <;> simp [*, max_add_add_right]

@[to_additive nsmul_inf']

中文:
引理 fold_max_add
  结论: [线性序 M] [加法 M] [AddRightMono M] (s : 有限集 ι) (a : WithBot M)
  证明: by
  classical induction s using Finset.induction_on <;> simp [*, max_add_add_right]

@[to_additive nsmul_inf']

Depends on / 依赖: Finset, Finset.induction_on, classical, induction_on, max_add_add_right
-/
lemma fold_max_add [LinearOrder M] [Add M] [AddRightMono M] (s : Finset ι) (a : WithBot M)
    (f : ι -> M) : s.fold max ⊥ (fun i => ↑(f i) + a) = s.fold max ⊥ ((↑) ∘ f) + a := by
  classical induction s using Finset.induction_on <;> simp [*, max_add_add_right]

@[to_additive nsmul_inf']
/--
lemma `inf'_pow` / 引理 `inf'_pow`

English:
lemma inf'_pow
  statement: [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
  proof: map_finset_inf' (OrderHom.mk _ <| pow_left_mono n) hs _

@[to_additive nsmul_sup']

中文:
引理 下确界'_pow
  结论: [线性序 M] [幺半群 M] [MulLeftMono M] [MulRightMono M] (s : 有限集 ι)
  证明: map_finset_inf' (OrderHom.mk _ <| pow_left_mono n) hs _

@[to_additive nsmul_sup']
-/
lemma inf'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι -> M) (n : Nat) (hs) : s.inf' hs f ^ n = s.inf' hs fun a => f a ^ n :=
  map_finset_inf' (OrderHom.mk _ <| pow_left_mono n) hs _

@[to_additive nsmul_sup']
/--
lemma `sup'_pow` / 引理 `sup'_pow`

English:
lemma sup'_pow
  statement: [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
  proof: map_finset_sup' (OrderHom.mk _ <| pow_left_mono n) hs _

中文:
引理 上确界'_pow
  结论: [线性序 M] [幺半群 M] [MulLeftMono M] [MulRightMono M] (s : 有限集 ι)
  证明: map_finset_sup' (OrderHom.mk _ <| pow_left_mono n) hs _
-/
lemma sup'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι -> M) (n : Nat) (hs) : s.sup' hs f ^ n = s.sup' hs fun a => f a ^ n :=
  map_finset_sup' (OrderHom.mk _ <| pow_left_mono n) hs _

section Group
variable [Group G] [LinearOrder G]

@[to_additive /-- Also see `Finset.sup'_add'` that works for canonically ordered monoids. -/]
/--
lemma `sup'_mul` / 引理 `sup'_mul`

English:
lemma sup'_mul
  given: [MulRightMono G] (s : Finset ι) (f : ι -> G) (a : G) (hs)
  proof: map_finset_sup' (OrderIso.mulRight a) hs f

中文:
引理 上确界'_mul
  条件: [MulRightMono G] (s : 有限集 ι) (f : ι -> G) (a : G) (hs)
  证明: map_finset_sup' (OrderIso.mulRight a) hs f
-/
lemma sup'_mul [MulRightMono G] (s : Finset ι) (f : ι -> G) (a : G) (hs) :
    s.sup' hs f * a = s.sup' hs fun i => f i * a := map_finset_sup' (OrderIso.mulRight a) hs f

set_option linter.docPrime false in
@[to_additive /-- Also see `Finset.add_sup''` that works for canonically ordered monoids. -/]
/--
lemma `mul_sup'` / 引理 `mul_sup'`

English:
lemma mul_sup'
  given: [MulLeftMono G] (s : Finset ι) (f : ι -> G) (a : G) (hs)
  proof: map_finset_sup' (OrderIso.mulLeft a) hs f

中文:
引理 mul_sup'
  条件: [MulLeftMono G] (s : 有限集 ι) (f : ι -> G) (a : G) (hs)
  证明: map_finset_sup' (OrderIso.mulLeft a) hs f

Depends on / 依赖: OrderIso, OrderIso.mulLeft, map_finset_sup, mulLeft
-/
lemma mul_sup' [MulLeftMono G] (s : Finset ι) (f : ι -> G) (a : G) (hs) :
    a * s.sup' hs f = s.sup' hs fun i => a * f i := map_finset_sup' (OrderIso.mulLeft a) hs f

end Group

section CanonicallyLinearOrderedAddCommMonoid
variable [AddCommMonoid M] [LinearOrder M] [CanonicallyOrderedAdd M]
  [Sub M] [AddLeftReflectLE M] [OrderedSub M] {s : Finset ι} {t : Finset κ}

/--
lemma `sup'_add'` / 引理 `sup'_add'`

English:
lemma sup'_add'
  given: (s : Finset ι) (f : ι -> M) (a : M) (hs : s.Nonempty)
  proof: by
  apply le_antisymm
  · apply add_le_of_le_tsub_right_of_le
    · exact Finset.le_sup'_of_le _ hs.choose_spec le_add_self
    · exact Finset.sup'_le _ _ fun i hi => le_tsub_of_add_le_right (Finset.le_sup' (f · + a) hi)
  · exact Finset.sup'_le _ _ fun i hi => by grw [← Finset.le_sup' _ hi]

中文:
引理 上确界'_add'
  条件: (s : 有限集 ι) (f : ι -> M) (a : M) (hs : s.非空)
  证明: by
  apply le_antisymm
  · apply add_le_of_le_tsub_right_of_le
    · exact Finset.le_sup'_of_le _ hs.choose_spec le_add_self
    · exact Finset.sup'_le _ _ fun i hi => le_tsub_of_add_le_right (Finset.le_sup' (f · + a) hi)
  · exact Finset.sup'_le _ _ fun i hi => by grw [← Finset.le_sup' _ hi]
-/
lemma sup'_add' (s : Finset ι) (f : ι -> M) (a : M) (hs : s.Nonempty) :
    s.sup' hs f + a = s.sup' hs fun i => f i + a := by
  apply le_antisymm
  · apply add_le_of_le_tsub_right_of_le
    · exact Finset.le_sup'_of_le _ hs.choose_spec le_add_self
    · exact Finset.sup'_le _ _ fun i hi => le_tsub_of_add_le_right (Finset.le_sup' (f · + a) hi)
  · exact Finset.sup'_le _ _ fun i hi => by grw [← Finset.le_sup' _ hi]

/--
lemma `add_sup''` / 引理 `add_sup''`

English:
lemma add_sup''
  given: (hs : s.Nonempty) (f : ι -> M) (a : M)
  proof: by simp_rw [add_comm a, Finset.sup'_add']

中文:
引理 add_sup''
  条件: (hs : s.非空) (f : ι -> M) (a : M)
  证明: by simp_rw [add_comm a, Finset.sup'_add']

Depends on / 依赖: Finset, Finset.sup, _add, add_comm, simp_rw
-/
lemma add_sup'' (hs : s.Nonempty) (f : ι -> M) (a : M) :
    a + s.sup' hs f = s.sup' hs fun i => a + f i := by simp_rw [add_comm a, Finset.sup'_add']

variable [OrderBot M]

/--
lemma `sup_add` / 引理 `sup_add`

English:
lemma sup_add
  given: (hs : s.Nonempty) (f : ι -> M) (a : M)
  proof: by
  rw [← Finset.sup'_eq_sup hs]; rw [← Finset.sup'_eq_sup hs]; rw [sup'_add']

中文:
引理 sup_add
  条件: (hs : s.非空) (f : ι -> M) (a : M)
  证明: by
  rw [← Finset.sup'_eq_sup hs]; rw [← Finset.sup'_eq_sup hs]; rw [sup'_add']
-/
protected lemma sup_add (hs : s.Nonempty) (f : ι -> M) (a : M) :
    s.sup f + a = s.sup fun i => f i + a := by
  rw [← Finset.sup'_eq_sup hs]; rw [← Finset.sup'_eq_sup hs]; rw [sup'_add']

/--
lemma `add_sup` / 引理 `add_sup`

English:
lemma add_sup
  given: (hs : s.Nonempty) (f : ι -> M) (a : M)
  proof: by
  rw [← Finset.sup'_eq_sup hs]; rw [← Finset.sup'_eq_sup hs]; rw [add_sup'']

中文:
引理 add_sup
  条件: (hs : s.非空) (f : ι -> M) (a : M)
  证明: by
  rw [← Finset.sup'_eq_sup hs]; rw [← Finset.sup'_eq_sup hs]; rw [add_sup'']
-/
protected lemma add_sup (hs : s.Nonempty) (f : ι -> M) (a : M) :
    a + s.sup f = s.sup fun i => a + f i := by
  rw [← Finset.sup'_eq_sup hs]; rw [← Finset.sup'_eq_sup hs]; rw [add_sup'']

/--
lemma `sup_add_sup` / 引理 `sup_add_sup`

English:
lemma sup_add_sup
  given: (hs : s.Nonempty) (ht : t.Nonempty) (f : ι -> M) (g : κ -> M)
  proof: by
  simp only [Finset.sup_add hs, Finset.add_sup ht, Finset.sup_product_left]

中文:
引理 sup_add_sup
  条件: (hs : s.非空) (ht : t.非空) (f : ι -> M) (g : κ -> M)
  证明: by
  simp only [Finset.sup_add hs, Finset.add_sup ht, Finset.sup_product_left]

Depends on / 依赖: Finset, Finset.add_sup, Finset.sup_add, Finset.sup_product_left, add_sup, sup_add, sup_product_left
-/
lemma sup_add_sup (hs : s.Nonempty) (ht : t.Nonempty) (f : ι -> M) (g : κ -> M) :
    s.sup f + t.sup g = (s ×ˢ t).sup fun ij => f ij.1 + g ij.2 := by
  simp only [Finset.sup_add hs, Finset.add_sup ht, Finset.sup_product_left]

end CanonicallyLinearOrderedAddCommMonoid
end Finset
