/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.EquivFin

/-!
# fintype instance for the product of two fintypes.

-/

public section


open Function

universe u v

variable {α β γ : Type*}

open Finset

namespace Set

variable {s t : Set α}

/--
theorem `toFinset_prod` / 定理 `toFinset_prod`

English:
theorem toFinset_prod
  given: (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s ×ˢ t)]
  proof: by
  ext
  simp

中文:
定理 toFinset_prod
  条件: (s : 集合 α) (t : 集合 β) [有限类型 s] [有限类型 t] [有限类型 (s ×ˢ t)]
  证明: by
  ext
  simp
-/
theorem toFinset_prod (s : Set α) (t : Set β) [Fintype s] [Fintype t] [Fintype (s ×ˢ t)] :
    (s ×ˢ t).toFinset = s.toFinset ×ˢ t.toFinset := by
  ext
  simp

/--
theorem `toFinset_offDiag` / 定理 `toFinset_offDiag`

English:
theorem toFinset_offDiag
  given: {s : Set α} [Fintype s] [Fintype s.offDiag]
  proof: Finset.ext by simp

@[deprecated (since := "2026-01-09")]
alias toFinset_off_diag := toFinset_offDiag

中文:
定理 toFinset_offDiag
  条件: {s : 集合 α} [有限类型 s] [有限类型 s.offDiag]
  证明: Finset.ext by simp

@[deprecated (since := "2026-01-09")]
alias toFinset_off_diag := toFinset_offDiag

Depends on / 依赖: Finset, Finset.ext
-/
theorem toFinset_offDiag {s : Set α} [Fintype s] [Fintype s.offDiag] :
    s.offDiag.toFinset = s.toFinset.offDiag :=
Finset.ext by simp

@[deprecated (since := "2026-01-09")]
alias toFinset_off_diag := toFinset_offDiag

end Set

/--
Instance `instFintypeProd` / 实例 `instFintypeProd`

English:
instance instFintypeProd
  signature: (α β : Type*) [Fintype α] [Fintype β]
  body: ⟨univ ×ˢ univ, fun ⟨a, b⟩ => by simp⟩

中文:
实例 instFintypeProd
  签名: (α β : 类型) [有限类型 α] [有限类型 β]
  定义体: ⟨univ ×ˢ univ, fun ⟨a, b⟩ => by simp⟩
-/
instance instFintypeProd (α β : Type*) [Fintype α] [Fintype β] : Fintype (α × β) :=
  ⟨univ ×ˢ univ, fun ⟨a, b⟩ => by simp⟩

namespace Finset
variable [Fintype α] [Fintype β] {s : Finset α} {t : Finset β}

/--
lemma `univ_product_univ` / 引理 `univ_product_univ`

English:
lemma univ_product_univ
  statement: univ ×ˢ univ = (univ : Finset (α × β))
  proof: rfl

中文:
引理 univ_product_univ
  结论: univ ×ˢ univ = (univ : 有限集 (α × β))
  证明: rfl
-/
@[simp] lemma univ_product_univ : univ ×ˢ univ = (univ : Finset (α × β)) := rfl

/--
lemma `product_eq_univ` / 引理 `product_eq_univ`

English:
lemma product_eq_univ
  given: [Nonempty α] [Nonempty β]
  statement: s ×ˢ t = univ ↔ s = univ ∧ t = univ
  proof: by
  simp [eq_univ_iff_forall, forall_and]

中文:
引理 product_eq_univ
  条件: [非空 α] [非空 β]
  结论: s ×ˢ t = univ ↔ s = univ ∧ t = univ
  证明: by
  simp [eq_univ_iff_forall, forall_and]
-/
@[simp] lemma product_eq_univ [Nonempty α] [Nonempty β] : s ×ˢ t = univ ↔ s = univ ∧ t = univ := by
  simp [eq_univ_iff_forall, forall_and]

end Finset

@[simp]
/--
theorem `Fintype.card_prod` / 定理 `Fintype.card_prod`

English:
theorem Fintype.card_prod
  given: (α β : Type*) [Fintype α] [Fintype β]
  proof: card_product _ _

中文:
定理 有限类型.card_prod
  条件: (α β : 类型) [有限类型 α] [有限类型 β]
  证明: card_product _ _

Depends on / 依赖: card_product
-/
theorem Fintype.card_prod (α β : Type*) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β :=
  card_product _ _

/--
lemma `Fintype.card_product_filter_lt` / 引理 `Fintype.card_product_filter_lt`

English:
lemma Fintype.card_product_filter_lt
  given: [Fintype α] [LinearOrder α]
  proof: by
  simpa using Finset.card_product_filter_lt (s := univ)

中文:
引理 有限类型.card_product_filter_lt
  条件: [有限类型 α] [线性序 α]
  证明: by
  simpa using Finset.card_product_filter_lt (s := univ)

Depends on / 依赖: Finset, Finset.card_product_filter_lt, card_product_filter_lt
-/
lemma Fintype.card_product_filter_lt [Fintype α] [LinearOrder α] :
    #{x : α × α | x.1 < x.2} = (Fintype.card α).choose 2 := by
  simpa using Finset.card_product_filter_lt (s := univ)

section

attribute [local instance] Fintype.ofFinite in
@[simp]
/--
theorem `infinite_prod` / 定理 `infinite_prod`

English:
theorem infinite_prod
  statement: Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ Infinite β
  proof: by
  refine
    ⟨fun H => ?_, fun H =>
      H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [and_comm]
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  contrapose! H; have := H.1 ⟨b⟩; have := H.2 ⟨a⟩
  infer_instance

中文:
定理 infinite_prod
  结论: 无限 (α × β) ↔ 无限 α ∧ 非空 β ∨ 非空 α ∧ 无限 β
  证明: by
  refine
    ⟨fun H => ?_, fun H =>
      H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [and_comm]
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  contrapose! H; have := H.1 ⟨b⟩; have := H.2 ⟨a⟩
  infer_instance

Depends on / 依赖: H.elim, Infinite, Infinite.nonempty, Prod.infinite_of_left, Prod.infinite_of_right, and_comm, and_imp, contrapose, infer_instance, infinite_of_left, infinite_of_right, nonempty
-/
theorem infinite_prod : Infinite (α × β) ↔ Infinite α ∧ Nonempty β ∨ Nonempty α ∧ Infinite β := by
  refine
    ⟨fun H => ?_, fun H =>
      H.elim (and_imp.2 <| @Prod.infinite_of_left α β) (and_imp.2 <| @Prod.infinite_of_right α β)⟩
  rw [and_comm]
  rcases Infinite.nonempty (α × β) with ⟨a, b⟩
  contrapose! H; have := H.1 ⟨b⟩; have := H.2 ⟨a⟩
  infer_instance

/--
Instance `Pi.infinite_of_left` / 实例 `Pi.infinite_of_left`

English:
instance Pi.infinite_of_left
  signature: {ι : Sort*} {π : ι -> Type*} [forall i, Nontrivial <| π i] [Infinite ι]
  body: by
  classical
  choose m n hm using fun i => exists_pair_ne (π i)
  refine Infinite.of_injective (fun i => update m i (n i)) fun x y h => of_not_not fun hne => ?_
  simp_rw [update_eq_iff, update_of_ne hne] at h
  exact (hm x h.1.symm).elim

中文:
实例 依赖函数类型.infinite_of_left
  签名: {ι : 类型层*} {π : ι -> 类型} [对任意 i, 非平凡 <| π i] [无限 ι]
  定义体: by
  classical
  choose m n hm using fun i => exists_pair_ne (π i)
  refine Infinite.of_injective (fun i => update m i (n i)) fun x y h => of_not_not fun hne => ?_
  simp_rw [update_eq_iff, update_of_ne hne] at h
  exact (hm x h.1.symm).elim

Depends on / 依赖: Infinite, Infinite.of_injective, classical, exists_pair_ne, of_injective, of_not_not, simp_rw, update, update_eq_iff, update_of_ne
-/
instance Pi.infinite_of_left {ι : Sort*} {π : ι -> Type*} [forall i, Nontrivial <| π i] [Infinite ι] :
    Infinite (forall i : ι, π i) := by
  classical
  choose m n hm using fun i => exists_pair_ne (π i)
  refine Infinite.of_injective (fun i => update m i (n i)) fun x y h => of_not_not fun hne => ?_
  simp_rw [update_eq_iff, update_of_ne hne] at h
  exact (hm x h.1.symm).elim

/--
theorem `Pi.infinite_of_exists_right` / 定理 `Pi.infinite_of_exists_right`

English:
theorem Pi.infinite_of_exists_right
  statement: {ι : Sort*} {π : ι -> Sort*} (i : ι) [Infinite <| π i]
  proof: by
  classical
  let ⟨m⟩ := @Pi.instNonempty ι π _
  exact Infinite.of_injective _ (update_injective m i)

中文:
定理 依赖函数类型.infinite_of_存在_right
  结论: {ι : 类型层*} {π : ι -> 类型层*} (i : ι) [无限 <| π i]
  证明: by
  classical
  let ⟨m⟩ := @Pi.instNonempty ι π _
  exact Infinite.of_injective _ (update_injective m i)

Depends on / 依赖: Infinite, Infinite.of_injective, Pi.instNonempty, classical, instNonempty, of_injective, update_injective
-/
theorem Pi.infinite_of_exists_right {ι : Sort*} {π : ι -> Sort*} (i : ι) [Infinite <| π i]
    [forall i, Nonempty <| π i] : Infinite (forall i : ι, π i) := by
  classical
  let ⟨m⟩ := @Pi.instNonempty ι π _
  exact Infinite.of_injective _ (update_injective m i)

/--
Instance `Pi.infinite_of_right` / 实例 `Pi.infinite_of_right`

English:
instance Pi.infinite_of_right
  signature: {ι : Sort*} {π : ι -> Type*} [forall i, Infinite <| π i] [Nonempty ι]
  body: Pi.infinite_of_exists_right (Classical.arbitrary ι)

中文:
实例 依赖函数类型.infinite_of_right
  签名: {ι : 类型层*} {π : ι -> 类型} [对任意 i, 无限 <| π i] [非空 ι]
  定义体: Pi.infinite_of_exists_right (Classical.arbitrary ι)

Depends on / 依赖: Classical, Classical.arbitrary, Pi.infinite_of_exists_right, arbitrary, infinite_of_exists_right
-/
instance Pi.infinite_of_right {ι : Sort*} {π : ι -> Type*} [forall i, Infinite <| π i] [Nonempty ι] :
    Infinite (forall i : ι, π i) :=
  Pi.infinite_of_exists_right (Classical.arbitrary ι)

/--
Instance `Function.infinite_of_left` / 实例 `Function.infinite_of_left`

English:
instance Function.infinite_of_left
  signature: {ι : Sort*} {π : Type*} [Nontrivial π] [Infinite ι]
  body: Pi.infinite_of_left

中文:
实例 函数.infinite_of_left
  签名: {ι : 类型层*} {π : 类型} [非平凡 π] [无限 ι]
  定义体: Pi.infinite_of_left

Depends on / 依赖: Pi.infinite_of_left, infinite_of_left
-/
instance Function.infinite_of_left {ι : Sort*} {π : Type*} [Nontrivial π] [Infinite ι] :
    Infinite (ι -> π) :=
  Pi.infinite_of_left

/--
Instance `Function.infinite_of_right` / 实例 `Function.infinite_of_right`

English:
instance Function.infinite_of_right
  signature: {ι : Sort*} {π : Type*} [Infinite π] [Nonempty ι]
  body: Pi.infinite_of_right

中文:
实例 函数.infinite_of_right
  签名: {ι : 类型层*} {π : 类型} [无限 π] [非空 ι]
  定义体: Pi.infinite_of_right

Depends on / 依赖: Pi.infinite_of_right, infinite_of_right
-/
instance Function.infinite_of_right {ι : Sort*} {π : Type*} [Infinite π] [Nonempty ι] :
    Infinite (ι -> π) :=
  Pi.infinite_of_right

end
