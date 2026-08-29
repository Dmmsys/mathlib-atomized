/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.GroupTheory.Index

/-!
# Complements

In this file we define the complement of a subgroup.

## Main definitions

- `Subgroup.IsComplement S T` where `S` and `T` are subsets of `G` states that every `g : G` can be
  written uniquely as a product `s * t` for `s ∈ S`, `t ∈ T`.
- `H.LeftTransversal` where `H` is a subgroup of `G` is the type of all left-complements of `H`,
  i.e. the set of all `S : Set G` that contain exactly one element of each left coset of `H`.
- `H.RightTransversal` where `H` is a subgroup of `G` is the set of all right-complements of `H`,
  i.e. the set of all `T : Set G` that contain exactly one element of each right coset of `H`.

## Main results

- `isComplement'_of_coprime` : Subgroups of coprime order are complements.
-/

@[expose] public section

open Function Set
open scoped Pointwise

namespace Subgroup

variable {G : Type*} [Group G] (H K : Subgroup G) (S T : Set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
This notion generalizes left transversals, right transversals, and complementary subgroups.

If `S` and `T` are `SetLike`s such as `Subgroup`s, see `isComplement_iff_bijective` for a
more ergonomic way to unfold.
-/
@[to_additive /-- `S` and `T` are complements if `(+) : S × T → G` is a bijection

If `S` and `T` are `SetLike`s such as `AddSubgroup`s, see `isComplement_iff_bijective` for a
more ergonomic way to unfold. -/]
/--
Definition of `IsComplement` / `IsComplement` 的定义

English:
definition IsComplement
  signature: : Prop
  body: Function.Bijective fun x : S × T => x.1.1 * x.2.1

中文:
定义 IsComplement
  签名: : 命题
  定义体: Function.Bijective fun x : S × T => x.1.1 * x.2.1

Depends on / 依赖: Bijective, Function, Function.Bijective
-/
def IsComplement : Prop :=
  Function.Bijective fun x : S × T => x.1.1 * x.2.1

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive /-- `H` and `K` are complements if `(+) : H × K → G` is a bijection -/]
/--
Definition of `IsComplement'` / `IsComplement'` 的定义

English:
abbreviation IsComplement'
  body: IsComplement (H : Set G) (K : Set G)

中文:
缩写 IsComplement'
  定义体: IsComplement (H : Set G) (K : Set G)

Depends on / 依赖: IsComplement
-/
abbrev IsComplement' :=
  IsComplement (H : Set G) (K : Set G)

variable {H K S T}

/-- The correct way to unfold `IsComplement` for `SetLike`s such as `Subgroup`s -/
@[to_additive /-- The correct way to unfold `IsComplement` for `SetLike`s such as `AddSubgroup`s -/]
/--
theorem `isComplement_iff_bijective` / 定理 `isComplement_iff_bijective`

English:
theorem isComplement_iff_bijective
  given: {S : Type*} [SetLike S G] (s t : S)
  proof: Iff.rfl

@[to_additive]

中文:
定理 isComplement_iff_bijective
  条件: {S : 类型} [集合状 S G] (s t : S)
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Bijective, Function, Function.Bijective
-/
theorem isComplement_iff_bijective {S : Type*} [SetLike S G] (s t : S) :
    IsComplement (G := G) s t ↔ Function.Bijective fun x : s × t => (x.1 : G) * (x.2 : G) :=
  Iff.rfl

@[to_additive]
/--
theorem `isComplement'_def` / 定理 `isComplement'_def`

English:
theorem isComplement'_def
  statement: IsComplement' H K ↔ IsComplement (H : Set G) (K : Set G)
  proof: Iff.rfl

@[to_additive]

中文:
定理 isComplement'_def
  结论: IsComplement' H K ↔ IsComplement (H : 集合 G) (K : 集合 G)
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem isComplement'_def : IsComplement' H K ↔ IsComplement (H : Set G) (K : Set G) :=
  Iff.rfl

@[to_additive]
/--
theorem `isComplement_iff_existsUnique` / 定理 `isComplement_iff_existsUnique`

English:
theorem isComplement_iff_existsUnique
  proof: Function.bijective_iff_existsUnique _

@[to_additive]

中文:
定理 isComplement_iff_存在Unique
  证明: Function.bijective_iff_existsUnique _

@[to_additive]

Depends on / 依赖: Function, Function.bijective_iff_existsUnique, bijective_iff_existsUnique
-/
theorem isComplement_iff_existsUnique :
    IsComplement S T ↔ forall g : G, exists! x : S × T, x.1.1 * x.2.1 = g :=
  Function.bijective_iff_existsUnique _

@[to_additive]
/--
theorem `IsComplement.existsUnique` / 定理 `IsComplement.existsUnique`

English:
theorem IsComplement.existsUnique
  given: (h : IsComplement S T) (g : G)
  proof: isComplement_iff_existsUnique.mp h g

@[to_additive]

中文:
定理 IsComplement.存在Unique
  条件: (h : IsComplement S T) (g : G)
  证明: isComplement_iff_existsUnique.mp h g

@[to_additive]

Depends on / 依赖: isComplement_iff_existsUnique, isComplement_iff_existsUnique.mp
-/
theorem IsComplement.existsUnique (h : IsComplement S T) (g : G) :
    exists! x : S × T, x.1.1 * x.2.1 = g :=
  isComplement_iff_existsUnique.mp h g

@[to_additive]
/--
theorem `IsComplement'.symm` / 定理 `IsComplement'.symm`

English:
theorem IsComplement'.symm
  given: (h : IsComplement' H K)
  statement: IsComplement' K H
  proof: by
  let ϕ : H × K ≃ K × H :=
    Equiv.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩)
      (fun x => Prod.ext (inv_inv _) (inv_inv _)) fun x => Prod.ext (inv_inv _) (inv_inv _)
  let ψ : G ≃ G := Equiv.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_inv inv_inv
  suffices hf : (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rwa [isComplement'_def, isComplement_iff_bijective, ← Equiv.bijective_comp ϕ, ← hf,
      ψ.comp_bijective]
  exact funext fun x => mul_inv_rev _ _

@[to_additive]

中文:
定理 IsComplement'.symm
  条件: (h : IsComplement' H K)
  结论: IsComplement' K H
  证明: by
  let ϕ : H × K ≃ K × H :=
    Equiv.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩)
      (fun x => Prod.ext (inv_inv _) (inv_inv _)) fun x => Prod.ext (inv_inv _) (inv_inv _)
  let ψ : G ≃ G := Equiv.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_inv inv_inv
  suffices hf : (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rwa [isComplement'_def, isComplement_iff_bijective, ← Equiv.bijective_comp ϕ, ← hf,
      ψ.comp_bijective]
  exact funext fun x => mul_inv_rev _ _

@[to_additive]
-/
theorem IsComplement'.symm (h : IsComplement' H K) : IsComplement' K H := by
  let ϕ : H × K ≃ K × H :=
    Equiv.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩)
      (fun x => Prod.ext (inv_inv _) (inv_inv _)) fun x => Prod.ext (inv_inv _) (inv_inv _)
  let ψ : G ≃ G := Equiv.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_inv inv_inv
  suffices hf : (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rwa [isComplement'_def, isComplement_iff_bijective, ← Equiv.bijective_comp ϕ, ← hf,
      ψ.comp_bijective]
  exact funext fun x => mul_inv_rev _ _

@[to_additive]
/--
theorem `isComplement'_comm` / 定理 `isComplement'_comm`

English:
theorem isComplement'_comm
  statement: IsComplement' H K ↔ IsComplement' K H
  proof: ⟨IsComplement'.symm, IsComplement'.symm⟩

@[to_additive]

中文:
定理 isComplement'_comm
  结论: IsComplement' H K ↔ IsComplement' K H
  证明: ⟨IsComplement'.symm, IsComplement'.symm⟩

@[to_additive]
-/
theorem isComplement'_comm : IsComplement' H K ↔ IsComplement' K H :=
  ⟨IsComplement'.symm, IsComplement'.symm⟩

@[to_additive]
/--
theorem `isComplement_univ_singleton` / 定理 `isComplement_univ_singleton`

English:
theorem isComplement_univ_singleton
  given: {g : G}
  statement: IsComplement (univ : Set G) {g}
  proof: ⟨fun ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ h => Prod.ext (Subtype.ext (mul_right_cancel h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive]

中文:
定理 isComplement_univ_singleton
  条件: {g : G}
  结论: IsComplement (univ : 集合 G) {g}
  证明: ⟨fun ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ h => Prod.ext (Subtype.ext (mul_right_cancel h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive]

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, inv_mul_cancel_right, mul_right_cancel
-/
theorem isComplement_univ_singleton {g : G} : IsComplement (univ : Set G) {g} :=
  ⟨fun ⟨_, _, rfl⟩ ⟨_, _, rfl⟩ h => Prod.ext (Subtype.ext (mul_right_cancel h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive]
/--
theorem `isComplement_singleton_univ` / 定理 `isComplement_singleton_univ`

English:
theorem isComplement_singleton_univ
  given: {g : G}
  statement: IsComplement ({g} : Set G) univ
  proof: ⟨fun ⟨⟨_, rfl⟩, _⟩ ⟨⟨_, rfl⟩, _⟩ h => Prod.ext rfl (Subtype.ext (mul_left_cancel h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive]

中文:
定理 isComplement_singleton_univ
  条件: {g : G}
  结论: IsComplement ({g} : 集合 G) univ
  证明: ⟨fun ⟨⟨_, rfl⟩, _⟩ ⟨⟨_, rfl⟩, _⟩ h => Prod.ext rfl (Subtype.ext (mul_left_cancel h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive]

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, mul_inv_cancel_left, mul_left_cancel
-/
theorem isComplement_singleton_univ {g : G} : IsComplement ({g} : Set G) univ :=
  ⟨fun ⟨⟨_, rfl⟩, _⟩ ⟨⟨_, rfl⟩, _⟩ h => Prod.ext rfl (Subtype.ext (mul_left_cancel h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive]
/--
theorem `isComplement_singleton_left` / 定理 `isComplement_singleton_left`

English:
theorem isComplement_singleton_left
  given: {g : G}
  statement: IsComplement {g} S ↔ S = univ
  proof: by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => (congr_arg _ h).mpr isComplement_singleton_univ⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  rwa [← mul_left_cancel hy]

@[to_additive]

中文:
定理 isComplement_singleton_left
  条件: {g : G}
  结论: IsComplement {g} S ↔ S = univ
  证明: by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => (congr_arg _ h).mpr isComplement_singleton_univ⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  rwa [← mul_left_cancel hy]

@[to_additive]

Depends on / 依赖: congr_arg, isComplement_singleton_univ, mul_left_cancel, top_le_iff, top_le_iff.mp
-/
theorem isComplement_singleton_left {g : G} : IsComplement {g} S ↔ S = univ := by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => (congr_arg _ h).mpr isComplement_singleton_univ⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  rwa [← mul_left_cancel hy]

@[to_additive]
/--
theorem `isComplement_singleton_right` / 定理 `isComplement_singleton_right`

English:
theorem isComplement_singleton_right
  given: {g : G}
  statement: IsComplement S {g} ↔ S = univ
  proof: by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => h ▸ isComplement_univ_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  rw [← mul_right_cancel hy]
  exact y.1.2

@[to_additive]

中文:
定理 isComplement_singleton_right
  条件: {g : G}
  结论: IsComplement S {g} ↔ S = univ
  证明: by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => h ▸ isComplement_univ_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  rw [← mul_right_cancel hy]
  exact y.1.2

@[to_additive]

Depends on / 依赖: conv_rhs, isComplement_univ_singleton, mul_right_cancel, top_le_iff, top_le_iff.mp
-/
theorem isComplement_singleton_right {g : G} : IsComplement S {g} ↔ S = univ := by
  refine
    ⟨fun h => top_le_iff.mp fun x _ => ?_, fun h => h ▸ isComplement_univ_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  rw [← mul_right_cancel hy]
  exact y.1.2

@[to_additive]
/--
theorem `isComplement_univ_left` / 定理 `isComplement_univ_left`

English:
theorem isComplement_univ_left
  statement: IsComplement univ S ↔ exists g : G, S = {g}
  proof: by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.2.1, a.2.2⟩
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_cancel a).trans (inv_mul_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).2
  · rintro ⟨g, rfl⟩
    exact isComplement_univ_singleton

@[to_additive]

中文:
定理 isComplement_univ_left
  结论: IsComplement univ S ↔ 存在 g : G, S = {g}
  证明: by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.2.1, a.2.2⟩
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_cancel a).trans (inv_mul_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).2
  · rintro ⟨g, rfl⟩
    exact isComplement_univ_singleton

@[to_additive]

Depends on / 依赖: Prod.ext_iff.mp, Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr, Subtype, Subtype.ext_iff.mp, exists_eq_singleton_iff_nonempty_subsingleton, ext_iff, inv_mul_cancel, isComplement_univ_singleton, mem_top
-/
theorem isComplement_univ_left : IsComplement univ S ↔ exists g : G, S = {g} := by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.2.1, a.2.2⟩
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_cancel a).trans (inv_mul_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).2
  · rintro ⟨g, rfl⟩
    exact isComplement_univ_singleton

@[to_additive]
/--
theorem `isComplement_univ_right` / 定理 `isComplement_univ_right`

English:
theorem isComplement_univ_right
  statement: IsComplement S univ ↔ exists g : G, S = {g}
  proof: by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.1.1, a.1.2⟩
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_cancel a).trans (mul_inv_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).1
  · rintro ⟨g, rfl⟩
    exact isComplement_singleton_univ

@[to_additive]

中文:
定理 isComplement_univ_right
  结论: IsComplement S univ ↔ 存在 g : G, S = {g}
  证明: by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.1.1, a.1.2⟩
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_cancel a).trans (mul_inv_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).1
  · rintro ⟨g, rfl⟩
    exact isComplement_singleton_univ

@[to_additive]

Depends on / 依赖: Prod.ext_iff.mp, Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr, Subtype, Subtype.ext_iff.mp, exists_eq_singleton_iff_nonempty_subsingleton, ext_iff, isComplement_singleton_univ, mem_top, mul_inv_cancel
-/
theorem isComplement_univ_right : IsComplement S univ ↔ exists g : G, S = {g} := by
  refine
    ⟨fun h => Set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨?_, fun a ha b hb => ?_⟩, ?_⟩
  · obtain ⟨a, _⟩ := h.2 1
    exact ⟨a.1.1, a.1.2⟩
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_cancel a).trans (mul_inv_cancel b).symm)
    exact Subtype.ext_iff.mp (Prod.ext_iff.mp this).1
  · rintro ⟨g, rfl⟩
    exact isComplement_singleton_univ

@[to_additive]
/--
lemma `IsComplement.mul_eq` / 引理 `IsComplement.mul_eq`

English:
lemma IsComplement.mul_eq
  given: (h : IsComplement S T)
  statement: S * T = univ
  proof: eq_univ_of_forall fun x => by simpa [mem_mul] using (h.existsUnique x).exists

@[to_additive (attr := simp)]

中文:
引理 IsComplement.mul_eq
  条件: (h : IsComplement S T)
  结论: S * T = univ
  证明: eq_univ_of_forall fun x => by simpa [mem_mul] using (h.existsUnique x).exists

@[to_additive (attr := simp)]

Depends on / 依赖: eq_univ_of_forall, existsUnique, h.existsUnique, mem_mul
-/
lemma IsComplement.mul_eq (h : IsComplement S T) : S * T = univ :=
  eq_univ_of_forall fun x => by simpa [mem_mul] using (h.existsUnique x).exists

@[to_additive (attr := simp)]
/--
lemma `not_isComplement_empty_left` / 引理 `not_isComplement_empty_left`

English:
lemma not_isComplement_empty_left
  statement: ¬ IsComplement ∅ T
  proof: fun h => by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive (attr := simp)]

中文:
引理 not_isComplement_empty_left
  结论: ¬ IsComplement ∅ T
  证明: fun h => by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive (attr := simp)]

Depends on / 依赖: eq_comm, h.mul_eq, mul_eq
-/
lemma not_isComplement_empty_left : ¬ IsComplement ∅ T :=
  fun h => by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive (attr := simp)]
/--
lemma `not_isComplement_empty_right` / 引理 `not_isComplement_empty_right`

English:
lemma not_isComplement_empty_right
  statement: ¬ IsComplement S ∅
  proof: fun h => by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive]

中文:
引理 not_isComplement_empty_right
  结论: ¬ IsComplement S ∅
  证明: fun h => by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive]

Depends on / 依赖: eq_comm, h.mul_eq, mul_eq
-/
lemma not_isComplement_empty_right : ¬ IsComplement S ∅ :=
  fun h => by simpa [eq_comm (a := ∅)] using h.mul_eq

@[to_additive]
/--
lemma `IsComplement.nonempty_left` / 引理 `IsComplement.nonempty_left`

English:
lemma IsComplement.nonempty_left
  given: (hst : IsComplement S T)
  statement: S.Nonempty
  proof: by
  contrapose! hst; simp [hst]

@[to_additive]

中文:
引理 IsComplement.nonempty_left
  条件: (hst : IsComplement S T)
  结论: S.非空
  证明: by
  contrapose! hst; simp [hst]

@[to_additive]

Depends on / 依赖: contrapose
-/
lemma IsComplement.nonempty_left (hst : IsComplement S T) : S.Nonempty := by
  contrapose! hst; simp [hst]

@[to_additive]
/--
lemma `IsComplement.nonempty_right` / 引理 `IsComplement.nonempty_right`

English:
lemma IsComplement.nonempty_right
  given: (hst : IsComplement S T)
  statement: T.Nonempty
  proof: by
  contrapose! hst; simp [hst]

中文:
引理 IsComplement.nonempty_right
  条件: (hst : IsComplement S T)
  结论: T.非空
  证明: by
  contrapose! hst; simp [hst]

Depends on / 依赖: contrapose
-/
lemma IsComplement.nonempty_right (hst : IsComplement S T) : T.Nonempty := by
  contrapose! hst; simp [hst]

/--
lemma `IsComplement.pairwiseDisjoint_smul` / 引理 `IsComplement.pairwiseDisjoint_smul`

English:
lemma IsComplement.pairwiseDisjoint_smul
  given: (hst : IsComplement S T)
  proof: fun a ha b hb hab => disjoint_iff_forall_ne.2 by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
  exact hst.1.ne (a₁ := (⟨a, ha⟩, ⟨c, hc⟩)) (a₂ := (⟨b, hb⟩, ⟨d, hd⟩)) (by simp [hab])

@[to_additive AddSubgroup.IsComplement.card_mul_card]

中文:
引理 IsComplement.pairwiseDisjoint_smul
  条件: (hst : IsComplement S T)
  证明: fun a ha b hb hab => disjoint_iff_forall_ne.2 by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
  exact hst.1.ne (a₁ := (⟨a, ha⟩, ⟨c, hc⟩)) (a₂ := (⟨b, hb⟩, ⟨d, hd⟩)) (by simp [hab])

@[to_additive AddSubgroup.IsComplement.card_mul_card]
-/
@[to_additive] lemma IsComplement.pairwiseDisjoint_smul (hst : IsComplement S T) :
S.PairwiseDisjoint (· • T) := fun a ha b hb hab => disjoint_iff_forall_ne.2 by
  rintro _ ⟨c, hc, rfl⟩ _ ⟨d, hd, rfl⟩
  exact hst.1.ne (a₁ := (⟨a, ha⟩, ⟨c, hc⟩)) (a₂ := (⟨b, hb⟩, ⟨d, hd⟩)) (by simp [hab])

@[to_additive AddSubgroup.IsComplement.card_mul_card]
/--
lemma `IsComplement.card_mul_card` / 引理 `IsComplement.card_mul_card`

English:
lemma IsComplement.card_mul_card
  given: (h : IsComplement S T)
  statement: Nat.card S * Nat.card T = Nat.card G
  proof: (Nat.card_prod _ _).symm.trans Nat.card_congr Equiv.ofBijective _ h

@[to_additive]

中文:
引理 IsComplement.card_mul_card
  条件: (h : IsComplement S T)
  结论: 自然数.card S * 自然数.card T = 自然数.card G
  证明: (Nat.card_prod _ _).symm.trans Nat.card_congr Equiv.ofBijective _ h

@[to_additive]

Depends on / 依赖: Equiv.ofBijective, Nat.card_congr, Nat.card_prod, card_congr, card_prod, ofBijective, symm.trans
-/
lemma IsComplement.card_mul_card (h : IsComplement S T) : Nat.card S * Nat.card T = Nat.card G :=
(Nat.card_prod _ _).symm.trans Nat.card_congr Equiv.ofBijective _ h

@[to_additive]
/--
theorem `isComplement'_top_bot` / 定理 `isComplement'_top_bot`

English:
theorem isComplement'_top_bot
  statement: IsComplement' (⊤ : Subgroup G) ⊥
  proof: isComplement_univ_singleton

@[to_additive]

中文:
定理 isComplement'_top_bot
  结论: IsComplement' (⊤ : 子群 G) ⊥
  证明: isComplement_univ_singleton

@[to_additive]
-/
theorem isComplement'_top_bot : IsComplement' (⊤ : Subgroup G) ⊥ :=
  isComplement_univ_singleton

@[to_additive]
/--
theorem `isComplement'_bot_top` / 定理 `isComplement'_bot_top`

English:
theorem isComplement'_bot_top
  statement: IsComplement' (⊥ : Subgroup G) ⊤
  proof: isComplement_singleton_univ

@[to_additive (attr := simp)]

中文:
定理 isComplement'_bot_top
  结论: IsComplement' (⊥ : 子群 G) ⊤
  证明: isComplement_singleton_univ

@[to_additive (attr := simp)]
-/
theorem isComplement'_bot_top : IsComplement' (⊥ : Subgroup G) ⊤ :=
  isComplement_singleton_univ

@[to_additive (attr := simp)]
/--
theorem `isComplement'_bot_left` / 定理 `isComplement'_bot_left`

English:
theorem isComplement'_bot_left
  statement: IsComplement' ⊥ H ↔ H = ⊤
  proof: isComplement_singleton_left.trans coe_eq_univ

@[to_additive (attr := simp)]

中文:
定理 isComplement'_bot_left
  结论: IsComplement' ⊥ H ↔ H = ⊤
  证明: isComplement_singleton_left.trans coe_eq_univ

@[to_additive (attr := simp)]
-/
theorem isComplement'_bot_left : IsComplement' ⊥ H ↔ H = ⊤ :=
  isComplement_singleton_left.trans coe_eq_univ

@[to_additive (attr := simp)]
/--
theorem `isComplement'_bot_right` / 定理 `isComplement'_bot_right`

English:
theorem isComplement'_bot_right
  statement: IsComplement' H ⊥ ↔ H = ⊤
  proof: isComplement_singleton_right.trans coe_eq_univ

@[to_additive (attr := simp)]

中文:
定理 isComplement'_bot_right
  结论: IsComplement' H ⊥ ↔ H = ⊤
  证明: isComplement_singleton_right.trans coe_eq_univ

@[to_additive (attr := simp)]
-/
theorem isComplement'_bot_right : IsComplement' H ⊥ ↔ H = ⊤ :=
  isComplement_singleton_right.trans coe_eq_univ

@[to_additive (attr := simp)]
/--
theorem `isComplement'_top_left` / 定理 `isComplement'_top_left`

English:
theorem isComplement'_top_left
  statement: IsComplement' ⊤ H ↔ H = ⊥
  proof: isComplement_univ_left.trans coe_eq_singleton

@[to_additive (attr := simp)]

中文:
定理 isComplement'_top_left
  结论: IsComplement' ⊤ H ↔ H = ⊥
  证明: isComplement_univ_left.trans coe_eq_singleton

@[to_additive (attr := simp)]
-/
theorem isComplement'_top_left : IsComplement' ⊤ H ↔ H = ⊥ :=
  isComplement_univ_left.trans coe_eq_singleton

@[to_additive (attr := simp)]
/--
theorem `isComplement'_top_right` / 定理 `isComplement'_top_right`

English:
theorem isComplement'_top_right
  statement: IsComplement' H ⊤ ↔ H = ⊥
  proof: isComplement_univ_right.trans coe_eq_singleton

@[to_additive]

中文:
定理 isComplement'_top_right
  结论: IsComplement' H ⊤ ↔ H = ⊥
  证明: isComplement_univ_right.trans coe_eq_singleton

@[to_additive]
-/
theorem isComplement'_top_right : IsComplement' H ⊤ ↔ H = ⊥ :=
  isComplement_univ_right.trans coe_eq_singleton

@[to_additive]
/--
lemma `isComplement_iff_existsUnique_inv_mul_mem` / 引理 `isComplement_iff_existsUnique_inv_mul_mem`

English:
lemma isComplement_iff_existsUnique_inv_mul_mem
  proof: by
  convert! isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(x, ⟨_, hx⟩), by simp, by aesop⟩
  · exact ⟨x.1, by simp [← hx], fun y hy => (Prod.ext_iff.1 <| by simpa using hx' (y, ⟨_, hy⟩)).1⟩

@[to_additive]

中文:
引理 isComplement_iff_存在Unique_inv_mul_mem
  证明: by
  convert! isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(x, ⟨_, hx⟩), by simp, by aesop⟩
  · exact ⟨x.1, by simp [← hx], fun y hy => (Prod.ext_iff.1 <| by simpa using hx' (y, ⟨_, hy⟩)).1⟩

@[to_additive]

Depends on / 依赖: Prod.ext_iff, convert, ext_iff, isComplement_iff_existsUnique
-/
lemma isComplement_iff_existsUnique_inv_mul_mem :
    IsComplement S T ↔ forall g, exists! s : S, (s : G)⁻¹ * g in T := by
  convert! isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(x, ⟨_, hx⟩), by simp, by aesop⟩
  · exact ⟨x.1, by simp [← hx], fun y hy => (Prod.ext_iff.1 <| by simpa using hx' (y, ⟨_, hy⟩)).1⟩

@[to_additive]
/--
lemma `isComplement_iff_existsUnique_mul_inv_mem` / 引理 `isComplement_iff_existsUnique_mul_inv_mem`

English:
lemma isComplement_iff_existsUnique_mul_inv_mem
  proof: by
  convert! isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(⟨_, hx⟩, x), by simp, by aesop⟩
  · exact ⟨x.2, by simp [← hx], fun y hy => (Prod.ext_iff.1 <| by simpa using hx' (⟨_, hy⟩, y)).2⟩

@[to_additive]

中文:
引理 isComplement_iff_存在Unique_mul_inv_mem
  证明: by
  convert! isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(⟨_, hx⟩, x), by simp, by aesop⟩
  · exact ⟨x.2, by simp [← hx], fun y hy => (Prod.ext_iff.1 <| by simpa using hx' (⟨_, hy⟩, y)).2⟩

@[to_additive]

Depends on / 依赖: Prod.ext_iff, convert, ext_iff, isComplement_iff_existsUnique
-/
lemma isComplement_iff_existsUnique_mul_inv_mem :
    IsComplement S T ↔ forall g, exists! t : T, g * (t : G)⁻¹ in S := by
  convert! isComplement_iff_existsUnique with g
  constructor <;> rintro ⟨x, hx, hx'⟩
  · exact ⟨(⟨_, hx⟩, x), by simp, by aesop⟩
  · exact ⟨x.2, by simp [← hx], fun y hy => (Prod.ext_iff.1 <| by simpa using hx' (⟨_, hy⟩, y)).2⟩

@[to_additive]
/--
lemma `isComplement_subgroup_right_iff_existsUnique_quotientGroupMk` / 引理 `isComplement_subgroup_right_iff_existsUnique_quotientGroupMk`

English:
lemma isComplement_subgroup_right_iff_existsUnique_quotientGroupMk
  proof: by
  simp_rw [isComplement_iff_existsUnique_inv_mul_mem, SetLike.mem_coe, ← QuotientGroup.eq,
    QuotientGroup.forall_mk]

中文:
引理 isComplement_subgroup_right_iff_存在Unique_quotientGroupMk
  证明: by
  simp_rw [isComplement_iff_existsUnique_inv_mul_mem, SetLike.mem_coe, ← QuotientGroup.eq,
    QuotientGroup.forall_mk]

Depends on / 依赖: QuotientGroup, QuotientGroup.eq, QuotientGroup.forall_mk, SetLike, SetLike.mem_coe, forall_mk, isComplement_iff_existsUnique_inv_mul_mem, mem_coe, simp_rw
-/
lemma isComplement_subgroup_right_iff_existsUnique_quotientGroupMk :
    IsComplement S H ↔ forall q : G ⧸ H, exists! s : S, QuotientGroup.mk s.1 = q := by
  simp_rw [isComplement_iff_existsUnique_inv_mul_mem, SetLike.mem_coe, ← QuotientGroup.eq,
    QuotientGroup.forall_mk]

set_option linter.docPrime false in
@[to_additive]
/--
lemma `isComplement_subgroup_left_iff_existsUnique_quotientMk''` / 引理 `isComplement_subgroup_left_iff_existsUnique_quotientMk''`

English:
lemma isComplement_subgroup_left_iff_existsUnique_quotientMk''
  proof: by
  simp_rw [isComplement_iff_existsUnique_mul_inv_mem, SetLike.mem_coe,
    ← QuotientGroup.rightRel_apply, ← Quotient.eq'', Quotient.forall]

@[to_additive]

中文:
引理 isComplement_subgroup_left_iff_存在Unique_quotientMk''
  证明: by
  simp_rw [isComplement_iff_existsUnique_mul_inv_mem, SetLike.mem_coe,
    ← QuotientGroup.rightRel_apply, ← Quotient.eq'', Quotient.forall]

@[to_additive]

Depends on / 依赖: Quotient, Quotient.eq, Quotient.forall, QuotientGroup, QuotientGroup.rightRel_apply, SetLike, SetLike.mem_coe, isComplement_iff_existsUnique_mul_inv_mem, mem_coe, rightRel_apply, simp_rw
-/
lemma isComplement_subgroup_left_iff_existsUnique_quotientMk'' :
    IsComplement H T ↔
      forall q : Quotient (QuotientGroup.rightRel H), exists! t : T, Quotient.mk'' t.1 = q := by
  simp_rw [isComplement_iff_existsUnique_mul_inv_mem, SetLike.mem_coe,
    ← QuotientGroup.rightRel_apply, ← Quotient.eq'', Quotient.forall]

@[to_additive]
/--
lemma `isComplement_subgroup_right_iff_bijective` / 引理 `isComplement_subgroup_right_iff_bijective`

English:
lemma isComplement_subgroup_right_iff_bijective
  proof: isComplement_subgroup_right_iff_existsUnique_quotientGroupMk.trans
    (bijective_iff_existsUnique (S.domRestrict QuotientGroup.mk)).symm

@[to_additive]

中文:
引理 isComplement_subgroup_right_iff_bijective
  证明: isComplement_subgroup_right_iff_existsUnique_quotientGroupMk.trans
    (bijective_iff_existsUnique (S.domRestrict QuotientGroup.mk)).symm

@[to_additive]

Depends on / 依赖: QuotientGroup, QuotientGroup.mk, S.domRestrict, bijective_iff_existsUnique, domRestrict, isComplement_subgroup_right_iff_existsUnique_quotientGroupMk, isComplement_subgroup_right_iff_existsUnique_quotientGroupMk.trans
-/
lemma isComplement_subgroup_right_iff_bijective :
    IsComplement S H ↔ Bijective (S.domRestrict (QuotientGroup.mk : G -> G ⧸ H)) :=
  isComplement_subgroup_right_iff_existsUnique_quotientGroupMk.trans
    (bijective_iff_existsUnique (S.domRestrict QuotientGroup.mk)).symm

@[to_additive]
/--
lemma `isComplement_subgroup_left_iff_bijective` / 引理 `isComplement_subgroup_left_iff_bijective`

English:
lemma isComplement_subgroup_left_iff_bijective
  proof: isComplement_subgroup_left_iff_existsUnique_quotientMk''.trans
    (bijective_iff_existsUnique (T.domRestrict Quotient.mk'')).symm

@[to_additive]

中文:
引理 isComplement_subgroup_left_iff_bijective
  证明: isComplement_subgroup_left_iff_existsUnique_quotientMk''.trans
    (bijective_iff_existsUnique (T.domRestrict Quotient.mk'')).symm

@[to_additive]

Depends on / 依赖: Quotient, Quotient.mk, T.domRestrict, bijective_iff_existsUnique, domRestrict, isComplement_subgroup_left_iff_existsUnique_quotientMk
-/
lemma isComplement_subgroup_left_iff_bijective :
    IsComplement H T ↔
      Bijective (T.domRestrict (Quotient.mk'' : G -> Quotient (QuotientGroup.rightRel H))) :=
  isComplement_subgroup_left_iff_existsUnique_quotientMk''.trans
    (bijective_iff_existsUnique (T.domRestrict Quotient.mk'')).symm

@[to_additive]
/--
lemma `IsComplement.card_left` / 引理 `IsComplement.card_left`

English:
lemma IsComplement.card_left
  given: (h : IsComplement S H)
  statement: Nat.card S = H.index
  proof: Nat.card_congr .ofBijective _ isComplement_subgroup_right_iff_bijective.mp h

@[to_additive]

中文:
引理 IsComplement.card_left
  条件: (h : IsComplement S H)
  结论: 自然数.card S = H.index
  证明: Nat.card_congr .ofBijective _ isComplement_subgroup_right_iff_bijective.mp h

@[to_additive]

Depends on / 依赖: Nat.card_congr, card_congr, isComplement_subgroup_right_iff_bijective, isComplement_subgroup_right_iff_bijective.mp, ofBijective
-/
lemma IsComplement.card_left (h : IsComplement S H) : Nat.card S = H.index :=
Nat.card_congr .ofBijective _ isComplement_subgroup_right_iff_bijective.mp h

@[to_additive]
/--
theorem `IsComplement.ncard_left` / 定理 `IsComplement.ncard_left`

English:
theorem IsComplement.ncard_left
  given: (h : IsComplement S H)
  statement: S.ncard = H.index
  proof: by
  rw [← Nat.card_coe_set_eq]; rw [h.card_left]

@[to_additive]

中文:
定理 IsComplement.ncard_left
  条件: (h : IsComplement S H)
  结论: S.ncard = H.index
  证明: by
  rw [← Nat.card_coe_set_eq]; rw [h.card_left]

@[to_additive]

Depends on / 依赖: Nat.card_coe_set_eq, card_coe_set_eq, card_left, h.card_left
-/
theorem IsComplement.ncard_left (h : IsComplement S H) : S.ncard = H.index := by
  rw [← Nat.card_coe_set_eq]; rw [h.card_left]

@[to_additive]
/--
lemma `IsComplement.card_right` / 引理 `IsComplement.card_right`

English:
lemma IsComplement.card_right
  given: (h : IsComplement H T)
  statement: Nat.card T = H.index
  proof: Nat.card_congr (Equiv.ofBijective _ <| isComplement_subgroup_left_iff_bijective.mp h).trans
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H

@[to_additive]

中文:
引理 IsComplement.card_right
  条件: (h : IsComplement H T)
  结论: 自然数.card T = H.index
  证明: Nat.card_congr (Equiv.ofBijective _ <| isComplement_subgroup_left_iff_bijective.mp h).trans
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H

@[to_additive]

Depends on / 依赖: Equiv.ofBijective, Nat.card_congr, QuotientGroup, QuotientGroup.quotientRightRelEquivQuotientLeftRel, card_congr, isComplement_subgroup_left_iff_bijective, isComplement_subgroup_left_iff_bijective.mp, ofBijective, quotientRightRelEquivQuotientLeftRel
-/
lemma IsComplement.card_right (h : IsComplement H T) : Nat.card T = H.index :=
Nat.card_congr (Equiv.ofBijective _ <| isComplement_subgroup_left_iff_bijective.mp h).trans
    QuotientGroup.quotientRightRelEquivQuotientLeftRel H

@[to_additive]
/--
theorem `IsComplement.ncard_right` / 定理 `IsComplement.ncard_right`

English:
theorem IsComplement.ncard_right
  given: (h : IsComplement H T)
  statement: T.ncard = H.index
  proof: by
  rw [← Nat.card_coe_set_eq]; rw [h.card_right]

@[to_additive]

中文:
定理 IsComplement.ncard_right
  条件: (h : IsComplement H T)
  结论: T.ncard = H.index
  证明: by
  rw [← Nat.card_coe_set_eq]; rw [h.card_right]

@[to_additive]

Depends on / 依赖: Nat.card_coe_set_eq, card_coe_set_eq, card_right, h.card_right
-/
theorem IsComplement.ncard_right (h : IsComplement H T) : T.ncard = H.index := by
  rw [← Nat.card_coe_set_eq]; rw [h.card_right]

@[to_additive]
/--
lemma `isComplement_range_left` / 引理 `isComplement_range_left`

English:
lemma isComplement_range_left
  given: {f : G ⧸ H -> G} (hf : forall q, ↑(f q) = q)
  proof: by
  rw [isComplement_subgroup_right_iff_bijective]
  refine ⟨?_, fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
exact Subtype.ext congr_arg f ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]

中文:
引理 isComplement_range_left
  条件: {f : G ⧸ H -> G} (hf : 对任意 q, ↑(f q) = q)
  证明: by
  rw [isComplement_subgroup_right_iff_bijective]
  refine ⟨?_, fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
exact Subtype.ext congr_arg f ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]

Depends on / 依赖: Subtype, Subtype.ext, congr_arg, isComplement_subgroup_right_iff_bijective, symm.trans
-/
lemma isComplement_range_left {f : G ⧸ H -> G} (hf : forall q, ↑(f q) = q) :
    IsComplement (range f) H := by
  rw [isComplement_subgroup_right_iff_bijective]
  refine ⟨?_, fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
exact Subtype.ext congr_arg f ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]
/--
lemma `isComplement_range_right` / 引理 `isComplement_range_right`

English:
lemma isComplement_range_right
  statement: {f : Quotient (QuotientGroup.rightRel H) -> G}
  proof: by
  rw [isComplement_subgroup_left_iff_bijective]
  refine ⟨?_, fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
exact Subtype.ext congr_arg f ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]

中文:
引理 isComplement_range_right
  结论: {f : 商 (商群.rightRel H) -> G}
  证明: by
  rw [isComplement_subgroup_left_iff_bijective]
  refine ⟨?_, fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
exact Subtype.ext congr_arg f ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]

Depends on / 依赖: Subtype, Subtype.ext, congr_arg, isComplement_subgroup_left_iff_bijective, symm.trans
-/
lemma isComplement_range_right {f : Quotient (QuotientGroup.rightRel H) -> G}
    (hf : forall q, Quotient.mk'' (f q) = q) : IsComplement H (range f) := by
  rw [isComplement_subgroup_left_iff_bijective]
  refine ⟨?_, fun q => ⟨⟨f q, q, rfl⟩, hf q⟩⟩
  rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h
exact Subtype.ext congr_arg f ((hf q₁).symm.trans h).trans (hf q₂)

@[to_additive]
/--
lemma `exists_isComplement_left` / 引理 `exists_isComplement_left`

English:
lemma exists_isComplement_left
  given: (H : Subgroup G) (g : G)
  statement: exists S, IsComplement S H ∧ g in S
  proof: by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_left fun q => ?_,
    QuotientGroup.mk g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · simp [Function.update, dif_neg hq, q.out_eq']

@[to_additive]

中文:
引理 存在_isComplement_left
  条件: (H : 子群 G) (g : G)
  结论: 存在 S, IsComplement S H ∧ g in S
  证明: by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_left fun q => ?_,
    QuotientGroup.mk g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · simp [Function.update, dif_neg hq, q.out_eq']

@[to_additive]

Depends on / 依赖: Function, Function.update, Function.update_self, Quotient, Quotient.mk, Quotient.out, QuotientGroup, QuotientGroup.mk, Set.range, classical, congr_arg, dif_neg, hq.symm, isComplement_range_left, out_eq, q.out_eq, update, update_self
-/
lemma exists_isComplement_left (H : Subgroup G) (g : G) : exists S, IsComplement S H ∧ g in S := by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_left fun q => ?_,
    QuotientGroup.mk g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · simp [Function.update, dif_neg hq, q.out_eq']

@[to_additive]
/--
lemma `exists_isComplement_right` / 引理 `exists_isComplement_right`

English:
lemma exists_isComplement_right
  given: (H : Subgroup G) (g : G)
  proof: by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_right fun q => ?_,
    Quotient.mk'' g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · simp [Function.update, dif_neg hq, q.out_eq']

中文:
引理 存在_isComplement_right
  条件: (H : 子群 G) (g : G)
  证明: by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_right fun q => ?_,
    Quotient.mk'' g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · simp [Function.update, dif_neg hq, q.out_eq']

Depends on / 依赖: Function, Function.update, Function.update_self, Quotient, Quotient.mk, Quotient.out, Set.range, classical, congr_arg, dif_neg, hq.symm, isComplement_range_right, out_eq, q.out_eq, update, update_self
-/
lemma exists_isComplement_right (H : Subgroup G) (g : G) :
    exists T, IsComplement H T ∧ g in T := by
  classical
  refine ⟨Set.range (Function.update Quotient.out _ g), isComplement_range_right fun q => ?_,
    Quotient.mk'' g, Function.update_self (Quotient.mk'' g) g Quotient.out⟩
  by_cases hq : q = Quotient.mk'' g
  · exact hq.symm ▸ congr_arg _ (Function.update_self (Quotient.mk'' g) g Quotient.out)
  · simp [Function.update, dif_neg hq, q.out_eq']

/-- Given two subgroups `H' ⊆ H`, there exists a left transversal to `H'` inside `H`. -/
@[to_additive /-- Given two subgroups `H' ⊆ H`, there exists a transversal to `H'` inside `H` -/]
/--
lemma `exists_left_transversal_of_le` / 引理 `exists_left_transversal_of_le`

English:
lemma exists_left_transversal_of_le
  given: {H' H : Subgroup G} (h : H' <= H)
  proof: by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_left 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (S * H'') = H.subtype '' S * H''.map H.subtype := image_mul H.subtype
    rw [← this]; rw [cmem.mul_eq]
    simp
  · rw [← cmem.card_mul_card]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

中文:
引理 存在_left_transversal_of_le
  条件: {H' H : 子群 G} (h : H' <= H)
  证明: by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_left 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (S * H'') = H.subtype '' S * H''.map H.subtype := image_mul H.subtype
    rw [← this]; rw [cmem.mul_eq]
    simp
  · rw [← cmem.card_mul_card]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

Depends on / 依赖: Equiv.Set.image, H.subtype, Nat.card_congr, Subgroup, card_congr, card_mul_card, cmem.card_mul_card, cmem.mul_eq, exists_isComplement_left, image_mul, mul_eq, subtype, subtype_injective
-/
lemma exists_left_transversal_of_le {H' H : Subgroup G} (h : H' <= H) :
    exists S : Set G, S * H' = H ∧ Nat.card S * Nat.card H' = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_left 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (S * H'') = H.subtype '' S * H''.map H.subtype := image_mul H.subtype
    rw [← this]; rw [cmem.mul_eq]
    simp
  · rw [← cmem.card_mul_card]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

/-- Given two subgroups `H' ⊆ H`, there exists a right transversal to `H'` inside `H`. -/
@[to_additive /-- Given two subgroups `H' ⊆ H`, there exists a transversal to `H'` inside `H` -/]
/--
lemma `exists_right_transversal_of_le` / 引理 `exists_right_transversal_of_le`

English:
lemma exists_right_transversal_of_le
  given: {H' H : Subgroup G} (h : H' <= H)
  proof: by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_right 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (H'' * S) = H''.map H.subtype * H.subtype '' S := image_mul H.subtype
    rw [← this]; rw [cmem.mul_eq]
    simp
  · have : Nat.card H'' * Nat.card S = Nat.card H := cmem.card_mul_card
    rw [← this]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

中文:
引理 存在_right_transversal_of_le
  条件: {H' H : 子群 G} (h : H' <= H)
  证明: by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_right 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (H'' * S) = H''.map H.subtype * H.subtype '' S := image_mul H.subtype
    rw [← this]; rw [cmem.mul_eq]
    simp
  · have : Nat.card H'' * Nat.card S = Nat.card H := cmem.card_mul_card
    rw [← this]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

Depends on / 依赖: Equiv.Set.image, H.subtype, Nat.card, Nat.card_congr, Subgroup, card_congr, card_mul_card, cmem.card_mul_card, cmem.mul_eq, exists_isComplement_right, image_mul, mul_eq, subtype, subtype_injective
-/
lemma exists_right_transversal_of_le {H' H : Subgroup G} (h : H' <= H) :
    exists S : Set G, H' * S = H ∧ Nat.card H' * Nat.card S = Nat.card H := by
  let H'' : Subgroup H := H'.comap H.subtype
  have : H' = H''.map H.subtype := by simp [H'', h]
  rw [this]
  obtain ⟨S, cmem, -⟩ := H''.exists_isComplement_right 1
  refine ⟨H.subtype '' S, ?_, ?_⟩
  · have : H.subtype '' (H'' * S) = H''.map H.subtype * H.subtype '' S := image_mul H.subtype
    rw [← this]; rw [cmem.mul_eq]
    simp
  · have : Nat.card H'' * Nat.card S = Nat.card H := cmem.card_mul_card
    rw [← this]
    refine congr_arg₂ (· * ·) ?_ ?_ <;>
      exact Nat.card_congr (Equiv.Set.image _ _ <| subtype_injective H).symm

namespace IsComplement

/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: {S T : Set G} (hST : IsComplement S T)
  body: (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).symm

中文:
定义 equiv
  签名: {S T : 集合 G} (hST : IsComplement S T)
  定义体: (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).symm

Depends on / 依赖: Equiv.ofBijective, ofBijective
-/
noncomputable def equiv {S T : Set G} (hST : IsComplement S T) : G ≃ S × T :=
  (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).symm

variable (hST : IsComplement S T) (hHT : IsComplement H T) (hSK : IsComplement S K)

/--
theorem `equiv_symm_apply` / 定理 `equiv_symm_apply`

English:
theorem equiv_symm_apply
  given: (x : S × T)
  statement: (hST.equiv.symm x : G) = x.1.1 * x.2.1
  proof: rfl

@[simp]

中文:
定理 equiv_symm_apply
  条件: (x : S × T)
  结论: (hST.equiv.symm x : G) = x.1.1 * x.2.1
  证明: rfl

@[simp]
-/
@[simp] theorem equiv_symm_apply (x : S × T) : (hST.equiv.symm x : G) = x.1.1 * x.2.1 := rfl

@[simp]
/--
theorem `equiv_fst_mul_equiv_snd` / 定理 `equiv_fst_mul_equiv_snd`

English:
theorem equiv_fst_mul_equiv_snd
  given: (g : G)
  statement: ↑(hST.equiv g).fst * (hST.equiv g).snd = g
  proof: (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).right_inv g

中文:
定理 equiv_fst_mul_equiv_snd
  条件: (g : G)
  结论: ↑(hST.equiv g).fst * (hST.equiv g).snd = g
  证明: (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).right_inv g

Depends on / 依赖: Equiv.ofBijective, ofBijective, right_inv
-/
theorem equiv_fst_mul_equiv_snd (g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd = g :=
  (Equiv.ofBijective (fun x : S × T => x.1.1 * x.2.1) hST).right_inv g

/--
theorem `equiv_fst_eq_mul_inv` / 定理 `equiv_fst_eq_mul_inv`

English:
theorem equiv_fst_eq_mul_inv
  given: (g : G)
  statement: ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
  proof: eq_mul_inv_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)

中文:
定理 equiv_fst_eq_mul_inv
  条件: (g : G)
  结论: ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
  证明: eq_mul_inv_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)

Depends on / 依赖: eq_mul_inv_of_mul_eq, equiv_fst_mul_equiv_snd, hST.equiv_fst_mul_equiv_snd
-/
theorem equiv_fst_eq_mul_inv (g : G) : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹ :=
  eq_mul_inv_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)

/--
theorem `equiv_snd_eq_inv_mul` / 定理 `equiv_snd_eq_inv_mul`

English:
theorem equiv_snd_eq_inv_mul
  given: (g : G)
  statement: ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
  proof: eq_inv_mul_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)

中文:
定理 equiv_snd_eq_inv_mul
  条件: (g : G)
  结论: ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g
  证明: eq_inv_mul_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)

Depends on / 依赖: eq_inv_mul_of_mul_eq, equiv_fst_mul_equiv_snd, hST.equiv_fst_mul_equiv_snd
-/
theorem equiv_snd_eq_inv_mul (g : G) : ↑(hST.equiv g).snd = ((hST.equiv g).fst : G)⁻¹ * g :=
  eq_inv_mul_of_mul_eq (hST.equiv_fst_mul_equiv_snd g)

/--
theorem `equiv_fst_eq_iff_leftCosetEquivalence` / 定理 `equiv_fst_eq_iff_leftCosetEquivalence`

English:
theorem equiv_fst_eq_iff_leftCosetEquivalence
  given: {g₁ g₂ : G}
  proof: by
  rw [LeftCosetEquivalence]; rw [leftCoset_eq_iff]
  constructor
  · intro h
    rw [← hSK.equiv_fst_mul_equiv_snd g₂]; rw [← hSK.equiv_fst_mul_equiv_snd g₁]; rw [← h]; rw [mul_inv_rev]; rw [← mul_assoc]; rw [inv_mul_cancel_right]; rw [← coe_inv]; rw [← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_inv_mul_mem.1 hSK g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_right h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp [← mul_assoc]

中文:
定理 equiv_fst_eq_iff_leftCosetEquivalence
  条件: {g₁ g₂ : G}
  证明: by
  rw [LeftCosetEquivalence]; rw [leftCoset_eq_iff]
  constructor
  · intro h
    rw [← hSK.equiv_fst_mul_equiv_snd g₂]; rw [← hSK.equiv_fst_mul_equiv_snd g₁]; rw [← h]; rw [mul_inv_rev]; rw [← mul_assoc]; rw [inv_mul_cancel_right]; rw [← coe_inv]; rw [← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_inv_mul_mem.1 hSK g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_right h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp [← mul_assoc]

Depends on / 依赖: LeftCosetEquivalence, SetLike, SetLike.mem_coe, Subtype, Subtype.property, before, coe_inv, coe_mul, equiv_fst_eq_mul_inv, equiv_fst_mul_equiv_snd, github, github.com, hSK.equiv_fst_mul_equiv_snd, inv_mul_cancel_right, isComplement_iff_existsUnique_inv_mul_mem, leanprover, leftCoset_eq_iff, mem_coe, mul_assoc, mul_inv_rev
-/
theorem equiv_fst_eq_iff_leftCosetEquivalence {g₁ g₂ : G} :
    (hSK.equiv g₁).fst = (hSK.equiv g₂).fst ↔ LeftCosetEquivalence K g₁ g₂ := by
  rw [LeftCosetEquivalence]; rw [leftCoset_eq_iff]
  constructor
  · intro h
    rw [← hSK.equiv_fst_mul_equiv_snd g₂]; rw [← hSK.equiv_fst_mul_equiv_snd g₁]; rw [← h]; rw [mul_inv_rev]; rw [← mul_assoc]; rw [inv_mul_cancel_right]; rw [← coe_inv]; rw [← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_inv_mul_mem.1 hSK g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_right h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_fst_eq_mul_inv]; simp [← mul_assoc]

/--
theorem `equiv_snd_eq_iff_rightCosetEquivalence` / 定理 `equiv_snd_eq_iff_rightCosetEquivalence`

English:
theorem equiv_snd_eq_iff_rightCosetEquivalence
  given: {g₁ g₂ : G}
  proof: by
  rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]
  constructor
  · intro h
    rw [← hHT.equiv_fst_mul_equiv_snd g₂]; rw [← hHT.equiv_fst_mul_equiv_snd g₁]; rw [← h]; rw [mul_inv_rev]; rw [mul_assoc]; rw [mul_inv_cancel_left]; rw [← coe_inv]; rw [← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_mul_inv_mem.1 hHT g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_left h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul]; rw [mul_assoc]; simp

中文:
定理 equiv_snd_eq_iff_rightCosetEquivalence
  条件: {g₁ g₂ : G}
  证明: by
  rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]
  constructor
  · intro h
    rw [← hHT.equiv_fst_mul_equiv_snd g₂]; rw [← hHT.equiv_fst_mul_equiv_snd g₁]; rw [← h]; rw [mul_inv_rev]; rw [mul_assoc]; rw [mul_inv_cancel_left]; rw [← coe_inv]; rw [← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_mul_inv_mem.1 hHT g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_left h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul]; rw [mul_assoc]; simp

Depends on / 依赖: RightCosetEquivalence, SetLike, SetLike.mem_coe, Subtype, Subtype.property, before, coe_inv, coe_mul, equiv_fst_mul_equiv_snd, equiv_snd_eq_inv_mul, github, github.com, hHT.equiv_fst_mul_equiv_snd, isComplement_iff_existsUnique_mul_inv_mem, leanprover, mem_coe, mul_assoc, mul_inv_cancel_left, mul_inv_rev, property
-/
theorem equiv_snd_eq_iff_rightCosetEquivalence {g₁ g₂ : G} :
    (hHT.equiv g₁).snd = (hHT.equiv g₂).snd ↔ RightCosetEquivalence H g₁ g₂ := by
  rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]
  constructor
  · intro h
    rw [← hHT.equiv_fst_mul_equiv_snd g₂]; rw [← hHT.equiv_fst_mul_equiv_snd g₁]; rw [← h]; rw [mul_inv_rev]; rw [mul_assoc]; rw [mul_inv_cancel_left]; rw [← coe_inv]; rw [← coe_mul]
    exact Subtype.property _
  · intro h
    apply (isComplement_iff_existsUnique_mul_inv_mem.1 hHT g₁).unique
    · -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul]; simp
    · rw [SetLike.mem_coe, ← mul_mem_cancel_left h]
      -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
      rw [equiv_snd_eq_inv_mul]; rw [mul_assoc]; simp

/--
theorem `leftCosetEquivalence_equiv_fst` / 定理 `leftCosetEquivalence_equiv_fst`

English:
theorem leftCosetEquivalence_equiv_fst
  given: (g : G)
  proof: by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [equiv_fst_eq_mul_inv]; simp [LeftCosetEquivalence, leftCoset_eq_iff]

中文:
定理 leftCosetEquivalence_equiv_fst
  条件: (g : G)
  证明: by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [equiv_fst_eq_mul_inv]; simp [LeftCosetEquivalence, leftCoset_eq_iff]
-/
theorem leftCosetEquivalence_equiv_fst (g : G) :
    LeftCosetEquivalence K g ((hSK.equiv g).fst : G) := by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [equiv_fst_eq_mul_inv]; simp [LeftCosetEquivalence, leftCoset_eq_iff]

/--
theorem `rightCosetEquivalence_equiv_snd` / 定理 `rightCosetEquivalence_equiv_snd`

English:
theorem rightCosetEquivalence_equiv_snd
  given: (g : G)
  proof: by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]; rw [equiv_snd_eq_inv_mul]; simp

中文:
定理 rightCosetEquivalence_equiv_snd
  条件: (g : G)
  证明: by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]; rw [equiv_snd_eq_inv_mul]; simp
-/
theorem rightCosetEquivalence_equiv_snd (g : G) :
    RightCosetEquivalence H g ((hHT.equiv g).snd : G) := by
  -- This used to be `simp [...]` before https://github.com/leanprover/lean4/pull/2644
  rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]; rw [equiv_snd_eq_inv_mul]; simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `equiv_fst_eq_self_of_mem_of_one_mem` / 定理 `equiv_fst_eq_self_of_mem_of_one_mem`

English:
theorem equiv_fst_eq_self_of_mem_of_one_mem
  given: {g : G} (h1 : 1 in T) (hg : g in S)
  proof: by
  have : hST.equiv.symm (⟨g, hg⟩, ⟨1, h1⟩) = g := by
    rw [equiv]; rw [Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

中文:
定理 equiv_fst_eq_self_of_mem_of_one_mem
  条件: {g : G} (h1 : 1 in T) (hg : g in S)
  证明: by
  have : hST.equiv.symm (⟨g, hg⟩, ⟨1, h1⟩) = g := by
    rw [equiv]; rw [Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.ofBijective, apply_symm_apply, conv_lhs, hST.equiv.symm, ofBijective
-/
theorem equiv_fst_eq_self_of_mem_of_one_mem {g : G} (h1 : 1 in T) (hg : g in S) :
    (hST.equiv g).fst = ⟨g, hg⟩ := by
  have : hST.equiv.symm (⟨g, hg⟩, ⟨1, h1⟩) = g := by
    rw [equiv]; rw [Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `equiv_snd_eq_self_of_mem_of_one_mem` / 定理 `equiv_snd_eq_self_of_mem_of_one_mem`

English:
theorem equiv_snd_eq_self_of_mem_of_one_mem
  given: {g : G} (h1 : 1 in S) (hg : g in T)
  proof: by
  have : hST.equiv.symm (⟨1, h1⟩, ⟨g, hg⟩) = g := by
    rw [equiv]; rw [Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

中文:
定理 equiv_snd_eq_self_of_mem_of_one_mem
  条件: {g : G} (h1 : 1 in S) (hg : g in T)
  证明: by
  have : hST.equiv.symm (⟨1, h1⟩, ⟨g, hg⟩) = g := by
    rw [equiv]; rw [Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

Depends on / 依赖: Equiv.apply_symm_apply, Equiv.ofBijective, apply_symm_apply, conv_lhs, hST.equiv.symm, ofBijective
-/
theorem equiv_snd_eq_self_of_mem_of_one_mem {g : G} (h1 : 1 in S) (hg : g in T) :
    (hST.equiv g).snd = ⟨g, hg⟩ := by
  have : hST.equiv.symm (⟨1, h1⟩, ⟨g, hg⟩) = g := by
    rw [equiv]; rw [Equiv.ofBijective]; simp
  conv_lhs => rw [← this, Equiv.apply_symm_apply]

/--
theorem `equiv_snd_eq_one_of_mem_of_one_mem` / 定理 `equiv_snd_eq_one_of_mem_of_one_mem`

English:
theorem equiv_snd_eq_one_of_mem_of_one_mem
  given: {g : G} (h1 : 1 in T) (hg : g in S)
  proof: by
  ext
  rw [equiv_snd_eq_inv_mul]; rw [equiv_fst_eq_self_of_mem_of_one_mem _ h1 hg]; rw [inv_mul_cancel]

中文:
定理 equiv_snd_eq_one_of_mem_of_one_mem
  条件: {g : G} (h1 : 1 in T) (hg : g in S)
  证明: by
  ext
  rw [equiv_snd_eq_inv_mul]; rw [equiv_fst_eq_self_of_mem_of_one_mem _ h1 hg]; rw [inv_mul_cancel]

Depends on / 依赖: equiv_fst_eq_self_of_mem_of_one_mem, equiv_snd_eq_inv_mul, inv_mul_cancel
-/
theorem equiv_snd_eq_one_of_mem_of_one_mem {g : G} (h1 : 1 in T) (hg : g in S) :
    (hST.equiv g).snd = ⟨1, h1⟩ := by
  ext
  rw [equiv_snd_eq_inv_mul]; rw [equiv_fst_eq_self_of_mem_of_one_mem _ h1 hg]; rw [inv_mul_cancel]

/--
theorem `equiv_fst_eq_one_of_mem_of_one_mem` / 定理 `equiv_fst_eq_one_of_mem_of_one_mem`

English:
theorem equiv_fst_eq_one_of_mem_of_one_mem
  given: {g : G} (h1 : 1 in S) (hg : g in T)
  proof: by
  ext
  rw [equiv_fst_eq_mul_inv]; rw [equiv_snd_eq_self_of_mem_of_one_mem _ h1 hg]; rw [mul_inv_cancel]

中文:
定理 equiv_fst_eq_one_of_mem_of_one_mem
  条件: {g : G} (h1 : 1 in S) (hg : g in T)
  证明: by
  ext
  rw [equiv_fst_eq_mul_inv]; rw [equiv_snd_eq_self_of_mem_of_one_mem _ h1 hg]; rw [mul_inv_cancel]

Depends on / 依赖: equiv_fst_eq_mul_inv, equiv_snd_eq_self_of_mem_of_one_mem, mul_inv_cancel
-/
theorem equiv_fst_eq_one_of_mem_of_one_mem {g : G} (h1 : 1 in S) (hg : g in T) :
    (hST.equiv g).fst = ⟨1, h1⟩ := by
  ext
  rw [equiv_fst_eq_mul_inv]; rw [equiv_snd_eq_self_of_mem_of_one_mem _ h1 hg]; rw [mul_inv_cancel]

/--
theorem `equiv_mul_right` / 定理 `equiv_mul_right`

English:
theorem equiv_mul_right
  given: (g : G) (k : K)
  proof: by
  have : (hSK.equiv (g * k)).fst = (hSK.equiv g).fst :=
    hSK.equiv_fst_eq_iff_leftCosetEquivalence.2
      (by simp [LeftCosetEquivalence, leftCoset_eq_iff])
  ext
  · rw [this]
  · rw [coe_mul, equiv_snd_eq_inv_mul, this, equiv_snd_eq_inv_mul, mul_assoc]

中文:
定理 equiv_mul_right
  条件: (g : G) (k : K)
  证明: by
  have : (hSK.equiv (g * k)).fst = (hSK.equiv g).fst :=
    hSK.equiv_fst_eq_iff_leftCosetEquivalence.2
      (by simp [LeftCosetEquivalence, leftCoset_eq_iff])
  ext
  · rw [this]
  · rw [coe_mul, equiv_snd_eq_inv_mul, this, equiv_snd_eq_inv_mul, mul_assoc]

Depends on / 依赖: LeftCosetEquivalence, coe_mul, equiv_fst_eq_iff_leftCosetEquivalence, equiv_snd_eq_inv_mul, hSK.equiv, hSK.equiv_fst_eq_iff_leftCosetEquivalence, leftCoset_eq_iff, mul_assoc
-/
theorem equiv_mul_right (g : G) (k : K) :
    hSK.equiv (g * k) = ((hSK.equiv g).fst, (hSK.equiv g).snd * k) := by
  have : (hSK.equiv (g * k)).fst = (hSK.equiv g).fst :=
    hSK.equiv_fst_eq_iff_leftCosetEquivalence.2
      (by simp [LeftCosetEquivalence, leftCoset_eq_iff])
  ext
  · rw [this]
  · rw [coe_mul, equiv_snd_eq_inv_mul, this, equiv_snd_eq_inv_mul, mul_assoc]

/--
theorem `equiv_mul_right_of_mem` / 定理 `equiv_mul_right_of_mem`

English:
theorem equiv_mul_right_of_mem
  given: {g k : G} (h : k in K)
  proof: equiv_mul_right _ g ⟨k, h⟩

中文:
定理 equiv_mul_right_of_mem
  条件: {g k : G} (h : k in K)
  证明: equiv_mul_right _ g ⟨k, h⟩

Depends on / 依赖: equiv_mul_right
-/
theorem equiv_mul_right_of_mem {g k : G} (h : k in K) :
    hSK.equiv (g * k) = ((hSK.equiv g).fst, (hSK.equiv g).snd * ⟨k, h⟩) :=
  equiv_mul_right _ g ⟨k, h⟩

/--
theorem `equiv_mul_left` / 定理 `equiv_mul_left`

English:
theorem equiv_mul_left
  given: (h : H) (g : G)
  proof: by
  have : (hHT.equiv (h * g)).2 = (hHT.equiv g).2 := hHT.equiv_snd_eq_iff_rightCosetEquivalence.2 ?_
  · ext
    · rw [coe_mul, equiv_fst_eq_mul_inv, this, equiv_fst_eq_mul_inv, mul_assoc]
    · rw [this]
  · simp [RightCosetEquivalence, ← smul_smul]

中文:
定理 equiv_mul_left
  条件: (h : H) (g : G)
  证明: by
  have : (hHT.equiv (h * g)).2 = (hHT.equiv g).2 := hHT.equiv_snd_eq_iff_rightCosetEquivalence.2 ?_
  · ext
    · rw [coe_mul, equiv_fst_eq_mul_inv, this, equiv_fst_eq_mul_inv, mul_assoc]
    · rw [this]
  · simp [RightCosetEquivalence, ← smul_smul]

Depends on / 依赖: RightCosetEquivalence, coe_mul, equiv_fst_eq_mul_inv, equiv_snd_eq_iff_rightCosetEquivalence, hHT.equiv, hHT.equiv_snd_eq_iff_rightCosetEquivalence, mul_assoc, smul_smul
-/
theorem equiv_mul_left (h : H) (g : G) :
    hHT.equiv (h * g) = (h * (hHT.equiv g).fst, (hHT.equiv g).snd) := by
  have : (hHT.equiv (h * g)).2 = (hHT.equiv g).2 := hHT.equiv_snd_eq_iff_rightCosetEquivalence.2 ?_
  · ext
    · rw [coe_mul, equiv_fst_eq_mul_inv, this, equiv_fst_eq_mul_inv, mul_assoc]
    · rw [this]
  · simp [RightCosetEquivalence, ← smul_smul]

/--
theorem `equiv_mul_left_of_mem` / 定理 `equiv_mul_left_of_mem`

English:
theorem equiv_mul_left_of_mem
  given: {h g : G} (hh : h in H)
  proof: equiv_mul_left _ ⟨h, hh⟩ g

中文:
定理 equiv_mul_left_of_mem
  条件: {h g : G} (hh : h in H)
  证明: equiv_mul_left _ ⟨h, hh⟩ g

Depends on / 依赖: equiv_mul_left
-/
theorem equiv_mul_left_of_mem {h g : G} (hh : h in H) :
    hHT.equiv (h * g) = (⟨h, hh⟩ * (hHT.equiv g).fst, (hHT.equiv g).snd) :=
  equiv_mul_left _ ⟨h, hh⟩ g

set_option backward.isDefEq.respectTransparency false in
/--
theorem `equiv_one` / 定理 `equiv_one`

English:
theorem equiv_one
  given: (hs1 : 1 in S) (ht1 : 1 in T)
  proof: by
  rw [← Equiv.eq_symm_apply]; simp [equiv]

中文:
定理 equiv_one
  条件: (hs1 : 1 in S) (ht1 : 1 in T)
  证明: by
  rw [← Equiv.eq_symm_apply]; simp [equiv]

Depends on / 依赖: Equiv.eq_symm_apply, eq_symm_apply
-/
theorem equiv_one (hs1 : 1 in S) (ht1 : 1 in T) :
    hST.equiv 1 = (⟨1, hs1⟩, ⟨1, ht1⟩) := by
  rw [← Equiv.eq_symm_apply]; simp [equiv]

/--
theorem `equiv_fst_eq_self_iff_mem` / 定理 `equiv_fst_eq_self_iff_mem`

English:
theorem equiv_fst_eq_self_iff_mem
  given: {g : G} (h1 : 1 in T)
  proof: by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_fst_eq_self_of_mem_of_one_mem h1 h]

中文:
定理 equiv_fst_eq_self_iff_mem
  条件: {g : G} (h1 : 1 in T)
  证明: by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_fst_eq_self_of_mem_of_one_mem h1 h]

Depends on / 依赖: Subtype, Subtype.prop, equiv_fst_eq_self_of_mem_of_one_mem, hST.equiv_fst_eq_self_of_mem_of_one_mem
-/
theorem equiv_fst_eq_self_iff_mem {g : G} (h1 : 1 in T) :
    ((hST.equiv g).fst : G) = g ↔ g in S := by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_fst_eq_self_of_mem_of_one_mem h1 h]

/--
theorem `equiv_snd_eq_self_iff_mem` / 定理 `equiv_snd_eq_self_iff_mem`

English:
theorem equiv_snd_eq_self_iff_mem
  given: {g : G} (h1 : 1 in S)
  proof: by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_snd_eq_self_of_mem_of_one_mem h1 h]

中文:
定理 equiv_snd_eq_self_iff_mem
  条件: {g : G} (h1 : 1 in S)
  证明: by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_snd_eq_self_of_mem_of_one_mem h1 h]

Depends on / 依赖: Subtype, Subtype.prop, equiv_snd_eq_self_of_mem_of_one_mem, hST.equiv_snd_eq_self_of_mem_of_one_mem
-/
theorem equiv_snd_eq_self_iff_mem {g : G} (h1 : 1 in S) :
    ((hST.equiv g).snd : G) = g ↔ g in T := by
  constructor
  · intro h
    rw [← h]
    exact Subtype.prop _
  · intro h
    rw [hST.equiv_snd_eq_self_of_mem_of_one_mem h1 h]

/--
theorem `coe_equiv_fst_eq_one_iff_mem` / 定理 `coe_equiv_fst_eq_one_iff_mem`

English:
theorem coe_equiv_fst_eq_one_iff_mem
  given: {g : G} (h1 : 1 in S)
  proof: by
  rw [equiv_fst_eq_mul_inv]; rw [mul_inv_eq_one]; rw [eq_comm]; rw [equiv_snd_eq_self_iff_mem _ h1]

中文:
定理 coe_equiv_fst_eq_one_iff_mem
  条件: {g : G} (h1 : 1 in S)
  证明: by
  rw [equiv_fst_eq_mul_inv]; rw [mul_inv_eq_one]; rw [eq_comm]; rw [equiv_snd_eq_self_iff_mem _ h1]

Depends on / 依赖: eq_comm, equiv_fst_eq_mul_inv, equiv_snd_eq_self_iff_mem, mul_inv_eq_one
-/
theorem coe_equiv_fst_eq_one_iff_mem {g : G} (h1 : 1 in S) :
    ((hST.equiv g).fst : G) = 1 ↔ g in T := by
  rw [equiv_fst_eq_mul_inv]; rw [mul_inv_eq_one]; rw [eq_comm]; rw [equiv_snd_eq_self_iff_mem _ h1]

/--
theorem `coe_equiv_snd_eq_one_iff_mem` / 定理 `coe_equiv_snd_eq_one_iff_mem`

English:
theorem coe_equiv_snd_eq_one_iff_mem
  given: {g : G} (h1 : 1 in T)
  proof: by
  rw [equiv_snd_eq_inv_mul]; rw [inv_mul_eq_one]; rw [equiv_fst_eq_self_iff_mem _ h1]

中文:
定理 coe_equiv_snd_eq_one_iff_mem
  条件: {g : G} (h1 : 1 in T)
  证明: by
  rw [equiv_snd_eq_inv_mul]; rw [inv_mul_eq_one]; rw [equiv_fst_eq_self_iff_mem _ h1]

Depends on / 依赖: equiv_fst_eq_self_iff_mem, equiv_snd_eq_inv_mul, inv_mul_eq_one
-/
theorem coe_equiv_snd_eq_one_iff_mem {g : G} (h1 : 1 in T) :
    ((hST.equiv g).snd : G) = 1 ↔ g in S := by
  rw [equiv_snd_eq_inv_mul]; rw [inv_mul_eq_one]; rw [equiv_fst_eq_self_iff_mem _ h1]

/-- A left transversal is in bijection with left cosets. -/
@[to_additive /-- A left transversal is in bijection with left cosets. -/]
/--
Definition of `leftQuotientEquiv` / `leftQuotientEquiv` 的定义

English:
definition leftQuotientEquiv
  signature: (hS : IsComplement S H)
  body: (Equiv.ofBijective _ (isComplement_subgroup_right_iff_bijective.mp hS)).symm

中文:
定义 leftQuotientEquiv
  签名: (hS : IsComplement S H)
  定义体: (Equiv.ofBijective _ (isComplement_subgroup_right_iff_bijective.mp hS)).symm

Depends on / 依赖: Equiv.ofBijective, isComplement_subgroup_right_iff_bijective, isComplement_subgroup_right_iff_bijective.mp, ofBijective
-/
noncomputable def leftQuotientEquiv (hS : IsComplement S H) : G ⧸ H ≃ S :=
  (Equiv.ofBijective _ (isComplement_subgroup_right_iff_bijective.mp hS)).symm

/-- A left transversal is finite iff the subgroup has finite index. -/
@[to_additive /-- A left transversal is finite iff the subgroup has finite index. -/]
/--
theorem `finite_left_iff` / 定理 `finite_left_iff`

English:
theorem finite_left_iff
  given: (h : IsComplement S H)
  statement: Finite S ↔ H.FiniteIndex
  proof: by
  rw [← h.leftQuotientEquiv.finite_iff]
  exact ⟨fun _ => finiteIndex_of_finite_quotient, fun _ => finite_quotient_of_finiteIndex⟩

@[to_additive]

中文:
定理 finite_left_iff
  条件: (h : IsComplement S H)
  结论: 有限 S ↔ H.FiniteIndex
  证明: by
  rw [← h.leftQuotientEquiv.finite_iff]
  exact ⟨fun _ => finiteIndex_of_finite_quotient, fun _ => finite_quotient_of_finiteIndex⟩

@[to_additive]

Depends on / 依赖: finiteIndex_of_finite_quotient, finite_iff, finite_quotient_of_finiteIndex, h.leftQuotientEquiv.finite_iff, leftQuotientEquiv
-/
theorem finite_left_iff (h : IsComplement S H) : Finite S ↔ H.FiniteIndex := by
  rw [← h.leftQuotientEquiv.finite_iff]
  exact ⟨fun _ => finiteIndex_of_finite_quotient, fun _ => finite_quotient_of_finiteIndex⟩

@[to_additive]
/--
lemma `finite_left` / 引理 `finite_left`

English:
lemma finite_left
  given: [H.FiniteIndex] (hS : IsComplement S H)
  statement: S.Finite
  proof: hS.finite_left_iff.2 ‹_›

@[to_additive]

中文:
引理 finite_left
  条件: [H.FiniteIndex] (hS : IsComplement S H)
  结论: S.有限
  证明: hS.finite_left_iff.2 ‹_›

@[to_additive]

Depends on / 依赖: finite_left_iff, hS.finite_left_iff
-/
lemma finite_left [H.FiniteIndex] (hS : IsComplement S H) : S.Finite := hS.finite_left_iff.2 ‹_›

@[to_additive]
/--
theorem `quotientGroupMk_leftQuotientEquiv` / 定理 `quotientGroupMk_leftQuotientEquiv`

English:
theorem quotientGroupMk_leftQuotientEquiv
  given: (hS : IsComplement S H) (q : G ⧸ H)
  proof: hS.leftQuotientEquiv.symm_apply_apply q

@[to_additive]

中文:
定理 quotientGroupMk_leftQuotientEquiv
  条件: (hS : IsComplement S H) (q : G ⧸ H)
  证明: hS.leftQuotientEquiv.symm_apply_apply q

@[to_additive]

Depends on / 依赖: hS.leftQuotientEquiv.symm_apply_apply, leftQuotientEquiv, symm_apply_apply
-/
theorem quotientGroupMk_leftQuotientEquiv (hS : IsComplement S H) (q : G ⧸ H) :
    Quotient.mk'' (leftQuotientEquiv hS q : G) = q :=
  hS.leftQuotientEquiv.symm_apply_apply q

@[to_additive]
/--
theorem `leftQuotientEquiv_apply` / 定理 `leftQuotientEquiv_apply`

English:
theorem leftQuotientEquiv_apply
  given: {f : G ⧸ H -> G} (hf : forall q, (f q : G ⧸ H) = q) (q : G ⧸ H)
  proof: by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (leftQuotientEquiv (isComplement_range_left hf)).eq_symm_apply.mp (hf q).symm

中文:
定理 leftQuotientEquiv_apply
  条件: {f : G ⧸ H -> G} (hf : 对任意 q, (f q : G ⧸ H) = q) (q : G ⧸ H)
  证明: by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (leftQuotientEquiv (isComplement_range_left hf)).eq_symm_apply.mp (hf q).symm

Depends on / 依赖: Subtype, Subtype.coe_mk, Subtype.ext_iff.mp, coe_mk, eq_symm_apply, eq_symm_apply.mp, ext_iff, isComplement_range_left, leftQuotientEquiv
-/
theorem leftQuotientEquiv_apply {f : G ⧸ H -> G} (hf : forall q, (f q : G ⧸ H) = q) (q : G ⧸ H) :
    (leftQuotientEquiv (isComplement_range_left hf) q : G) = f q := by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (leftQuotientEquiv (isComplement_range_left hf)).eq_symm_apply.mp (hf q).symm

/-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/
@[to_additive /-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/]
/--
Definition of `toLeftFun` / `toLeftFun` 的定义

English:
definition toLeftFun
  signature: (hS : IsComplement S H)
  body: leftQuotientEquiv hS ∘ Quotient.mk''

@[to_additive]

中文:
定义 toLeftFun
  签名: (hS : IsComplement S H)
  定义体: leftQuotientEquiv hS ∘ Quotient.mk''

@[to_additive]

Depends on / 依赖: Quotient, Quotient.mk, leftQuotientEquiv
-/
noncomputable def toLeftFun (hS : IsComplement S H) : G -> S := leftQuotientEquiv hS ∘ Quotient.mk''

@[to_additive]
/--
theorem `inv_toLeftFun_mul_mem` / 定理 `inv_toLeftFun_mul_mem`

English:
theorem inv_toLeftFun_mul_mem
  given: (hS : IsComplement S H) (g : G)
  proof: QuotientGroup.leftRel_apply.mp Quotient.exact' quotientGroupMk_leftQuotientEquiv _ _

@[to_additive]

中文:
定理 inv_toLeftFun_mul_mem
  条件: (hS : IsComplement S H) (g : G)
  证明: QuotientGroup.leftRel_apply.mp Quotient.exact' quotientGroupMk_leftQuotientEquiv _ _

@[to_additive]

Depends on / 依赖: Quotient, Quotient.exact, QuotientGroup, QuotientGroup.leftRel_apply.mp, leftRel_apply, quotientGroupMk_leftQuotientEquiv
-/
theorem inv_toLeftFun_mul_mem (hS : IsComplement S H) (g : G) :
    (toLeftFun hS g : G)⁻¹ * g in H :=
QuotientGroup.leftRel_apply.mp Quotient.exact' quotientGroupMk_leftQuotientEquiv _ _

@[to_additive]
/--
theorem `inv_mul_toLeftFun_mem` / 定理 `inv_mul_toLeftFun_mem`

English:
theorem inv_mul_toLeftFun_mem
  given: (hS : IsComplement S H) (g : G)
  proof: (congr_arg (· in H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_toLeftFun_mul_mem hS g))

中文:
定理 inv_mul_toLeftFun_mem
  条件: (hS : IsComplement S H) (g : G)
  证明: (congr_arg (· in H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_toLeftFun_mul_mem hS g))

Depends on / 依赖: H.inv_mem, congr_arg, inv_inv, inv_mem, inv_toLeftFun_mul_mem, mul_inv_rev
-/
theorem inv_mul_toLeftFun_mem (hS : IsComplement S H) (g : G) :
    g⁻¹ * toLeftFun hS g in H :=
  (congr_arg (· in H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (inv_toLeftFun_mul_mem hS g))

/-- A right transversal is in bijection with right cosets. -/
@[to_additive /-- A right transversal is in bijection with right cosets. -/]
/--
Definition of `rightQuotientEquiv` / `rightQuotientEquiv` 的定义

English:
definition rightQuotientEquiv
  signature: (hT : IsComplement H T)
  body: (Equiv.ofBijective _ (isComplement_subgroup_left_iff_bijective.mp hT)).symm

中文:
定义 rightQuotientEquiv
  签名: (hT : IsComplement H T)
  定义体: (Equiv.ofBijective _ (isComplement_subgroup_left_iff_bijective.mp hT)).symm

Depends on / 依赖: Equiv.ofBijective, isComplement_subgroup_left_iff_bijective, isComplement_subgroup_left_iff_bijective.mp, ofBijective
-/
noncomputable def rightQuotientEquiv (hT : IsComplement H T) :
    Quotient (QuotientGroup.rightRel H) ≃ T :=
  (Equiv.ofBijective _ (isComplement_subgroup_left_iff_bijective.mp hT)).symm

/-- A right transversal is finite iff the subgroup has finite index. -/
@[to_additive /-- A right transversal is finite iff the subgroup has finite index. -/]
/--
theorem `finite_right_iff` / 定理 `finite_right_iff`

English:
theorem finite_right_iff
  given: (h : IsComplement H T)
  statement: Finite T ↔ H.FiniteIndex
  proof: by
  rw [← h.rightQuotientEquiv.finite_iff]; rw [(QuotientGroup.quotientRightRelEquivQuotientLeftRel H).finite_iff]
  exact ⟨fun _ => finiteIndex_of_finite_quotient, fun _ => finite_quotient_of_finiteIndex⟩

@[to_additive]

中文:
定理 finite_right_iff
  条件: (h : IsComplement H T)
  结论: 有限 T ↔ H.FiniteIndex
  证明: by
  rw [← h.rightQuotientEquiv.finite_iff]; rw [(QuotientGroup.quotientRightRelEquivQuotientLeftRel H).finite_iff]
  exact ⟨fun _ => finiteIndex_of_finite_quotient, fun _ => finite_quotient_of_finiteIndex⟩

@[to_additive]

Depends on / 依赖: QuotientGroup, QuotientGroup.quotientRightRelEquivQuotientLeftRel, finiteIndex_of_finite_quotient, finite_iff, finite_quotient_of_finiteIndex, h.rightQuotientEquiv.finite_iff, quotientRightRelEquivQuotientLeftRel, rightQuotientEquiv
-/
theorem finite_right_iff (h : IsComplement H T) : Finite T ↔ H.FiniteIndex := by
  rw [← h.rightQuotientEquiv.finite_iff]; rw [(QuotientGroup.quotientRightRelEquivQuotientLeftRel H).finite_iff]
  exact ⟨fun _ => finiteIndex_of_finite_quotient, fun _ => finite_quotient_of_finiteIndex⟩

@[to_additive]
/--
lemma `finite_right` / 引理 `finite_right`

English:
lemma finite_right
  given: [H.FiniteIndex] (hT : IsComplement H T)
  statement: T.Finite
  proof: hT.finite_right_iff.2 ‹_›

@[to_additive]

中文:
引理 finite_right
  条件: [H.FiniteIndex] (hT : IsComplement H T)
  结论: T.有限
  证明: hT.finite_right_iff.2 ‹_›

@[to_additive]

Depends on / 依赖: finite_right_iff, hT.finite_right_iff
-/
lemma finite_right [H.FiniteIndex] (hT : IsComplement H T) : T.Finite := hT.finite_right_iff.2 ‹_›

@[to_additive]
/--
theorem `mk''_rightQuotientEquiv` / 定理 `mk''_rightQuotientEquiv`

English:
theorem mk''_rightQuotientEquiv
  statement: (hT : IsComplement H T)
  proof: (rightQuotientEquiv hT).symm_apply_apply q

@[to_additive]

中文:
定理 mk''_rightQuotientEquiv
  结论: (hT : IsComplement H T)
  证明: (rightQuotientEquiv hT).symm_apply_apply q

@[to_additive]

Depends on / 依赖: rightQuotientEquiv, symm_apply_apply
-/
theorem mk''_rightQuotientEquiv (hT : IsComplement H T)
     (q : Quotient (QuotientGroup.rightRel H)) : Quotient.mk'' (rightQuotientEquiv hT q : G) = q :=
  (rightQuotientEquiv hT).symm_apply_apply q

@[to_additive]
/--
theorem `rightQuotientEquiv_apply` / 定理 `rightQuotientEquiv_apply`

English:
theorem rightQuotientEquiv_apply
  statement: {f : Quotient (QuotientGroup.rightRel H) -> G}
  proof: by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (rightQuotientEquiv (isComplement_range_right hf)).eq_symm_apply.1 (hf q).symm

中文:
定理 rightQuotientEquiv_apply
  结论: {f : 商 (商群.rightRel H) -> G}
  证明: by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (rightQuotientEquiv (isComplement_range_right hf)).eq_symm_apply.1 (hf q).symm

Depends on / 依赖: Subtype, Subtype.coe_mk, Subtype.ext_iff.mp, coe_mk, eq_symm_apply, ext_iff, isComplement_range_right, rightQuotientEquiv
-/
theorem rightQuotientEquiv_apply {f : Quotient (QuotientGroup.rightRel H) -> G}
    (hf : forall q, Quotient.mk'' (f q) = q) (q : Quotient (QuotientGroup.rightRel H)) :
    (rightQuotientEquiv (isComplement_range_right hf) q : G) = f q := by
  refine (Subtype.ext_iff.mp ?_).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (rightQuotientEquiv (isComplement_range_right hf)).eq_symm_apply.1 (hf q).symm

/-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/
@[to_additive /-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/]
/--
Definition of `toRightFun` / `toRightFun` 的定义

English:
definition toRightFun
  signature: (hT : IsComplement H T)
  body: rightQuotientEquiv hT ∘ .mk''

@[to_additive]

中文:
定义 toRightFun
  签名: (hT : IsComplement H T)
  定义体: rightQuotientEquiv hT ∘ .mk''

@[to_additive]

Depends on / 依赖: rightQuotientEquiv
-/
noncomputable def toRightFun (hT : IsComplement H T) : G -> T := rightQuotientEquiv hT ∘ .mk''

@[to_additive]
/--
theorem `mul_inv_toRightFun_mem` / 定理 `mul_inv_toRightFun_mem`

English:
theorem mul_inv_toRightFun_mem
  given: (hT : IsComplement H T) (g : G)
  proof: QuotientGroup.rightRel_apply.mp Quotient.exact' mk''_rightQuotientEquiv _ _

@[to_additive]

中文:
定理 mul_inv_toRightFun_mem
  条件: (hT : IsComplement H T) (g : G)
  证明: QuotientGroup.rightRel_apply.mp Quotient.exact' mk''_rightQuotientEquiv _ _

@[to_additive]

Depends on / 依赖: Quotient, Quotient.exact, QuotientGroup, QuotientGroup.rightRel_apply.mp, _rightQuotientEquiv, rightRel_apply
-/
theorem mul_inv_toRightFun_mem (hT : IsComplement H T) (g : G) :
    g * (toRightFun hT g : G)⁻¹ in H :=
QuotientGroup.rightRel_apply.mp Quotient.exact' mk''_rightQuotientEquiv _ _

@[to_additive]
/--
theorem `toRightFun_mul_inv_mem` / 定理 `toRightFun_mul_inv_mem`

English:
theorem toRightFun_mul_inv_mem
  given: (hT : IsComplement H T) (g : G)
  proof: (congr_arg (· in H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_toRightFun_mem hT g))

@[to_additive]

中文:
定理 toRightFun_mul_inv_mem
  条件: (hT : IsComplement H T) (g : G)
  证明: (congr_arg (· in H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_toRightFun_mem hT g))

@[to_additive]

Depends on / 依赖: H.inv_mem, congr_arg, inv_inv, inv_mem, mul_inv_rev, mul_inv_toRightFun_mem
-/
theorem toRightFun_mul_inv_mem (hT : IsComplement H T) (g : G) :
    (toRightFun hT g : G) * g⁻¹ in H :=
  (congr_arg (· in H) (by rw [mul_inv_rev, inv_inv])).mp (H.inv_mem (mul_inv_toRightFun_mem hT g))

@[to_additive]
/--
theorem `encard_left` / 定理 `encard_left`

English:
theorem encard_left
  given: [H.FiniteIndex] (h : IsComplement S H)
  statement: S.encard = H.index
  proof: by
  rw [← h.finite_left.cast_ncard_eq]; rw [h.ncard_left]

@[to_additive]

中文:
定理 encard_left
  条件: [H.FiniteIndex] (h : IsComplement S H)
  结论: S.encard = H.index
  证明: by
  rw [← h.finite_left.cast_ncard_eq]; rw [h.ncard_left]

@[to_additive]

Depends on / 依赖: cast_ncard_eq, finite_left, h.finite_left.cast_ncard_eq, h.ncard_left, ncard_left
-/
theorem encard_left [H.FiniteIndex] (h : IsComplement S H) : S.encard = H.index := by
  rw [← h.finite_left.cast_ncard_eq]; rw [h.ncard_left]

@[to_additive]
/--
theorem `encard_right` / 定理 `encard_right`

English:
theorem encard_right
  given: [H.FiniteIndex] (h : IsComplement H T)
  statement: T.encard = H.index
  proof: by
  rw [← h.finite_right.cast_ncard_eq]; rw [h.ncard_right]

中文:
定理 encard_right
  条件: [H.FiniteIndex] (h : IsComplement H T)
  结论: T.encard = H.index
  证明: by
  rw [← h.finite_right.cast_ncard_eq]; rw [h.ncard_right]

Depends on / 依赖: cast_ncard_eq, finite_right, h.finite_right.cast_ncard_eq, h.ncard_right, ncard_right
-/
theorem encard_right [H.FiniteIndex] (h : IsComplement H T) : T.encard = H.index := by
  rw [← h.finite_right.cast_ncard_eq]; rw [h.ncard_right]

end IsComplement

section Action

open scoped Pointwise
open MulAction

/-- The collection of left transversals of a subgroup -/
@[to_additive /-- The collection of left transversals of a subgroup. -/]
/--
Definition of `LeftTransversal` / `LeftTransversal` 的定义

English:
abbreviation LeftTransversal
  signature: (H : Subgroup G)
  body: {S : Set G // IsComplement S H}

中文:
缩写 LeftTransversal
  签名: (H : 子群 G)
  定义体: {S : Set G // IsComplement S H}

Depends on / 依赖: IsComplement
-/
abbrev LeftTransversal (H : Subgroup G) := {S : Set G // IsComplement S H}

/-- The collection of right transversals of a subgroup -/
@[to_additive /-- The collection of right transversals of a subgroup. -/]
/--
Definition of `RightTransversal` / `RightTransversal` 的定义

English:
abbreviation RightTransversal
  signature: (H : Subgroup G)
  body: {T : Set G // IsComplement H T}

中文:
缩写 RightTransversal
  签名: (H : 子群 G)
  定义体: {T : Set G // IsComplement H T}

Depends on / 依赖: IsComplement
-/
abbrev RightTransversal (H : Subgroup G) := {T : Set G // IsComplement H T}

variable {F : Type*} [Group F] [MulAction F G] [QuotientAction F H]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction F H.LeftTransversal
  body: ⟨f • (T : Set G), by
      refine isComplement_iff_existsUnique_inv_mul_mem.mpr fun g => ?_
      obtain ⟨t, ht1, ht2⟩ := isComplement_iff_existsUnique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      refine ⟨⟨f • (t : G), Set.smul_mem_smul_set t.2⟩, ?_, ?_⟩
      · exact smul_inv_smul f g ▸ QuotientAction.inv_mul_mem f ht1
      · rintro ⟨-, t', ht', rfl⟩ h
        replace h := QuotientAction.inv_mul_mem f⁻¹ h
        simp only [Subtype.ext_iff, smul_left_cancel_iff, inv_smul_smul] at h ⊢
        exact Subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)⟩
  one_smul T := Subtype.ext (one_smul F (T : Set G))
  mul_smul f₁ f₂ T := Subtype.ext (mul_smul f₁ f₂ (T : Set G))

@[to_additive]

中文:
实例 :
  签名: 乘法作用 F H.LeftTransversal
  定义体: ⟨f • (T : Set G), by
      refine isComplement_iff_existsUnique_inv_mul_mem.mpr fun g => ?_
      obtain ⟨t, ht1, ht2⟩ := isComplement_iff_existsUnique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      refine ⟨⟨f • (t : G), Set.smul_mem_smul_set t.2⟩, ?_, ?_⟩
      · exact smul_inv_smul f g ▸ QuotientAction.inv_mul_mem f ht1
      · rintro ⟨-, t', ht', rfl⟩ h
        replace h := QuotientAction.inv_mul_mem f⁻¹ h
        simp only [Subtype.ext_iff, smul_left_cancel_iff, inv_smul_smul] at h ⊢
        exact Subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)⟩
  one_smul T := Subtype.ext (one_smul F (T : Set G))
  mul_smul f₁ f₂ T := Subtype.ext (mul_smul f₁ f₂ (T : Set G))

@[to_additive]

Depends on / 依赖: QuotientAction, QuotientAction.inv_mul_mem, Set.smul_mem_smul_set, Subtype, Subtype.ext_iff, Subtype.ext_iff.mp, ext_iff, inv_mul_mem, inv_smul_smul, isComplement_iff_existsUnique_inv_mul_mem, isComplement_iff_existsUnique_inv_mul_mem.mp, isComplement_iff_existsUnique_inv_mul_mem.mpr, one_smul, replace, smul_inv_smul, smul_left_cancel_iff, smul_mem_smul_set
-/
noncomputable instance : MulAction F H.LeftTransversal where
  smul f T :=
    ⟨f • (T : Set G), by
      refine isComplement_iff_existsUnique_inv_mul_mem.mpr fun g => ?_
      obtain ⟨t, ht1, ht2⟩ := isComplement_iff_existsUnique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      refine ⟨⟨f • (t : G), Set.smul_mem_smul_set t.2⟩, ?_, ?_⟩
      · exact smul_inv_smul f g ▸ QuotientAction.inv_mul_mem f ht1
      · rintro ⟨-, t', ht', rfl⟩ h
        replace h := QuotientAction.inv_mul_mem f⁻¹ h
        simp only [Subtype.ext_iff, smul_left_cancel_iff, inv_smul_smul] at h ⊢
        exact Subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)⟩
  one_smul T := Subtype.ext (one_smul F (T : Set G))
  mul_smul f₁ f₂ T := Subtype.ext (mul_smul f₁ f₂ (T : Set G))

@[to_additive]
/--
theorem `smul_toLeftFun` / 定理 `smul_toLeftFun`

English:
theorem smul_toLeftFun
  given: (f : F) (S : H.LeftTransversal) (g : G)
  proof: Subtype.ext_iff.mp @ExistsUnique.unique (↥(f • (S : Set G))) (fun s => (↑s)⁻¹ * f • g in H)
    (isComplement_iff_existsUnique_inv_mul_mem.mp (f • S).2 (f • g))
    ⟨f • (S.2.toLeftFun g : G), Set.smul_mem_smul_set (Subtype.coe_prop _)⟩
      ((f • S).2.toLeftFun (f • g))
    (QuotientAction.inv_mul_mem f (S.2.inv_toLeftFun_mul_mem g))
      ((f • S).2.inv_toLeftFun_mul_mem (f • g))

@[to_additive]

中文:
定理 smul_toLeftFun
  条件: (f : F) (S : H.LeftTransversal) (g : G)
  证明: Subtype.ext_iff.mp @ExistsUnique.unique (↥(f • (S : Set G))) (fun s => (↑s)⁻¹ * f • g in H)
    (isComplement_iff_existsUnique_inv_mul_mem.mp (f • S).2 (f • g))
    ⟨f • (S.2.toLeftFun g : G), Set.smul_mem_smul_set (Subtype.coe_prop _)⟩
      ((f • S).2.toLeftFun (f • g))
    (QuotientAction.inv_mul_mem f (S.2.inv_toLeftFun_mul_mem g))
      ((f • S).2.inv_toLeftFun_mul_mem (f • g))

@[to_additive]

Depends on / 依赖: ExistsUnique, ExistsUnique.unique, QuotientAction, QuotientAction.inv_mul_mem, Set.smul_mem_smul_set, Subtype, Subtype.coe_prop, Subtype.ext_iff.mp, coe_prop, ext_iff, inv_mul_mem, inv_toLeftFun_mul_mem, isComplement_iff_existsUnique_inv_mul_mem, isComplement_iff_existsUnique_inv_mul_mem.mp, smul_mem_smul_set, toLeftFun, unique
-/
theorem smul_toLeftFun (f : F) (S : H.LeftTransversal) (g : G) :
    (f • (S.2.toLeftFun g : G)) = (f • S).2.toLeftFun (f • g) :=
Subtype.ext_iff.mp @ExistsUnique.unique (↥(f • (S : Set G))) (fun s => (↑s)⁻¹ * f • g in H)
    (isComplement_iff_existsUnique_inv_mul_mem.mp (f • S).2 (f • g))
    ⟨f • (S.2.toLeftFun g : G), Set.smul_mem_smul_set (Subtype.coe_prop _)⟩
      ((f • S).2.toLeftFun (f • g))
    (QuotientAction.inv_mul_mem f (S.2.inv_toLeftFun_mul_mem g))
      ((f • S).2.inv_toLeftFun_mul_mem (f • g))

@[to_additive]
/--
theorem `smul_leftQuotientEquiv` / 定理 `smul_leftQuotientEquiv`

English:
theorem smul_leftQuotientEquiv
  given: (f : F) (S : H.LeftTransversal) (q : G ⧸ H)
  proof: Quotient.inductionOn' q fun g => smul_toLeftFun f S g

@[to_additive]

中文:
定理 smul_leftQuotientEquiv
  条件: (f : F) (S : H.LeftTransversal) (q : G ⧸ H)
  证明: Quotient.inductionOn' q fun g => smul_toLeftFun f S g

@[to_additive]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, smul_toLeftFun
-/
theorem smul_leftQuotientEquiv (f : F) (S : H.LeftTransversal) (q : G ⧸ H) :
    f • (S.2.leftQuotientEquiv q : G) = (f • S).2.leftQuotientEquiv (f • q) :=
  Quotient.inductionOn' q fun g => smul_toLeftFun f S g

@[to_additive]
/--
theorem `smul_apply_eq_smul_apply_inv_smul` / 定理 `smul_apply_eq_smul_apply_inv_smul`

English:
theorem smul_apply_eq_smul_apply_inv_smul
  given: (f : F) (S : H.LeftTransversal) (q : G ⧸ H)
  proof: by
  rw [smul_leftQuotientEquiv]; rw [smul_inv_smul]

中文:
定理 smul_apply_eq_smul_apply_inv_smul
  条件: (f : F) (S : H.LeftTransversal) (q : G ⧸ H)
  证明: by
  rw [smul_leftQuotientEquiv]; rw [smul_inv_smul]

Depends on / 依赖: smul_inv_smul, smul_leftQuotientEquiv
-/
theorem smul_apply_eq_smul_apply_inv_smul (f : F) (S : H.LeftTransversal) (q : G ⧸ H) :
    ((f • S).2.leftQuotientEquiv q : G) = f • (S.2.leftQuotientEquiv (f⁻¹ • q) : G) := by
  rw [smul_leftQuotientEquiv]; rw [smul_inv_smul]

end Action

@[to_additive]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited H.LeftTransversal
  body: ⟨⟨Set.range Quotient.out, isComplement_range_left Quotient.out_eq'⟩⟩

@[to_additive]

中文:
实例 :
  签名: 可居 H.LeftTransversal
  定义体: ⟨⟨Set.range Quotient.out, isComplement_range_left Quotient.out_eq'⟩⟩

@[to_additive]

Depends on / 依赖: Quotient, Quotient.out, Quotient.out_eq, Set.range, isComplement_range_left, out_eq
-/
noncomputable instance : Inhabited H.LeftTransversal :=
  ⟨⟨Set.range Quotient.out, isComplement_range_left Quotient.out_eq'⟩⟩

@[to_additive]
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited H.RightTransversal
  body: ⟨⟨Set.range Quotient.out, isComplement_range_right Quotient.out_eq'⟩⟩

中文:
实例 :
  签名: 可居 H.RightTransversal
  定义体: ⟨⟨Set.range Quotient.out, isComplement_range_right Quotient.out_eq'⟩⟩

Depends on / 依赖: Quotient, Quotient.out, Quotient.out_eq, Set.range, isComplement_range_right, out_eq
-/
noncomputable instance : Inhabited H.RightTransversal :=
  ⟨⟨Set.range Quotient.out, isComplement_range_right Quotient.out_eq'⟩⟩

/--
theorem `IsComplement'.isCompl` / 定理 `IsComplement'.isCompl`

English:
theorem IsComplement'.isCompl
  given: (h : IsComplement' H K)
  statement: IsCompl H K
  proof: by
  refine
    ⟨disjoint_iff_inf_le.mpr fun g ⟨p, q⟩ =>
        let x : H × K := ⟨⟨g, p⟩, 1⟩
        let y : H × K := ⟨1, g, q⟩
        Subtype.ext_iff.mp
          (Prod.ext_iff.mp (show x = y from h.1 ((mul_one g).trans (one_mul g).symm))).1,
      codisjoint_iff_le_sup.mpr fun g _ => ?_⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  exact Subgroup.mul_mem_sup h.2 k.2

中文:
定理 IsComplement'.isCompl
  条件: (h : IsComplement' H K)
  结论: 是补集 H K
  证明: by
  refine
    ⟨disjoint_iff_inf_le.mpr fun g ⟨p, q⟩ =>
        let x : H × K := ⟨⟨g, p⟩, 1⟩
        let y : H × K := ⟨1, g, q⟩
        Subtype.ext_iff.mp
          (Prod.ext_iff.mp (show x = y from h.1 ((mul_one g).trans (one_mul g).symm))).1,
      codisjoint_iff_le_sup.mpr fun g _ => ?_⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  exact Subgroup.mul_mem_sup h.2 k.2
-/
theorem IsComplement'.isCompl (h : IsComplement' H K) : IsCompl H K := by
  refine
    ⟨disjoint_iff_inf_le.mpr fun g ⟨p, q⟩ =>
        let x : H × K := ⟨⟨g, p⟩, 1⟩
        let y : H × K := ⟨1, g, q⟩
        Subtype.ext_iff.mp
          (Prod.ext_iff.mp (show x = y from h.1 ((mul_one g).trans (one_mul g).symm))).1,
      codisjoint_iff_le_sup.mpr fun g _ => ?_⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  exact Subgroup.mul_mem_sup h.2 k.2

/--
theorem `IsComplement'.sup_eq_top` / 定理 `IsComplement'.sup_eq_top`

English:
theorem IsComplement'.sup_eq_top
  given: (h : IsComplement' H K)
  statement: H ⊔ K = ⊤
  proof: h.isCompl.sup_eq_top

中文:
定理 IsComplement'.sup_eq_top
  条件: (h : IsComplement' H K)
  结论: H ⊔ K = ⊤
  证明: h.isCompl.sup_eq_top
-/
theorem IsComplement'.sup_eq_top (h : IsComplement' H K) : H ⊔ K = ⊤ :=
  h.isCompl.sup_eq_top

/--
theorem `IsComplement'.disjoint` / 定理 `IsComplement'.disjoint`

English:
theorem IsComplement'.disjoint
  given: (h : IsComplement' H K)
  statement: Disjoint H K
  proof: h.isCompl.disjoint

中文:
定理 IsComplement'.disjoint
  条件: (h : IsComplement' H K)
  结论: Disjoint H K
  证明: h.isCompl.disjoint
-/
theorem IsComplement'.disjoint (h : IsComplement' H K) : Disjoint H K :=
  h.isCompl.disjoint

/--
theorem `IsComplement'.index_eq_card` / 定理 `IsComplement'.index_eq_card`

English:
theorem IsComplement'.index_eq_card
  given: (h : IsComplement' H K)
  statement: K.index = Nat.card H
  proof: h.card_left.symm

#adaptation_note

中文:
定理 IsComplement'.index_eq_card
  条件: (h : IsComplement' H K)
  结论: K.index = 自然数.card H
  证明: h.card_left.symm

#adaptation_note
-/
theorem IsComplement'.index_eq_card (h : IsComplement' H K) : K.index = Nat.card H :=
  h.card_left.symm

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- If `H` and `K` are complementary with `K` normal, then `G ⧸ K` is isomorphic to `H`. -/
@[simps!]
/--
Definition of `IsComplement'.QuotientMulEquiv` / `IsComplement'.QuotientMulEquiv` 的定义

English:
definition IsComplement'.QuotientMulEquiv
  signature: [K.Normal] (h : H.IsComplement' K)
  body: MulEquiv.symm
  { h.leftQuotientEquiv.symm with
    map_mul' := fun _ _ => rfl }

中文:
定义 IsComplement'.QuotientMulEquiv
  签名: [K.正规] (h : H.IsComplement' K)
  定义体: MulEquiv.symm
  { h.leftQuotientEquiv.symm with
    map_mul' := fun _ _ => rfl }
-/
noncomputable def IsComplement'.QuotientMulEquiv [K.Normal] (h : H.IsComplement' K) :
    G ⧸ K ≃* H :=
  MulEquiv.symm
  { h.leftQuotientEquiv.symm with
    map_mul' := fun _ _ => rfl }

/--
theorem `IsComplement'.card_mul_card` / 定理 `IsComplement'.card_mul_card`

English:
theorem IsComplement'.card_mul_card
  given: (h : IsComplement' H K)
  proof: IsComplement.card_mul_card h

@[deprecated (since := "2026-08-06")]
alias IsComplement.card_mul := IsComplement.card_mul_card

@[deprecated (since := "2026-08-06")]
alias IsComplement'.card_mul := IsComplement'.card_mul_card

中文:
定理 IsComplement'.card_mul_card
  条件: (h : IsComplement' H K)
  证明: IsComplement.card_mul_card h

@[deprecated (since := "2026-08-06")]
alias IsComplement.card_mul := IsComplement.card_mul_card

@[deprecated (since := "2026-08-06")]
alias IsComplement'.card_mul := IsComplement'.card_mul_card
-/
theorem IsComplement'.card_mul_card (h : IsComplement' H K) :
    Nat.card H * Nat.card K = Nat.card G :=
  IsComplement.card_mul_card h

@[deprecated (since := "2026-08-06")]
alias IsComplement.card_mul := IsComplement.card_mul_card

@[deprecated (since := "2026-08-06")]
alias IsComplement'.card_mul := IsComplement'.card_mul_card

/--
theorem `isComplement'_of_disjoint_and_mul_eq_univ` / 定理 `isComplement'_of_disjoint_and_mul_eq_univ`

English:
theorem isComplement'_of_disjoint_and_mul_eq_univ
  statement: (h1 : Disjoint H K)
  proof: by
  refine ⟨mul_injective_of_disjoint h1, fun g => ?_⟩
  obtain ⟨h, hh, k, hk, hg⟩ := Set.eq_univ_iff_forall.mp h2 g
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩

中文:
定理 isComplement'_of_disjoint_and_mul_eq_univ
  结论: (h1 : Disjoint H K)
  证明: by
  refine ⟨mul_injective_of_disjoint h1, fun g => ?_⟩
  obtain ⟨h, hh, k, hk, hg⟩ := Set.eq_univ_iff_forall.mp h2 g
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩
-/
theorem isComplement'_of_disjoint_and_mul_eq_univ (h1 : Disjoint H K)
    (h2 : ↑H * ↑K = (Set.univ : Set G)) : IsComplement' H K := by
  refine ⟨mul_injective_of_disjoint h1, fun g => ?_⟩
  obtain ⟨h, hh, k, hk, hg⟩ := Set.eq_univ_iff_forall.mp h2 g
  exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), hg⟩

/--
theorem `isComplement'_of_card_mul_and_disjoint` / 定理 `isComplement'_of_card_mul_and_disjoint`

English:
theorem isComplement'_of_card_mul_and_disjoint
  statement: [Finite G]
  proof: (Nat.bijective_iff_injective_and_card _).mpr
    ⟨mul_injective_of_disjoint h2, (Nat.card_prod H K).trans h1⟩

中文:
定理 isComplement'_of_card_mul_and_disjoint
  结论: [有限 G]
  证明: (Nat.bijective_iff_injective_and_card _).mpr
    ⟨mul_injective_of_disjoint h2, (Nat.card_prod H K).trans h1⟩
-/
theorem isComplement'_of_card_mul_and_disjoint [Finite G]
    (h1 : Nat.card H * Nat.card K = Nat.card G) (h2 : Disjoint H K) :
    IsComplement' H K :=
  (Nat.bijective_iff_injective_and_card _).mpr
    ⟨mul_injective_of_disjoint h2, (Nat.card_prod H K).trans h1⟩

/--
theorem `isComplement'_iff_card_mul_and_disjoint` / 定理 `isComplement'_iff_card_mul_and_disjoint`

English:
theorem isComplement'_iff_card_mul_and_disjoint
  given: [Finite G]
  proof: ⟨fun h => ⟨h.card_mul_card, h.disjoint⟩, fun h => isComplement'_of_card_mul_and_disjoint h.1 h.2⟩

中文:
定理 isComplement'_iff_card_mul_and_disjoint
  条件: [有限 G]
  证明: ⟨fun h => ⟨h.card_mul_card, h.disjoint⟩, fun h => isComplement'_of_card_mul_and_disjoint h.1 h.2⟩
-/
theorem isComplement'_iff_card_mul_and_disjoint [Finite G] :
    IsComplement' H K ↔ Nat.card H * Nat.card K = Nat.card G ∧ Disjoint H K :=
  ⟨fun h => ⟨h.card_mul_card, h.disjoint⟩, fun h => isComplement'_of_card_mul_and_disjoint h.1 h.2⟩

/--
theorem `isComplement'_of_coprime` / 定理 `isComplement'_of_coprime`

English:
theorem isComplement'_of_coprime
  statement: [Finite G]
  proof: isComplement'_of_card_mul_and_disjoint h1 disjoint_of_coprime_natCard h2

中文:
定理 isComplement'_of_coprime
  结论: [有限 G]
  证明: isComplement'_of_card_mul_and_disjoint h1 disjoint_of_coprime_natCard h2
-/
theorem isComplement'_of_coprime [Finite G]
    (h1 : Nat.card H * Nat.card K = Nat.card G)
    (h2 : Nat.Coprime (Nat.card H) (Nat.card K)) : IsComplement' H K :=
isComplement'_of_card_mul_and_disjoint h1 disjoint_of_coprime_natCard h2

/--
theorem `isComplement'_stabilizer` / 定理 `isComplement'_stabilizer`

English:
theorem isComplement'_stabilizer
  statement: {α : Type*} [MulAction G α] (a : α)
  proof: by
  refine isComplement_iff_existsUnique.mpr fun g => ?_
  obtain ⟨h, hh⟩ := h2 g
  have hh' : (↑h * g) • a = a := by rwa [mul_smul]
  refine ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_left ↑h g, ?_⟩
  rintro ⟨h', g, hg : g • a = a⟩ rfl
  specialize h1 (h * h') (by rwa [mul_smul, smul_def h', ← hg, ← mul_smul, hg])
  refine Prod.ext (eq_inv_of_mul_eq_one_right h1) (Subtype.ext ?_)
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← right_eq_mul, mul_assoc (↑h) (↑h') g] at h1

中文:
定理 isComplement'_stabilizer
  结论: {α : 类型} [乘法作用 G α] (a : α)
  证明: by
  refine isComplement_iff_existsUnique.mpr fun g => ?_
  obtain ⟨h, hh⟩ := h2 g
  have hh' : (↑h * g) • a = a := by rwa [mul_smul]
  refine ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_left ↑h g, ?_⟩
  rintro ⟨h', g, hg : g • a = a⟩ rfl
  specialize h1 (h * h') (by rwa [mul_smul, smul_def h', ← hg, ← mul_smul, hg])
  refine Prod.ext (eq_inv_of_mul_eq_one_right h1) (Subtype.ext ?_)
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← right_eq_mul, mul_assoc (↑h) (↑h') g] at h1
-/
theorem isComplement'_stabilizer {α : Type*} [MulAction G α] (a : α)
    (h1 : forall h : H, h • a = a -> h = 1) (h2 : forall g : G, exists h : H, h • g • a = a) :
    IsComplement' H (MulAction.stabilizer G a) := by
  refine isComplement_iff_existsUnique.mpr fun g => ?_
  obtain ⟨h, hh⟩ := h2 g
  have hh' : (↑h * g) • a = a := by rwa [mul_smul]
  refine ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_left ↑h g, ?_⟩
  rintro ⟨h', g, hg : g • a = a⟩ rfl
  specialize h1 (h * h') (by rwa [mul_smul, smul_def h', ← hg, ← mul_smul, hg])
  refine Prod.ext (eq_inv_of_mul_eq_one_right h1) (Subtype.ext ?_)
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← right_eq_mul, mul_assoc (↑h) (↑h') g] at h1

end Subgroup
