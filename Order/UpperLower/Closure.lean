/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Order.Interval.Set.OrdConnected
public import Mathlib.Order.Minimal
public import Mathlib.Order.UpperLower.Principal

/-!
# Upper and lower closures

Upper (lower) closures generalise principal upper (lower) sets to arbitrary included sets. Indeed,
they are equivalent to a union over principal upper (lower) sets, as shown in `coe_upperClosure`
(`coe_lowerClosure`).

## Main declarations

* `upperClosure`: The greatest upper set containing a set.
* `lowerClosure`: The least lower set containing a set.
-/

@[expose] public section

open OrderDual Set

variable {α β : Type*} {ι : Sort*}

section Preorder
variable [Preorder α] [Preorder β] {s t : Set α} {x : α}

/-- The greatest upper set containing a given set. -/
@[to_dual /-- The least lower set containing a given set. -/]
/--
Definition of `upperClosure` / `upperClosure` 的定义

English:
definition upperClosure
  signature: (s : Set α)
  body: ⟨{ x | exists a in s, a <= x }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hx.2.trans hle⟩⟩

@[to_dual (attr := simp)]

中文:
定义 upperClosure
  签名: (s : Set α)
  定义体: ⟨{ x | exists a in s, a <= x }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hx.2.trans hle⟩⟩

@[to_dual (attr := simp)]

Depends on / 依赖: h.imp
-/
def upperClosure (s : Set α) : UpperSet α :=
  ⟨{ x | exists a in s, a <= x }, fun _ _ hle h => h.imp fun _x hx => ⟨hx.1, hx.2.trans hle⟩⟩

@[to_dual (attr := simp)]
/--
theorem `mem_upperClosure` / 定理 `mem_upperClosure`

English:
theorem mem_upperClosure
  statement: x in upperClosure s ↔ exists a in s, a <= x
  proof: Iff.rfl

中文:
定理 mem_upperClosure
  结论: x in upperClosure s ↔ 存在 a in s, a <= x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_upperClosure : x in upperClosure s ↔ exists a in s, a <= x :=
  Iff.rfl

-- We do not tag this as `simp` to respect the abstraction.
@[to_dual (attr := norm_cast)]
/--
theorem `coe_upperClosure` / 定理 `coe_upperClosure`

English:
theorem coe_upperClosure
  given: (s : Set α)
  statement: ↑(upperClosure s) = ⋃ a in s, Ici a
  proof: by
  ext
  simp

@[to_dual]

中文:
定理 coe_upperClosure
  条件: (s : Set α)
  结论: ↑(upperClosure s) = ⋃ a in s, Ici a
  证明: by
  ext
  simp

@[to_dual]
-/
theorem coe_upperClosure (s : Set α) : ↑(upperClosure s) = ⋃ a in s, Ici a := by
  ext
  simp

@[to_dual]
/--
Instance `instDecidablePredMemUpperClosure` / 实例 `instDecidablePredMemUpperClosure`

English:
instance instDecidablePredMemUpperClosure
  signature: [DecidablePred (exists a in s, a <= ·)]
  body: ‹DecidablePred _›

@[to_dual]

中文:
实例 instDecidablePredMemUpperClosure
  签名: [DecidablePred (存在 a in s, a <= ·)]
  定义体: ‹DecidablePred _›

@[to_dual]

Depends on / 依赖: DecidablePred
-/
instance instDecidablePredMemUpperClosure [DecidablePred (exists a in s, a <= ·)] :
    DecidablePred (· in upperClosure s) := ‹DecidablePred _›

@[to_dual]
/--
theorem `subset_upperClosure` / 定理 `subset_upperClosure`

English:
theorem subset_upperClosure
  statement: s subseteq upperClosure s
  proof: fun x hx => ⟨x, hx, le_rfl⟩

@[to_dual lowerClosure_min]

中文:
定理 subset_upperClosure
  结论: s subseteq upperClosure s
  证明: fun x hx => ⟨x, hx, le_rfl⟩

@[to_dual lowerClosure_min]

Depends on / 依赖: le_rfl
-/
theorem subset_upperClosure : s subseteq upperClosure s := fun x hx => ⟨x, hx, le_rfl⟩

@[to_dual lowerClosure_min]
/--
theorem `upperClosure_min` / 定理 `upperClosure_min`

English:
theorem upperClosure_min
  given: (h : s subseteq t) (ht : IsUpperSet t)
  statement: ↑(upperClosure s) subseteq t
  proof: fun _a ⟨_b, hb, hba⟩ => ht hba h hb

@[to_dual]

中文:
定理 upperClosure_min
  条件: (h : s subseteq t) (ht : IsUpperSet t)
  结论: ↑(upperClosure s) subseteq t
  证明: fun _a ⟨_b, hb, hba⟩ => ht hba h hb

@[to_dual]
-/
theorem upperClosure_min (h : s subseteq t) (ht : IsUpperSet t) : ↑(upperClosure s) subseteq t :=
fun _a ⟨_b, hb, hba⟩ => ht hba h hb

@[to_dual]
/--
theorem `IsUpperSet.upperClosure` / 定理 `IsUpperSet.upperClosure`

English:
theorem IsUpperSet.upperClosure
  given: (hs : IsUpperSet s)
  statement: ↑(upperClosure s) = s
  proof: (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure

@[to_dual (attr := simp)]

中文:
定理 IsUpperSet.upperClosure
  条件: (hs : IsUpperSet s)
  结论: ↑(upperClosure s) = s
  证明: (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure

@[to_dual (attr := simp)]
-/
protected theorem IsUpperSet.upperClosure (hs : IsUpperSet s) : ↑(upperClosure s) = s :=
  (upperClosure_min Subset.rfl hs).antisymm subset_upperClosure

@[to_dual (attr := simp)]
/--
theorem `UpperSet.upperClosure` / 定理 `UpperSet.upperClosure`

English:
theorem UpperSet.upperClosure
  given: (s : UpperSet α)
  statement: upperClosure (s : Set α) = s
  proof: SetLike.coe_injective s.2.upperClosure

@[to_dual (attr := simp)]

中文:
定理 UpperSet.upperClosure
  条件: (s : UpperSet α)
  结论: upperClosure (s : Set α) = s
  证明: SetLike.coe_injective s.2.upperClosure

@[to_dual (attr := simp)]
-/
protected theorem UpperSet.upperClosure (s : UpperSet α) : upperClosure (s : Set α) = s :=
  SetLike.coe_injective s.2.upperClosure

@[to_dual (attr := simp)]
/--
theorem `upperClosure_image` / 定理 `upperClosure_image`

English:
theorem upperClosure_image
  given: (f : α ≃o β)
  proof: by
  rw [← f.symm_symm]; rw [← UpperSet.symm_map]; rw [f.symm_symm]
  ext
  simp only [SetLike.mem_coe]
  simp [f.le_symm_apply]

@[to_dual (attr := simp)]

中文:
定理 upperClosure_image
  条件: (f : α ≃o β)
  证明: by
  rw [← f.symm_symm]; rw [← UpperSet.symm_map]; rw [f.symm_symm]
  ext
  simp only [SetLike.mem_coe]
  simp [f.le_symm_apply]

@[to_dual (attr := simp)]

Depends on / 依赖: SetLike, SetLike.mem_coe, UpperSet, UpperSet.symm_map, f.le_symm_apply, f.symm_symm, le_symm_apply, mem_coe, symm_map, symm_symm
-/
theorem upperClosure_image (f : α ≃o β) :
    upperClosure (f '' s) = UpperSet.map f (upperClosure s) := by
  rw [← f.symm_symm]; rw [← UpperSet.symm_map]; rw [f.symm_symm]
  ext
  simp only [SetLike.mem_coe]
  simp [f.le_symm_apply]

@[to_dual (attr := simp)]
/--
theorem `UpperSet.iInf_Ici` / 定理 `UpperSet.iInf_Ici`

English:
theorem UpperSet.iInf_Ici
  given: (s : Set α)
  statement: ⨅ a in s, UpperSet.Ici a = upperClosure s
  proof: by
  ext
  simp

@[to_dual (attr := simp) le_upperClosure]

中文:
定理 UpperSet.iInf_Ici
  条件: (s : Set α)
  结论: ⨅ a in s, UpperSet.Ici a = upperClosure s
  证明: by
  ext
  simp

@[to_dual (attr := simp) le_upperClosure]
-/
theorem UpperSet.iInf_Ici (s : Set α) : ⨅ a in s, UpperSet.Ici a = upperClosure s := by
  ext
  simp

@[to_dual (attr := simp) le_upperClosure]
/--
lemma `lowerClosure_le` / 引理 `lowerClosure_le`

English:
lemma lowerClosure_le
  given: {t : LowerSet α}
  statement: lowerClosure s <= t ↔ s subseteq t
  proof: ⟨fun h => subset_lowerClosure.trans LowerSet.coe_subset_coe.2 h,
    fun h => lowerClosure_min h t.lower⟩

中文:
引理 lowerClosure_le
  条件: {t : LowerSet α}
  结论: lowerClosure s <= t ↔ s subseteq t
  证明: ⟨fun h => subset_lowerClosure.trans LowerSet.coe_subset_coe.2 h,
    fun h => lowerClosure_min h t.lower⟩

Depends on / 依赖: LowerSet, LowerSet.coe_subset_coe, coe_subset_coe, lowerClosure_min, subset_lowerClosure, subset_lowerClosure.trans, t.lower
-/
lemma lowerClosure_le {t : LowerSet α} : lowerClosure s <= t ↔ s subseteq t :=
⟨fun h => subset_lowerClosure.trans LowerSet.coe_subset_coe.2 h,
    fun h => lowerClosure_min h t.lower⟩

/--
theorem `gc_upperClosure_coe` / 定理 `gc_upperClosure_coe`

English:
theorem gc_upperClosure_coe
  proof: fun _s _t => le_upperClosure

中文:
定理 gc_upperClosure_coe
  证明: fun _s _t => le_upperClosure

Depends on / 依赖: le_upperClosure
-/
theorem gc_upperClosure_coe :
    GaloisConnection (toDual ∘ upperClosure : Set α -> (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) :=
  fun _s _t => le_upperClosure

/--
theorem `gc_lowerClosure_coe` / 定理 `gc_lowerClosure_coe`

English:
theorem gc_lowerClosure_coe
  proof: fun _s _t => lowerClosure_le

中文:
定理 gc_lowerClosure_coe
  证明: fun _s _t => lowerClosure_le

Depends on / 依赖: lowerClosure_le
-/
theorem gc_lowerClosure_coe :
    GaloisConnection (lowerClosure : Set α -> LowerSet α) (↑) := fun _s _t => lowerClosure_le

/--
Definition of `giUpperClosureCoe` / `giUpperClosureCoe` 的定义

English:
definition giUpperClosureCoe
  signature: :
  body: toDual (⟨s, fun a _b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
choice_eq _s hs := ofDual.injective SetLike.coe_injective subset_upperClosure.antisymm hs

中文:
定义 giUpperClosureCoe
  签名: :
  定义体: toDual (⟨s, fun a _b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
choice_eq _s hs := ofDual.injective SetLike.coe_injective subset_upperClosure.antisymm hs

Depends on / 依赖: UpperSet, toDual
-/
def giUpperClosureCoe :
    GaloisInsertion (toDual ∘ upperClosure : Set α -> (UpperSet α)ᵒᵈ) ((↑) ∘ ofDual) where
  choice s hs := toDual (⟨s, fun a _b hab ha => hs ⟨a, ha, hab⟩⟩ : UpperSet α)
  gc := gc_upperClosure_coe
  le_l_u _ := subset_upperClosure
choice_eq _s hs := ofDual.injective SetLike.coe_injective subset_upperClosure.antisymm hs

/--
Definition of `giLowerClosureCoe` / `giLowerClosureCoe` 的定义

English:
definition giLowerClosureCoe
  signature: : GaloisInsertion (lowerClosure : Set α -> LowerSet α) (↑) where
  body: ⟨s, fun a _b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
choice_eq _s hs := SetLike.coe_injective subset_lowerClosure.antisymm hs

中文:
定义 giLowerClosureCoe
  签名: : GaloisInsertion (lowerClosure : Set α -> LowerSet α) (↑) where
  定义体: ⟨s, fun a _b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
choice_eq _s hs := SetLike.coe_injective subset_lowerClosure.antisymm hs
-/
def giLowerClosureCoe : GaloisInsertion (lowerClosure : Set α -> LowerSet α) (↑) where
  choice s hs := ⟨s, fun a _b hba ha => hs ⟨a, ha, hba⟩⟩
  gc := gc_lowerClosure_coe
  le_l_u _ := subset_lowerClosure
choice_eq _s hs := SetLike.coe_injective subset_lowerClosure.antisymm hs

/--
theorem `upperClosure_anti` / 定理 `upperClosure_anti`

English:
theorem upperClosure_anti
  statement: Antitone (upperClosure : Set α -> UpperSet α)
  proof: gc_upperClosure_coe.monotone_l

中文:
定理 upperClosure_anti
  结论: Antitone (upperClosure : Set α -> UpperSet α)
  证明: gc_upperClosure_coe.monotone_l

Depends on / 依赖: gc_upperClosure_coe, gc_upperClosure_coe.monotone_l, monotone_l
-/
theorem upperClosure_anti : Antitone (upperClosure : Set α -> UpperSet α) :=
  gc_upperClosure_coe.monotone_l

/--
theorem `lowerClosure_mono` / 定理 `lowerClosure_mono`

English:
theorem lowerClosure_mono
  statement: Monotone (lowerClosure : Set α -> LowerSet α)
  proof: gc_lowerClosure_coe.monotone_l

@[to_dual (attr := simp)]

中文:
定理 lowerClosure_mono
  结论: Monotone (lowerClosure : Set α -> LowerSet α)
  证明: gc_lowerClosure_coe.monotone_l

@[to_dual (attr := simp)]

Depends on / 依赖: gc_lowerClosure_coe, gc_lowerClosure_coe.monotone_l, monotone_l
-/
theorem lowerClosure_mono : Monotone (lowerClosure : Set α -> LowerSet α) :=
  gc_lowerClosure_coe.monotone_l

@[to_dual (attr := simp)]
/--
theorem `upperClosure_eq_top_iff` / 定理 `upperClosure_eq_top_iff`

English:
theorem upperClosure_eq_top_iff
  statement: upperClosure s = ⊤ ↔ s = ∅
  proof: by
  rw [eq_top_iff]; rw [le_upperClosure]; simp

@[to_dual (attr := simp)]

中文:
定理 upperClosure_eq_top_iff
  结论: upperClosure s = ⊤ ↔ s = ∅
  证明: by
  rw [eq_top_iff]; rw [le_upperClosure]; simp

@[to_dual (attr := simp)]

Depends on / 依赖: eq_top_iff, le_upperClosure
-/
theorem upperClosure_eq_top_iff : upperClosure s = ⊤ ↔ s = ∅ := by
  rw [eq_top_iff]; rw [le_upperClosure]; simp

@[to_dual (attr := simp)]
/--
theorem `upperClosure_empty` / 定理 `upperClosure_empty`

English:
theorem upperClosure_empty
  statement: upperClosure (∅ : Set α) = ⊤
  proof: upperClosure_eq_top_iff.mpr rfl

@[to_dual (attr := simp)]

中文:
定理 upperClosure_empty
  结论: upperClosure (∅ : Set α) = ⊤
  证明: upperClosure_eq_top_iff.mpr rfl

@[to_dual (attr := simp)]

Depends on / 依赖: upperClosure_eq_top_iff, upperClosure_eq_top_iff.mpr
-/
theorem upperClosure_empty : upperClosure (∅ : Set α) = ⊤ :=
  upperClosure_eq_top_iff.mpr rfl

@[to_dual (attr := simp)]
/--
theorem `upperClosure_singleton` / 定理 `upperClosure_singleton`

English:
theorem upperClosure_singleton
  given: (a : α)
  statement: upperClosure ({a} : Set α) = UpperSet.Ici a
  proof: by
  ext
  simp

@[to_dual (attr := simp)]

中文:
定理 upperClosure_singleton
  条件: (a : α)
  结论: upperClosure ({a} : Set α) = UpperSet.Ici a
  证明: by
  ext
  simp

@[to_dual (attr := simp)]
-/
theorem upperClosure_singleton (a : α) : upperClosure ({a} : Set α) = UpperSet.Ici a := by
  ext
  simp

@[to_dual (attr := simp)]
/--
theorem `upperClosure_univ` / 定理 `upperClosure_univ`

English:
theorem upperClosure_univ
  statement: upperClosure (univ : Set α) = ⊥
  proof: bot_unique subset_upperClosure

中文:
定理 upperClosure_univ
  结论: upperClosure (univ : Set α) = ⊥
  证明: bot_unique subset_upperClosure

Depends on / 依赖: bot_unique, subset_upperClosure
-/
theorem upperClosure_univ : upperClosure (univ : Set α) = ⊥ :=
  bot_unique subset_upperClosure

/--
theorem `upperClosure_union` / 定理 `upperClosure_union`

English:
theorem upperClosure_union
  given: (s t : Set α)
  statement: upperClosure (s union t) = upperClosure s ⊓ upperClosure t
  proof: (@gc_upperClosure_coe α _).l_sup

@[to_dual existing (attr := simp)]

中文:
定理 upperClosure_union
  条件: (s t : Set α)
  结论: upperClosure (s union t) = upperClosure s ⊓ upperClosure t
  证明: (@gc_upperClosure_coe α _).l_sup

@[to_dual existing (attr := simp)]

Depends on / 依赖: gc_upperClosure_coe, l_sup
-/
theorem upperClosure_union (s t : Set α) : upperClosure (s union t) = upperClosure s ⊓ upperClosure t :=
  (@gc_upperClosure_coe α _).l_sup

@[to_dual existing (attr := simp)]
/--
theorem `lowerClosure_union` / 定理 `lowerClosure_union`

English:
theorem lowerClosure_union
  given: (s t : Set α)
  statement: lowerClosure (s union t) = lowerClosure s ⊔ lowerClosure t
  proof: (@gc_lowerClosure_coe α _).l_sup

中文:
定理 lowerClosure_union
  条件: (s t : Set α)
  结论: lowerClosure (s union t) = lowerClosure s ⊔ lowerClosure t
  证明: (@gc_lowerClosure_coe α _).l_sup

Depends on / 依赖: gc_lowerClosure_coe, l_sup
-/
theorem lowerClosure_union (s t : Set α) : lowerClosure (s union t) = lowerClosure s ⊔ lowerClosure t :=
  (@gc_lowerClosure_coe α _).l_sup

/--
theorem `upperClosure_iUnion` / 定理 `upperClosure_iUnion`

English:
theorem upperClosure_iUnion
  given: (f : ι -> Set α)
  statement: upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i)
  proof: (@gc_upperClosure_coe α _).l_iSup

@[to_dual existing (attr := simp)]

中文:
定理 upperClosure_iUnion
  条件: (f : ι -> Set α)
  结论: upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i)
  证明: (@gc_upperClosure_coe α _).l_iSup

@[to_dual existing (attr := simp)]

Depends on / 依赖: gc_upperClosure_coe, l_iSup
-/
theorem upperClosure_iUnion (f : ι -> Set α) : upperClosure (⋃ i, f i) = ⨅ i, upperClosure (f i) :=
  (@gc_upperClosure_coe α _).l_iSup

@[to_dual existing (attr := simp)]
/--
theorem `lowerClosure_iUnion` / 定理 `lowerClosure_iUnion`

English:
theorem lowerClosure_iUnion
  given: (f : ι -> Set α)
  statement: lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i)
  proof: (@gc_lowerClosure_coe α _).l_iSup

@[to_dual (attr := simp)]

中文:
定理 lowerClosure_iUnion
  条件: (f : ι -> Set α)
  结论: lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i)
  证明: (@gc_lowerClosure_coe α _).l_iSup

@[to_dual (attr := simp)]

Depends on / 依赖: gc_lowerClosure_coe, l_iSup
-/
theorem lowerClosure_iUnion (f : ι -> Set α) : lowerClosure (⋃ i, f i) = ⨆ i, lowerClosure (f i) :=
  (@gc_lowerClosure_coe α _).l_iSup

@[to_dual (attr := simp)]
/--
theorem `upperClosure_sUnion` / 定理 `upperClosure_sUnion`

English:
theorem upperClosure_sUnion
  given: (S : Set (Set α))
  statement: upperClosure (⋃₀ S) = ⨅ s in S, upperClosure s
  proof: by
  simp_rw [sUnion_eq_biUnion, upperClosure_iUnion]

中文:
定理 upperClosure_sUnion
  条件: (S : Set (Set α))
  结论: upperClosure (⋃₀ S) = ⨅ s in S, upperClosure s
  证明: by
  simp_rw [sUnion_eq_biUnion, upperClosure_iUnion]

Depends on / 依赖: sUnion_eq_biUnion, simp_rw, upperClosure_iUnion
-/
theorem upperClosure_sUnion (S : Set (Set α)) : upperClosure (⋃₀ S) = ⨅ s in S, upperClosure s := by
  simp_rw [sUnion_eq_biUnion, upperClosure_iUnion]

/--
theorem `Set.OrdConnected.upperClosure_inter_lowerClosure` / 定理 `Set.OrdConnected.upperClosure_inter_lowerClosure`

English:
theorem Set.OrdConnected.upperClosure_inter_lowerClosure
  given: (h : s.OrdConnected)
  proof: (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun _a ⟨⟨_b, hb, hba⟩, _c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩

中文:
定理 Set.OrdConnected.upperClosure_inter_lowerClosure
  条件: (h : s.OrdConnected)
  证明: (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun _a ⟨⟨_b, hb, hba⟩, _c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩

Depends on / 依赖: antisymm, h.out, subset_inter, subset_lowerClosure, subset_upperClosure
-/
theorem Set.OrdConnected.upperClosure_inter_lowerClosure (h : s.OrdConnected) :
    ↑(upperClosure s) inter ↑(lowerClosure s) = s :=
  (subset_inter subset_upperClosure subset_lowerClosure).antisymm'
    fun _a ⟨⟨_b, hb, hba⟩, _c, hc, hac⟩ => h.out hb hc ⟨hba, hac⟩

/--
theorem `ordConnected_iff_upperClosure_inter_lowerClosure` / 定理 `ordConnected_iff_upperClosure_inter_lowerClosure`

English:
theorem ordConnected_iff_upperClosure_inter_lowerClosure
  proof: by
  refine ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => ?_⟩
  rw [← h]
  exact (UpperSet.upper _).ordConnected.inter (LowerSet.lower _).ordConnected

@[to_dual (attr := simp)]

中文:
定理 ordConnected_iff_upperClosure_inter_lowerClosure
  证明: by
  refine ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => ?_⟩
  rw [← h]
  exact (UpperSet.upper _).ordConnected.inter (LowerSet.lower _).ordConnected

@[to_dual (attr := simp)]

Depends on / 依赖: LowerSet, LowerSet.lower, OrdConnected, Set.OrdConnected.upperClosure_inter_lowerClosure, UpperSet, UpperSet.upper, ordConnected, ordConnected.inter, upperClosure_inter_lowerClosure
-/
theorem ordConnected_iff_upperClosure_inter_lowerClosure :
    s.OrdConnected ↔ ↑(upperClosure s) inter ↑(lowerClosure s) = s := by
  refine ⟨Set.OrdConnected.upperClosure_inter_lowerClosure, fun h => ?_⟩
  rw [← h]
  exact (UpperSet.upper _).ordConnected.inter (LowerSet.lower _).ordConnected

@[to_dual (attr := simp)]
/--
theorem `lowerBounds_upperClosure` / 定理 `lowerBounds_upperClosure`

English:
theorem lowerBounds_upperClosure
  statement: lowerBounds (upperClosure s : Set α) = lowerBounds s
  proof: (lowerBounds_mono_set subset_upperClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ => (ha hc).trans hcb

@[to_dual (attr := simp)]

中文:
定理 lowerBounds_upperClosure
  结论: lowerBounds (upperClosure s : Set α) = lowerBounds s
  证明: (lowerBounds_mono_set subset_upperClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ => (ha hc).trans hcb

@[to_dual (attr := simp)]

Depends on / 依赖: antisymm, lowerBounds_mono_set, subset_upperClosure
-/
theorem lowerBounds_upperClosure : lowerBounds (upperClosure s : Set α) = lowerBounds s :=
  (lowerBounds_mono_set subset_upperClosure).antisymm
    fun _a ha _b ⟨_c, hc, hcb⟩ => (ha hc).trans hcb

@[to_dual (attr := simp)]
/--
theorem `bddBelow_upperClosure` / 定理 `bddBelow_upperClosure`

English:
theorem bddBelow_upperClosure
  statement: BddBelow (upperClosure s : Set α) ↔ BddBelow s
  proof: by
  simp_rw [BddBelow, lowerBounds_upperClosure]

@[to_dual]
protected alias ⟨BddBelow.of_upperClosure, BddBelow.upperClosure⟩ := bddBelow_upperClosure

@[to_dual (attr := simp) disjoint_lowerClosure_left]

中文:
定理 bddBelow_upperClosure
  结论: BddBelow (upperClosure s : Set α) ↔ BddBelow s
  证明: by
  simp_rw [BddBelow, lowerBounds_upperClosure]

@[to_dual]
protected alias ⟨BddBelow.of_upperClosure, BddBelow.upperClosure⟩ := bddBelow_upperClosure

@[to_dual (attr := simp) disjoint_lowerClosure_left]

Depends on / 依赖: BddBelow, lowerBounds_upperClosure, simp_rw
-/
theorem bddBelow_upperClosure : BddBelow (upperClosure s : Set α) ↔ BddBelow s := by
  simp_rw [BddBelow, lowerBounds_upperClosure]

@[to_dual]
protected alias ⟨BddBelow.of_upperClosure, BddBelow.upperClosure⟩ := bddBelow_upperClosure

@[to_dual (attr := simp) disjoint_lowerClosure_left]
/--
lemma `IsLowerSet.disjoint_upperClosure_left` / 引理 `IsLowerSet.disjoint_upperClosure_left`

English:
lemma IsLowerSet.disjoint_upperClosure_left
  given: (ht : IsLowerSet t)
  proof: by
  refine ⟨Disjoint.mono_left subset_upperClosure, ?_⟩
  simp only [disjoint_left, SetLike.mem_coe, mem_upperClosure, forall_exists_index, and_imp]
exact fun h a b hb hba ha => h hb ht hba ha

@[to_dual (attr := simp) disjoint_lowerClosure_right]

中文:
引理 IsLowerSet.disjoint_upperClosure_left
  条件: (ht : IsLowerSet t)
  证明: by
  refine ⟨Disjoint.mono_left subset_upperClosure, ?_⟩
  simp only [disjoint_left, SetLike.mem_coe, mem_upperClosure, forall_exists_index, and_imp]
exact fun h a b hb hba ha => h hb ht hba ha

@[to_dual (attr := simp) disjoint_lowerClosure_right]

Depends on / 依赖: Disjoint, Disjoint.mono_left, SetLike, SetLike.mem_coe, and_imp, disjoint_left, forall_exists_index, mem_coe, mem_upperClosure, mono_left, subset_upperClosure
-/
lemma IsLowerSet.disjoint_upperClosure_left (ht : IsLowerSet t) :
    Disjoint ↑(upperClosure s) t ↔ Disjoint s t := by
  refine ⟨Disjoint.mono_left subset_upperClosure, ?_⟩
  simp only [disjoint_left, SetLike.mem_coe, mem_upperClosure, forall_exists_index, and_imp]
exact fun h a b hb hba ha => h hb ht hba ha

@[to_dual (attr := simp) disjoint_lowerClosure_right]
/--
lemma `IsLowerSet.disjoint_upperClosure_right` / 引理 `IsLowerSet.disjoint_upperClosure_right`

English:
lemma IsLowerSet.disjoint_upperClosure_right
  given: (hs : IsLowerSet s)
  proof: by
  simpa only [disjoint_comm] using hs.disjoint_upperClosure_left

@[to_dual (attr := simp)]

中文:
引理 IsLowerSet.disjoint_upperClosure_right
  条件: (hs : IsLowerSet s)
  证明: by
  simpa only [disjoint_comm] using hs.disjoint_upperClosure_left

@[to_dual (attr := simp)]

Depends on / 依赖: disjoint_comm, disjoint_upperClosure_left, hs.disjoint_upperClosure_left
-/
lemma IsLowerSet.disjoint_upperClosure_right (hs : IsLowerSet s) :
    Disjoint s (upperClosure t) ↔ Disjoint s t := by
  simpa only [disjoint_comm] using hs.disjoint_upperClosure_left

@[to_dual (attr := simp)]
/--
lemma `upperClosure_eq` / 引理 `upperClosure_eq`

English:
lemma upperClosure_eq
  proof: ⟨(· ▸ UpperSet.upper _), IsUpperSet.upperClosure⟩

中文:
引理 upperClosure_eq
  证明: ⟨(· ▸ UpperSet.upper _), IsUpperSet.upperClosure⟩

Depends on / 依赖: IsUpperSet, IsUpperSet.upperClosure, UpperSet, UpperSet.upper, upperClosure
-/
lemma upperClosure_eq :
    ↑(upperClosure s) = s ↔ IsUpperSet s :=
  ⟨(· ▸ UpperSet.upper _), IsUpperSet.upperClosure⟩

end Preorder

section PartialOrder
variable [PartialOrder α] {s : Set α} {x : α}

/--
lemma `IsAntichain.minimal_mem_upperClosure_iff_mem` / 引理 `IsAntichain.minimal_mem_upperClosure_iff_mem`

English:
lemma IsAntichain.minimal_mem_upperClosure_iff_mem
  given: (hs : IsAntichain (· <= ·) s)
  proof: by
  simp only [upperClosure]
  refine ⟨fun h => ?_, fun h => ⟨⟨x, h, rfl.le⟩, fun b ⟨a, has, hab⟩ hbx => ?_⟩⟩
  · obtain ⟨a, has, hax⟩ := h.prop
    rwa [h.eq_of_ge ⟨a, has, rfl.le⟩ hax]
  rwa [← hs.eq has h (hab.trans hbx)]

中文:
引理 IsAntichain.minimal_mem_upperClosure_iff_mem
  条件: (hs : IsAntichain (· <= ·) s)
  证明: by
  simp only [upperClosure]
  refine ⟨fun h => ?_, fun h => ⟨⟨x, h, rfl.le⟩, fun b ⟨a, has, hab⟩ hbx => ?_⟩⟩
  · obtain ⟨a, has, hax⟩ := h.prop
    rwa [h.eq_of_ge ⟨a, has, rfl.le⟩ hax]
  rwa [← hs.eq has h (hab.trans hbx)]

Depends on / 依赖: eq_of_ge, h.eq_of_ge, h.prop, hab.trans, hs.eq, rfl.le, upperClosure
-/
lemma IsAntichain.minimal_mem_upperClosure_iff_mem (hs : IsAntichain (· <= ·) s) :
    Minimal (· in upperClosure s) x ↔ x in s := by
  simp only [upperClosure]
  refine ⟨fun h => ?_, fun h => ⟨⟨x, h, rfl.le⟩, fun b ⟨a, has, hab⟩ hbx => ?_⟩⟩
  · obtain ⟨a, has, hax⟩ := h.prop
    rwa [h.eq_of_ge ⟨a, has, rfl.le⟩ hax]
  rwa [← hs.eq has h (hab.trans hbx)]

/--
lemma `IsAntichain.maximal_mem_lowerClosure_iff_mem` / 引理 `IsAntichain.maximal_mem_lowerClosure_iff_mem`

English:
lemma IsAntichain.maximal_mem_lowerClosure_iff_mem
  given: (hs : IsAntichain (· <= ·) s)
  proof: hs.to_dual.minimal_mem_upperClosure_iff_mem

中文:
引理 IsAntichain.maximal_mem_lowerClosure_iff_mem
  条件: (hs : IsAntichain (· <= ·) s)
  证明: hs.to_dual.minimal_mem_upperClosure_iff_mem

Depends on / 依赖: hs.to_dual.minimal_mem_upperClosure_iff_mem, minimal_mem_upperClosure_iff_mem, to_dual
-/
lemma IsAntichain.maximal_mem_lowerClosure_iff_mem (hs : IsAntichain (· <= ·) s) :
    Maximal (· in lowerClosure s) x ↔ x in s :=
  hs.to_dual.minimal_mem_upperClosure_iff_mem

end PartialOrder

section LinearOrder

variable [LinearOrder α]

@[to_dual]
/--
lemma `upperClosure_eq_bot` / 引理 `upperClosure_eq_bot`

English:
lemma upperClosure_eq_bot
  given: {s : Set α} (hs : ¬ BddBelow s)
  statement: upperClosure s = ⊥
  proof: le_bot_iff.mp fun x _ => ⟨_, (not_bddBelow_iff.mp hs x).choose_spec.imp id le_of_lt⟩

@[to_dual]

中文:
引理 upperClosure_eq_bot
  条件: {s : Set α} (hs : ¬ BddBelow s)
  结论: upperClosure s = ⊥
  证明: le_bot_iff.mp fun x _ => ⟨_, (not_bddBelow_iff.mp hs x).choose_spec.imp id le_of_lt⟩

@[to_dual]

Depends on / 依赖: choose_spec, choose_spec.imp, le_bot_iff, le_bot_iff.mp, le_of_lt, not_bddBelow_iff, not_bddBelow_iff.mp
-/
lemma upperClosure_eq_bot {s : Set α} (hs : ¬ BddBelow s) : upperClosure s = ⊥ :=
  le_bot_iff.mp fun x _ => ⟨_, (not_bddBelow_iff.mp hs x).choose_spec.imp id le_of_lt⟩

@[to_dual]
/--
lemma `upperClosure_eq_bot_iff` / 引理 `upperClosure_eq_bot_iff`

English:
lemma upperClosure_eq_bot_iff
  given: [NoMinOrder α] {s : Set α}
  statement: upperClosure s = ⊥ ↔ ¬ BddBelow s
  proof: ⟨fun h₁ h₂ => by simpa [h₁] using bddBelow_upperClosure.mpr h₂, upperClosure_eq_bot⟩

中文:
引理 upperClosure_eq_bot_iff
  条件: [NoMinOrder α] {s : Set α}
  结论: upperClosure s = ⊥ ↔ ¬ BddBelow s
  证明: ⟨fun h₁ h₂ => by simpa [h₁] using bddBelow_upperClosure.mpr h₂, upperClosure_eq_bot⟩

Depends on / 依赖: bddBelow_upperClosure, bddBelow_upperClosure.mpr, upperClosure_eq_bot
-/
lemma upperClosure_eq_bot_iff [NoMinOrder α] {s : Set α} : upperClosure s = ⊥ ↔ ¬ BddBelow s :=
  ⟨fun h₁ h₂ => by simpa [h₁] using bddBelow_upperClosure.mpr h₂, upperClosure_eq_bot⟩

end LinearOrder

/-! ### Set Difference -/

namespace UpperSet
variable [Preorder α] {s : UpperSet α} {t : Set α} {a : α}

/-- The biggest upper subset of an upper set `s` disjoint from a set `t`. -/
@[to_dual /-- The biggest lower subset of a lower set `s` disjoint from a set `t`. -/]
/--
Definition of `sdiff` / `sdiff` 的定义

English:
definition sdiff
  signature: (s : UpperSet α) (t : Set α)
  body: s \ lowerClosure t
  upper' := s.upper.sdiff_of_isLowerSet (lowerClosure t).lower

中文:
定义 sdiff
  签名: (s : UpperSet α) (t : Set α)
  定义体: s \ lowerClosure t
  upper' := s.upper.sdiff_of_isLowerSet (lowerClosure t).lower

Depends on / 依赖: lowerClosure
-/
def sdiff (s : UpperSet α) (t : Set α) : UpperSet α where
  carrier := s \ lowerClosure t
  upper' := s.upper.sdiff_of_isLowerSet (lowerClosure t).lower

/-- The biggest upper subset of an upper set `s` not containing an element `a`. -/
@[to_dual /-- The biggest lower subset of a lower set `s` not containing an element `a`. -/]
/--
Definition of `erase` / `erase` 的定义

English:
definition erase
  signature: (s : UpperSet α) (a : α)
  body: s \ LowerSet.Iic a
  upper' := s.upper.sdiff_of_isLowerSet (LowerSet.Iic a).lower

@[to_dual (attr := simp, norm_cast)]

中文:
定义 erase
  签名: (s : UpperSet α) (a : α)
  定义体: s \ LowerSet.Iic a
  upper' := s.upper.sdiff_of_isLowerSet (LowerSet.Iic a).lower

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: LowerSet, LowerSet.Iic
-/
def erase (s : UpperSet α) (a : α) : UpperSet α where
  carrier := s \ LowerSet.Iic a
  upper' := s.upper.sdiff_of_isLowerSet (LowerSet.Iic a).lower

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_sdiff` / 引理 `coe_sdiff`

English:
lemma coe_sdiff
  given: (s : UpperSet α) (t : Set α)
  statement: s.sdiff t = (s : Set α) \ lowerClosure t
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
引理 coe_sdiff
  条件: (s : UpperSet α) (t : Set α)
  结论: s.sdiff t = (s : Set α) \ lowerClosure t
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
lemma coe_sdiff (s : UpperSet α) (t : Set α) : s.sdiff t = (s : Set α) \ lowerClosure t := rfl

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_erase` / 引理 `coe_erase`

English:
lemma coe_erase
  given: (s : UpperSet α) (a : α)
  statement: s.erase a = (s : Set α) \ LowerSet.Iic a
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 coe_erase
  条件: (s : UpperSet α) (a : α)
  结论: s.erase a = (s : Set α) \ LowerSet.Iic a
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma coe_erase (s : UpperSet α) (a : α) : s.erase a = (s : Set α) \ LowerSet.Iic a := rfl

@[to_dual (attr := simp)]
/--
lemma `sdiff_singleton` / 引理 `sdiff_singleton`

English:
lemma sdiff_singleton
  given: (s : UpperSet α) (a : α)
  statement: s.sdiff {a} = s.erase a
  proof: by
  simp [sdiff, erase]

中文:
引理 sdiff_singleton
  条件: (s : UpperSet α) (a : α)
  结论: s.sdiff {a} = s.erase a
  证明: by
  simp [sdiff, erase]
-/
lemma sdiff_singleton (s : UpperSet α) (a : α) : s.sdiff {a} = s.erase a := by
  simp [sdiff, erase]

/--
lemma `le_sdiff_left` / 引理 `le_sdiff_left`

English:
lemma le_sdiff_left
  statement: s <= s.sdiff t
  proof: sdiff_subset

中文:
引理 le_sdiff_left
  结论: s <= s.sdiff t
  证明: sdiff_subset
-/
@[to_dual sdiff_le_left] lemma le_sdiff_left : s <= s.sdiff t := sdiff_subset
/--
lemma `le_erase` / 引理 `le_erase`

English:
lemma le_erase
  statement: s <= s.erase a
  proof: sdiff_subset

@[to_dual (attr := simp)]

中文:
引理 le_erase
  结论: s <= s.erase a
  证明: sdiff_subset

@[to_dual (attr := simp)]
-/
@[to_dual erase_le] lemma le_erase : s <= s.erase a := sdiff_subset

@[to_dual (attr := simp)]
/--
lemma `sdiff_eq_left` / 引理 `sdiff_eq_left`

English:
lemma sdiff_eq_left
  statement: s.sdiff t = s ↔ Disjoint ↑s t
  proof: by
  simp [← SetLike.coe_set_eq]

@[to_dual (attr := simp)]

中文:
引理 sdiff_eq_left
  结论: s.sdiff t = s ↔ Disjoint ↑s t
  证明: by
  simp [← SetLike.coe_set_eq]

@[to_dual (attr := simp)]
-/
protected lemma sdiff_eq_left : s.sdiff t = s ↔ Disjoint ↑s t := by
  simp [← SetLike.coe_set_eq]

@[to_dual (attr := simp)]
/--
lemma `erase_eq` / 引理 `erase_eq`

English:
lemma erase_eq
  statement: s.erase a = s ↔ a ∉ s
  proof: by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[to_dual (attr := simp) sdiff_lt_left]

中文:
引理 erase_eq
  结论: s.erase a = s ↔ a ∉ s
  证明: by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[to_dual (attr := simp) sdiff_lt_left]

Depends on / 依赖: sdiff_singleton
-/
lemma erase_eq : s.erase a = s ↔ a ∉ s := by rw [← sdiff_singleton]; simp [-sdiff_singleton]

@[to_dual (attr := simp) sdiff_lt_left]
/--
lemma `lt_sdiff_left` / 引理 `lt_sdiff_left`

English:
lemma lt_sdiff_left
  statement: s < s.sdiff t ↔ ¬ Disjoint ↑s t
  proof: le_sdiff_left.lt_iff_ne'.trans UpperSet.sdiff_eq_left.not

@[to_dual (attr := simp) erase_lt]

中文:
引理 lt_sdiff_left
  结论: s < s.sdiff t ↔ ¬ Disjoint ↑s t
  证明: le_sdiff_left.lt_iff_ne'.trans UpperSet.sdiff_eq_left.not

@[to_dual (attr := simp) erase_lt]

Depends on / 依赖: UpperSet, UpperSet.sdiff_eq_left.not, le_sdiff_left, le_sdiff_left.lt_iff_ne, lt_iff_ne, sdiff_eq_left
-/
lemma lt_sdiff_left : s < s.sdiff t ↔ ¬ Disjoint ↑s t :=
  le_sdiff_left.lt_iff_ne'.trans UpperSet.sdiff_eq_left.not

@[to_dual (attr := simp) erase_lt]
/--
lemma `lt_erase` / 引理 `lt_erase`

English:
lemma lt_erase
  statement: s < s.erase a ↔ a in s
  proof: le_erase.lt_iff_ne'.trans erase_eq.not_left

@[to_dual (attr := simp)]

中文:
引理 lt_erase
  结论: s < s.erase a ↔ a in s
  证明: le_erase.lt_iff_ne'.trans erase_eq.not_left

@[to_dual (attr := simp)]

Depends on / 依赖: erase_eq, erase_eq.not_left, le_erase, le_erase.lt_iff_ne, lt_iff_ne, not_left
-/
lemma lt_erase : s < s.erase a ↔ a in s := le_erase.lt_iff_ne'.trans erase_eq.not_left

@[to_dual (attr := simp)]
/--
lemma `sdiff_idem` / 引理 `sdiff_idem`

English:
lemma sdiff_idem
  given: (s : UpperSet α) (t : Set α)
  statement: (s.sdiff t).sdiff t = s.sdiff t
  proof: SetLike.coe_injective sdiff_idem

@[to_dual (attr := simp)]

中文:
引理 sdiff_idem
  条件: (s : UpperSet α) (t : Set α)
  结论: (s.sdiff t).sdiff t = s.sdiff t
  证明: SetLike.coe_injective sdiff_idem

@[to_dual (attr := simp)]
-/
protected lemma sdiff_idem (s : UpperSet α) (t : Set α) : (s.sdiff t).sdiff t = s.sdiff t :=
  SetLike.coe_injective sdiff_idem

@[to_dual (attr := simp)]
/--
lemma `erase_idem` / 引理 `erase_idem`

English:
lemma erase_idem
  given: (s : UpperSet α) (a : α)
  statement: (s.erase a).erase a = s.erase a
  proof: SetLike.coe_injective sdiff_idem

@[to_dual]

中文:
引理 erase_idem
  条件: (s : UpperSet α) (a : α)
  结论: (s.erase a).erase a = s.erase a
  证明: SetLike.coe_injective sdiff_idem

@[to_dual]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, sdiff_idem
-/
lemma erase_idem (s : UpperSet α) (a : α) : (s.erase a).erase a = s.erase a :=
  SetLike.coe_injective sdiff_idem

@[to_dual]
/--
lemma `sdiff_inf_upperClosure` / 引理 `sdiff_inf_upperClosure`

English:
lemma sdiff_inf_upperClosure
  given: (hts : t subseteq s) (hst : forall b in s, forall c in t, b <= c -> b in t)
  proof: by
  refine ge_antisymm (le_inf le_sdiff_left <| le_upperClosure.2 hts) fun a ha => ?_
  obtain hat | hat := em (a in t)
  · exact subset_union_right (subset_upperClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hab⟩
exact hat hst _ ha _ hb hab

@[to_dual]

中文:
引理 sdiff_inf_upperClosure
  条件: (hts : t subseteq s) (hst : 对任意 b in s, 对任意 c in t, b <= c -> b in t)
  证明: by
  refine ge_antisymm (le_inf le_sdiff_left <| le_upperClosure.2 hts) fun a ha => ?_
  obtain hat | hat := em (a in t)
  · exact subset_union_right (subset_upperClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hab⟩
exact hat hst _ ha _ hb hab

@[to_dual]

Depends on / 依赖: ge_antisymm, le_inf, le_sdiff_left, le_upperClosure, subset_union_left, subset_union_right, subset_upperClosure
-/
lemma sdiff_inf_upperClosure (hts : t subseteq s) (hst : forall b in s, forall c in t, b <= c -> b in t) :
    s.sdiff t ⊓ upperClosure t = s := by
  refine ge_antisymm (le_inf le_sdiff_left <| le_upperClosure.2 hts) fun a ha => ?_
  obtain hat | hat := em (a in t)
  · exact subset_union_right (subset_upperClosure hat)
  · refine subset_union_left ⟨ha, ?_⟩
    rintro ⟨b, hb, hab⟩
exact hat hst _ ha _ hb hab

@[to_dual]
/--
lemma `upperClosure_inf_sdiff` / 引理 `upperClosure_inf_sdiff`

English:
lemma upperClosure_inf_sdiff
  given: (hts : t subseteq s) (hst : forall b in s, forall c in t, b <= c -> b in t)
  proof: by rw [inf_comm, sdiff_inf_upperClosure hts hst]

@[to_dual]

中文:
引理 upperClosure_inf_sdiff
  条件: (hts : t subseteq s) (hst : 对任意 b in s, 对任意 c in t, b <= c -> b in t)
  证明: by rw [inf_comm, sdiff_inf_upperClosure hts hst]

@[to_dual]

Depends on / 依赖: inf_comm, sdiff_inf_upperClosure
-/
lemma upperClosure_inf_sdiff (hts : t subseteq s) (hst : forall b in s, forall c in t, b <= c -> b in t) :
    upperClosure t ⊓ s.sdiff t = s := by rw [inf_comm, sdiff_inf_upperClosure hts hst]

@[to_dual]
/--
lemma `erase_inf_Ici` / 引理 `erase_inf_Ici`

English:
lemma erase_inf_Ici
  given: (ha : a in s) (has : forall b in s, b <= a -> b = a)
  statement: s.erase a ⊓ Ici a = s
  proof: by
  rw [← upperClosure_singleton]; rw [← sdiff_singleton]; rw [sdiff_inf_upperClosure] <;> simpa

@[to_dual]

中文:
引理 erase_inf_Ici
  条件: (ha : a in s) (has : 对任意 b in s, b <= a -> b = a)
  结论: s.erase a ⊓ Ici a = s
  证明: by
  rw [← upperClosure_singleton]; rw [← sdiff_singleton]; rw [sdiff_inf_upperClosure] <;> simpa

@[to_dual]

Depends on / 依赖: sdiff_inf_upperClosure, sdiff_singleton, upperClosure_singleton
-/
lemma erase_inf_Ici (ha : a in s) (has : forall b in s, b <= a -> b = a) : s.erase a ⊓ Ici a = s := by
  rw [← upperClosure_singleton]; rw [← sdiff_singleton]; rw [sdiff_inf_upperClosure] <;> simpa

@[to_dual]
/--
lemma `Ici_inf_erase` / 引理 `Ici_inf_erase`

English:
lemma Ici_inf_erase
  given: (ha : a in s) (has : forall b in s, b <= a -> b = a)
  statement: Ici a ⊓ s.erase a = s
  proof: by
  rw [inf_comm]; rw [erase_inf_Ici ha has]

中文:
引理 Ici_inf_erase
  条件: (ha : a in s) (has : 对任意 b in s, b <= a -> b = a)
  结论: Ici a ⊓ s.erase a = s
  证明: by
  rw [inf_comm]; rw [erase_inf_Ici ha has]

Depends on / 依赖: erase_inf_Ici, inf_comm
-/
lemma Ici_inf_erase (ha : a in s) (has : forall b in s, b <= a -> b = a) : Ici a ⊓ s.erase a = s := by
  rw [inf_comm]; rw [erase_inf_Ici ha has]

end UpperSet
