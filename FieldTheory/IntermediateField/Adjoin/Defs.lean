/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# Adjoining Elements to Fields

In this file we introduce the notion of adjoining elements to fields.
This isn't quite the same as adjoining elements to rings.
For example, `K[x]` might not include `x⁻¹`.

## Notation

- `F⟮α⟯`: adjoin a single element `α` to `F` (in scope `IntermediateField`).
-/

@[expose] public section

open Module Polynomial

namespace IntermediateField

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

/-- `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`. -/
@[stacks 09FZ "first part"]
/--
Definition of `adjoin` / `adjoin` 的定义

English:
definition adjoin
  signature: : IntermediateField F E
  body: { Subfield.closure (Set.range (algebraMap F E) union S) with
    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

@[simp]

中文:
定义 adjoin
  签名: : 中间域 F E
  定义体: { Subfield.closure (Set.range (algebraMap F E) union S) with
    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

@[simp]

Depends on / 依赖: Or.inl, Set.mem_range_self, Set.range, Subfield, Subfield.closure, Subfield.subset_closure, algebraMap, algebraMap_mem, closure, mem_range_self, subset_closure
-/
def adjoin : IntermediateField F E :=
  { Subfield.closure (Set.range (algebraMap F E) union S) with
    algebraMap_mem' := fun x => Subfield.subset_closure (Or.inl (Set.mem_range_self x)) }

@[simp]
/--
theorem `adjoin_toSubfield` / 定理 `adjoin_toSubfield`

English:
theorem adjoin_toSubfield
  proof: rfl

中文:
定理 adjoin_toSubfield
  证明: rfl
-/
theorem adjoin_toSubfield :
    (adjoin F S).toSubfield = Subfield.closure (Set.range (algebraMap F E) union S) := rfl

variable {F S} in
/--
theorem `mem_adjoin_iff_div` / 定理 `mem_adjoin_iff_div`

English:
theorem mem_adjoin_iff_div
  given: {x : E}
  statement: x in adjoin F S ↔
  proof: by
  simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring, eq_comm]

中文:
定理 mem_adjoin_iff_div
  条件: {x : E}
  结论: x in adjoin F S ↔
  证明: by
  simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring, eq_comm]

Depends on / 依赖: Algebra, Algebra.adjoin_eq_ring_closure, Subalgebra, Subalgebra.mem_toSubring, Subfield, Subfield.mem_closure_iff, Subfield.mem_toSubring, Subring, Subring.mem_toSubsemiring, adjoin, adjoin_eq_ring_closure, eq_comm, mem_closure_iff, mem_mk, mem_toSubring, mem_toSubsemiring, simp_rw
-/
theorem mem_adjoin_iff_div {x : E} : x in adjoin F S ↔
    exists r in Algebra.adjoin F S, exists s in Algebra.adjoin F S, x = r / s := by
  simp_rw [adjoin, mem_mk, Subring.mem_toSubsemiring, Subfield.mem_toSubring,
    Subfield.mem_closure_iff, ← Algebra.adjoin_eq_ring_closure, Subalgebra.mem_toSubring, eq_comm]

end AdjoinDef

section Lattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

@[simp]
/--
theorem `adjoin_le_iff` / 定理 `adjoin_le_iff`

English:
theorem adjoin_le_iff
  given: {S : Set E} {T : IntermediateField F E}
  statement: adjoin F S <= T ↔ S subseteq T
  proof: ⟨fun H => le_trans (le_trans Set.subset_union_right Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.range (algebraMap F E) union S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

中文:
定理 adjoin_le_iff
  条件: {S : 集合 E} {T : 中间域 F E}
  结论: adjoin F S <= T ↔ S subseteq T
  证明: ⟨fun H => le_trans (le_trans Set.subset_union_right Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.range (algebraMap F E) union S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

Depends on / 依赖: IntermediateField, IntermediateField.set_range_subset, Set.range, Set.subset_union_right, Set.union_subset, Subfield, Subfield.closure_le, Subfield.subset_closure, T.toSubfield, algebraMap, closure_le, le_trans, set_range_subset, subset_closure, subset_union_right, toSubfield, union_subset
-/
theorem adjoin_le_iff {S : Set E} {T : IntermediateField F E} : adjoin F S <= T ↔ S subseteq T :=
  ⟨fun H => le_trans (le_trans Set.subset_union_right Subfield.subset_closure) H, fun H =>
    (@Subfield.closure_le E _ (Set.range (algebraMap F E) union S) T.toSubfield).mpr
      (Set.union_subset (IntermediateField.set_range_subset T) H)⟩

/--
theorem `gc` / 定理 `gc`

English:
theorem gc
  statement: GaloisConnection (adjoin F : Set E -> IntermediateField F E)
  proof: fun _ _ =>
  adjoin_le_iff

中文:
定理 gc
  结论: GaloisConnection (adjoin F : 集合 E -> 中间域 F E)
  证明: fun _ _ =>
  adjoin_le_iff
-/
theorem gc : GaloisConnection (adjoin F : Set E -> IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) := fun _ _ =>
  adjoin_le_iff

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (adjoin F : Set E -> IntermediateField F E)
  body: (adjoin F s).copy s le_antisymm (gc.le_u_l s) hs
  gc := IntermediateField.gc
le_l_u S := (IntermediateField.gc (S : Set E) (adjoin F S)).1 le_rfl
  choice_eq _ _ := copy_eq _ _ _

中文:
定义 gi
  签名: : Galois嵌入 (adjoin F : 集合 E -> 中间域 F E)
  定义体: (adjoin F s).copy s le_antisymm (gc.le_u_l s) hs
  gc := IntermediateField.gc
le_l_u S := (IntermediateField.gc (S : Set E) (adjoin F S)).1 le_rfl
  choice_eq _ _ := copy_eq _ _ _

Depends on / 依赖: adjoin, gc.le_u_l, le_antisymm, le_u_l
-/
def gi : GaloisInsertion (adjoin F : Set E -> IntermediateField F E)
    (fun (x : IntermediateField F E) => (x : Set E)) where
choice s hs := (adjoin F s).copy s le_antisymm (gc.le_u_l s) hs
  gc := IntermediateField.gc
le_l_u S := (IntermediateField.gc (S : Set E) (adjoin F S)).1 le_rfl
  choice_eq _ _ := copy_eq _ _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (IntermediateField F E)
  body: GaloisInsertion.liftCompleteLattice IntermediateField.gi
  bot :=
    { toSubalgebra := ⊥
      inv_mem' := by rintro x ⟨r, rfl⟩; exact ⟨r⁻¹, map_inv₀ _ _⟩ }
  bot_le x := (bot_le : ⊥ <= x.toSubalgebra)

中文:
实例 :
  签名: 完备格 (中间域 F E)
  定义体: GaloisInsertion.liftCompleteLattice IntermediateField.gi
  bot :=
    { toSubalgebra := ⊥
      inv_mem' := by rintro x ⟨r, rfl⟩; exact ⟨r⁻¹, map_inv₀ _ _⟩ }
  bot_le x := (bot_le : ⊥ <= x.toSubalgebra)

Depends on / 依赖: GaloisInsertion, GaloisInsertion.liftCompleteLattice, IntermediateField, IntermediateField.gi, liftCompleteLattice
-/
instance : CompleteLattice (IntermediateField F E) where
  __ := GaloisInsertion.liftCompleteLattice IntermediateField.gi
  bot :=
    { toSubalgebra := ⊥
      inv_mem' := by rintro x ⟨r, rfl⟩; exact ⟨r⁻¹, map_inv₀ _ _⟩ }
  bot_le x := (bot_le : ⊥ <= x.toSubalgebra)

instance (K₁ K₂ : IntermediateField F E) : Algebra ↥(K₁ ⊓ K₂) K₁ :=
inferInstanceAs Algebra ↑(K₁.toSubalgebra ⊓ K₂.toSubalgebra) K₁.toSubalgebra

instance (K₁ K₂ : IntermediateField F E) : Algebra ↥(K₁ ⊓ K₂) K₂ :=
inferInstanceAs Algebra ↑(K₁.toSubalgebra ⊓ K₂.toSubalgebra) K₂.toSubalgebra

/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  given: (S T : IntermediateField F E)
  statement: S ⊔ T = adjoin F (S union T : Set E)
  proof: rfl

中文:
定理 sup_def
  条件: (S T : 中间域 F E)
  结论: S ⊔ T = adjoin F (S union T : 集合 E)
  证明: rfl
-/
theorem sup_def (S T : IntermediateField F E) : S ⊔ T = adjoin F (S union T : Set E) := rfl

/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: (S : Set (IntermediateField F E))
  proof: rfl

中文:
定理 sSup_def
  条件: (S : 集合 (中间域 F E))
  证明: rfl
-/
theorem sSup_def (S : Set (IntermediateField F E)) :
    sSup S = adjoin F (⋃₀ (SetLike.coe '' S)) := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (IntermediateField F E)
  body: ⟨⊤⟩

中文:
实例 :
  签名: 可居 (中间域 F E)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (IntermediateField F E) :=
  ⟨⊤⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (IntermediateField F F)
  body: { (inferInstance : Inhabited (IntermediateField F F)) with
uniq := fun _ => toSubalgebra_injective Subsingleton.elim _ _ }

中文:
实例 :
  签名: 唯一 (中间域 F F)
  定义体: { (inferInstance : Inhabited (IntermediateField F F)) with
uniq := fun _ => toSubalgebra_injective Subsingleton.elim _ _ }

Depends on / 依赖: Inhabited, IntermediateField, Subsingleton, Subsingleton.elim, toSubalgebra_injective
-/
instance : Unique (IntermediateField F F) :=
  { (inferInstance : Inhabited (IntermediateField F F)) with
uniq := fun _ => toSubalgebra_injective Subsingleton.elim _ _ }

/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ↑(⊥ : IntermediateField F E) = Set.range (algebraMap F E)
  proof: rfl

中文:
定理 coe_bot
  结论: ↑(⊥ : 中间域 F E) = 集合.range (algebraMap F E)
  证明: rfl
-/
theorem coe_bot : ↑(⊥ : IntermediateField F E) = Set.range (algebraMap F E) := rfl

/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  given: {x : E}
  statement: x in (⊥ : IntermediateField F E) ↔ x in Set.range (algebraMap F E)
  proof: Iff.rfl

@[simp]

中文:
定理 mem_bot
  条件: {x : E}
  结论: x in (⊥ : 中间域 F E) ↔ x in 集合.range (algebraMap F E)
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_bot {x : E} : x in (⊥ : IntermediateField F E) ↔ x in Set.range (algebraMap F E) :=
  Iff.rfl

@[simp]
/--
theorem `bot_toSubalgebra` / 定理 `bot_toSubalgebra`

English:
theorem bot_toSubalgebra
  statement: (⊥ : IntermediateField F E).toSubalgebra = ⊥
  proof: rfl

中文:
定理 bot_toSubalgebra
  结论: (⊥ : 中间域 F E).toSubalgebra = ⊥
  证明: rfl
-/
theorem bot_toSubalgebra : (⊥ : IntermediateField F E).toSubalgebra = ⊥ := rfl

/--
theorem `bot_toSubfield` / 定理 `bot_toSubfield`

English:
theorem bot_toSubfield
  statement: (⊥ : IntermediateField F E).toSubfield = (algebraMap F E).fieldRange
  proof: rfl

@[simp]

中文:
定理 bot_toSubfield
  结论: (⊥ : 中间域 F E).toSubfield = (algebraMap F E).fieldRange
  证明: rfl

@[simp]
-/
theorem bot_toSubfield : (⊥ : IntermediateField F E).toSubfield = (algebraMap F E).fieldRange :=
  rfl

@[simp]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ↑(⊤ : IntermediateField F E) = (Set.univ : Set E)
  proof: rfl

@[simp]

中文:
定理 coe_top
  结论: ↑(⊤ : 中间域 F E) = (集合.univ : 集合 E)
  证明: rfl

@[simp]
-/
theorem coe_top : ↑(⊤ : IntermediateField F E) = (Set.univ : Set E) :=
  rfl

@[simp]
/--
theorem `mem_top` / 定理 `mem_top`

English:
theorem mem_top
  given: {x : E}
  statement: x in (⊤ : IntermediateField F E)
  proof: trivial

@[simp]

中文:
定理 mem_top
  条件: {x : E}
  结论: x in (⊤ : 中间域 F E)
  证明: trivial

@[simp]
-/
theorem mem_top {x : E} : x in (⊤ : IntermediateField F E) :=
  trivial

@[simp]
/--
theorem `top_toSubalgebra` / 定理 `top_toSubalgebra`

English:
theorem top_toSubalgebra
  statement: (⊤ : IntermediateField F E).toSubalgebra = ⊤
  proof: rfl

@[simp]

中文:
定理 top_toSubalgebra
  结论: (⊤ : 中间域 F E).toSubalgebra = ⊤
  证明: rfl

@[simp]
-/
theorem top_toSubalgebra : (⊤ : IntermediateField F E).toSubalgebra = ⊤ :=
  rfl

@[simp]
/--
theorem `top_toSubfield` / 定理 `top_toSubfield`

English:
theorem top_toSubfield
  statement: (⊤ : IntermediateField F E).toSubfield = ⊤
  proof: rfl

@[simp, norm_cast]

中文:
定理 top_toSubfield
  结论: (⊤ : 中间域 F E).toSubfield = ⊤
  证明: rfl

@[simp, norm_cast]
-/
theorem top_toSubfield : (⊤ : IntermediateField F E).toSubfield = ⊤ :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (S T : IntermediateField F E)
  statement: (↑(S ⊓ T) : Set E) = (S : Set E) inter T
  proof: rfl

@[simp]

中文:
定理 coe_inf
  条件: (S T : 中间域 F E)
  结论: (↑(S ⊓ T) : 集合 E) = (S : 集合 E) inter T
  证明: rfl

@[simp]
-/
theorem coe_inf (S T : IntermediateField F E) : (↑(S ⊓ T) : Set E) = (S : Set E) inter T :=
  rfl

@[simp]
/--
theorem `mem_inf` / 定理 `mem_inf`

English:
theorem mem_inf
  given: {S T : IntermediateField F E} {x : E}
  statement: x in S ⊓ T ↔ x in S ∧ x in T
  proof: Iff.rfl

@[simp]

中文:
定理 mem_inf
  条件: {S T : 中间域 F E} {x : E}
  结论: x in S ⊓ T ↔ x in S ∧ x in T
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf {S T : IntermediateField F E} {x : E} : x in S ⊓ T ↔ x in S ∧ x in T :=
  Iff.rfl

@[simp]
/--
theorem `inf_toSubalgebra` / 定理 `inf_toSubalgebra`

English:
theorem inf_toSubalgebra
  given: (S T : IntermediateField F E)
  proof: rfl

@[simp]

中文:
定理 inf_toSubalgebra
  条件: (S T : 中间域 F E)
  证明: rfl

@[simp]
-/
theorem inf_toSubalgebra (S T : IntermediateField F E) :
    (S ⊓ T).toSubalgebra = S.toSubalgebra ⊓ T.toSubalgebra :=
  rfl

@[simp]
/--
theorem `inf_toSubfield` / 定理 `inf_toSubfield`

English:
theorem inf_toSubfield
  given: (S T : IntermediateField F E)
  proof: rfl

@[simp]

中文:
定理 inf_toSubfield
  条件: (S T : 中间域 F E)
  证明: rfl

@[simp]
-/
theorem inf_toSubfield (S T : IntermediateField F E) :
    (S ⊓ T).toSubfield = S.toSubfield ⊓ T.toSubfield :=
  rfl

@[simp]
/--
theorem `sup_toSubfield` / 定理 `sup_toSubfield`

English:
theorem sup_toSubfield
  given: (S T : IntermediateField F E)
  proof: by
  rw [← S.toSubfield.closure_eq]; rw [← T.toSubfield.closure_eq]; rw [← Subfield.closure_union]
  simp_rw [sup_def, adjoin_toSubfield, coe_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_cast]

中文:
定理 sup_toSubfield
  条件: (S T : 中间域 F E)
  证明: by
  rw [← S.toSubfield.closure_eq]; rw [← T.toSubfield.closure_eq]; rw [← Subfield.closure_union]
  simp_rw [sup_def, adjoin_toSubfield, coe_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_cast]

Depends on / 依赖: S.toSubfield.closure_eq, Set.mem_union_left, Set.union_eq_right, Subfield, Subfield.closure_union, T.toSubfield.closure_eq, adjoin_toSubfield, algebraMap_mem, closure_eq, closure_union, coe_toSubfield, mem_union_left, simp_rw, sup_def, toSubfield, union_eq_right
-/
theorem sup_toSubfield (S T : IntermediateField F E) :
    (S ⊔ T).toSubfield = S.toSubfield ⊔ T.toSubfield := by
  rw [← S.toSubfield.closure_eq]; rw [← T.toSubfield.closure_eq]; rw [← Subfield.closure_union]
  simp_rw [sup_def, adjoin_toSubfield, coe_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  exact Set.mem_union_left _ (algebraMap_mem S x)

@[simp, norm_cast]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (IntermediateField F E))
  statement: (↑(sInf S) : Set E) = ⋂ s in S, ↑s
  proof: show sInf ((fun (x : IntermediateField F E) => (x : Set E)) '' S) = ⋂ s in S, ↑s by simp

@[simp, grind =]

中文:
定理 coe_sInf
  条件: (S : 集合 (中间域 F E))
  结论: (↑(sInf S) : 集合 E) = ⋂ s in S, ↑s
  证明: show sInf ((fun (x : IntermediateField F E) => (x : Set E)) '' S) = ⋂ s in S, ↑s by simp

@[simp, grind =]

Depends on / 依赖: IntermediateField
-/
theorem coe_sInf (S : Set (IntermediateField F E)) : (↑(sInf S) : Set E) = ⋂ s in S, ↑s :=
  show sInf ((fun (x : IntermediateField F E) => (x : Set E)) '' S) = ⋂ s in S, ↑s by simp

@[simp, grind =]
/--
theorem `mem_sInf` / 定理 `mem_sInf`

English:
theorem mem_sInf
  given: {S : Set (IntermediateField F E)} {x : E}
  statement: x in sInf S ↔ forall p in S, x in p
  proof: by
  simpa only [Set.mem_iInter] using! Set.ext_iff.1 (coe_sInf S) x

@[simp]

中文:
定理 mem_sInf
  条件: {S : 集合 (中间域 F E)} {x : E}
  结论: x in sInf S ↔ 对任意 p in S, x in p
  证明: by
  simpa only [Set.mem_iInter] using! Set.ext_iff.1 (coe_sInf S) x

@[simp]

Depends on / 依赖: Set.ext_iff, Set.mem_iInter, coe_sInf, ext_iff, mem_iInter
-/
theorem mem_sInf {S : Set (IntermediateField F E)} {x : E} : x in sInf S ↔ forall p in S, x in p := by
  simpa only [Set.mem_iInter] using! Set.ext_iff.1 (coe_sInf S) x

@[simp]
/--
theorem `sInf_toSubalgebra` / 定理 `sInf_toSubalgebra`

English:
theorem sInf_toSubalgebra
  given: (S : Set (IntermediateField F E))
  proof: SetLike.coe_injective by simp

@[simp]

中文:
定理 sInf_toSubalgebra
  条件: (S : 集合 (中间域 F E))
  证明: SetLike.coe_injective by simp

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem sInf_toSubalgebra (S : Set (IntermediateField F E)) :
    (sInf S).toSubalgebra = sInf (toSubalgebra '' S) :=
SetLike.coe_injective by simp

@[simp]
/--
theorem `sInf_toSubfield` / 定理 `sInf_toSubfield`

English:
theorem sInf_toSubfield
  given: (S : Set (IntermediateField F E))
  proof: SetLike.coe_injective by simp

@[simp]

中文:
定理 sInf_toSubfield
  条件: (S : 集合 (中间域 F E))
  证明: SetLike.coe_injective by simp

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem sInf_toSubfield (S : Set (IntermediateField F E)) :
    (sInf S).toSubfield = sInf (toSubfield '' S) :=
SetLike.coe_injective by simp

@[simp]
/--
theorem `sSup_toSubfield` / 定理 `sSup_toSubfield`

English:
theorem sSup_toSubfield
  given: (S : Set (IntermediateField F E)) (hS : S.Nonempty)
  proof: by
  have h : toSubfield '' S = Subfield.closure '' SetLike.coe '' S := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubfield.closure_eq.symm
  rw [h]; rw [sSup_image]; rw [← Subfield.closure_sUnion]; rw [sSup_def]; rw [adjoin_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hS
  simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and, SetLike.mem_coe]
  exact ⟨y, hy, algebraMap_mem y x⟩

@[simp, norm_cast]

中文:
定理 sSup_toSubfield
  条件: (S : 集合 (中间域 F E)) (hS : S.非空)
  证明: by
  have h : toSubfield '' S = Subfield.closure '' SetLike.coe '' S := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubfield.closure_eq.symm
  rw [h]; rw [sSup_image]; rw [← Subfield.closure_sUnion]; rw [sSup_def]; rw [adjoin_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hS
  simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and, SetLike.mem_coe]
  exact ⟨y, hy, algebraMap_mem y x⟩

@[simp, norm_cast]

Depends on / 依赖: Set.image_image, Set.mem_image, Set.mem_sUnion, Set.union_eq_right, SetLike, SetLike.coe, SetLike.mem_coe, Subfield, Subfield.closure, Subfield.closure_sUnion, adjoin_toSubfield, algebraMap_mem, closure, closure_eq, closure_sUnion, exists_exists_and_eq_and, image_image, mem_coe, mem_image, mem_sUnion
-/
theorem sSup_toSubfield (S : Set (IntermediateField F E)) (hS : S.Nonempty) :
    (sSup S).toSubfield = sSup (toSubfield '' S) := by
  have h : toSubfield '' S = Subfield.closure '' SetLike.coe '' S := by
    rw [Set.image_image]
    congr! with x
    exact x.toSubfield.closure_eq.symm
  rw [h]; rw [sSup_image]; rw [← Subfield.closure_sUnion]; rw [sSup_def]; rw [adjoin_toSubfield]
  congr 1
  rw [Set.union_eq_right]
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hS
  simp only [Set.mem_sUnion, Set.mem_image, exists_exists_and_eq_and, SetLike.mem_coe]
  exact ⟨y, hy, algebraMap_mem y x⟩

@[simp, norm_cast]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} (S : ι -> IntermediateField F E)
  statement: (↑(iInf S) : Set E) = ⋂ i, S i
  proof: by
  simp [iInf]

@[simp]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} (S : ι -> 中间域 F E)
  结论: (↑(iInf S) : 集合 E) = ⋂ i, S i
  证明: by
  simp [iInf]

@[simp]
-/
theorem coe_iInf {ι : Sort*} (S : ι -> IntermediateField F E) : (↑(iInf S) : Set E) = ⋂ i, S i := by
  simp [iInf]

@[simp]
/--
theorem `iInf_toSubalgebra` / 定理 `iInf_toSubalgebra`

English:
theorem iInf_toSubalgebra
  given: {ι : Sort*} (S : ι -> IntermediateField F E)
  proof: SetLike.coe_injective by simp [iInf]

@[simp]

中文:
定理 iInf_toSubalgebra
  条件: {ι : 类型层*} (S : ι -> 中间域 F E)
  证明: SetLike.coe_injective by simp [iInf]

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem iInf_toSubalgebra {ι : Sort*} (S : ι -> IntermediateField F E) :
    (iInf S).toSubalgebra = ⨅ i, (S i).toSubalgebra :=
SetLike.coe_injective by simp [iInf]

@[simp]
/--
theorem `iInf_toSubfield` / 定理 `iInf_toSubfield`

English:
theorem iInf_toSubfield
  given: {ι : Sort*} (S : ι -> IntermediateField F E)
  proof: SetLike.coe_injective by simp [iInf]

@[simp]

中文:
定理 iInf_toSubfield
  条件: {ι : 类型层*} (S : ι -> 中间域 F E)
  证明: SetLike.coe_injective by simp [iInf]

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem iInf_toSubfield {ι : Sort*} (S : ι -> IntermediateField F E) :
    (iInf S).toSubfield = ⨅ i, (S i).toSubfield :=
SetLike.coe_injective by simp [iInf]

@[simp]
/--
theorem `iSup_toSubfield` / 定理 `iSup_toSubfield`

English:
theorem iSup_toSubfield
  given: {ι : Sort*} [Nonempty ι] (S : ι -> IntermediateField F E)
  proof: by
  simp only [iSup, Set.range_nonempty, sSup_toSubfield, ← Set.range_comp, Function.comp_def]

中文:
定理 iSup_toSubfield
  条件: {ι : 类型层*} [非空 ι] (S : ι -> 中间域 F E)
  证明: by
  simp only [iSup, Set.range_nonempty, sSup_toSubfield, ← Set.range_comp, Function.comp_def]

Depends on / 依赖: Function, Function.comp_def, Set.range_comp, Set.range_nonempty, comp_def, range_comp, range_nonempty, sSup_toSubfield
-/
theorem iSup_toSubfield {ι : Sort*} [Nonempty ι] (S : ι -> IntermediateField F E) :
    (iSup S).toSubfield = ⨆ i, (S i).toSubfield := by
  simp only [iSup, Set.range_nonempty, sSup_toSubfield, ← Set.range_comp, Function.comp_def]

variable (F E)

/--
Definition of `botEquiv` / `botEquiv` 的定义

English:
definition botEquiv
  signature: : (⊥ : IntermediateField F E) ≃ₐ[F] F
  body: (Subalgebra.equivOfEq _ _ bot_toSubalgebra).trans (Algebra.botEquiv F E)

中文:
定义 botEquiv
  签名: : (⊥ : 中间域 F E) ≃ₐ[F] F
  定义体: (Subalgebra.equivOfEq _ _ bot_toSubalgebra).trans (Algebra.botEquiv F E)

Depends on / 依赖: Algebra, Algebra.botEquiv, Subalgebra, Subalgebra.equivOfEq, botEquiv, bot_toSubalgebra, equivOfEq
-/
noncomputable def botEquiv : (⊥ : IntermediateField F E) ≃ₐ[F] F :=
  (Subalgebra.equivOfEq _ _ bot_toSubalgebra).trans (Algebra.botEquiv F E)

variable {F E}

/--
theorem `botEquiv_def` / 定理 `botEquiv_def`

English:
theorem botEquiv_def
  given: (x : F)
  statement: botEquiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x
  proof: by
  simp

@[simp]

中文:
定理 botEquiv_def
  条件: (x : F)
  结论: botEquiv F E (algebraMap F (⊥ : 中间域 F E) x) = x
  证明: by
  simp

@[simp]
-/
theorem botEquiv_def (x : F) : botEquiv F E (algebraMap F (⊥ : IntermediateField F E) x) = x := by
  simp

@[simp]
/--
theorem `botEquiv_symm` / 定理 `botEquiv_symm`

English:
theorem botEquiv_symm
  given: (x : F)
  statement: (botEquiv F E).symm x = algebraMap F _ x
  proof: rfl

中文:
定理 botEquiv_symm
  条件: (x : F)
  结论: (botEquiv F E).symm x = algebraMap F _ x
  证明: rfl
-/
theorem botEquiv_symm (x : F) : (botEquiv F E).symm x = algebraMap F _ x :=
  rfl

/--
Instance `algebraOverBot` / 实例 `algebraOverBot`

English:
instance algebraOverBot
  signature: : Algebra (⊥ : IntermediateField F E) F
  body: (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra

中文:
实例 algebraOverBot
  签名: : 代数 (⊥ : 中间域 F E) F
  定义体: (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra

Depends on / 依赖: IntermediateField, IntermediateField.botEquiv, botEquiv, toAlgHom, toAlgHom.toRingHom.toAlgebra, toAlgebra, toRingHom
-/
noncomputable instance algebraOverBot : Algebra (⊥ : IntermediateField F E) F :=
  (IntermediateField.botEquiv F E).toAlgHom.toRingHom.toAlgebra

/--
theorem `coe_algebraMap_over_bot` / 定理 `coe_algebraMap_over_bot`

English:
theorem coe_algebraMap_over_bot
  proof: rfl

中文:
定理 coe_algebraMap_over_bot
  证明: rfl
-/
theorem coe_algebraMap_over_bot :
    (algebraMap (⊥ : IntermediateField F E) F : (⊥ : IntermediateField F E) -> F) =
      IntermediateField.botEquiv F E :=
  rfl

/--
Instance `isScalarTower_over_bot` / 实例 `isScalarTower_over_bot`

English:
instance isScalarTower_over_bot
  signature: : IsScalarTower (⊥ : IntermediateField F E) F E
  body: IsScalarTower.of_algebraMap_eq
    (by
      intro x
      obtain ⟨y, rfl⟩ := (botEquiv F E).symm.surjective x
      rw [coe_algebraMap_over_bot]; rw [(botEquiv F E).apply_symm_apply]; rw [botEquiv_symm]; rw [IsScalarTower.algebraMap_apply F (⊥ : IntermediateField F E) E])

中文:
实例 isScalarTower_over_bot
  签名: : 标量塔 (⊥ : 中间域 F E) F E
  定义体: IsScalarTower.of_algebraMap_eq
    (by
      intro x
      obtain ⟨y, rfl⟩ := (botEquiv F E).symm.surjective x
      rw [coe_algebraMap_over_bot]; rw [(botEquiv F E).apply_symm_apply]; rw [botEquiv_symm]; rw [IsScalarTower.algebraMap_apply F (⊥ : IntermediateField F E) E])

Depends on / 依赖: IntermediateField, IsScalarTower, IsScalarTower.algebraMap_apply, IsScalarTower.of_algebraMap_eq, algebraMap_apply, apply_symm_apply, botEquiv, botEquiv_symm, coe_algebraMap_over_bot, of_algebraMap_eq, surjective, symm.surjective
-/
instance isScalarTower_over_bot : IsScalarTower (⊥ : IntermediateField F E) F E :=
  IsScalarTower.of_algebraMap_eq
    (by
      intro x
      obtain ⟨y, rfl⟩ := (botEquiv F E).symm.surjective x
      rw [coe_algebraMap_over_bot]; rw [(botEquiv F E).apply_symm_apply]; rw [botEquiv_symm]; rw [IsScalarTower.algebraMap_apply F (⊥ : IntermediateField F E) E])

/-- The top `IntermediateField` is isomorphic to the field.

This is the intermediate field version of `Subalgebra.topEquiv`. -/
@[simps!]
/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : IntermediateField F E) ≃ₐ[F] E
  body: Subalgebra.topEquiv

中文:
定义 topEquiv
  签名: : (⊤ : 中间域 F E) ≃ₐ[F] E
  定义体: Subalgebra.topEquiv

Depends on / 依赖: Subalgebra, Subalgebra.topEquiv, topEquiv
-/
def topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E :=
  Subalgebra.topEquiv

section RestrictScalars

@[simp]
/--
theorem `restrictScalars_bot_eq_self` / 定理 `restrictScalars_bot_eq_self`

English:
theorem restrictScalars_bot_eq_self
  given: (K : IntermediateField F E)
  proof: SetLike.coe_injective Subtype.range_coe

中文:
定理 restrictScalars_bot_eq_self
  条件: (K : 中间域 F E)
  证明: SetLike.coe_injective Subtype.range_coe

Depends on / 依赖: SetLike, SetLike.coe_injective, Subtype, Subtype.range_coe, coe_injective, range_coe
-/
theorem restrictScalars_bot_eq_self (K : IntermediateField F E) :
    (⊥ : IntermediateField K E).restrictScalars _ = K :=
  SetLike.coe_injective Subtype.range_coe

variable {K : Type*} [Field K] [Algebra K E] [Algebra K F] [IsScalarTower K F E]

@[simp]
/--
theorem `restrictScalars_top` / 定理 `restrictScalars_top`

English:
theorem restrictScalars_top
  statement: (⊤ : IntermediateField F E).restrictScalars K = ⊤
  proof: rfl

@[simp]

中文:
定理 restrictScalars_top
  结论: (⊤ : 中间域 F E).restrictScalars K = ⊤
  证明: rfl

@[simp]
-/
theorem restrictScalars_top : (⊤ : IntermediateField F E).restrictScalars K = ⊤ :=
  rfl

@[simp]
/--
theorem `restrictScalars_eq_top_iff` / 定理 `restrictScalars_eq_top_iff`

English:
theorem restrictScalars_eq_top_iff
  given: {L : IntermediateField F E}
  proof: by
  simp [SetLike.ext_iff]

中文:
定理 restrictScalars_eq_top_iff
  条件: {L : 中间域 F E}
  证明: by
  simp [SetLike.ext_iff]

Depends on / 依赖: SetLike, SetLike.ext_iff, ext_iff
-/
theorem restrictScalars_eq_top_iff {L : IntermediateField F E} :
    L.restrictScalars K = ⊤ ↔ L = ⊤ := by
  simp [SetLike.ext_iff]

variable (K)
variable (L L' : IntermediateField F E)

/--
theorem `restrictScalars_sup` / 定理 `restrictScalars_sup`

English:
theorem restrictScalars_sup
  proof: toSubfield_injective (by simp)

中文:
定理 restrictScalars_sup
  证明: toSubfield_injective (by simp)

Depends on / 依赖: toSubfield_injective
-/
theorem restrictScalars_sup :
    L.restrictScalars K ⊔ L'.restrictScalars K = (L ⊔ L').restrictScalars K :=
  toSubfield_injective (by simp)

/--
theorem `restrictScalars_inf` / 定理 `restrictScalars_inf`

English:
theorem restrictScalars_inf
  proof: rfl

中文:
定理 restrictScalars_inf
  证明: rfl
-/
theorem restrictScalars_inf :
    L.restrictScalars K ⊓ L'.restrictScalars K = (L ⊓ L').restrictScalars K := rfl

end RestrictScalars

variable {K : Type*} [Field K] [Algebra F K]

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : E ->ₐ[F] K)
  proof: toSubalgebra_injective Algebra.map_bot _

中文:
定理 map_bot
  条件: (f : E ->ₐ[F] K)
  证明: toSubalgebra_injective Algebra.map_bot _

Depends on / 依赖: Algebra, Algebra.map_bot, map_bot, toSubalgebra_injective
-/
theorem map_bot (f : E ->ₐ[F] K) :
    IntermediateField.map f ⊥ = ⊥ :=
toSubalgebra_injective Algebra.map_bot _

/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (s t : IntermediateField F E) (f : E ->ₐ[F] K)
  statement: (s ⊔ t).map f = s.map f ⊔ t.map f
  proof: (gc_map_comap f).l_sup

中文:
定理 map_sup
  条件: (s t : 中间域 F E) (f : E ->ₐ[F] K)
  结论: (s ⊔ t).map f = s.map f ⊔ t.map f
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
theorem map_sup (s t : IntermediateField F E) (f : E ->ₐ[F] K) : (s ⊔ t).map f = s.map f ⊔ t.map f :=
  (gc_map_comap f).l_sup

/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : E ->ₐ[F] K) (s : ι -> IntermediateField F E)
  proof: (gc_map_comap f).l_iSup

中文:
定理 map_iSup
  条件: {ι : 类型层*} (f : E ->ₐ[F] K) (s : ι -> 中间域 F E)
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : E ->ₐ[F] K) (s : ι -> IntermediateField F E) :
    (iSup s).map f = ⨆ i, (s i).map f :=
  (gc_map_comap f).l_iSup

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (s t : IntermediateField F E) (f : E ->ₐ[F] K)
  proof: SetLike.coe_injective (Set.image_inter f.injective)

中文:
定理 map_inf
  条件: (s t : 中间域 F E) (f : E ->ₐ[F] K)
  证明: SetLike.coe_injective (Set.image_inter f.injective)

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, f.injective, image_inter, injective
-/
theorem map_inf (s t : IntermediateField F E) (f : E ->ₐ[F] K) :
    (s ⊓ t).map f = s.map f ⊓ t.map f := SetLike.coe_injective (Set.image_inter f.injective)

/--
theorem `map_iInf` / 定理 `map_iInf`

English:
theorem map_iInf
  given: {ι : Sort*} [Nonempty ι] (f : E ->ₐ[F] K) (s : ι -> IntermediateField F E)
  proof: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

中文:
定理 map_iInf
  条件: {ι : 类型层*} [非空 ι] (f : E ->ₐ[F] K) (s : ι -> 中间域 F E)
  证明: by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

Depends on / 依赖: Set.injOn_of_injective, SetLike, SetLike.coe, SetLike.coe_injective, coe_injective, f.injective, image_iInter_eq, injOn_of_injective, injective
-/
theorem map_iInf {ι : Sort*} [Nonempty ι] (f : E ->ₐ[F] K) (s : ι -> IntermediateField F E) :
    (iInf s).map f = ⨅ i, (s i).map f := by
  apply SetLike.coe_injective
  simpa using (Set.injOn_of_injective f.injective).image_iInter_eq (s := SetLike.coe ∘ s)

/--
theorem `_root_.AlgHom.fieldRange_eq_map` / 定理 `_root_.AlgHom.fieldRange_eq_map`

English:
theorem _root_.AlgHom.fieldRange_eq_map
  given: (f : E ->ₐ[F] K)
  proof: SetLike.ext' Set.image_univ.symm

中文:
定理 _root_.代数态射.fieldRange_eq_map
  条件: (f : E ->ₐ[F] K)
  证明: SetLike.ext' Set.image_univ.symm

Depends on / 依赖: Set.image_univ.symm, SetLike, SetLike.ext, image_univ
-/
theorem _root_.AlgHom.fieldRange_eq_map (f : E ->ₐ[F] K) :
    f.fieldRange = IntermediateField.map f ⊤ :=
  SetLike.ext' Set.image_univ.symm

/--
theorem `_root_.AlgHom.map_fieldRange` / 定理 `_root_.AlgHom.map_fieldRange`

English:
theorem _root_.AlgHom.map_fieldRange
  statement: {L : Type*} [Field L] [Algebra F L]
  proof: SetLike.ext' (Set.range_comp g f).symm

中文:
定理 _root_.代数态射.map_fieldRange
  结论: {L : 类型} [域 L] [代数 F L]
  证明: SetLike.ext' (Set.range_comp g f).symm

Depends on / 依赖: Set.range_comp, SetLike, SetLike.ext, range_comp
-/
theorem _root_.AlgHom.map_fieldRange {L : Type*} [Field L] [Algebra F L]
    (f : E ->ₐ[F] K) (g : K ->ₐ[F] L) : f.fieldRange.map g = (g.comp f).fieldRange :=
  SetLike.ext' (Set.range_comp g f).symm

/--
theorem `_root_.AlgHom.fieldRange_eq_top` / 定理 `_root_.AlgHom.fieldRange_eq_top`

English:
theorem _root_.AlgHom.fieldRange_eq_top
  given: {f : E ->ₐ[F] K}
  proof: SetLike.ext'_iff.trans Set.range_eq_univ

@[simp]

中文:
定理 _root_.代数态射.fieldRange_eq_top
  条件: {f : E ->ₐ[F] K}
  证明: SetLike.ext'_iff.trans Set.range_eq_univ

@[simp]

Depends on / 依赖: Set.range_eq_univ, SetLike, SetLike.ext, _iff, _iff.trans, range_eq_univ
-/
theorem _root_.AlgHom.fieldRange_eq_top {f : E ->ₐ[F] K} :
    f.fieldRange = ⊤ ↔ Function.Surjective f :=
  SetLike.ext'_iff.trans Set.range_eq_univ

@[simp]
/--
theorem `_root_.AlgEquiv.fieldRange_eq_top` / 定理 `_root_.AlgEquiv.fieldRange_eq_top`

English:
theorem _root_.AlgEquiv.fieldRange_eq_top
  given: (f : E ≃ₐ[F] K)
  proof: AlgHom.fieldRange_eq_top.mpr f.surjective

中文:
定理 _root_.代数等价.fieldRange_eq_top
  条件: (f : E ≃ₐ[F] K)
  证明: AlgHom.fieldRange_eq_top.mpr f.surjective

Depends on / 依赖: AlgHom, AlgHom.fieldRange_eq_top.mpr, f.surjective, fieldRange_eq_top, surjective
-/
theorem _root_.AlgEquiv.fieldRange_eq_top (f : E ≃ₐ[F] K) :
    (f : E ->ₐ[F] K).fieldRange = ⊤ :=
  AlgHom.fieldRange_eq_top.mpr f.surjective

end Lattice

section AdjoinDef

variable (F : Type*) [Field F] {E : Type*} [Field E] [Algebra F E] (S : Set E)

/--
theorem `adjoin_eq_range_algebraMap_adjoin` / 定理 `adjoin_eq_range_algebraMap_adjoin`

English:
theorem adjoin_eq_range_algebraMap_adjoin
  proof: Subtype.range_coe.symm

中文:
定理 adjoin_eq_range_algebraMap_adjoin
  证明: Subtype.range_coe.symm

Depends on / 依赖: Subtype, Subtype.range_coe.symm, range_coe
-/
theorem adjoin_eq_range_algebraMap_adjoin :
    (adjoin F S : Set E) = Set.range (algebraMap (adjoin F S) E) :=
  Subtype.range_coe.symm

/--
theorem `adjoin.algebraMap_mem` / 定理 `adjoin.algebraMap_mem`

English:
theorem adjoin.algebraMap_mem
  given: (x : F)
  statement: algebraMap F E x in adjoin F S
  proof: IntermediateField.algebraMap_mem (adjoin F S) x

中文:
定理 adjoin.algebraMap_mem
  条件: (x : F)
  结论: algebraMap F E x in adjoin F S
  证明: IntermediateField.algebraMap_mem (adjoin F S) x

Depends on / 依赖: IntermediateField, IntermediateField.algebraMap_mem, adjoin, algebraMap_mem
-/
theorem adjoin.algebraMap_mem (x : F) : algebraMap F E x in adjoin F S :=
  IntermediateField.algebraMap_mem (adjoin F S) x

/--
theorem `adjoin.range_algebraMap_subset` / 定理 `adjoin.range_algebraMap_subset`

English:
theorem adjoin.range_algebraMap_subset
  statement: Set.range (algebraMap F E) subseteq adjoin F S
  proof: set_range_subset (adjoin F S)

中文:
定理 adjoin.range_algebraMap_subset
  结论: 集合.range (algebraMap F E) subseteq adjoin F S
  证明: set_range_subset (adjoin F S)

Depends on / 依赖: adjoin, set_range_subset
-/
theorem adjoin.range_algebraMap_subset : Set.range (algebraMap F E) subseteq adjoin F S :=
  set_range_subset (adjoin F S)

/--
Instance `adjoin.fieldCoe` / 实例 `adjoin.fieldCoe`

English:
instance adjoin.fieldCoe
  signature: : CoeTC F (adjoin F S) where
  body: ⟨algebraMap F E x, adjoin.algebraMap_mem F S x⟩

@[simp, aesop safe 20 (rule_sets := [SetLike])]

中文:
实例 adjoin.fieldCoe
  签名: : CoeTC F (adjoin F S) where
  定义体: ⟨algebraMap F E x, adjoin.algebraMap_mem F S x⟩

@[simp, aesop safe 20 (rule_sets := [SetLike])]

Depends on / 依赖: adjoin, adjoin.algebraMap_mem, algebraMap, algebraMap_mem
-/
instance adjoin.fieldCoe : CoeTC F (adjoin F S) where
  coe x := ⟨algebraMap F E x, adjoin.algebraMap_mem F S x⟩

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
theorem `subset_adjoin` / 定理 `subset_adjoin`

English:
theorem subset_adjoin
  statement: S subseteq adjoin F S
  proof: fun _ hx => Subfield.subset_closure (Or.inr hx)

@[aesop 80% (rule_sets := [SetLike])]

中文:
定理 subset_adjoin
  结论: S subseteq adjoin F S
  证明: fun _ hx => Subfield.subset_closure (Or.inr hx)

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: Or.inr, Subfield, Subfield.subset_closure, subset_closure
-/
theorem subset_adjoin : S subseteq adjoin F S := fun _ hx => Subfield.subset_closure (Or.inr hx)

@[aesop 80% (rule_sets := [SetLike])]
/--
theorem `mem_adjoin_of_mem` / 定理 `mem_adjoin_of_mem`

English:
theorem mem_adjoin_of_mem
  given: {S : Set E} {s : E} (hs : s in S)
  statement: s in adjoin F S
  proof: subset_adjoin F S hs

中文:
定理 mem_adjoin_of_mem
  条件: {S : 集合 E} {s : E} (hs : s in S)
  结论: s in adjoin F S
  证明: subset_adjoin F S hs

Depends on / 依赖: subset_adjoin
-/
theorem mem_adjoin_of_mem {S : Set E} {s : E} (hs : s in S) : s in adjoin F S := subset_adjoin F S hs

/--
theorem `notMem_of_notMem_adjoin` / 定理 `notMem_of_notMem_adjoin`

English:
theorem notMem_of_notMem_adjoin
  given: {S : Set E} {s : E} (hs : s ∉ adjoin F S)
  statement: s ∉ S
  proof: fun h =>
hs mem_adjoin_of_mem F h

中文:
定理 notMem_of_notMem_adjoin
  条件: {S : 集合 E} {s : E} (hs : s ∉ adjoin F S)
  结论: s ∉ S
  证明: fun h =>
hs mem_adjoin_of_mem F h
-/
theorem notMem_of_notMem_adjoin {S : Set E} {s : E} (hs : s ∉ adjoin F S) : s ∉ S := fun h =>
hs mem_adjoin_of_mem F h

/--
Instance `adjoin.setCoe` / 实例 `adjoin.setCoe`

English:
instance adjoin.setCoe
  signature: : CoeTC S (adjoin F S) where coe x
  body: ⟨x, subset_adjoin F S (Subtype.mem x)⟩

@[mono, gcongr]

中文:
实例 adjoin.setCoe
  签名: : CoeTC S (adjoin F S) where coe x
  定义体: ⟨x, subset_adjoin F S (Subtype.mem x)⟩

@[mono, gcongr]

Depends on / 依赖: Subtype, Subtype.mem, subset_adjoin
-/
instance adjoin.setCoe : CoeTC S (adjoin F S) where coe x := ⟨x, subset_adjoin F S (Subtype.mem x)⟩

@[mono, gcongr]
/--
theorem `adjoin.mono` / 定理 `adjoin.mono`

English:
theorem adjoin.mono
  given: (T : Set E) (h : S subseteq T)
  statement: adjoin F S <= adjoin F T
  proof: GaloisConnection.monotone_l gc h

中文:
定理 adjoin.mono
  条件: (T : 集合 E) (h : S subseteq T)
  结论: adjoin F S <= adjoin F T
  证明: GaloisConnection.monotone_l gc h

Depends on / 依赖: GaloisConnection, GaloisConnection.monotone_l, monotone_l
-/
theorem adjoin.mono (T : Set E) (h : S subseteq T) : adjoin F S <= adjoin F T :=
  GaloisConnection.monotone_l gc h

/--
theorem `adjoin_contains_field_as_subfield` / 定理 `adjoin_contains_field_as_subfield`

English:
theorem adjoin_contains_field_as_subfield
  given: (F : Subfield E)
  statement: (F : Set E) subseteq adjoin F S
  proof: fun x hx =>
  adjoin.algebraMap_mem F S ⟨x, hx⟩

中文:
定理 adjoin_contains_field_as_subfield
  条件: (F : 子域 E)
  结论: (F : 集合 E) subseteq adjoin F S
  证明: fun x hx =>
  adjoin.algebraMap_mem F S ⟨x, hx⟩
-/
theorem adjoin_contains_field_as_subfield (F : Subfield E) : (F : Set E) subseteq adjoin F S := fun x hx =>
  adjoin.algebraMap_mem F S ⟨x, hx⟩

/--
theorem `subset_adjoin_of_subset_left` / 定理 `subset_adjoin_of_subset_left`

English:
theorem subset_adjoin_of_subset_left
  given: {F : Subfield E} {T : Set E} (HT : T subseteq F)
  statement: T subseteq adjoin F S
  proof: fun x hx => (adjoin F S).algebraMap_mem ⟨x, HT hx⟩

中文:
定理 subset_adjoin_of_subset_left
  条件: {F : 子域 E} {T : 集合 E} (HT : T subseteq F)
  结论: T subseteq adjoin F S
  证明: fun x hx => (adjoin F S).algebraMap_mem ⟨x, HT hx⟩

Depends on / 依赖: adjoin, algebraMap_mem
-/
theorem subset_adjoin_of_subset_left {F : Subfield E} {T : Set E} (HT : T subseteq F) : T subseteq adjoin F S :=
  fun x hx => (adjoin F S).algebraMap_mem ⟨x, HT hx⟩

/--
theorem `subset_adjoin_of_subset_right` / 定理 `subset_adjoin_of_subset_right`

English:
theorem subset_adjoin_of_subset_right
  given: {T : Set E} (H : T subseteq S)
  statement: T subseteq adjoin F S
  proof: fun _ hx =>
  subset_adjoin F S (H hx)

@[simp]

中文:
定理 subset_adjoin_of_subset_right
  条件: {T : 集合 E} (H : T subseteq S)
  结论: T subseteq adjoin F S
  证明: fun _ hx =>
  subset_adjoin F S (H hx)

@[simp]
-/
theorem subset_adjoin_of_subset_right {T : Set E} (H : T subseteq S) : T subseteq adjoin F S := fun _ hx =>
  subset_adjoin F S (H hx)

@[simp]
/--
theorem `adjoin_empty` / 定理 `adjoin_empty`

English:
theorem adjoin_empty
  given: (F E : Type*) [Field F] [Field E] [Algebra F E]
  statement: adjoin F (∅ : Set E) = ⊥
  proof: eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))

@[simp]

中文:
定理 adjoin_empty
  条件: (F E : 类型) [域 F] [域 E] [代数 F E]
  结论: adjoin F (∅ : 集合 E) = ⊥
  证明: eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))

@[simp]

Depends on / 依赖: Set.empty_subset, adjoin_le_iff, adjoin_le_iff.mpr, empty_subset, eq_bot_iff, eq_bot_iff.mpr
-/
theorem adjoin_empty (F E : Type*) [Field F] [Field E] [Algebra F E] : adjoin F (∅ : Set E) = ⊥ :=
  eq_bot_iff.mpr (adjoin_le_iff.mpr (Set.empty_subset _))

@[simp]
/--
theorem `adjoin_univ` / 定理 `adjoin_univ`

English:
theorem adjoin_univ
  given: (F E : Type*) [Field F] [Field E] [Algebra F E]
  proof: eq_top_iff.mpr subset_adjoin _ _

中文:
定理 adjoin_univ
  条件: (F E : 类型) [域 F] [域 E] [代数 F E]
  证明: eq_top_iff.mpr subset_adjoin _ _

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr, subset_adjoin
-/
theorem adjoin_univ (F E : Type*) [Field F] [Field E] [Algebra F E] :
    adjoin F (Set.univ : Set E) = ⊤ :=
eq_top_iff.mpr subset_adjoin _ _

/--
theorem `adjoin_union` / 定理 `adjoin_union`

English:
theorem adjoin_union
  given: {S T : Set E}
  statement: adjoin F (S union T) = adjoin F S ⊔ adjoin F T
  proof: gc.l_sup

中文:
定理 adjoin_union
  条件: {S T : 集合 E}
  结论: adjoin F (S union T) = adjoin F S ⊔ adjoin F T
  证明: gc.l_sup

Depends on / 依赖: gc.l_sup, l_sup
-/
theorem adjoin_union {S T : Set E} : adjoin F (S union T) = adjoin F S ⊔ adjoin F T :=
  gc.l_sup

/--
theorem `adjoin_le_subfield` / 定理 `adjoin_le_subfield`

English:
theorem adjoin_le_subfield
  given: {K : Subfield E} (HF : Set.range (algebraMap F E) subseteq K) (HS : S subseteq K)
  proof: by
  simpa using ⟨HF, HS⟩

中文:
定理 adjoin_le_subfield
  条件: {K : 子域 E} (HF : 集合.range (algebraMap F E) subseteq K) (HS : S subseteq K)
  证明: by
  simpa using ⟨HF, HS⟩
-/
theorem adjoin_le_subfield {K : Subfield E} (HF : Set.range (algebraMap F E) subseteq K) (HS : S subseteq K) :
    (adjoin F S).toSubfield <= K := by
  simpa using ⟨HF, HS⟩

/--
theorem `adjoin_subset_adjoin_iff` / 定理 `adjoin_subset_adjoin_iff`

English:
theorem adjoin_subset_adjoin_iff
  given: {F' : Type*} [Field F'] [Algebra F' E] {S S' : Set E}
  proof: ⟨fun h => ⟨(adjoin.range_algebraMap_subset _ _).trans h,
    (subset_adjoin _ _).trans h⟩, fun ⟨hF, hS⟩ =>
      (Subfield.closure_le (t := (adjoin F' S').toSubfield)).mpr (Set.union_subset hF hS)⟩

中文:
定理 adjoin_subset_adjoin_iff
  条件: {F' : 类型} [域 F'] [代数 F' E] {S S' : 集合 E}
  证明: ⟨fun h => ⟨(adjoin.range_algebraMap_subset _ _).trans h,
    (subset_adjoin _ _).trans h⟩, fun ⟨hF, hS⟩ =>
      (Subfield.closure_le (t := (adjoin F' S').toSubfield)).mpr (Set.union_subset hF hS)⟩

Depends on / 依赖: Set.union_subset, Subfield, Subfield.closure_le, adjoin, adjoin.range_algebraMap_subset, closure_le, range_algebraMap_subset, subset_adjoin, toSubfield, union_subset
-/
theorem adjoin_subset_adjoin_iff {F' : Type*} [Field F'] [Algebra F' E] {S S' : Set E} :
    (adjoin F S : Set E) subseteq adjoin F' S' ↔
      Set.range (algebraMap F E) subseteq adjoin F' S' ∧ S subseteq adjoin F' S' :=
  ⟨fun h => ⟨(adjoin.range_algebraMap_subset _ _).trans h,
    (subset_adjoin _ _).trans h⟩, fun ⟨hF, hS⟩ =>
      (Subfield.closure_le (t := (adjoin F' S').toSubfield)).mpr (Set.union_subset hF hS)⟩

/--
theorem `adjoin_adjoin_left` / 定理 `adjoin_adjoin_left`

English:
theorem adjoin_adjoin_left
  given: (T : Set E)
  proof: by
  rw [SetLike.ext'_iff]
  change (adjoin (adjoin F S) T : Set E) = _
  apply subset_antisymm <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩; exact adjoin.mono _ _ _ Set.subset_union_left hx
  · exact subset_adjoin_of_subset_right _ _ Set.subset_union_right
  · exact Set.range_subset_iff.mpr fun f => Subfield.subset_closure (.inl ⟨f, rfl⟩)
  · exact Set.union_subset
      (fun x hx => Subfield.subset_closure <| .inl ⟨⟨x, Subfield.subset_closure (.inr hx)⟩, rfl⟩)
      (fun x hx => Subfield.subset_closure <| .inr hx)

中文:
定理 adjoin_adjoin_left
  条件: (T : 集合 E)
  证明: by
  rw [SetLike.ext'_iff]
  change (adjoin (adjoin F S) T : Set E) = _
  apply subset_antisymm <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩; exact adjoin.mono _ _ _ Set.subset_union_left hx
  · exact subset_adjoin_of_subset_right _ _ Set.subset_union_right
  · exact Set.range_subset_iff.mpr fun f => Subfield.subset_closure (.inl ⟨f, rfl⟩)
  · exact Set.union_subset
      (fun x hx => Subfield.subset_closure <| .inl ⟨⟨x, Subfield.subset_closure (.inr hx)⟩, rfl⟩)
      (fun x hx => Subfield.subset_closure <| .inr hx)

Depends on / 依赖: Set.range_subset_iff.mpr, Set.subset_union_left, Set.subset_union_right, Set.union_subset, SetLike, SetLike.ext, Subfiel, Subfield, Subfield.subset_closure, _iff, adjoin, adjoin.mono, adjoin_subset_adjoin_iff, range_subset_iff, subset_adjoin_of_subset_right, subset_antisymm, subset_closure, subset_union_left, subset_union_right, union_subset
-/
theorem adjoin_adjoin_left (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars _ = adjoin F (S union T) := by
  rw [SetLike.ext'_iff]
  change (adjoin (adjoin F S) T : Set E) = _
  apply subset_antisymm <;> rw [adjoin_subset_adjoin_iff] <;> constructor
  · rintro _ ⟨⟨x, hx⟩, rfl⟩; exact adjoin.mono _ _ _ Set.subset_union_left hx
  · exact subset_adjoin_of_subset_right _ _ Set.subset_union_right
  · exact Set.range_subset_iff.mpr fun f => Subfield.subset_closure (.inl ⟨f, rfl⟩)
  · exact Set.union_subset
      (fun x hx => Subfield.subset_closure <| .inl ⟨⟨x, Subfield.subset_closure (.inr hx)⟩, rfl⟩)
      (fun x hx => Subfield.subset_closure <| .inr hx)

/-- Adjoining is idempotent: adjoining an adjoin is the same as a single adjoin. -/
@[simp]
/--
lemma `adjoin_adjoin_right` / 引理 `adjoin_adjoin_right`

English:
lemma adjoin_adjoin_right
  given: {K : Type*} [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E]
  proof: by
  refine le_antisymm ?_ (adjoin.mono F S (adjoin K S) (subset_adjoin K S))
  rw [adjoin_le_iff]; rw [← (adjoin F S).coe_restrictScalars K]; rw [SetLike.coe_subset_coe]
  simp

@[simp]

中文:
引理 adjoin_adjoin_right
  条件: {K : 类型} [域 K] [代数 K F] [代数 K E] [标量塔 K F E]
  证明: by
  refine le_antisymm ?_ (adjoin.mono F S (adjoin K S) (subset_adjoin K S))
  rw [adjoin_le_iff]; rw [← (adjoin F S).coe_restrictScalars K]; rw [SetLike.coe_subset_coe]
  simp

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_subset_coe, adjoin, adjoin.mono, adjoin_le_iff, coe_restrictScalars, coe_subset_coe, le_antisymm, subset_adjoin
-/
lemma adjoin_adjoin_right {K : Type*} [Field K] [Algebra K F] [Algebra K E] [IsScalarTower K F E] :
    adjoin F (adjoin K S) = adjoin F S := by
  refine le_antisymm ?_ (adjoin.mono F S (adjoin K S) (subset_adjoin K S))
  rw [adjoin_le_iff]; rw [← (adjoin F S).coe_restrictScalars K]; rw [SetLike.coe_subset_coe]
  simp

@[simp]
/--
theorem `adjoin_insert_adjoin` / 定理 `adjoin_insert_adjoin`

English:
theorem adjoin_insert_adjoin
  given: (x : E)
  proof: by
  simp_rw [← Set.singleton_union, adjoin_union, adjoin_adjoin_right]

中文:
定理 adjoin_insert_adjoin
  条件: (x : E)
  证明: by
  simp_rw [← Set.singleton_union, adjoin_union, adjoin_adjoin_right]

Depends on / 依赖: Set.singleton_union, adjoin_adjoin_right, adjoin_union, simp_rw, singleton_union
-/
theorem adjoin_insert_adjoin (x : E) :
    adjoin F (insert x (adjoin F S : Set E)) = adjoin F (insert x S) := by
  simp_rw [← Set.singleton_union, adjoin_union, adjoin_adjoin_right]

/--
theorem `adjoin_adjoin_comm` / 定理 `adjoin_adjoin_comm`

English:
theorem adjoin_adjoin_comm
  given: (T : Set E)
  proof: by
  rw [adjoin_adjoin_left]; rw [adjoin_adjoin_left]; rw [Set.union_comm]

中文:
定理 adjoin_adjoin_comm
  条件: (T : 集合 E)
  证明: by
  rw [adjoin_adjoin_left]; rw [adjoin_adjoin_left]; rw [Set.union_comm]

Depends on / 依赖: Set.union_comm, adjoin_adjoin_left, union_comm
-/
theorem adjoin_adjoin_comm (T : Set E) :
    (adjoin (adjoin F S) T).restrictScalars F = (adjoin (adjoin F T) S).restrictScalars F := by
  rw [adjoin_adjoin_left]; rw [adjoin_adjoin_left]; rw [Set.union_comm]

/--
theorem `adjoin_map` / 定理 `adjoin_map`

English:
theorem adjoin_map
  given: {E' : Type*} [Field E'] [Algebra F E'] (f : E ->ₐ[F] E')
  proof: le_antisymm
    (map_le_iff_le_comap.mpr <| adjoin_le_iff.mpr fun x hx => subset_adjoin _ _ ⟨x, hx, rfl⟩)
    (adjoin_le_iff.mpr <| Set.monotone_image <| subset_adjoin _ _)

@[simp]

中文:
定理 adjoin_map
  条件: {E' : 类型} [域 E'] [代数 F E'] (f : E ->ₐ[F] E')
  证明: le_antisymm
    (map_le_iff_le_comap.mpr <| adjoin_le_iff.mpr fun x hx => subset_adjoin _ _ ⟨x, hx, rfl⟩)
    (adjoin_le_iff.mpr <| Set.monotone_image <| subset_adjoin _ _)

@[simp]

Depends on / 依赖: Set.monotone_image, adjoin_le_iff, adjoin_le_iff.mpr, le_antisymm, map_le_iff_le_comap, map_le_iff_le_comap.mpr, monotone_image, subset_adjoin
-/
theorem adjoin_map {E' : Type*} [Field E'] [Algebra F E'] (f : E ->ₐ[F] E') :
    (adjoin F S).map f = adjoin F (f '' S) :=
  le_antisymm
    (map_le_iff_le_comap.mpr <| adjoin_le_iff.mpr fun x hx => subset_adjoin _ _ ⟨x, hx, rfl⟩)
    (adjoin_le_iff.mpr <| Set.monotone_image <| subset_adjoin _ _)

@[simp]
/--
theorem `lift_adjoin` / 定理 `lift_adjoin`

English:
theorem lift_adjoin
  given: (K : IntermediateField F E) (S : Set K)
  proof: adjoin_map _ _ _

中文:
定理 lift_adjoin
  条件: (K : 中间域 F E) (S : 集合 K)
  证明: adjoin_map _ _ _

Depends on / 依赖: adjoin_map
-/
theorem lift_adjoin (K : IntermediateField F E) (S : Set K) :
    lift (adjoin F S) = adjoin F (Subtype.val '' S) :=
  adjoin_map _ _ _

/--
theorem `lift_adjoin_simple` / 定理 `lift_adjoin_simple`

English:
theorem lift_adjoin_simple
  given: (K : IntermediateField F E) (α : K)
  proof: by
  simp only [lift_adjoin, Set.image_singleton]

@[simp]

中文:
定理 lift_adjoin_simple
  条件: (K : 中间域 F E) (α : K)
  证明: by
  simp only [lift_adjoin, Set.image_singleton]

@[simp]

Depends on / 依赖: Set.image_singleton, image_singleton, lift_adjoin
-/
theorem lift_adjoin_simple (K : IntermediateField F E) (α : K) :
    lift (adjoin F {α}) = adjoin F {α.1} := by
  simp only [lift_adjoin, Set.image_singleton]

@[simp]
/--
theorem `lift_bot` / 定理 `lift_bot`

English:
theorem lift_bot
  given: (K : IntermediateField F E)
  proof: map_bot _

@[simp]

中文:
定理 lift_bot
  条件: (K : 中间域 F E)
  证明: map_bot _

@[simp]

Depends on / 依赖: map_bot
-/
theorem lift_bot (K : IntermediateField F E) :
    lift (F := K) ⊥ = ⊥ := map_bot _

@[simp]
/--
theorem `lift_top` / 定理 `lift_top`

English:
theorem lift_top
  given: (K : IntermediateField F E)
  proof: by rw [lift, ← AlgHom.fieldRange_eq_map, fieldRange_val]

中文:
定理 lift_top
  条件: (K : 中间域 F E)
  证明: by rw [lift, ← AlgHom.fieldRange_eq_map, fieldRange_val]

Depends on / 依赖: AlgHom, AlgHom.fieldRange_eq_map, fieldRange_eq_map, fieldRange_val
-/
theorem lift_top (K : IntermediateField F E) :
    lift (F := K) ⊤ = K := by rw [lift, ← AlgHom.fieldRange_eq_map, fieldRange_val]

/--
theorem `lift_sup` / 定理 `lift_sup`

English:
theorem lift_sup
  given: (K : IntermediateField F E) (L L' : IntermediateField F K)
  proof: by
  simp [lift, map_sup]

中文:
定理 lift_sup
  条件: (K : 中间域 F E) (L L' : 中间域 F K)
  证明: by
  simp [lift, map_sup]

Depends on / 依赖: map_sup
-/
theorem lift_sup (K : IntermediateField F E) (L L' : IntermediateField F K) :
    lift (L ⊔ L') = lift L ⊔ lift L' := by
  simp [lift, map_sup]

/--
theorem `lift_inf` / 定理 `lift_inf`

English:
theorem lift_inf
  given: (K : IntermediateField F E) (L L' : IntermediateField F K)
  proof: by
  simp [lift, map_inf]

@[simp]

中文:
定理 lift_inf
  条件: (K : 中间域 F E) (L L' : 中间域 F K)
  证明: by
  simp [lift, map_inf]

@[simp]

Depends on / 依赖: map_inf
-/
theorem lift_inf (K : IntermediateField F E) (L L' : IntermediateField F K) :
    lift (L ⊓ L') = lift L ⊓ lift L' := by
  simp [lift, map_inf]

@[simp]
/--
theorem `adjoin_self` / 定理 `adjoin_self`

English:
theorem adjoin_self
  given: (K : IntermediateField F E)
  proof: le_antisymm (adjoin_le_iff.2 fun _ => id) (subset_adjoin F _)

中文:
定理 adjoin_self
  条件: (K : 中间域 F E)
  证明: le_antisymm (adjoin_le_iff.2 fun _ => id) (subset_adjoin F _)

Depends on / 依赖: adjoin_le_iff, le_antisymm, subset_adjoin
-/
theorem adjoin_self (K : IntermediateField F E) :
    adjoin F K = K := le_antisymm (adjoin_le_iff.2 fun _ => id) (subset_adjoin F _)

/--
theorem `restrictScalars_adjoin` / 定理 `restrictScalars_adjoin`

English:
theorem restrictScalars_adjoin
  given: (K : IntermediateField F E) (S : Set E)
  proof: by
  rw [← adjoin_self _ K]; rw [adjoin_adjoin_left]; rw [adjoin_self _ K]

中文:
定理 restrictScalars_adjoin
  条件: (K : 中间域 F E) (S : 集合 E)
  证明: by
  rw [← adjoin_self _ K]; rw [adjoin_adjoin_left]; rw [adjoin_self _ K]

Depends on / 依赖: adjoin_adjoin_left, adjoin_self
-/
theorem restrictScalars_adjoin (K : IntermediateField F E) (S : Set E) :
    restrictScalars F (adjoin K S) = adjoin F (K union S) := by
  rw [← adjoin_self _ K]; rw [adjoin_adjoin_left]; rw [adjoin_self _ K]

variable {F} in
/--
theorem `extendScalars_adjoin` / 定理 `extendScalars_adjoin`

English:
theorem extendScalars_adjoin
  given: {K : IntermediateField F E} {S : Set E} (h : K <= adjoin F S)
  proof: restrictScalars_injective F by
  rw [extendScalars_restrictScalars]; rw [restrictScalars_adjoin]
exact le_antisymm (adjoin.mono F S _ Set.subset_union_right) adjoin_le_iff.2
    Set.union_subset h (subset_adjoin F S)

中文:
定理 extendScalars_adjoin
  条件: {K : 中间域 F E} {S : 集合 E} (h : K <= adjoin F S)
  证明: restrictScalars_injective F by
  rw [extendScalars_restrictScalars]; rw [restrictScalars_adjoin]
exact le_antisymm (adjoin.mono F S _ Set.subset_union_right) adjoin_le_iff.2
    Set.union_subset h (subset_adjoin F S)

Depends on / 依赖: Set.subset_union_right, Set.union_subset, adjoin, adjoin.mono, adjoin_le_iff, extendScalars_restrictScalars, le_antisymm, restrictScalars_adjoin, restrictScalars_injective, subset_adjoin, subset_union_right, union_subset
-/
theorem extendScalars_adjoin {K : IntermediateField F E} {S : Set E} (h : K <= adjoin F S) :
extendScalars h = adjoin K S := restrictScalars_injective F by
  rw [extendScalars_restrictScalars]; rw [restrictScalars_adjoin]
exact le_antisymm (adjoin.mono F S _ Set.subset_union_right) adjoin_le_iff.2
    Set.union_subset h (subset_adjoin F S)

/--
theorem `restrictScalars_adjoin_eq_sup` / 定理 `restrictScalars_adjoin_eq_sup`

English:
theorem restrictScalars_adjoin_eq_sup
  given: (K : IntermediateField F E) (S : Set E)
  proof: by
  rw [restrictScalars_adjoin]; rw [adjoin_union]; rw [adjoin_self]

中文:
定理 restrictScalars_adjoin_eq_sup
  条件: (K : 中间域 F E) (S : 集合 E)
  证明: by
  rw [restrictScalars_adjoin]; rw [adjoin_union]; rw [adjoin_self]

Depends on / 依赖: adjoin_self, adjoin_union, restrictScalars_adjoin
-/
theorem restrictScalars_adjoin_eq_sup (K : IntermediateField F E) (S : Set E) :
    restrictScalars F (adjoin K S) = K ⊔ adjoin F S := by
  rw [restrictScalars_adjoin]; rw [adjoin_union]; rw [adjoin_self]

/--
theorem `adjoin_iUnion` / 定理 `adjoin_iUnion`

English:
theorem adjoin_iUnion
  given: {ι} (f : ι -> Set E)
  statement: adjoin F (⋃ i, f i) = ⨆ i, adjoin F (f i)
  proof: gc.l_iSup

中文:
定理 adjoin_iUnion
  条件: {ι} (f : ι -> 集合 E)
  结论: adjoin F (⋃ i, f i) = ⨆ i, adjoin F (f i)
  证明: gc.l_iSup

Depends on / 依赖: gc.l_iSup, l_iSup
-/
theorem adjoin_iUnion {ι} (f : ι -> Set E) : adjoin F (⋃ i, f i) = ⨆ i, adjoin F (f i) :=
  gc.l_iSup

/--
theorem `iSup_eq_adjoin` / 定理 `iSup_eq_adjoin`

English:
theorem iSup_eq_adjoin
  given: {ι} (f : ι -> IntermediateField F E)
  proof: by
  simp_rw [adjoin_iUnion, adjoin_self]

中文:
定理 iSup_eq_adjoin
  条件: {ι} (f : ι -> 中间域 F E)
  证明: by
  simp_rw [adjoin_iUnion, adjoin_self]

Depends on / 依赖: adjoin_iUnion, adjoin_self, simp_rw
-/
theorem iSup_eq_adjoin {ι} (f : ι -> IntermediateField F E) :
    ⨆ i, f i = adjoin F (⋃ i, f i : Set E) := by
  simp_rw [adjoin_iUnion, adjoin_self]

variable {F} in
/--
theorem `restrictScalars_adjoin_of_algEquiv` / 定理 `restrictScalars_adjoin_of_algEquiv`

English:
theorem restrictScalars_adjoin_of_algEquiv
  proof: by
  apply_fun toSubfield using (fun K K' h => by
    ext x; change x in K.toSubfield ↔ x in K'.toSubfield; rw [h])
  simp [hi]

@[elab_as_elim]

中文:
定理 restrictScalars_adjoin_of_algEquiv
  证明: by
  apply_fun toSubfield using (fun K K' h => by
    ext x; change x in K.toSubfield ↔ x in K'.toSubfield; rw [h])
  simp [hi]

@[elab_as_elim]

Depends on / 依赖: K.toSubfield, apply_fun, toSubfield
-/
theorem restrictScalars_adjoin_of_algEquiv
    {L L' : Type*} [Field L] [Field L']
    [Algebra F L] [Algebra L E] [Algebra F L'] [Algebra L' E]
    [IsScalarTower F L E] [IsScalarTower F L' E] (i : L ≃ₐ[F] L')
    (hi : algebraMap L E = (algebraMap L' E) ∘ i) (S : Set E) :
    (adjoin L S).restrictScalars F = (adjoin L' S).restrictScalars F := by
  apply_fun toSubfield using (fun K K' h => by
    ext x; change x in K.toSubfield ↔ x in K'.toSubfield; rw [h])
  simp [hi]

@[elab_as_elim]
/--
theorem `adjoin_induction` / 定理 `adjoin_induction`

English:
theorem adjoin_induction
  statement: {s : Set E} {p : forall x in adjoin F s, Prop}
  proof: Subfield.closure_induction
    (fun x hx => Or.casesOn hx (fun ⟨x, hx⟩ => hx ▸ algebraMap x) (mem x))
    (by simp_rw [← (Algebra.algebraMap F E).map_one]; exact algebraMap 1) add
    (fun x _ h => by
      simp_rw [← neg_one_smul F x, Algebra.smul_def]; exact mul _ _ _ _ (algebraMap _) h) inv mul h

中文:
定理 adjoin_induction
  结论: {s : 集合 E} {p : 对任意 x in adjoin F s, 命题}
  证明: Subfield.closure_induction
    (fun x hx => Or.casesOn hx (fun ⟨x, hx⟩ => hx ▸ algebraMap x) (mem x))
    (by simp_rw [← (Algebra.algebraMap F E).map_one]; exact algebraMap 1) add
    (fun x _ h => by
      simp_rw [← neg_one_smul F x, Algebra.smul_def]; exact mul _ _ _ _ (algebraMap _) h) inv mul h

Depends on / 依赖: Algebra, Algebra.algebraMap, Algebra.smul_def, Or.casesOn, Subfield, Subfield.closure_induction, algebraMap, casesOn, closure_induction, map_one, neg_one_smul, simp_rw, smul_def
-/
theorem adjoin_induction {s : Set E} {p : forall x in adjoin F s, Prop}
    (mem : forall x hx, p x (subset_adjoin _ _ hx))
    (algebraMap : forall x, p (algebraMap F E x) (algebraMap_mem _ _))
    (add : forall x y hx hy, p x hx -> p y hy -> p (x + y) (add_mem hx hy))
    (inv : forall x hx, p x hx -> p x⁻¹ (inv_mem hx))
    (mul : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy))
    {x} (h : x in adjoin F s) : p x h :=
  Subfield.closure_induction
    (fun x hx => Or.casesOn hx (fun ⟨x, hx⟩ => hx ▸ algebraMap x) (mem x))
    (by simp_rw [← (Algebra.algebraMap F E).map_one]; exact algebraMap 1) add
    (fun x _ h => by
      simp_rw [← neg_one_smul F x, Algebra.smul_def]; exact mul _ _ _ _ (algebraMap _) h) inv mul h

section

variable {K : Type*} [Semiring K] [Algebra F K]

/--
theorem `adjoin_algHom_ext` / 定理 `adjoin_algHom_ext`

English:
theorem adjoin_algHom_ext
  given: {s : Set E} ⦃φ₁ φ₂
  statement: adjoin F s ->ₐ[F] K⦄
  proof: AlgHom.ext fun ⟨x, hx⟩ => adjoin_induction _ h (fun _ => φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ => eq_on_inv₀ _ _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl)
    hx

中文:
定理 adjoin_algHom_ext
  条件: {s : 集合 E} ⦃φ₁ φ₂
  结论: adjoin F s ->ₐ[F] K⦄
  证明: AlgHom.ext fun ⟨x, hx⟩ => adjoin_induction _ h (fun _ => φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ => eq_on_inv₀ _ _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl)
    hx

Depends on / 依赖: AlgHom, AlgHom.ext, adjoin_induction, commutes, convert, map_add, map_mul
-/
theorem adjoin_algHom_ext {s : Set E} ⦃φ₁ φ₂ : adjoin F s ->ₐ[F] K⦄
    (h : forall x hx, φ₁ ⟨x, subset_adjoin _ _ hx⟩ = φ₂ ⟨x, subset_adjoin _ _ hx⟩) :
    φ₁ = φ₂ :=
  AlgHom.ext fun ⟨x, hx⟩ => adjoin_induction _ h (fun _ => φ₂.commutes _ ▸ φ₁.commutes _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· + ·) h₁ h₂ <;> rw [← map_add] <;> rfl)
    (fun _ _ => eq_on_inv₀ _ _)
    (fun _ _ _ _ h₁ h₂ => by convert! congr_arg₂ (· * ·) h₁ h₂ <;> rw [← map_mul] <;> rfl)
    hx

/--
theorem `algHom_ext_of_eq_adjoin` / 定理 `algHom_ext_of_eq_adjoin`

English:
theorem algHom_ext_of_eq_adjoin
  statement: {S : IntermediateField F E} {s : Set E} (hS : S = adjoin F s)
  proof: by
  subst hS; exact adjoin_algHom_ext F h

中文:
定理 algHom_ext_of_eq_adjoin
  结论: {S : 中间域 F E} {s : 集合 E} (hS : S = adjoin F s)
  证明: by
  subst hS; exact adjoin_algHom_ext F h

Depends on / 依赖: adjoin_algHom_ext
-/
theorem algHom_ext_of_eq_adjoin {S : IntermediateField F E} {s : Set E} (hS : S = adjoin F s)
    ⦃φ₁ φ₂ : S ->ₐ[F] K⦄
    (h : forall x hx, φ₁ ⟨x, hS.ge (subset_adjoin _ _ hx)⟩ = φ₂ ⟨x, hS.ge (subset_adjoin _ _ hx)⟩) :
    φ₁ = φ₂ := by
  subst hS; exact adjoin_algHom_ext F h

end

open Lean in
/-- Supporting function for the `F⟮x₁,x₂,...,xₙ⟯` adjunction notation. -/
private meta def mkInsertTerm {m : Type -> Type} [Monad m] [MonadQuotation m]
    (xs : TSyntaxArray `term) : m Term := run 0 where
  run (i : Nat) : m Term := do
    if h : i + 1 = xs.size then
      ``(singleton $(xs[i]))
    else if h : i < xs.size then
      ``(insert $(xs[i]) $(← run (i + 1)))
    else
      ``(EmptyCollection.emptyCollection)

/-- If `x₁ x₂ ... xₙ : E` then `F⟮x₁,x₂,...,xₙ⟯` is the `IntermediateField F E`
generated by these elements. -/
scoped macro:max K:term "⟮" xs:term,* "⟯" : term => do ``(adjoin $K $(← mkInsertTerm xs.getElems))

open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab IntermediateField.adjoin]
meta partial def delabAdjoinNotation : Delab := whenPPOption getPPNotation do
  let e ← getExpr
guard e.isAppOfArity ``adjoin 6
  let F ← withNaryArg 0 delab
  let xs ← withNaryArg 5 delabInsertArray
  `($F⟮$(xs.toArray),*⟯)
where
  delabInsertArray : DelabM (List Term) := do
    let e ← getExpr
    if e.isAppOfArity ``EmptyCollection.emptyCollection 2 then
      return []
    else if e.isAppOfArity ``singleton 4 then
      let x ← withNaryArg 3 delab
      return [x]
    else if e.isAppOfArity ``insert 5 then
      let x ← withNaryArg 3 delab
      let xs ← withNaryArg 4 delabInsertArray
      return x :: xs
    else failure

section AdjoinSimple

variable (α : E)

/--
theorem `mem_adjoin_simple_self` / 定理 `mem_adjoin_simple_self`

English:
theorem mem_adjoin_simple_self
  statement: α in F⟮α⟯
  proof: subset_adjoin F {α} (Set.mem_singleton α)

中文:
定理 mem_adjoin_simple_self
  结论: α in F⟮α⟯
  证明: subset_adjoin F {α} (Set.mem_singleton α)

Depends on / 依赖: Set.mem_singleton, mem_singleton, subset_adjoin
-/
theorem mem_adjoin_simple_self : α in F⟮α⟯ :=
  subset_adjoin F {α} (Set.mem_singleton α)

/--
Definition of `AdjoinSimple.gen` / `AdjoinSimple.gen` 的定义

English:
definition AdjoinSimple.gen
  signature: : F⟮α⟯
  body: ⟨α, mem_adjoin_simple_self F α⟩

@[simp]

中文:
定义 AdjoinSimple.gen
  签名: : F⟮α⟯
  定义体: ⟨α, mem_adjoin_simple_self F α⟩

@[simp]

Depends on / 依赖: mem_adjoin_simple_self
-/
def AdjoinSimple.gen : F⟮α⟯ :=
  ⟨α, mem_adjoin_simple_self F α⟩

@[simp]
/--
theorem `AdjoinSimple.coe_gen` / 定理 `AdjoinSimple.coe_gen`

English:
theorem AdjoinSimple.coe_gen
  statement: (AdjoinSimple.gen F α : E) = α
  proof: rfl

中文:
定理 AdjoinSimple.coe_gen
  结论: (AdjoinSimple.gen F α : E) = α
  证明: rfl
-/
theorem AdjoinSimple.coe_gen : (AdjoinSimple.gen F α : E) = α :=
  rfl

/--
theorem `AdjoinSimple.algebraMap_gen` / 定理 `AdjoinSimple.algebraMap_gen`

English:
theorem AdjoinSimple.algebraMap_gen
  statement: algebraMap F⟮α⟯ E (AdjoinSimple.gen F α) = α
  proof: rfl

中文:
定理 AdjoinSimple.algebraMap_gen
  结论: algebraMap F⟮α⟯ E (AdjoinSimple.gen F α) = α
  证明: rfl
-/
theorem AdjoinSimple.algebraMap_gen : algebraMap F⟮α⟯ E (AdjoinSimple.gen F α) = α :=
  rfl

-- Note: After unfolding `AdjoinSimple.gen`, the simp lemma `coe_aeval_mk_apply`
-- does not fire, so we have to add this.
@[simp]
/--
theorem `AdjoinSimple.coe_aeval_gen_apply` / 定理 `AdjoinSimple.coe_aeval_gen_apply`

English:
theorem AdjoinSimple.coe_aeval_gen_apply
  given: (f : F[X])
  proof: Polynomial.coe_aeval_mk_apply ..

中文:
定理 AdjoinSimple.coe_aeval_gen_apply
  条件: (f : F[X])
  证明: Polynomial.coe_aeval_mk_apply ..

Depends on / 依赖: Polynomial, Polynomial.coe_aeval_mk_apply, coe_aeval_mk_apply
-/
theorem AdjoinSimple.coe_aeval_gen_apply (f : F[X]) :
    aeval (AdjoinSimple.gen F α) f = aeval α f :=
  Polynomial.coe_aeval_mk_apply ..

/--
theorem `adjoin_simple_adjoin_simple` / 定理 `adjoin_simple_adjoin_simple`

English:
theorem adjoin_simple_adjoin_simple
  given: (β : E)
  statement: F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯
  proof: adjoin_adjoin_left _ _ _

中文:
定理 adjoin_simple_adjoin_simple
  条件: (β : E)
  结论: F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯
  证明: adjoin_adjoin_left _ _ _

Depends on / 依赖: adjoin_adjoin_left
-/
theorem adjoin_simple_adjoin_simple (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮α, β⟯ :=
  adjoin_adjoin_left _ _ _

/--
theorem `adjoin_simple_comm` / 定理 `adjoin_simple_comm`

English:
theorem adjoin_simple_comm
  given: (β : E)
  statement: F⟮α⟯⟮β⟯.restrictScalars F = F⟮β⟯⟮α⟯.restrictScalars F
  proof: adjoin_adjoin_comm _ _ _

中文:
定理 adjoin_simple_comm
  条件: (β : E)
  结论: F⟮α⟯⟮β⟯.restrictScalars F = F⟮β⟯⟮α⟯.restrictScalars F
  证明: adjoin_adjoin_comm _ _ _

Depends on / 依赖: adjoin_adjoin_comm
-/
theorem adjoin_simple_comm (β : E) : F⟮α⟯⟮β⟯.restrictScalars F = F⟮β⟯⟮α⟯.restrictScalars F :=
  adjoin_adjoin_comm _ _ _

variable {F} {α}

/--
theorem `adjoin_simple_le_iff` / 定理 `adjoin_simple_le_iff`

English:
theorem adjoin_simple_le_iff
  given: {K : IntermediateField F E}
  statement: F⟮α⟯ <= K ↔ α in K
  proof: by simp

中文:
定理 adjoin_simple_le_iff
  条件: {K : 中间域 F E}
  结论: F⟮α⟯ <= K ↔ α in K
  证明: by simp
-/
theorem adjoin_simple_le_iff {K : IntermediateField F E} : F⟮α⟯ <= K ↔ α in K := by simp

/--
theorem `biSup_adjoin_simple` / 定理 `biSup_adjoin_simple`

English:
theorem biSup_adjoin_simple
  statement: ⨆ x in S, F⟮x⟯ = adjoin F S
  proof: by
  rw [← iSup_subtype'']; rw [← gc.l_iSup]; rw [iSup_subtype'']; congr; exact S.biUnion_of_singleton

中文:
定理 biSup_adjoin_simple
  结论: ⨆ x in S, F⟮x⟯ = adjoin F S
  证明: by
  rw [← iSup_subtype'']; rw [← gc.l_iSup]; rw [iSup_subtype'']; congr; exact S.biUnion_of_singleton

Depends on / 依赖: S.biUnion_of_singleton, biUnion_of_singleton, gc.l_iSup, iSup_subtype, l_iSup
-/
theorem biSup_adjoin_simple : ⨆ x in S, F⟮x⟯ = adjoin F S := by
  rw [← iSup_subtype'']; rw [← gc.l_iSup]; rw [iSup_subtype'']; congr; exact S.biUnion_of_singleton

variable {A B C : Type*} [Field A] [Field B] [Field C] [Algebra A B] [Algebra B C] [Algebra A C]
  [IsScalarTower A B C] (b : B)

/--
Definition of `RingHom.adjoinAlgebraMap` / `RingHom.adjoinAlgebraMap` 的定义

English:
definition RingHom.adjoinAlgebraMap
  signature: : A⟮b⟯ ->+* A⟮((algebraMap B C) b)⟯
  body: RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp (IntermediateField.val A⟮b⟯)) _
    (fun x => by
      rw [show (algebraMap B C) b = (Algebra.ofId B C).restrictScalars A b by rfl]; rw [← Set.image_singleton]; rw [← IntermediateField.adjoin_map A {b}]
      use x
      simp)

中文:
定义 环态射.adjoinAlgebraMap
  签名: : A⟮b⟯ ->+* A⟮((algebraMap B C) b)⟯
  定义体: RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp (IntermediateField.val A⟮b⟯)) _
    (fun x => by
      rw [show (algebraMap B C) b = (Algebra.ofId B C).restrictScalars A b by rfl]; rw [← Set.image_singleton]; rw [← IntermediateField.adjoin_map A {b}]
      use x
      simp)

Depends on / 依赖: Algebra, Algebra.ofId, IntermediateField, IntermediateField.adjoin_map, IntermediateField.val, RingHom, RingHom.codRestrict, Set.image_singleton, adjoin_map, algebraMap, codRestrict, image_singleton, restrictScalars
-/
def RingHom.adjoinAlgebraMap : A⟮b⟯ ->+* A⟮((algebraMap B C) b)⟯ :=
  RingHom.codRestrict (((Algebra.ofId B C).restrictScalars A).comp (IntermediateField.val A⟮b⟯)) _
    (fun x => by
      rw [show (algebraMap B C) b = (Algebra.ofId B C).restrictScalars A b by rfl]; rw [← Set.image_singleton]; rw [← IntermediateField.adjoin_map A {b}]
      use x
      simp)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra A⟮b⟯ A⟮(algebraMap B C) b⟯
  body: RingHom.toAlgebra (RingHom.adjoinAlgebraMap _)

中文:
实例 :
  签名: 代数 A⟮b⟯ A⟮(algebraMap B C) b⟯
  定义体: RingHom.toAlgebra (RingHom.adjoinAlgebraMap _)

Depends on / 依赖: RingHom, RingHom.adjoinAlgebraMap, RingHom.toAlgebra, adjoinAlgebraMap, toAlgebra
-/
instance : Algebra A⟮b⟯ A⟮(algebraMap B C) b⟯ :=
  RingHom.toAlgebra (RingHom.adjoinAlgebraMap _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsScalarTower A⟮b⟯ A⟮(algebraMap B C) b⟯ C
  body: IsScalarTower.of_algebraMap_eq' rfl

中文:
实例 :
  签名: 标量塔 A⟮b⟯ A⟮(algebraMap B C) b⟯ C
  定义体: IsScalarTower.of_algebraMap_eq' rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance : IsScalarTower A⟮b⟯ A⟮(algebraMap B C) b⟯ C :=
  IsScalarTower.of_algebraMap_eq' rfl

end AdjoinSimple

end AdjoinDef

section AdjoinIntermediateFieldLattice

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E] {α : E} {S : Set E}

@[simp]
/--
theorem `adjoin_eq_bot_iff` / 定理 `adjoin_eq_bot_iff`

English:
theorem adjoin_eq_bot_iff
  statement: adjoin F S = ⊥ ↔ S subseteq (⊥ : IntermediateField F E)
  proof: by
  rw [eq_bot_iff]; rw [adjoin_le_iff]

中文:
定理 adjoin_eq_bot_iff
  结论: adjoin F S = ⊥ ↔ S subseteq (⊥ : 中间域 F E)
  证明: by
  rw [eq_bot_iff]; rw [adjoin_le_iff]

Depends on / 依赖: adjoin_le_iff, eq_bot_iff
-/
theorem adjoin_eq_bot_iff : adjoin F S = ⊥ ↔ S subseteq (⊥ : IntermediateField F E) := by
  rw [eq_bot_iff]; rw [adjoin_le_iff]

/--
theorem `adjoin_simple_eq_bot_iff` / 定理 `adjoin_simple_eq_bot_iff`

English:
theorem adjoin_simple_eq_bot_iff
  statement: F⟮α⟯ = ⊥ ↔ α in (⊥ : IntermediateField F E)
  proof: by
  simp

@[simp]

中文:
定理 adjoin_simple_eq_bot_iff
  结论: F⟮α⟯ = ⊥ ↔ α in (⊥ : 中间域 F E)
  证明: by
  simp

@[simp]
-/
theorem adjoin_simple_eq_bot_iff : F⟮α⟯ = ⊥ ↔ α in (⊥ : IntermediateField F E) := by
  simp

@[simp]
/--
theorem `adjoin_zero` / 定理 `adjoin_zero`

English:
theorem adjoin_zero
  statement: F⟮(0 : E)⟯ = ⊥
  proof: adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

@[simp]

中文:
定理 adjoin_zero
  结论: F⟮(0 : E)⟯ = ⊥
  证明: adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

@[simp]

Depends on / 依赖: adjoin_simple_eq_bot_iff, adjoin_simple_eq_bot_iff.mpr, zero_mem
-/
theorem adjoin_zero : F⟮(0 : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (zero_mem ⊥)

@[simp]
/--
theorem `adjoin_one` / 定理 `adjoin_one`

English:
theorem adjoin_one
  statement: F⟮(1 : E)⟯ = ⊥
  proof: adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

@[simp]

中文:
定理 adjoin_one
  结论: F⟮(1 : E)⟯ = ⊥
  证明: adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

@[simp]

Depends on / 依赖: adjoin_simple_eq_bot_iff, adjoin_simple_eq_bot_iff.mpr, one_mem
-/
theorem adjoin_one : F⟮(1 : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (one_mem ⊥)

@[simp]
/--
theorem `adjoin_intCast` / 定理 `adjoin_intCast`

English:
theorem adjoin_intCast
  given: (n : Int)
  statement: F⟮(n : E)⟯ = ⊥
  proof: by
  exact adjoin_simple_eq_bot_iff.mpr (intCast_mem ⊥ n)

@[simp]

中文:
定理 adjoin_intCast
  条件: (n : 整数)
  结论: F⟮(n : E)⟯ = ⊥
  证明: by
  exact adjoin_simple_eq_bot_iff.mpr (intCast_mem ⊥ n)

@[simp]

Depends on / 依赖: adjoin_simple_eq_bot_iff, adjoin_simple_eq_bot_iff.mpr, intCast_mem
-/
theorem adjoin_intCast (n : Int) : F⟮(n : E)⟯ = ⊥ := by
  exact adjoin_simple_eq_bot_iff.mpr (intCast_mem ⊥ n)

@[simp]
/--
theorem `adjoin_natCast` / 定理 `adjoin_natCast`

English:
theorem adjoin_natCast
  given: (n : Nat)
  statement: F⟮(n : E)⟯ = ⊥
  proof: adjoin_simple_eq_bot_iff.mpr (natCast_mem ⊥ n)

中文:
定理 adjoin_natCast
  条件: (n : 自然数)
  结论: F⟮(n : E)⟯ = ⊥
  证明: adjoin_simple_eq_bot_iff.mpr (natCast_mem ⊥ n)

Depends on / 依赖: adjoin_simple_eq_bot_iff, adjoin_simple_eq_bot_iff.mpr, natCast_mem
-/
theorem adjoin_natCast (n : Nat) : F⟮(n : E)⟯ = ⊥ :=
  adjoin_simple_eq_bot_iff.mpr (natCast_mem ⊥ n)

end AdjoinIntermediateFieldLattice

section Induction

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]

/-- An intermediate field `S` is finitely generated if there exists `t : Finset E` such that
`IntermediateField.adjoin F t = S`.

We use the class `Algebra.EssFiniteType F E` instead of `(⊤ : IntermediateField F E).FG` to say that
`E` is finitely generated as an `F` extension.
See `IntermediateField.fg_top_iff`. -/
@[stacks 09FZ "second part"]
/--
Definition of `FG` / `FG` 的定义

English:
definition FG
  signature: (S : IntermediateField F E)
  body: exists t : Finset E, adjoin F ↑t = S

中文:
定义 FG
  签名: (S : 中间域 F E)
  定义体: exists t : Finset E, adjoin F ↑t = S

Depends on / 依赖: Finset, adjoin
-/
def FG (S : IntermediateField F E) : Prop :=
  exists t : Finset E, adjoin F ↑t = S

/--
theorem `fg_adjoin_finset` / 定理 `fg_adjoin_finset`

English:
theorem fg_adjoin_finset
  given: (t : Finset E)
  statement: (adjoin F (↑t : Set E)).FG
  proof: ⟨t, rfl⟩

中文:
定理 fg_adjoin_finset
  条件: (t : 有限集 E)
  结论: (adjoin F (↑t : 集合 E)).FG
  证明: ⟨t, rfl⟩
-/
theorem fg_adjoin_finset (t : Finset E) : (adjoin F (↑t : Set E)).FG :=
  ⟨t, rfl⟩

/--
theorem `fg_def` / 定理 `fg_def`

English:
theorem fg_def
  given: {S : IntermediateField F E}
  statement: S.FG ↔ exists t : Set E, Set.Finite t ∧ adjoin F t = S
  proof: Iff.symm Set.exists_finite_iff_finset

中文:
定理 fg_def
  条件: {S : 中间域 F E}
  结论: S.FG ↔ 存在 t : 集合 E, 集合.有限 t ∧ adjoin F t = S
  证明: Iff.symm Set.exists_finite_iff_finset

Depends on / 依赖: Iff.symm, Set.exists_finite_iff_finset, exists_finite_iff_finset
-/
theorem fg_def {S : IntermediateField F E} : S.FG ↔ exists t : Set E, Set.Finite t ∧ adjoin F t = S :=
  Iff.symm Set.exists_finite_iff_finset

/--
theorem `fg_adjoin_of_finite` / 定理 `fg_adjoin_of_finite`

English:
theorem fg_adjoin_of_finite
  given: {t : Set E} (h : Set.Finite t)
  statement: (adjoin F t).FG
  proof: fg_def.mpr ⟨t, h, rfl⟩

中文:
定理 fg_adjoin_of_finite
  条件: {t : 集合 E} (h : 集合.有限 t)
  结论: (adjoin F t).FG
  证明: fg_def.mpr ⟨t, h, rfl⟩

Depends on / 依赖: fg_def, fg_def.mpr
-/
theorem fg_adjoin_of_finite {t : Set E} (h : Set.Finite t) : (adjoin F t).FG :=
  fg_def.mpr ⟨t, h, rfl⟩

/--
theorem `fg_bot` / 定理 `fg_bot`

English:
theorem fg_bot
  statement: (⊥ : IntermediateField F E).FG
  proof: ⟨∅, by simp only [Finset.coe_empty, adjoin_empty]⟩

中文:
定理 fg_bot
  结论: (⊥ : 中间域 F E).FG
  证明: ⟨∅, by simp only [Finset.coe_empty, adjoin_empty]⟩

Depends on / 依赖: Finset, Finset.coe_empty, adjoin_empty, coe_empty
-/
theorem fg_bot : (⊥ : IntermediateField F E).FG :=
  ⟨∅, by simp only [Finset.coe_empty, adjoin_empty]⟩

/--
theorem `fg_sup` / 定理 `fg_sup`

English:
theorem fg_sup
  given: {S T : IntermediateField F E} (hS : S.FG) (hT : T.FG)
  statement: (S ⊔ T).FG
  proof: by
  obtain ⟨s, rfl⟩ := hS; obtain ⟨t, rfl⟩ := hT
  classical rw [← adjoin_union, ← Finset.coe_union]
  exact fg_adjoin_finset _

中文:
定理 fg_sup
  条件: {S T : 中间域 F E} (hS : S.FG) (hT : T.FG)
  结论: (S ⊔ T).FG
  证明: by
  obtain ⟨s, rfl⟩ := hS; obtain ⟨t, rfl⟩ := hT
  classical rw [← adjoin_union, ← Finset.coe_union]
  exact fg_adjoin_finset _

Depends on / 依赖: Finset, Finset.coe_union, adjoin_union, classical, coe_union, fg_adjoin_finset
-/
theorem fg_sup {S T : IntermediateField F E} (hS : S.FG) (hT : T.FG) : (S ⊔ T).FG := by
  obtain ⟨s, rfl⟩ := hS; obtain ⟨t, rfl⟩ := hT
  classical rw [← adjoin_union, ← Finset.coe_union]
  exact fg_adjoin_finset _

/--
theorem `fg_iSup` / 定理 `fg_iSup`

English:
theorem fg_iSup
  given: {ι : Sort*} [Finite ι] {S : ι -> IntermediateField F E} (h : forall i, (S i).FG)
  proof: by
  choose s hs using h
  simp_rw [← hs, ← adjoin_iUnion]
  exact fg_adjoin_of_finite (Set.finite_iUnion fun _ => Finset.finite_toSet _)

中文:
定理 fg_iSup
  条件: {ι : 类型层*} [有限 ι] {S : ι -> 中间域 F E} (h : 对任意 i, (S i).FG)
  证明: by
  choose s hs using h
  simp_rw [← hs, ← adjoin_iUnion]
  exact fg_adjoin_of_finite (Set.finite_iUnion fun _ => Finset.finite_toSet _)

Depends on / 依赖: Finset, Finset.finite_toSet, Set.finite_iUnion, adjoin_iUnion, fg_adjoin_of_finite, finite_iUnion, finite_toSet, simp_rw
-/
theorem fg_iSup {ι : Sort*} [Finite ι] {S : ι -> IntermediateField F E} (h : forall i, (S i).FG) :
    (⨆ i, S i).FG := by
  choose s hs using h
  simp_rw [← hs, ← adjoin_iUnion]
  exact fg_adjoin_of_finite (Set.finite_iUnion fun _ => Finset.finite_toSet _)

/--
theorem `_root_.Field.fg_iff_fg_top_bot` / 定理 `_root_.Field.fg_iff_fg_top_bot`

English:
theorem _root_.Field.fg_iff_fg_top_bot
  proof: by
  simp [Field.fg_iff, fg_def, Set.exists_finite_iff_finset,
    ← toSubfield_inj, Subfield.algebraMap_ofSubfield, Subfield.closure_union]

中文:
定理 _root_.域.fg_iff_fg_top_bot
  证明: by
  simp [Field.fg_iff, fg_def, Set.exists_finite_iff_finset,
    ← toSubfield_inj, Subfield.algebraMap_ofSubfield, Subfield.closure_union]

Depends on / 依赖: Field.fg_iff, Set.exists_finite_iff_finset, Subfield, Subfield.algebraMap_ofSubfield, Subfield.closure_union, algebraMap_ofSubfield, closure_union, exists_finite_iff_finset, fg_def, fg_iff, toSubfield_inj
-/
theorem _root_.Field.fg_iff_fg_top_bot :
    Field.FG F ↔ (⊤ : IntermediateField (⊥ : Subfield F) F).FG := by
  simp [Field.fg_iff, fg_def, Set.exists_finite_iff_finset,
    ← toSubfield_inj, Subfield.algebraMap_ofSubfield, Subfield.closure_union]

/--
theorem `induction_on_adjoin_finset` / 定理 `induction_on_adjoin_finset`

English:
theorem induction_on_adjoin_finset
  statement: (S : Finset E) (P : IntermediateField F E -> Prop) (base : P ⊥)
  proof: by
  classical
  refine Finset.induction_on' S ?_ (fun _ _ ha _ _ h => ?_)
  · simp [base]
  · rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    exact ih (adjoin F _) _ ha h

中文:
定理 induction_on_adjoin_finset
  结论: (S : 有限集 E) (P : 中间域 F E -> 命题) (base : P ⊥)
  证明: by
  classical
  refine Finset.induction_on' S ?_ (fun _ _ ha _ _ h => ?_)
  · simp [base]
  · rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    exact ih (adjoin F _) _ ha h

Depends on / 依赖: Finset, Finset.coe_insert, Finset.induction_on, Set.insert_eq, Set.union_comm, adjoin, adjoin_adjoin_left, classical, coe_insert, induction_on, insert_eq, union_comm
-/
theorem induction_on_adjoin_finset (S : Finset E) (P : IntermediateField F E -> Prop) (base : P ⊥)
    (ih : forall (K : IntermediateField F E), forall x in S, P K -> P (K⟮x⟯.restrictScalars F)) :
    P (adjoin F S) := by
  classical
  refine Finset.induction_on' S ?_ (fun _ _ ha _ _ h => ?_)
  · simp [base]
  · rw [Finset.coe_insert, Set.insert_eq, Set.union_comm, ← adjoin_adjoin_left]
    exact ih (adjoin F _) _ ha h

/--
theorem `induction_on_adjoin_fg` / 定理 `induction_on_adjoin_fg`

English:
theorem induction_on_adjoin_fg
  statement: (P : IntermediateField F E -> Prop) (base : P ⊥)
  proof: by
  obtain ⟨S, rfl⟩ := hK
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK

中文:
定理 induction_on_adjoin_fg
  结论: (P : 中间域 F E -> 命题) (base : P ⊥)
  证明: by
  obtain ⟨S, rfl⟩ := hK
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK

Depends on / 依赖: induction_on_adjoin_finset
-/
theorem induction_on_adjoin_fg (P : IntermediateField F E -> Prop) (base : P ⊥)
    (ih : forall (K : IntermediateField F E) (x : E), P K -> P (K⟮x⟯.restrictScalars F))
    (K : IntermediateField F E) (hK : K.FG) : P K := by
  obtain ⟨S, rfl⟩ := hK
  exact induction_on_adjoin_finset S P base fun K x _ hK => ih K x hK

end Induction

end IntermediateField

namespace IntermediateField

variable {K L L' : Type*} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']

/--
theorem `map_comap_eq` / 定理 `map_comap_eq`

English:
theorem map_comap_eq
  given: (f : L ->ₐ[K] L') (S : IntermediateField K L')
  proof: SetLike.coe_injective Set.image_preimage_eq_inter_range

中文:
定理 map_comap_eq
  条件: (f : L ->ₐ[K] L') (S : 中间域 K L')
  证明: SetLike.coe_injective Set.image_preimage_eq_inter_range

Depends on / 依赖: Set.image_preimage_eq_inter_range, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq_inter_range
-/
theorem map_comap_eq (f : L ->ₐ[K] L') (S : IntermediateField K L') :
    (S.comap f).map f = S ⊓ f.fieldRange :=
  SetLike.coe_injective Set.image_preimage_eq_inter_range

/--
theorem `map_comap_eq_self` / 定理 `map_comap_eq_self`

English:
theorem map_comap_eq_self
  given: {f : L ->ₐ[K] L'} {S : IntermediateField K L'} (h : S <= f.fieldRange)
  proof: by
  simpa only [inf_of_le_left h] using map_comap_eq f S

中文:
定理 map_comap_eq_self
  条件: {f : L ->ₐ[K] L'} {S : 中间域 K L'} (h : S <= f.fieldRange)
  证明: by
  simpa only [inf_of_le_left h] using map_comap_eq f S

Depends on / 依赖: inf_of_le_left, map_comap_eq
-/
theorem map_comap_eq_self {f : L ->ₐ[K] L'} {S : IntermediateField K L'} (h : S <= f.fieldRange) :
    (S.comap f).map f = S := by
  simpa only [inf_of_le_left h] using map_comap_eq f S

/--
theorem `map_comap_eq_self_of_surjective` / 定理 `map_comap_eq_self_of_surjective`

English:
theorem map_comap_eq_self_of_surjective
  statement: {f : L ->ₐ[K] L'} (hf : Function.Surjective f)
  proof: SetLike.coe_injective (Set.image_preimage_eq _ hf)

中文:
定理 map_comap_eq_self_of_surjective
  结论: {f : L ->ₐ[K] L'} (hf : 函数.满射 f)
  证明: SetLike.coe_injective (Set.image_preimage_eq _ hf)

Depends on / 依赖: Set.image_preimage_eq, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq
-/
theorem map_comap_eq_self_of_surjective {f : L ->ₐ[K] L'} (hf : Function.Surjective f)
    (S : IntermediateField K L') : (S.comap f).map f = S :=
  SetLike.coe_injective (Set.image_preimage_eq _ hf)

/--
theorem `comap_map` / 定理 `comap_map`

English:
theorem comap_map
  given: (f : L ->ₐ[K] L') (S : IntermediateField K L)
  statement: (S.map f).comap f = S
  proof: SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

中文:
定理 comap_map
  条件: (f : L ->ₐ[K] L') (S : 中间域 K L)
  结论: (S.map f).comap f = S
  证明: SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

Depends on / 依赖: Set.preimage_image_eq, SetLike, SetLike.coe_injective, coe_injective, f.injective, injective, preimage_image_eq
-/
theorem comap_map (f : L ->ₐ[K] L') (S : IntermediateField K L) : (S.map f).comap f = S :=
  SetLike.coe_injective (Set.preimage_image_eq _ f.injective)

end IntermediateField

section ExtendScalars

variable {K : Type*} [Field K] {L : Type*} [Field L] [Algebra K L]

namespace Subfield

variable (F : Subfield L)

@[simp]
/--
theorem `extendScalars_self` / 定理 `extendScalars_self`

English:
theorem extendScalars_self
  statement: extendScalars (le_refl F) = ⊥
  proof: by
  ext x
  rw [mem_extendScalars]; rw [IntermediateField.mem_bot]
  refine ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩
  rintro ⟨y, rfl⟩
  exact y.2

@[simp]

中文:
定理 extendScalars_self
  结论: extendScalars (le_refl F) = ⊥
  证明: by
  ext x
  rw [mem_extendScalars]; rw [IntermediateField.mem_bot]
  refine ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩
  rintro ⟨y, rfl⟩
  exact y.2

@[simp]

Depends on / 依赖: IntermediateField, IntermediateField.mem_bot, mem_bot, mem_extendScalars
-/
theorem extendScalars_self : extendScalars (le_refl F) = ⊥ := by
  ext x
  rw [mem_extendScalars]; rw [IntermediateField.mem_bot]
  refine ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩
  rintro ⟨y, rfl⟩
  exact y.2

@[simp]
/--
theorem `extendScalars_top` / 定理 `extendScalars_top`

English:
theorem extendScalars_top
  statement: extendScalars (le_top : F <= ⊤) = ⊤
  proof: IntermediateField.toSubfield_injective (by simp)

中文:
定理 extendScalars_top
  结论: extendScalars (le_top : F <= ⊤) = ⊤
  证明: IntermediateField.toSubfield_injective (by simp)

Depends on / 依赖: IntermediateField, IntermediateField.toSubfield_injective, toSubfield_injective
-/
theorem extendScalars_top : extendScalars (le_top : F <= ⊤) = ⊤ :=
  IntermediateField.toSubfield_injective (by simp)

variable {F}
variable {E E' : Subfield L} (h : F <= E) (h' : F <= E')

/--
theorem `extendScalars_sup` / 定理 `extendScalars_sup`

English:
theorem extendScalars_sup
  proof: ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm

中文:
定理 extendScalars_sup
  证明: ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm

Depends on / 依赖: extendScalars, extendScalars.orderIso, map_sup, orderIso
-/
theorem extendScalars_sup :
    extendScalars h ⊔ extendScalars h' = extendScalars (le_sup_of_le_left h : F <= E ⊔ E') :=
  ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm

/--
theorem `extendScalars_inf` / 定理 `extendScalars_inf`

English:
theorem extendScalars_inf
  statement: extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h')
  proof: ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

中文:
定理 extendScalars_inf
  结论: extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h')
  证明: ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

Depends on / 依赖: extendScalars, extendScalars.orderIso, map_inf, orderIso
-/
theorem extendScalars_inf : extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h') :=
  ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

end Subfield

namespace IntermediateField

variable (F : IntermediateField K L)

@[simp]
/--
theorem `extendScalars_self` / 定理 `extendScalars_self`

English:
theorem extendScalars_self
  statement: extendScalars (le_refl F) = ⊥
  proof: restrictScalars_injective K (by simp)

@[simp]

中文:
定理 extendScalars_self
  结论: extendScalars (le_refl F) = ⊥
  证明: restrictScalars_injective K (by simp)

@[simp]

Depends on / 依赖: restrictScalars_injective
-/
theorem extendScalars_self : extendScalars (le_refl F) = ⊥ :=
  restrictScalars_injective K (by simp)

@[simp]
/--
theorem `extendScalars_top` / 定理 `extendScalars_top`

English:
theorem extendScalars_top
  statement: extendScalars (le_top : F <= ⊤) = ⊤
  proof: restrictScalars_injective K (by simp)

中文:
定理 extendScalars_top
  结论: extendScalars (le_top : F <= ⊤) = ⊤
  证明: restrictScalars_injective K (by simp)

Depends on / 依赖: restrictScalars_injective
-/
theorem extendScalars_top : extendScalars (le_top : F <= ⊤) = ⊤ :=
  restrictScalars_injective K (by simp)

variable {F}
variable {E E' : IntermediateField K L} (h : F <= E) (h' : F <= E')

/--
theorem `extendScalars_sup` / 定理 `extendScalars_sup`

English:
theorem extendScalars_sup
  proof: ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm

中文:
定理 extendScalars_sup
  证明: ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm

Depends on / 依赖: extendScalars, extendScalars.orderIso, map_sup, orderIso
-/
theorem extendScalars_sup :
    extendScalars h ⊔ extendScalars h' = extendScalars (le_sup_of_le_left h : F <= E ⊔ E') :=
  ((extendScalars.orderIso F).map_sup ⟨_, h⟩ ⟨_, h'⟩).symm

/--
theorem `extendScalars_inf` / 定理 `extendScalars_inf`

English:
theorem extendScalars_inf
  statement: extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h')
  proof: ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

中文:
定理 extendScalars_inf
  结论: extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h')
  证明: ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

Depends on / 依赖: extendScalars, extendScalars.orderIso, map_inf, orderIso
-/
theorem extendScalars_inf : extendScalars h ⊓ extendScalars h' = extendScalars (le_inf h h') :=
  ((extendScalars.orderIso F).map_inf ⟨_, h⟩ ⟨_, h'⟩).symm

end IntermediateField

end ExtendScalars
