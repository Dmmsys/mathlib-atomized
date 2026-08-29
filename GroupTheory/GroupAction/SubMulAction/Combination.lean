/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.
This file provides some API for handling them in the context of a group action.

* `Set.powersetCard.subMulAction`:
  When a group `G` acts on `α`, the `SubMulAction` of `G` on `powersetCard α n`.

This induces a `MulAction G (powersetCard α n)` instance. Then:

* `Set.powerSetCard.mulActionHom_of_embedding`:
  the equivariant map from `Fin n ↪ α` to `powersetCard α n`.

* `Set.powersetCard.isPretransitive_of_isMultiplyPretransitive`
  shows the pretransitivity of that action if the action of `G` on `α` is `n`-pretransitive.

* `Set.powersetCard.isPretransitive` shows that `Equiv.Perm α`
  acts pretransitively on `powersetCard α n`, for all `n`.

* `Set.powersetCard.compl`: Given an equality `m + n = Fintype.card α`,
  the complement of an `n`-combination, as an `m`-combination.
  This map is an equivariant map with respect to a group action on `α`.

* `Set.powersetCard.mulActionHom_singleton`:
  The obvious map from `α` to `powersetCard α 1`, as an equivariant map.

-/

@[expose] public section

namespace Set.powersetCard

open scoped Pointwise

open MulAction Finset Set Equiv Equiv.Perm

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]
  {n : Nat} {s t : powersetCard α n}

section

variable [DecidableEq α]

variable (α n) in
/-- `Set.powersetCard α n` as a `SubMulAction` of `Finset α`. -/
@[to_additive /--`Set.powersetCard α n` as a `SubAddAction` of `Finsetα`.-/]
/--
Definition of `subMulAction` / `subMulAction` 的定义

English:
definition subMulAction
  signature: : SubMulAction G (Finset α) where
  body: powersetCard α n
  smul_mem' g s := (card_smul_finset g s).trans

@[to_additive]

中文:
定义 subMulAction
  签名: : SubMul作用 G (有限集 α) where
  定义体: powersetCard α n
  smul_mem' g s := (card_smul_finset g s).trans

@[to_additive]

Depends on / 依赖: powersetCard
-/
def subMulAction : SubMulAction G (Finset α) where
  carrier := powersetCard α n
  smul_mem' g s := (card_smul_finset g s).trans

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction G (powersetCard α n)
  body: inferInstanceAs MulAction G (subMulAction G α n)

中文:
实例 :
  签名: 乘法作用 G (powersetCard α n)
  定义体: inferInstanceAs MulAction G (subMulAction G α n)

Depends on / 依赖: MulAction, subMulAction
-/
instance : MulAction G (powersetCard α n) :=
inferInstanceAs MulAction G (subMulAction G α n)

variable {G}

@[to_additive (attr := simp)]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: {n : Nat} {g : G} {s : powersetCard α n}
  proof: SubMulAction.val_smul (p := subMulAction G α n) g s

@[to_additive addAction_stabilizer_coe]

中文:
定理 coe_smul
  条件: {n : 自然数} {g : G} {s : powersetCard α n}
  证明: SubMulAction.val_smul (p := subMulAction G α n) g s

@[to_additive addAction_stabilizer_coe]

Depends on / 依赖: SubMulAction, SubMulAction.val_smul, subMulAction, val_smul
-/
theorem coe_smul {n : Nat} {g : G} {s : powersetCard α n} :
    ((g • s : powersetCard α n) : Finset α) = g • s :=
  SubMulAction.val_smul (p := subMulAction G α n) g s

@[to_additive addAction_stabilizer_coe]
/--
theorem `stabilizer_coe` / 定理 `stabilizer_coe`

English:
theorem stabilizer_coe
  given: {n : Nat} (s : powersetCard α n)
  proof: by
  ext g
  simp [mem_stabilizer_iff, ← Subtype.coe_inj, ← coe_inj]

中文:
定理 stabilizer_coe
  条件: {n : 自然数} (s : powersetCard α n)
  证明: by
  ext g
  simp [mem_stabilizer_iff, ← Subtype.coe_inj, ← coe_inj]

Depends on / 依赖: Subtype, Subtype.coe_inj, coe_inj, mem_stabilizer_iff
-/
theorem stabilizer_coe {n : Nat} (s : powersetCard α n) :
    stabilizer G s = stabilizer G (s : Set α) := by
  ext g
  simp [mem_stabilizer_iff, ← Subtype.coe_inj, ← coe_inj]

/--
theorem `addAction_faithful` / 定理 `addAction_faithful`

English:
theorem addAction_faithful
  statement: {G : Type*} [AddGroup G] [AddAction G α] {n : Nat}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose h with h
    have : exists a, (g +ᵥ a : α) != a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff]; rw [not_forall]
    use s
    contrapose has'
    simp only [AddAction.toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa [← mem_coe_iff]
  · simp only [Equiv.ext_iff, AddAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_vadd_finset, h]

中文:
定理 addAction_faithful
  结论: {G : 类型} [加法群 G] [加法作用 G α] {n : 自然数}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose h with h
    have : exists a, (g +ᵥ a : α) != a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff]; rw [not_forall]
    use s
    contrapose has'
    simp only [AddAction.toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa [← mem_coe_iff]
  · simp only [Equiv.ext_iff, AddAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_vadd_finset, h]

Depends on / 依赖: AddAction, AddAction.toPerm_apply, Equiv.ext_iff, Finset, Finset.ext_iff, Ne.symm, Subtype, Subtype.ext_iff, coe_one, contrapose, exists_mem_notMem, ext_iff, id_eq, mem_coe_iff, mem_vadd_finset, not_forall, toPerm_apply
-/
theorem addAction_faithful {G : Type*} [AddGroup G] [AddAction G α] {n : Nat}
    (hn : 1 <= n) (hα : n < ENat.card α) {g : G} :
    AddAction.toPerm g = (1 : Perm (powersetCard α n)) ↔ AddAction.toPerm g = (1 : Perm α) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose h with h
    have : exists a, (g +ᵥ a : α) != a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff]; rw [not_forall]
    use s
    contrapose has'
    simp only [AddAction.toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa [← mem_coe_iff]
  · simp only [Equiv.ext_iff, AddAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_vadd_finset, h]

/--
theorem `faithfulVAdd` / 定理 `faithfulVAdd`

English:
theorem faithfulVAdd
  statement: {G : Type*} [AddGroup G] [AddAction G α] {n : Nat}
  proof: by
  rw [faithfulVAdd_iff]
  intro g hg
  apply AddAction.toPerm_injective (α := G) (β := α)
  rw [AddAction.toPerm_zero]; rw [← addAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

中文:
定理 faithfulVAdd
  结论: {G : 类型} [加法群 G] [加法作用 G α] {n : 自然数}
  证明: by
  rw [faithfulVAdd_iff]
  intro g hg
  apply AddAction.toPerm_injective (α := G) (β := α)
  rw [AddAction.toPerm_zero]; rw [← addAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

Depends on / 依赖: AddAction, AddAction.toPerm_injective, AddAction.toPerm_zero, Perm.ext_iff.mpr, addAction_faithful, ext_iff, faithfulVAdd_iff, toPerm_injective, toPerm_zero
-/
theorem faithfulVAdd {G : Type*} [AddGroup G] [AddAction G α] {n : Nat}
    (hn : 1 <= n) (hα : n < ENat.card α) [FaithfulVAdd G α] :
    FaithfulVAdd G (powersetCard α n) := by
  rw [faithfulVAdd_iff]
  intro g hg
  apply AddAction.toPerm_injective (α := G) (β := α)
  rw [AddAction.toPerm_zero]; rw [← addAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

/--
theorem `mulAction_faithful` / 定理 `mulAction_faithful`

English:
theorem mulAction_faithful
  given: (hn : 1 <= n) (hα : n < ENat.card α) {g : G}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose h with h
    have : exists a, (g • a : α) != a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff]; rw [not_forall]
    use s
    contrapose! has'
    simp only [toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa only [coe_smul, smul_mem_smul_finset_iff, ← mem_coe_iff]
  · simp only [Equiv.ext_iff, toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_smul_finset, h]

中文:
定理 mulAction_faithful
  条件: (hn : 1 <= n) (hα : n < E自然数.card α) {g : G}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose h with h
    have : exists a, (g • a : α) != a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff]; rw [not_forall]
    use s
    contrapose! has'
    simp only [toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa only [coe_smul, smul_mem_smul_finset_iff, ← mem_coe_iff]
  · simp only [Equiv.ext_iff, toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_smul_finset, h]

Depends on / 依赖: Equiv.ext_iff, Finset, Finset.ext_iff, Ne.symm, Subtype, Subtype.ext_iff, coe_one, coe_smul, contrapose, exists_mem_notMem, ext_iff, id_eq, mem_coe_iff, mem_smul_finset, not_forall, smul_mem_smul_finset_iff, toPerm_apply
-/
theorem mulAction_faithful (hn : 1 <= n) (hα : n < ENat.card α) {g : G} :
    toPerm g = (1 : Perm (powersetCard α n)) ↔ toPerm g = (1 : Perm α) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · contrapose h with h
    have : exists a, (g • a : α) != a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff]; rw [not_forall]
    use s
    contrapose! has'
    simp only [toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa only [coe_smul, smul_mem_smul_finset_iff, ← mem_coe_iff]
  · simp only [Equiv.ext_iff, toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_smul_finset, h]

/--
theorem `faithfulSMul` / 定理 `faithfulSMul`

English:
theorem faithfulSMul
  given: (hn : 1 <= n) (hα : n < ENat.card α) [FaithfulSMul G α]
  proof: by
  rw [faithfulSMul_iff]
  intro g hg
  apply toPerm_injective (α := G) (β := α)
  rw [toPerm_one]; rw [← mulAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

中文:
定理 faithfulSMul
  条件: (hn : 1 <= n) (hα : n < E自然数.card α) [忠实标量乘法 G α]
  证明: by
  rw [faithfulSMul_iff]
  intro g hg
  apply toPerm_injective (α := G) (β := α)
  rw [toPerm_one]; rw [← mulAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

Depends on / 依赖: Perm.ext_iff.mpr, ext_iff, faithfulSMul_iff, mulAction_faithful, toPerm_injective, toPerm_one
-/
theorem faithfulSMul (hn : 1 <= n) (hα : n < ENat.card α) [FaithfulSMul G α] :
    FaithfulSMul G (powersetCard α n) := by
  rw [faithfulSMul_iff]
  intro g hg
  apply toPerm_injective (α := G) (β := α)
  rw [toPerm_one]; rw [← mulAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

attribute [to_additive existing] faithfulSMul

variable (α G)

set_option backward.isDefEq.respectTransparency false in
variable (n) in
/-- The equivariant map from embeddings of `Fin n` (aka arrangement) to combinations. -/
@[to_additive /-- The equivariant map from embeddings of `Fin n`
  (aka arrangements) to combinations. -/]
/--
Definition of `mulActionHom_of_embedding` / `mulActionHom_of_embedding` 的定义

English:
definition mulActionHom_of_embedding
  signature: : (Fin n ↪ α) ->[G] powersetCard α n where
  body: ofFinEmb n α
  map_smul' g f := by
    rw [← Subtype.coe_inj]; rw [coe_smul]; rw [f.smul_def]; rw [val_ofFinEmb]; rw [val_ofFinEmb]; rw [smul_finset_def]; rw [← map_map]; rw [map_eq_image]
    simp [toPerm]

@[to_additive]

中文:
定义 mulActionHom_of_embedding
  签名: : (有限集 n ↪ α) ->[G] powersetCard α n where
  定义体: ofFinEmb n α
  map_smul' g f := by
    rw [← Subtype.coe_inj]; rw [coe_smul]; rw [f.smul_def]; rw [val_ofFinEmb]; rw [val_ofFinEmb]; rw [smul_finset_def]; rw [← map_map]; rw [map_eq_image]
    simp [toPerm]

@[to_additive]

Depends on / 依赖: ofFinEmb
-/
def mulActionHom_of_embedding : (Fin n ↪ α) ->[G] powersetCard α n where
  toFun := ofFinEmb n α
  map_smul' g f := by
    rw [← Subtype.coe_inj]; rw [coe_smul]; rw [f.smul_def]; rw [val_ofFinEmb]; rw [val_ofFinEmb]; rw [smul_finset_def]; rw [← map_map]; rw [map_eq_image]
    simp [toPerm]

@[to_additive]
/--
theorem `coe_mulActionHom_of_embedding` / 定理 `coe_mulActionHom_of_embedding`

English:
theorem coe_mulActionHom_of_embedding
  given: (f : Fin n ↪ α)
  proof: rfl

@[to_additive]

中文:
定理 coe_mulActionHom_of_embedding
  条件: (f : 有限集 n ↪ α)
  证明: rfl

@[to_additive]
-/
theorem coe_mulActionHom_of_embedding (f : Fin n ↪ α) :
    ↑((mulActionHom_of_embedding G α n).toFun f) = Finset.univ.map f :=
  rfl

@[to_additive]
/--
theorem `mulActionHom_of_embedding_surjective` / 定理 `mulActionHom_of_embedding_surjective`

English:
theorem mulActionHom_of_embedding_surjective
  proof: by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ α, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

中文:
定理 mulActionHom_of_embedding_surjective
  证明: by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ α, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

Depends on / 依赖: Embedding, Fintype, Fintype.card_fin, Function, Function.Embedding.exists_of_card_eq_finset, Subtype, Subtype.ext, card_fin, exists_of_card_eq_finset
-/
theorem mulActionHom_of_embedding_surjective :
    Function.Surjective (mulActionHom_of_embedding G α n) := by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ α, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

end

variable [DecidableEq α]

@[to_additive isPretransitive_of_isMultiplyPretransitive']
/--
theorem `isPretransitive_of_isMultiplyPretransitive` / 定理 `isPretransitive_of_isMultiplyPretransitive`

English:
theorem isPretransitive_of_isMultiplyPretransitive
  given: (h : IsMultiplyPretransitive G α n)
  proof: IsPretransitive.of_surjective_map (mulActionHom_of_embedding_surjective G α) h

中文:
定理 isPretransitive_of_isMultiplyPretransitive
  条件: (h : IsMultiplyPretransitive G α n)
  证明: IsPretransitive.of_surjective_map (mulActionHom_of_embedding_surjective G α) h

Depends on / 依赖: IsPretransitive, IsPretransitive.of_surjective_map, mulActionHom_of_embedding_surjective, of_surjective_map
-/
theorem isPretransitive_of_isMultiplyPretransitive (h : IsMultiplyPretransitive G α n) :
    IsPretransitive G (powersetCard α n) :=
  IsPretransitive.of_surjective_map (mulActionHom_of_embedding_surjective G α) h

/--
theorem `isPretransitive` / 定理 `isPretransitive`

English:
theorem isPretransitive
  statement: IsPretransitive (Perm α) (powersetCard α n)
  proof: isPretransitive_of_isMultiplyPretransitive _ (isMultiplyPretransitive α n)

中文:
定理 isPretransitive
  结论: 是Pretransitive (置换 α) (powersetCard α n)
  证明: isPretransitive_of_isMultiplyPretransitive _ (isMultiplyPretransitive α n)

Depends on / 依赖: isMultiplyPretransitive, isPretransitive_of_isMultiplyPretransitive
-/
theorem isPretransitive : IsPretransitive (Perm α) (powersetCard α n) :=
  isPretransitive_of_isMultiplyPretransitive _ (isMultiplyPretransitive α n)

section compl

variable (α)

variable [Fintype α] {m : Nat} (hm : m + n = Fintype.card α)
include hm

/--
Definition of `mulActionHom_compl` / `mulActionHom_compl` 的定义

English:
definition mulActionHom_compl
  signature: : powersetCard α n ->[G] powersetCard α m where
  body: compl hm
  map_smul' g s := by ext; simp [← inv_smul_mem_iff]

中文:
定义 mulActionHom_compl
  签名: : powersetCard α n ->[G] powersetCard α m where
  定义体: compl hm
  map_smul' g s := by ext; simp [← inv_smul_mem_iff]
-/
def mulActionHom_compl : powersetCard α n ->[G] powersetCard α m where
  toFun := compl hm
  map_smul' g s := by ext; simp [← inv_smul_mem_iff]

variable {hm} in
/--
theorem `coe_mulActionHom_compl` / 定理 `coe_mulActionHom_compl`

English:
theorem coe_mulActionHom_compl
  given: {s : powersetCard α n}
  proof: rfl

中文:
定理 coe_mulActionHom_compl
  条件: {s : powersetCard α n}
  证明: rfl
-/
theorem coe_mulActionHom_compl {s : powersetCard α n} :
    (mulActionHom_compl G α hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

variable {hm} in
/--
theorem `mem_mulActionHom_compl` / 定理 `mem_mulActionHom_compl`

English:
theorem mem_mulActionHom_compl
  given: {s : powersetCard α n} {a : α}
  proof: mem_compl

中文:
定理 mem_mulActionHom_compl
  条件: {s : powersetCard α n} {a : α}
  证明: mem_compl

Depends on / 依赖: mem_compl
-/
theorem mem_mulActionHom_compl {s : powersetCard α n} {a : α} :
    a in mulActionHom_compl G α hm s ↔ a ∉ s :=
  mem_compl

/--
theorem `mulActionHom_compl_mulActionHom_compl` / 定理 `mulActionHom_compl_mulActionHom_compl`

English:
theorem mulActionHom_compl_mulActionHom_compl
  proof: by
  ext s a
  change a in (mulActionHom_compl G α _).comp (mulActionHom_compl G α hm) s ↔ a in s
  simp [MulActionHom.comp_apply, mem_mulActionHom_compl]

中文:
定理 mulActionHom_compl_mulActionHom_compl
  证明: by
  ext s a
  change a in (mulActionHom_compl G α _).comp (mulActionHom_compl G α hm) s ↔ a in s
  simp [MulActionHom.comp_apply, mem_mulActionHom_compl]

Depends on / 依赖: MulActionHom, MulActionHom.comp_apply, comp_apply, mem_mulActionHom_compl, mulActionHom_compl
-/
theorem mulActionHom_compl_mulActionHom_compl :
    (mulActionHom_compl G α <| (n.add_comm m).trans hm).comp
    (mulActionHom_compl G α hm) = .id G := by
  ext s a
  change a in (mulActionHom_compl G α _).comp (mulActionHom_compl G α hm) s ↔ a in s
  simp [MulActionHom.comp_apply, mem_mulActionHom_compl]

/--
theorem `mulActionHom_compl_bijective` / 定理 `mulActionHom_compl_bijective`

English:
theorem mulActionHom_compl_bijective
  proof: Function.bijective_iff_has_inverse.mpr ⟨mulActionHom_compl G α ((n.add_comm m).trans hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α _)⟩

中文:
定理 mulActionHom_compl_bijective
  证明: Function.bijective_iff_has_inverse.mpr ⟨mulActionHom_compl G α ((n.add_comm m).trans hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α _)⟩

Depends on / 依赖: DFunLike, DFunLike.ext_iff.mp, Function, Function.bijective_iff_has_inverse.mpr, add_comm, bijective_iff_has_inverse, ext_iff, mulActionHom_compl, mulActionHom_compl_mulActionHom_compl, n.add_comm
-/
theorem mulActionHom_compl_bijective :
    Function.Bijective (mulActionHom_compl G α hm) :=
  Function.bijective_iff_has_inverse.mpr ⟨mulActionHom_compl G α ((n.add_comm m).trans hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α _)⟩

end compl

variable {G} in
/--
theorem `fixedPoints_ne_univ_of_faithfulSMul` / 定理 `fixedPoints_ne_univ_of_faithfulSMul`

English:
theorem fixedPoints_ne_univ_of_faithfulSMul
  proof: by
  obtain ⟨g, h⟩ := exists_ne (1 : G)
  contrapose! h
  replace h : (toPerm g : Perm (powersetCard α n)) = 1 := by
    ext1 s
    exact eq_univ_iff_forall.mp h s g
  rwa [← toPermHom_apply, map_eq_one_iff] at h
  have := powersetCard.faithfulSMul (G := G) (α := α) hn ?_
  · exact MulAction.toPerm_injective
  · simpa [ENat.card_eq_coe_natCard, Nat.cast_lt, Nat.finite_of_card_ne_zero (ne_zero_of_lt hn')]

中文:
定理 fixedPoints_ne_univ_of_faithfulSMul
  证明: by
  obtain ⟨g, h⟩ := exists_ne (1 : G)
  contrapose! h
  replace h : (toPerm g : Perm (powersetCard α n)) = 1 := by
    ext1 s
    exact eq_univ_iff_forall.mp h s g
  rwa [← toPermHom_apply, map_eq_one_iff] at h
  have := powersetCard.faithfulSMul (G := G) (α := α) hn ?_
  · exact MulAction.toPerm_injective
  · simpa [ENat.card_eq_coe_natCard, Nat.cast_lt, Nat.finite_of_card_ne_zero (ne_zero_of_lt hn')]

Depends on / 依赖: ENat.card_eq_coe_natCard, MulAction, MulAction.toPerm_injective, Nat.cast_lt, Nat.finite_of_card_ne_zero, card_eq_coe_natCard, cast_lt, contrapose, eq_univ_iff_forall, eq_univ_iff_forall.mp, exists_ne, faithfulSMul, finite_of_card_ne_zero, map_eq_one_iff, ne_zero_of_lt, powersetCard, powersetCard.faithfulSMul, replace, toPerm, toPermHom_apply
-/
theorem fixedPoints_ne_univ_of_faithfulSMul
    [Nontrivial G] [FaithfulSMul G α]
    {n : Nat} (hn : 0 < n) (hn' : n < Nat.card α) :
    fixedPoints G (powersetCard α n) != univ := by
  obtain ⟨g, h⟩ := exists_ne (1 : G)
  contrapose! h
  replace h : (toPerm g : Perm (powersetCard α n)) = 1 := by
    ext1 s
    exact eq_univ_iff_forall.mp h s g
  rwa [← toPermHom_apply, map_eq_one_iff] at h
  have := powersetCard.faithfulSMul (G := G) (α := α) hn ?_
  · exact MulAction.toPerm_injective
  · simpa [ENat.card_eq_coe_natCard, Nat.cast_lt, Nat.finite_of_card_ne_zero (ne_zero_of_lt hn')]

variable (α)

/-- The obvious map from a type to its 1-combinations, as an equivariant map. -/
@[to_additive /-- The obvious map from a type to its 1-combinations, as an equivariant map. -/]
/--
Definition of `mulActionHom_singleton` / `mulActionHom_singleton` 的定义

English:
definition mulActionHom_singleton
  signature: : α ->[G] powersetCard α 1 where
  body: ofSingleton
  map_smul' _ _ := rfl

@[to_additive]

中文:
定义 mulActionHom_singleton
  签名: : α ->[G] powersetCard α 1 where
  定义体: ofSingleton
  map_smul' _ _ := rfl

@[to_additive]

Depends on / 依赖: ofSingleton
-/
noncomputable def mulActionHom_singleton : α ->[G] powersetCard α 1 where
  toFun := ofSingleton
  map_smul' _ _ := rfl

@[to_additive]
/--
theorem `mulActionHom_singleton_bijective` / 定理 `mulActionHom_singleton_bijective`

English:
theorem mulActionHom_singleton_bijective
  proof: by
  refine ⟨fun a b h => Finset.singleton_injective congr($h.1), fun ⟨s, hs⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := card_eq_one.mp hs
  exact ⟨a, rfl⟩

中文:
定理 mulActionHom_singleton_bijective
  证明: by
  refine ⟨fun a b h => Finset.singleton_injective congr($h.1), fun ⟨s, hs⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := card_eq_one.mp hs
  exact ⟨a, rfl⟩

Depends on / 依赖: Finset, Finset.singleton_injective, card_eq_one, card_eq_one.mp, singleton_injective
-/
theorem mulActionHom_singleton_bijective :
    Function.Bijective (mulActionHom_singleton G α) := by
  refine ⟨fun a b h => Finset.singleton_injective congr($h.1), fun ⟨s, hs⟩ => ?_⟩
  obtain ⟨a, rfl⟩ := card_eq_one.mp hs
  exact ⟨a, rfl⟩

variable {α}

/--
theorem `isPreprimitive_perm` / 定理 `isPreprimitive_perm`

English:
theorem isPreprimitive_perm
  statement: {n : Nat} (h_one_le : 1 <= n) (hn : n < Nat.card α)
  proof: by
  -- The finiteness of `α` follows from the assumptions of the theorem.
  have : Finite α := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt hn)
  have : Fintype α := Fintype.ofFinite α
  -- The action is pretransitive.
  have : IsPretransitive (Perm α) (powersetCard α n) := powersetCard.isPretransitive
  -- The type on which the group acts is nontrivial.
  have : Nontrivial (powersetCard α n) := powersetCard.nontrivial' h_one_le hn
  obtain ⟨s⟩ := this.to_nonempty
  -- It remains to prove that stabilizer of some point is maximal.
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]
  -- The stabilizer of a combination is the stabilizer of the underlying set.
  rw [stabilizer_coe]
  -- We conclude by `Equiv.Perm.isCoatom_stabilizer`
  apply isCoatom_stabilizer
  -- `s` is nonempty because `n ≠ 0`.
  · rwa [powersetCard.coe_nonempty_iff]
  -- `sᶜ` is nonempty because `n < Nat.card α`.
  · rw [nonempty_compl, ne_eq, eq_univ_iff_ncard, ncard_eq]
    exact hn.ne
  -- `Nat.card α ≠ 2 * s.ncard` because `Nat.card α ≠ 2 * s`.
  · rwa [ncard_eq]

中文:
定理 isPreprimitive_perm
  结论: {n : 自然数} (h_one_le : 1 <= n) (hn : n < 自然数.card α)
  证明: by
  -- The finiteness of `α` follows from the assumptions of the theorem.
  have : Finite α := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt hn)
  have : Fintype α := Fintype.ofFinite α
  -- The action is pretransitive.
  have : IsPretransitive (Perm α) (powersetCard α n) := powersetCard.isPretransitive
  -- The type on which the group acts is nontrivial.
  have : Nontrivial (powersetCard α n) := powersetCard.nontrivial' h_one_le hn
  obtain ⟨s⟩ := this.to_nonempty
  -- It remains to prove that stabilizer of some point is maximal.
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]
  -- The stabilizer of a combination is the stabilizer of the underlying set.
  rw [stabilizer_coe]
  -- We conclude by `Equiv.Perm.isCoatom_stabilizer`
  apply isCoatom_stabilizer
  -- `s` is nonempty because `n ≠ 0`.
  · rwa [powersetCard.coe_nonempty_iff]
  -- `sᶜ` is nonempty because `n < Nat.card α`.
  · rw [nonempty_compl, ne_eq, eq_univ_iff_ncard, ncard_eq]
    exact hn.ne
  -- `Nat.card α ≠ 2 * s.ncard` because `Nat.card α ≠ 2 * s`.
  · rwa [ncard_eq]
-/
theorem isPreprimitive_perm {n : Nat} (h_one_le : 1 <= n) (hn : n < Nat.card α)
    (hα : Nat.card α != 2 * n) :
    IsPreprimitive (Perm α) (powersetCard α n) := by
  -- The finiteness of `α` follows from the assumptions of the theorem.
  have : Finite α := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt hn)
  have : Fintype α := Fintype.ofFinite α
  -- The action is pretransitive.
  have : IsPretransitive (Perm α) (powersetCard α n) := powersetCard.isPretransitive
  -- The type on which the group acts is nontrivial.
  have : Nontrivial (powersetCard α n) := powersetCard.nontrivial' h_one_le hn
  obtain ⟨s⟩ := this.to_nonempty
  -- It remains to prove that stabilizer of some point is maximal.
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]
  -- The stabilizer of a combination is the stabilizer of the underlying set.
  rw [stabilizer_coe]
  -- We conclude by `Equiv.Perm.isCoatom_stabilizer`
  apply isCoatom_stabilizer
  -- `s` is nonempty because `n ≠ 0`.
  · rwa [powersetCard.coe_nonempty_iff]
  -- `sᶜ` is nonempty because `n < Nat.card α`.
  · rw [nonempty_compl, ne_eq, eq_univ_iff_ncard, ncard_eq]
    exact hn.ne
  -- `Nat.card α ≠ 2 * s.ncard` because `Nat.card α ≠ 2 * s`.
  · rwa [ncard_eq]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isPretransitive_alternatingGroup` / 定理 `isPretransitive_alternatingGroup`

English:
theorem isPretransitive_alternatingGroup
  given: [Fintype α] (hα : 3 <= Nat.card α)
  proof: by
  wlog! hn : 2 * n <= Nat.card α
  · have : IsPretransitive (alternatingGroup α) (powersetCard α (Nat.card α - n)) := by
      apply this hα
      grind
    by_cases hn' : n <= Nat.card α
    · apply IsPretransitive.of_surjective_map
        (mulActionHom_compl_bijective (alternatingGroup α) α _).surjective this
      aesop
    · suffices Subsingleton (powersetCard α n) by infer_instance
      rw [not_le] at hn'
      rw [← Finite.card_le_one_iff_subsingleton]; rw [powersetCard.card]; rw [Nat.choose_eq_zero_iff.mpr hn']
      simp
  apply isPretransitive_of_isMultiplyPretransitive
  rcases eq_or_ne n 0 with rfl | hn0
  · infer_instance
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [is_one_pretransitive_iff]
    exact alternatingGroup.isPretransitive_of_three_le_card α hα
  have := alternatingGroup.isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) <;> grind

中文:
定理 isPretransitive_alternatingGroup
  条件: [有限类型 α] (hα : 3 <= 自然数.card α)
  证明: by
  wlog! hn : 2 * n <= Nat.card α
  · have : IsPretransitive (alternatingGroup α) (powersetCard α (Nat.card α - n)) := by
      apply this hα
      grind
    by_cases hn' : n <= Nat.card α
    · apply IsPretransitive.of_surjective_map
        (mulActionHom_compl_bijective (alternatingGroup α) α _).surjective this
      aesop
    · suffices Subsingleton (powersetCard α n) by infer_instance
      rw [not_le] at hn'
      rw [← Finite.card_le_one_iff_subsingleton]; rw [powersetCard.card]; rw [Nat.choose_eq_zero_iff.mpr hn']
      simp
  apply isPretransitive_of_isMultiplyPretransitive
  rcases eq_or_ne n 0 with rfl | hn0
  · infer_instance
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [is_one_pretransitive_iff]
    exact alternatingGroup.isPretransitive_of_three_le_card α hα
  have := alternatingGroup.isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) <;> grind

Depends on / 依赖: Finite, Finite.card_le_one_iff_subsingleton, IsPretransitive, IsPretransitive.of_surjective_map, Nat.card, Nat.choose_eq_zero_iff.mpr, Subsingleton, alternatingGroup, card_le_one_iff_subsingleton, choose_eq_zero_iff, infer_instance, isPretransitiv, mulActionHom_compl_bijective, not_le, of_surjective_map, powersetCard, powersetCard.card, surjective
-/
theorem isPretransitive_alternatingGroup [Fintype α] (hα : 3 <= Nat.card α) :
    IsPretransitive (alternatingGroup α) (powersetCard α n) := by
  wlog! hn : 2 * n <= Nat.card α
  · have : IsPretransitive (alternatingGroup α) (powersetCard α (Nat.card α - n)) := by
      apply this hα
      grind
    by_cases hn' : n <= Nat.card α
    · apply IsPretransitive.of_surjective_map
        (mulActionHom_compl_bijective (alternatingGroup α) α _).surjective this
      aesop
    · suffices Subsingleton (powersetCard α n) by infer_instance
      rw [not_le] at hn'
      rw [← Finite.card_le_one_iff_subsingleton]; rw [powersetCard.card]; rw [Nat.choose_eq_zero_iff.mpr hn']
      simp
  apply isPretransitive_of_isMultiplyPretransitive
  rcases eq_or_ne n 0 with rfl | hn0
  · infer_instance
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [is_one_pretransitive_iff]
    exact alternatingGroup.isPretransitive_of_three_le_card α hα
  have := alternatingGroup.isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) <;> grind

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isPreprimitive_alternatingGroup` / 定理 `isPreprimitive_alternatingGroup`

English:
theorem isPreprimitive_alternatingGroup
  statement: [Fintype α] {n : Nat}
  proof: by
  have : IsPretransitive (alternatingGroup α) (powersetCard α n) :=
    isPretransitive_alternatingGroup (le_trans h_three_le hn.le)
  have : Nontrivial (powersetCard α n) := nontrivial (by positivity) (by simpa using hn)
  obtain ⟨s⟩ := this.to_nonempty
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]; rw [stabilizer_coe]
  apply alternatingGroup.isCoatom_stabilizer
  · rw [powersetCard.coe_nonempty_iff]
    exact le_trans (by norm_num) h_three_le
  · simpa [nonempty_compl, ne_eq, eq_univ_iff_ncard, ncard_eq] using ne_of_lt hn
  · simpa only [ncard_eq]

中文:
定理 isPreprimitive_alternatingGroup
  结论: [有限类型 α] {n : 自然数}
  证明: by
  have : IsPretransitive (alternatingGroup α) (powersetCard α n) :=
    isPretransitive_alternatingGroup (le_trans h_three_le hn.le)
  have : Nontrivial (powersetCard α n) := nontrivial (by positivity) (by simpa using hn)
  obtain ⟨s⟩ := this.to_nonempty
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]; rw [stabilizer_coe]
  apply alternatingGroup.isCoatom_stabilizer
  · rw [powersetCard.coe_nonempty_iff]
    exact le_trans (by norm_num) h_three_le
  · simpa [nonempty_compl, ne_eq, eq_univ_iff_ncard, ncard_eq] using ne_of_lt hn
  · simpa only [ncard_eq]

Depends on / 依赖: IsPretransitive, Nontrivial, alternatingGroup, alternatingGroup.isCoatom_stabilizer, coe_nonempty_iff, eq_univ_iff_ncard, h_three_le, hn.le, isCoatom_stabilizer, isCoatom_stabilizer_iff_preprimitive, isPretransitive_alternatingGroup, le_trans, ncard_eq, ne_eq, nonempty_compl, nontrivial, powersetCard, powersetCard.coe_nonempty_iff, stabilizer_coe, this.to_nonempty
-/
theorem isPreprimitive_alternatingGroup [Fintype α] {n : Nat}
    (h_three_le : 3 <= n) (hn : n < Nat.card α) (hα : Nat.card α != 2 * n) :
    IsPreprimitive (alternatingGroup α) (powersetCard α n) := by
  have : IsPretransitive (alternatingGroup α) (powersetCard α n) :=
    isPretransitive_alternatingGroup (le_trans h_three_le hn.le)
  have : Nontrivial (powersetCard α n) := nontrivial (by positivity) (by simpa using hn)
  obtain ⟨s⟩ := this.to_nonempty
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]; rw [stabilizer_coe]
  apply alternatingGroup.isCoatom_stabilizer
  · rw [powersetCard.coe_nonempty_iff]
    exact le_trans (by norm_num) h_three_le
  · simpa [nonempty_compl, ne_eq, eq_univ_iff_ncard, ncard_eq] using ne_of_lt hn
  · simpa only [ncard_eq]

end Set.powersetCard
