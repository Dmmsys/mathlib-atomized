/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Fintype.Inv

/-! # Equivalence between fintypes

This file contains some basic results on equivalences where one or both
sides of the equivalence are `Fintype`s.

## Main definitions

- `Function.Embedding.toEquivRange`: computably turn an embedding of a
  fintype into an `Equiv` of the domain to its range
- `Equiv.Perm.viaFintypeEmbedding : Perm α → (α ↪ β) → Perm β` extends the domain of
  a permutation, fixing everything outside the range of the embedding

## Implementation details

- `Function.Embedding.toEquivRange` uses a computable inverse, but one that has poor
  computational performance, since it operates by exhaustive search over the input `Fintype`s.
-/

@[expose] public section

assert_not_exists Equiv.Perm.sign

section Fintype

variable {α β : Type*} [Fintype α] [DecidableEq β] (e : Equiv.Perm α) (f : α ↪ β)

/--
Definition of `Function.Embedding.toEquivRange` / `Function.Embedding.toEquivRange` 的定义

English:
definition Function.Embedding.toEquivRange
  signature: : α ≃ Set.range f where
  body: fun a => ⟨f a, Set.mem_range_self a⟩
  invFun := f.invOfMemRange
  left_inv := fun _ => by simp
  right_inv := fun _ => by simp

@[simp]

中文:
定义 函数.嵌入.toEquivRange
  签名: : α ≃ 集合.range f where
  定义体: fun a => ⟨f a, Set.mem_range_self a⟩
  invFun := f.invOfMemRange
  left_inv := fun _ => by simp
  right_inv := fun _ => by simp

@[simp]

Depends on / 依赖: Set.mem_range_self, mem_range_self
-/
def Function.Embedding.toEquivRange : α ≃ Set.range f where
  toFun := fun a => ⟨f a, Set.mem_range_self a⟩
  invFun := f.invOfMemRange
  left_inv := fun _ => by simp
  right_inv := fun _ => by simp

@[simp]
/--
theorem `Function.Embedding.toEquivRange_apply` / 定理 `Function.Embedding.toEquivRange_apply`

English:
theorem Function.Embedding.toEquivRange_apply
  given: (a : α)
  proof: rfl

@[simp]

中文:
定理 函数.嵌入.toEquivRange_apply
  条件: (a : α)
  证明: rfl

@[simp]
-/
theorem Function.Embedding.toEquivRange_apply (a : α) :
    f.toEquivRange a = ⟨f a, Set.mem_range_self a⟩ :=
  rfl

@[simp]
/--
theorem `Function.Embedding.toEquivRange_symm_apply_self` / 定理 `Function.Embedding.toEquivRange_symm_apply_self`

English:
theorem Function.Embedding.toEquivRange_symm_apply_self
  given: (a : α)
  proof: by simp [Equiv.symm_apply_eq]

中文:
定理 函数.嵌入.toEquivRange_symm_apply_self
  条件: (a : α)
  证明: by simp [Equiv.symm_apply_eq]

Depends on / 依赖: Equiv.symm_apply_eq, symm_apply_eq
-/
theorem Function.Embedding.toEquivRange_symm_apply_self (a : α) :
    f.toEquivRange.symm ⟨f a, Set.mem_range_self a⟩ = a := by simp [Equiv.symm_apply_eq]

/--
theorem `Function.Embedding.toEquivRange_eq_ofInjective` / 定理 `Function.Embedding.toEquivRange_eq_ofInjective`

English:
theorem Function.Embedding.toEquivRange_eq_ofInjective
  proof: by
  ext
  simp

中文:
定理 函数.嵌入.toEquivRange_eq_ofInjective
  证明: by
  ext
  simp
-/
theorem Function.Embedding.toEquivRange_eq_ofInjective :
    f.toEquivRange = Equiv.ofInjective f f.injective := by
  ext
  simp

/--
Definition of `Equiv.Perm.viaFintypeEmbedding` / `Equiv.Perm.viaFintypeEmbedding` 的定义

English:
definition Equiv.Perm.viaFintypeEmbedding
  signature: : Equiv.Perm β
  body: e.extendDomain f.toEquivRange

@[simp]

中文:
定义 等价.置换.viaFintypeEmbedding
  签名: : 等价.置换 β
  定义体: e.extendDomain f.toEquivRange

@[simp]

Depends on / 依赖: e.extendDomain, extendDomain, f.toEquivRange, toEquivRange
-/
def Equiv.Perm.viaFintypeEmbedding : Equiv.Perm β :=
  e.extendDomain f.toEquivRange

@[simp]
/--
theorem `Equiv.Perm.viaFintypeEmbedding_apply_image` / 定理 `Equiv.Perm.viaFintypeEmbedding_apply_image`

English:
theorem Equiv.Perm.viaFintypeEmbedding_apply_image
  given: (a : α)
  proof: by
  rw [Equiv.Perm.viaFintypeEmbedding]
  convert! Equiv.Perm.extendDomain_apply_image e (Function.Embedding.toEquivRange f) a

中文:
定理 等价.置换.viaFintypeEmbedding_apply_image
  条件: (a : α)
  证明: by
  rw [Equiv.Perm.viaFintypeEmbedding]
  convert! Equiv.Perm.extendDomain_apply_image e (Function.Embedding.toEquivRange f) a

Depends on / 依赖: Embedding, Equiv.Perm.extendDomain_apply_image, Equiv.Perm.viaFintypeEmbedding, Function, Function.Embedding.toEquivRange, convert, extendDomain_apply_image, toEquivRange, viaFintypeEmbedding
-/
theorem Equiv.Perm.viaFintypeEmbedding_apply_image (a : α) :
    e.viaFintypeEmbedding f (f a) = f (e a) := by
  rw [Equiv.Perm.viaFintypeEmbedding]
  convert! Equiv.Perm.extendDomain_apply_image e (Function.Embedding.toEquivRange f) a

/--
theorem `Equiv.Perm.viaFintypeEmbedding_apply_mem_range` / 定理 `Equiv.Perm.viaFintypeEmbedding_apply_mem_range`

English:
theorem Equiv.Perm.viaFintypeEmbedding_apply_mem_range
  given: {b : β} (h : b in Set.range f)
  proof: by
  simp only [viaFintypeEmbedding, Function.Embedding.invOfMemRange]
  rw [Equiv.Perm.extendDomain_apply_subtype _ _ h]
  congr

中文:
定理 等价.置换.viaFintypeEmbedding_apply_mem_range
  条件: {b : β} (h : b in 集合.range f)
  证明: by
  simp only [viaFintypeEmbedding, Function.Embedding.invOfMemRange]
  rw [Equiv.Perm.extendDomain_apply_subtype _ _ h]
  congr

Depends on / 依赖: Embedding, Equiv.Perm.extendDomain_apply_subtype, Function, Function.Embedding.invOfMemRange, extendDomain_apply_subtype, invOfMemRange, viaFintypeEmbedding
-/
theorem Equiv.Perm.viaFintypeEmbedding_apply_mem_range {b : β} (h : b in Set.range f) :
    e.viaFintypeEmbedding f b = f (e (f.invOfMemRange ⟨b, h⟩)) := by
  simp only [viaFintypeEmbedding, Function.Embedding.invOfMemRange]
  rw [Equiv.Perm.extendDomain_apply_subtype _ _ h]
  congr

/--
theorem `Equiv.Perm.viaFintypeEmbedding_apply_notMem_range` / 定理 `Equiv.Perm.viaFintypeEmbedding_apply_notMem_range`

English:
theorem Equiv.Perm.viaFintypeEmbedding_apply_notMem_range
  given: {b : β} (h : b ∉ Set.range f)
  proof: by
  rwa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_not_subtype]

中文:
定理 等价.置换.viaFintypeEmbedding_apply_notMem_range
  条件: {b : β} (h : b ∉ 集合.range f)
  证明: by
  rwa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_not_subtype]

Depends on / 依赖: Equiv.Perm.extendDomain_apply_not_subtype, Equiv.Perm.viaFintypeEmbedding, extendDomain_apply_not_subtype, viaFintypeEmbedding
-/
theorem Equiv.Perm.viaFintypeEmbedding_apply_notMem_range {b : β} (h : b ∉ Set.range f) :
    e.viaFintypeEmbedding f b = b := by
  rwa [Equiv.Perm.viaFintypeEmbedding, Equiv.Perm.extendDomain_apply_not_subtype]

end Fintype

namespace Equiv

variable {α β : Type*}

/--
Definition of `setDiffEquiv` / `setDiffEquiv` 的定义

English:
definition setDiffEquiv
  signature: {s t : Set α} [Fintype s] [Fintype t]
  body: by
  classical
  let fs : Finset α := Finset.univ.map (Function.Embedding.subtype (· in s))
  let ft : Finset α := Finset.univ.map (Function.Embedding.subtype (· in t))
  have hs (x : α) : x in fs ↔ x in s := by simp [fs]
  have ht (x : α) : x in ft ↔ x in t := by simp [ft]
  have hst (x : α) : x in fs \ ft ↔ x in s \ t := by simp [hs, ht]
  have hts (x : α) : x in ft \ fs ↔ x in t \ s := by simp [hs, ht]
  have hc : fs.card = ft.card := by
    rw [← Fintype.subtype_card fs hs]; rw [← Fintype.subtype_card ft ht]; convert! h
  replace hc := Finset.card_sdiff_comm hc
  rw [← Fintype.subtype_card (fs \ ft) hst]; rw [← Fintype.subtype_card (ft \ fs) hts] at hc
  exact ((Fintype.card_eq (_F := (_)) (_G := (_))).mp hc).some

中文:
定义 setDiffEquiv
  签名: {s t : 集合 α} [有限类型 s] [有限类型 t]
  定义体: by
  classical
  let fs : Finset α := Finset.univ.map (Function.Embedding.subtype (· in s))
  let ft : Finset α := Finset.univ.map (Function.Embedding.subtype (· in t))
  have hs (x : α) : x in fs ↔ x in s := by simp [fs]
  have ht (x : α) : x in ft ↔ x in t := by simp [ft]
  have hst (x : α) : x in fs \ ft ↔ x in s \ t := by simp [hs, ht]
  have hts (x : α) : x in ft \ fs ↔ x in t \ s := by simp [hs, ht]
  have hc : fs.card = ft.card := by
    rw [← Fintype.subtype_card fs hs]; rw [← Fintype.subtype_card ft ht]; convert! h
  replace hc := Finset.card_sdiff_comm hc
  rw [← Fintype.subtype_card (fs \ ft) hst]; rw [← Fintype.subtype_card (ft \ fs) hts] at hc
  exact ((Fintype.card_eq (_F := (_)) (_G := (_))).mp hc).some

Depends on / 依赖: Embedding, Finset, Finset.univ.map, Fintype, Fintype.subtype_card, Function, Function.Embedding.subtype, classical, fs.card, ft.card, subtype, subtype_card
-/
noncomputable def setDiffEquiv {s t : Set α} [Fintype s] [Fintype t]
    (h : Fintype.card s = Fintype.card t) : (s \ t : Set α) ≃ (t \ s : Set α) := by
  classical
  let fs : Finset α := Finset.univ.map (Function.Embedding.subtype (· in s))
  let ft : Finset α := Finset.univ.map (Function.Embedding.subtype (· in t))
  have hs (x : α) : x in fs ↔ x in s := by simp [fs]
  have ht (x : α) : x in ft ↔ x in t := by simp [ft]
  have hst (x : α) : x in fs \ ft ↔ x in s \ t := by simp [hs, ht]
  have hts (x : α) : x in ft \ fs ↔ x in t \ s := by simp [hs, ht]
  have hc : fs.card = ft.card := by
    rw [← Fintype.subtype_card fs hs]; rw [← Fintype.subtype_card ft ht]; convert! h
  replace hc := Finset.card_sdiff_comm hc
  rw [← Fintype.subtype_card (fs \ ft) hst]; rw [← Fintype.subtype_card (ft \ fs) hts] at hc
  exact ((Fintype.card_eq (_F := (_)) (_G := (_))).mp hc).some

open scoped Classical in
/--
Definition of `toCompl` / `toCompl` 的定义

English:
definition toCompl
  signature: {p q : α -> Prop} [Finite {x | p x}]
  body: let sp : Set α := {x | p x}
  let sq : Set α := {x | q x}
  letI : Fintype sp := Fintype.ofFinite sp
  letI : Fintype sq := Fintype.ofEquiv sp e
  have h := setDiffEquiv (Fintype.card_congr e)
  have hpc : spᶜ = (sq \ sp) union (sp union sq)ᶜ := by ext; simp; tauto
  have hqc : sqᶜ = (sp \ sq) union (sp union sq)ᶜ := by ext; simp; tauto
  let epc := (Equiv.setCongr hpc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
  let eqc := (Equiv.setCongr hqc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
epc.trans .trans (h.symm.sumCongr <| .refl _) eqc.symm

中文:
定义 toCompl
  签名: {p q : α -> 命题} [有限 {x | p x}]
  定义体: let sp : Set α := {x | p x}
  let sq : Set α := {x | q x}
  letI : Fintype sp := Fintype.ofFinite sp
  letI : Fintype sq := Fintype.ofEquiv sp e
  have h := setDiffEquiv (Fintype.card_congr e)
  have hpc : spᶜ = (sq \ sp) union (sp union sq)ᶜ := by ext; simp; tauto
  have hqc : sqᶜ = (sp \ sq) union (sp union sq)ᶜ := by ext; simp; tauto
  let epc := (Equiv.setCongr hpc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
  let eqc := (Equiv.setCongr hqc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
epc.trans .trans (h.symm.sumCongr <| .refl _) eqc.symm

Depends on / 依赖: Equiv.Set.union, Equiv.setCongr, Fintype, Fintype.card_congr, Fintype.ofEquiv, Fintype.ofFinite, Set.disjoint_le, Set.disjoint_left, card_congr, disjoint_le, disjoint_left, ofEquiv, ofFinite, setCongr, setDiffEquiv
-/
noncomputable def toCompl {p q : α -> Prop} [Finite {x | p x}]
    (e : { x | p x } ≃ { x | q x }) : { x | ¬p x } ≃ { x | ¬q x } :=
  let sp : Set α := {x | p x}
  let sq : Set α := {x | q x}
  letI : Fintype sp := Fintype.ofFinite sp
  letI : Fintype sq := Fintype.ofEquiv sp e
  have h := setDiffEquiv (Fintype.card_congr e)
  have hpc : spᶜ = (sq \ sp) union (sp union sq)ᶜ := by ext; simp; tauto
  have hqc : sqᶜ = (sp \ sq) union (sp union sq)ᶜ := by ext; simp; tauto
  let epc := (Equiv.setCongr hpc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
  let eqc := (Equiv.setCongr hqc).trans (Equiv.Set.union (by simp [Set.disjoint_left]; tauto))
epc.trans .trans (h.symm.sumCongr <| .refl _) eqc.symm

variable {p q : α -> Prop} [DecidablePred p] [DecidablePred q] [Finite {x | p x}]

/--
Definition of `extendSubtype` / `extendSubtype` 的定义

English:
abbreviation extendSubtype
  signature: (e : { x // p x } ≃ { x // q x })
  body: subtypeCongr e e.toCompl

中文:
缩写 extendSubtype
  签名: (e : { x // p x } ≃ { x // q x })
  定义体: subtypeCongr e e.toCompl

Depends on / 依赖: e.toCompl, subtypeCongr, toCompl
-/
noncomputable abbrev extendSubtype (e : { x // p x } ≃ { x // q x }) : Perm α :=
  subtypeCongr e e.toCompl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `extendSubtype_apply_of_mem` / 定理 `extendSubtype_apply_of_mem`

English:
theorem extendSubtype_apply_of_mem
  given: (e : { x // p x } ≃ { x // q x }) (x) (hx : p x)
  proof: by
  simp [extendSubtype, subtypeCongr, sumCompl_symm_apply_of_pos hx]

中文:
定理 extendSubtype_apply_of_mem
  条件: (e : { x // p x } ≃ { x // q x }) (x) (hx : p x)
  证明: by
  simp [extendSubtype, subtypeCongr, sumCompl_symm_apply_of_pos hx]

Depends on / 依赖: extendSubtype, subtypeCongr, sumCompl_symm_apply_of_pos
-/
theorem extendSubtype_apply_of_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    e.extendSubtype x = e ⟨x, hx⟩ := by
  simp [extendSubtype, subtypeCongr, sumCompl_symm_apply_of_pos hx]

/--
theorem `extendSubtype_mem` / 定理 `extendSubtype_mem`

English:
theorem extendSubtype_mem
  given: (e : { x // p x } ≃ { x // q x }) (x) (hx : p x)
  proof: (e.extendSubtype_apply_of_mem _ hx).symm ▸ (e ⟨x, hx⟩).2

中文:
定理 extendSubtype_mem
  条件: (e : { x // p x } ≃ { x // q x }) (x) (hx : p x)
  证明: (e.extendSubtype_apply_of_mem _ hx).symm ▸ (e ⟨x, hx⟩).2

Depends on / 依赖: e.extendSubtype_apply_of_mem, extendSubtype_apply_of_mem
-/
theorem extendSubtype_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : p x) :
    q (e.extendSubtype x) :=
  (e.extendSubtype_apply_of_mem _ hx).symm ▸ (e ⟨x, hx⟩).2

/--
theorem `extendSubtype_apply_of_not_mem` / 定理 `extendSubtype_apply_of_not_mem`

English:
theorem extendSubtype_apply_of_not_mem
  given: (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x)
  proof: by
  simp only [extendSubtype, subtypeCongr, Equiv.trans_apply,
    sumCompl_symm_apply_of_neg hx]
  rfl

中文:
定理 extendSubtype_apply_of_not_mem
  条件: (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x)
  证明: by
  simp only [extendSubtype, subtypeCongr, Equiv.trans_apply,
    sumCompl_symm_apply_of_neg hx]
  rfl

Depends on / 依赖: Equiv.trans_apply, extendSubtype, subtypeCongr, sumCompl_symm_apply_of_neg, trans_apply
-/
theorem extendSubtype_apply_of_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    e.extendSubtype x = e.toCompl ⟨x, hx⟩ := by
  simp only [extendSubtype, subtypeCongr, Equiv.trans_apply,
    sumCompl_symm_apply_of_neg hx]
  rfl

/--
theorem `extendSubtype_not_mem` / 定理 `extendSubtype_not_mem`

English:
theorem extendSubtype_not_mem
  given: (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x)
  proof: e.extendSubtype_apply_of_not_mem _ hx ▸ (e.toCompl ⟨x, hx⟩).2

中文:
定理 extendSubtype_not_mem
  条件: (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x)
  证明: e.extendSubtype_apply_of_not_mem _ hx ▸ (e.toCompl ⟨x, hx⟩).2

Depends on / 依赖: e.extendSubtype_apply_of_not_mem, e.toCompl, extendSubtype_apply_of_not_mem, toCompl
-/
theorem extendSubtype_not_mem (e : { x // p x } ≃ { x // q x }) (x) (hx : ¬p x) :
    ¬q (e.extendSubtype x) :=
  e.extendSubtype_apply_of_not_mem _ hx ▸ (e.toCompl ⟨x, hx⟩).2

/--
theorem `Perm.exists_extending_pair` / 定理 `Perm.exists_extending_pair`

English:
theorem Perm.exists_extending_pair
  statement: [Finite α]
  proof: by
  classical
  have : Finite {x | x in Set.range f} := .of_surjective _ (Set.codRestrict_range_surjective f)
  refine ⟨((Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)).extendSubtype, ?_⟩
  simp [Equiv.extendSubtype_apply_of_mem]

中文:
定理 置换.存在_extending_pair
  结论: [有限 α]
  证明: by
  classical
  have : Finite {x | x in Set.range f} := .of_surjective _ (Set.codRestrict_range_surjective f)
  refine ⟨((Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)).extendSubtype, ?_⟩
  simp [Equiv.extendSubtype_apply_of_mem]

Depends on / 依赖: Equiv.extendSubtype_apply_of_mem, Equiv.ofInjective, Finite, Set.codRestrict_range_surjective, Set.range, classical, codRestrict_range_surjective, extendSubtype, extendSubtype_apply_of_mem, ofInjective, of_surjective, symm.trans
-/
theorem Perm.exists_extending_pair [Finite α]
    (f g : α -> β) (hf : Function.Injective f) (hg : Function.Injective g) :
    exists σ : Perm β, forall a, σ (f a) = g a := by
  classical
  have : Finite {x | x in Set.range f} := .of_surjective _ (Set.codRestrict_range_surjective f)
  refine ⟨((Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)).extendSubtype, ?_⟩
  simp [Equiv.extendSubtype_apply_of_mem]

/--
theorem `Perm.exists_map_finset_eq` / 定理 `Perm.exists_map_finset_eq`

English:
theorem Perm.exists_map_finset_eq
  proof: by
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair
    (fun x : s => (x : β)) (fun x : s => ((s.equivOfCardEq h) x : β))
    Subtype.val_injective (Subtype.val_injective.comp (s.equivOfCardEq h).injective)
  refine ⟨σ, Finset.eq_of_subset_of_card_le (fun b hb => ?_) (by simp [h])⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
  exact (hσ ⟨a, ha⟩) ▸ ((s.equivOfCardEq h) ⟨a, ha⟩).2

中文:
定理 置换.存在_map_finset_eq
  证明: by
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair
    (fun x : s => (x : β)) (fun x : s => ((s.equivOfCardEq h) x : β))
    Subtype.val_injective (Subtype.val_injective.comp (s.equivOfCardEq h).injective)
  refine ⟨σ, Finset.eq_of_subset_of_card_le (fun b hb => ?_) (by simp [h])⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
  exact (hσ ⟨a, ha⟩) ▸ ((s.equivOfCardEq h) ⟨a, ha⟩).2

Depends on / 依赖: Finset, Finset.eq_of_subset_of_card_le, Finset.mem_map.mp, Perm.exists_extending_pair, Subtype, Subtype.val_injective, Subtype.val_injective.comp, eq_of_subset_of_card_le, equivOfCardEq, exists_extending_pair, injective, mem_map, s.equivOfCardEq, val_injective
-/
theorem Perm.exists_map_finset_eq
    (s t : Finset β) (h : s.card = t.card) :
    exists σ : Perm β, s.map σ.toEmbedding = t := by
  obtain ⟨σ, hσ⟩ := Perm.exists_extending_pair
    (fun x : s => (x : β)) (fun x : s => ((s.equivOfCardEq h) x : β))
    Subtype.val_injective (Subtype.val_injective.comp (s.equivOfCardEq h).injective)
  refine ⟨σ, Finset.eq_of_subset_of_card_le (fun b hb => ?_) (by simp [h])⟩
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hb
  exact (hσ ⟨a, ha⟩) ▸ ((s.equivOfCardEq h) ⟨a, ha⟩).2

end Equiv
