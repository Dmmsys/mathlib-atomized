/-
Copyright (c) 2021 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
module

public import Mathlib.Logic.Embedding.Set

/-!
# Equivalences on embeddings

This file shows some advanced equivalences on embeddings, useful for constructing larger
embeddings from smaller ones.
-/

@[expose] public section


open Function.Embedding

namespace Equiv

/--
Definition of `sumEmbeddingEquivProdEmbeddingDisjoint` / `sumEmbeddingEquivProdEmbeddingDisjoint` 的定义

English:
definition sumEmbeddingEquivProdEmbeddingDisjoint
  signature: {α β γ : Type*}
  body: ⟨(inl.trans f, inr.trans f), by
      rw [Set.disjoint_left]
      rintro _ ⟨a, h⟩ ⟨b, rfl⟩
      simp only at h
      have : Sum.inl a = Sum.inr b := f.injective h
      simp only [reduceCtorEq] at this⟩
  invFun := fun ⟨⟨f, g⟩, disj⟩ =>
    ⟨fun x =>
      match x with
      | Sum.inl a => f a
   

中文:
定义 sumEmbeddingEquivProdEmbeddingDisjoint
  签名: {α β γ : 类型}
  定义体: ⟨(inl.trans f, inr.trans f), by
      rw [Set.disjoint_left]
      rintro _ ⟨a, h⟩ ⟨b, rfl⟩
      simp only at h
      have : Sum.inl a = Sum.inr b := f.injective h
      simp only [reduceCtorEq] at this⟩
  invFun := fun ⟨⟨f, g⟩, disj⟩ =>
    ⟨fun x =>
      match x with
      | Sum.inl a => f a
   

Depends on / 依赖: Set.disjoint_left, Sum.inl, Sum.inr, disj.le_bot, disjoint_left, f.injective, f_eq, g.injective, injective, inl.trans, inr.trans, invFun, le_bot, left_inv, reduceCtorEq
-/
def sumEmbeddingEquivProdEmbeddingDisjoint {α β γ : Type*} :
    (α oplus β ↪ γ) ≃ { f : (α ↪ γ) × (β ↪ γ) // Disjoint (Set.range f.1) (Set.range f.2) } where
  toFun f :=
    ⟨(inl.trans f, inr.trans f), by
      rw [Set.disjoint_left]
      rintro _ ⟨a, h⟩ ⟨b, rfl⟩
      simp only at h
      have : Sum.inl a = Sum.inr b := f.injective h
      simp only [reduceCtorEq] at this⟩
  invFun := fun ⟨⟨f, g⟩, disj⟩ =>
    ⟨fun x =>
      match x with
      | Sum.inl a => f a
      | Sum.inr b => g b, by
      rintro (a₁ | b₁) (a₂ | b₂) f_eq <;>
        simp only at f_eq
      · rw [f.injective f_eq]
      · exfalso
        exact disj.le_bot ⟨⟨a₁, f_eq⟩, ⟨b₂, by simp⟩⟩
      · exfalso
        exact disj.le_bot ⟨⟨a₂, rfl⟩, ⟨b₁, f_eq⟩⟩
      · rw [g.injective f_eq]⟩
  left_inv f := by
    dsimp only
    ext x
    cases x <;> simp!
  right_inv := fun ⟨⟨f, g⟩, _⟩ => by
    simp only
    rfl

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (α : Type*) {β : Type*} (bs : Set β)
  body: (f : α ↪ β).codRestrict bs f.prop
  invFun f := ⟨f.trans (Function.Embedding.subtype _), fun a => (f a).prop⟩

中文:
定义 codRestrict
  签名: (α : 类型) {β : 类型} (bs : Set β)
  定义体: (f : α ↪ β).codRestrict bs f.prop
  invFun f := ⟨f.trans (Function.Embedding.subtype _), fun a => (f a).prop⟩

Depends on / 依赖: codRestrict, f.prop
-/
def codRestrict (α : Type*) {β : Type*} (bs : Set β) :
    { f : α ↪ β // forall a, f a in bs } ≃
      (α ↪ bs) where
  toFun f := (f : α ↪ β).codRestrict bs f.prop
  invFun f := ⟨f.trans (Function.Embedding.subtype _), fun a => (f a).prop⟩

/--
Definition of `prodEmbeddingDisjointEquivSigmaEmbeddingRestricted` / `prodEmbeddingDisjointEquivSigmaEmbeddingRestricted` 的定义

English:
definition prodEmbeddingDisjointEquivSigmaEmbeddingRestricted
  signature: {α β γ : Type*}
  body: (subtypeProdEquivSigmaSubtype fun (a : α ↪ γ) (b : β ↪ _) =>
        Disjoint (Set.range a) (Set.range b)).trans <|
    Equiv.sigmaCongrRight fun a =>
      (subtypeEquivProp <| by
            ext f
            rw [← Set.range_subset_iff]; rw [Set.subset_compl_iff_disjoint_right]; rw [disjoint_comm]

中文:
定义 prodEmbeddingDisjointEquivSigmaEmbeddingRestricted
  签名: {α β γ : 类型}
  定义体: (subtypeProdEquivSigmaSubtype fun (a : α ↪ γ) (b : β ↪ _) =>
        Disjoint (Set.range a) (Set.range b)).trans <|
    Equiv.sigmaCongrRight fun a =>
      (subtypeEquivProp <| by
            ext f
            rw [← Set.range_subset_iff]; rw [Set.subset_compl_iff_disjoint_right]; rw [disjoint_comm]

Depends on / 依赖: Disjoint, Equiv.sigmaCongrRight, Set.range, Set.range_subset_iff, Set.subset_compl_iff_disjoint_right, codRestrict, disjoint_comm, range_subset_iff, sigmaCongrRight, subset_compl_iff_disjoint_right, subtypeEquivProp, subtypeProdEquivSigmaSubtype
-/
def prodEmbeddingDisjointEquivSigmaEmbeddingRestricted {α β γ : Type*} :
    { f : (α ↪ γ) × (β ↪ γ) // Disjoint (Set.range f.1) (Set.range f.2) } ≃
      Σ f : α ↪ γ, β ↪ ↥(Set.range f)ᶜ :=
  (subtypeProdEquivSigmaSubtype fun (a : α ↪ γ) (b : β ↪ _) =>
        Disjoint (Set.range a) (Set.range b)).trans <|
    Equiv.sigmaCongrRight fun a =>
      (subtypeEquivProp <| by
            ext f
            rw [← Set.range_subset_iff]; rw [Set.subset_compl_iff_disjoint_right]; rw [disjoint_comm]).trans
        (codRestrict _ _)

/--
Definition of `sumEmbeddingEquivSigmaEmbeddingRestricted` / `sumEmbeddingEquivSigmaEmbeddingRestricted` 的定义

English:
definition sumEmbeddingEquivSigmaEmbeddingRestricted
  signature: {α β γ : Type*}
  body: Equiv.trans sumEmbeddingEquivProdEmbeddingDisjoint
    prodEmbeddingDisjointEquivSigmaEmbeddingRestricted

中文:
定义 sumEmbeddingEquivSigmaEmbeddingRestricted
  签名: {α β γ : 类型}
  定义体: Equiv.trans sumEmbeddingEquivProdEmbeddingDisjoint
    prodEmbeddingDisjointEquivSigmaEmbeddingRestricted

Depends on / 依赖: Equiv.trans, prodEmbeddingDisjointEquivSigmaEmbeddingRestricted, sumEmbeddingEquivProdEmbeddingDisjoint
-/
def sumEmbeddingEquivSigmaEmbeddingRestricted {α β γ : Type*} :
    (α oplus β ↪ γ) ≃ Σ f : α ↪ γ, β ↪ ↥(Set.range f)ᶜ :=
  Equiv.trans sumEmbeddingEquivProdEmbeddingDisjoint
    prodEmbeddingDisjointEquivSigmaEmbeddingRestricted

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `uniqueEmbeddingEquivResult` / `uniqueEmbeddingEquivResult` 的定义

English:
definition uniqueEmbeddingEquivResult
  signature: {α β : Type*} [Unique α]
  body: f default
  invFun x := ⟨fun _ => x, fun _ _ _ => Subsingleton.elim _ _⟩
  left_inv _ := by
    ext x
    simp_rw [Function.Embedding.coeFn_mk]
    congr 1
    exact Subsingleton.elim _ x
  right_inv _ := by simp

中文:
定义 uniqueEmbeddingEquivResult
  签名: {α β : 类型} [Unique α]
  定义体: f default
  invFun x := ⟨fun _ => x, fun _ _ _ => Subsingleton.elim _ _⟩
  left_inv _ := by
    ext x
    simp_rw [Function.Embedding.coeFn_mk]
    congr 1
    exact Subsingleton.elim _ x
  right_inv _ := by simp
-/
def uniqueEmbeddingEquivResult {α β : Type*} [Unique α] :
    (α ↪ β) ≃ β where
  toFun f := f default
  invFun x := ⟨fun _ => x, fun _ _ _ => Subsingleton.elim _ _⟩
  left_inv _ := by
    ext x
    simp_rw [Function.Embedding.coeFn_mk]
    congr 1
    exact Subsingleton.elim _ x
  right_inv _ := by simp

end Equiv
