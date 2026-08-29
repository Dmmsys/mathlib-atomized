/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Computability.Halting

/-!
# Strong reducibility and degrees.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notation

This file uses the local notation `⊕'` for `Sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/

@[expose] public section


universe u v w

open Function

/--
Definition of `ManyOneReducible` / `ManyOneReducible` 的定义

English:
definition ManyOneReducible
  signature: {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -> Prop)
  body: exists f, Computable f ∧ forall a, p a ↔ q (f a)

@[inherit_doc ManyOneReducible]
infixl:1000 " <=₀ " => ManyOneReducible

中文:
定义 ManyOneReducible
  签名: {α β} [Primcodable α] [Primcodable β] (p : α -> 命题) (q : β -> 命题)
  定义体: exists f, Computable f ∧ forall a, p a ↔ q (f a)

@[inherit_doc ManyOneReducible]
infixl:1000 " <=₀ " => ManyOneReducible

Depends on / 依赖: Computable
-/
def ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -> Prop) :=
  exists f, Computable f ∧ forall a, p a ↔ q (f a)

@[inherit_doc ManyOneReducible]
infixl:1000 " <=₀ " => ManyOneReducible

/--
theorem `ManyOneReducible.mk` / 定理 `ManyOneReducible.mk`

English:
theorem ManyOneReducible.mk
  statement: {α β} [Primcodable α] [Primcodable β] {f : α -> β} (q : β -> Prop)
  proof: ⟨f, h, fun _ => Iff.rfl⟩

@[refl]

中文:
定理 ManyOneReducible.mk
  结论: {α β} [Primcodable α] [Primcodable β] {f : α -> β} (q : β -> 命题)
  证明: ⟨f, h, fun _ => Iff.rfl⟩

@[refl]

Depends on / 依赖: Iff.rfl
-/
theorem ManyOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α -> β} (q : β -> Prop)
    (h : Computable f) : (fun a => q (f a)) <=₀ q :=
  ⟨f, h, fun _ => Iff.rfl⟩

@[refl]
/--
theorem `manyOneReducible_refl` / 定理 `manyOneReducible_refl`

English:
theorem manyOneReducible_refl
  given: {α} [Primcodable α] (p : α -> Prop)
  statement: p <=₀ p
  proof: ⟨id, Computable.id, by simp⟩

@[trans]

中文:
定理 manyOneReducible_refl
  条件: {α} [Primcodable α] (p : α -> 命题)
  结论: p <=₀ p
  证明: ⟨id, Computable.id, by simp⟩

@[trans]

Depends on / 依赖: Computable, Computable.id
-/
theorem manyOneReducible_refl {α} [Primcodable α] (p : α -> Prop) : p <=₀ p :=
  ⟨id, Computable.id, by simp⟩

@[trans]
/--
theorem `ManyOneReducible.trans` / 定理 `ManyOneReducible.trans`

English:
theorem ManyOneReducible.trans
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]

中文:
定理 ManyOneReducible.trans
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
-/
theorem ManyOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} : p <=₀ q -> q <=₀ r -> p <=₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁,
      fun a => ⟨fun h => by rw [comp_apply, ← h₂, ← h₁]; assumption, fun h => by rwa [h₁, h₂]⟩⟩

/--
Instance `stdRefl_manyOneReducible` / 实例 `stdRefl_manyOneReducible`

English:
instance stdRefl_manyOneReducible
  signature: {α} [Primcodable α]
  body: manyOneReducible_refl

@[deprecated (since := "2026-03-27")] alias reflexive_manyOneReducible := stdRefl_manyOneReducible

中文:
实例 stdRefl_manyOneReducible
  签名: {α} [Primcodable α]
  定义体: manyOneReducible_refl

@[deprecated (since := "2026-03-27")] alias reflexive_manyOneReducible := stdRefl_manyOneReducible

Depends on / 依赖: manyOneReducible_refl
-/
instance stdRefl_manyOneReducible {α} [Primcodable α] : Std.Refl (@ManyOneReducible α α _ _) where
  refl := manyOneReducible_refl

@[deprecated (since := "2026-03-27")] alias reflexive_manyOneReducible := stdRefl_manyOneReducible

/--
Instance `isTrans_manyOneReducible` / 实例 `isTrans_manyOneReducible`

English:
instance isTrans_manyOneReducible
  signature: {α} [Primcodable α]
  body: ManyOneReducible.trans

@[deprecated (since := "2026-02-21")] alias transitive_manyOneReducible := isTrans_manyOneReducible

中文:
实例 isTrans_manyOneReducible
  签名: {α} [Primcodable α]
  定义体: ManyOneReducible.trans

@[deprecated (since := "2026-02-21")] alias transitive_manyOneReducible := isTrans_manyOneReducible

Depends on / 依赖: ManyOneReducible, ManyOneReducible.trans
-/
instance isTrans_manyOneReducible {α} [Primcodable α] : IsTrans (α -> Prop) ManyOneReducible where
  trans _ _ _ := ManyOneReducible.trans

@[deprecated (since := "2026-02-21")] alias transitive_manyOneReducible := isTrans_manyOneReducible

/--
Definition of `OneOneReducible` / `OneOneReducible` 的定义

English:
definition OneOneReducible
  signature: {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -> Prop)
  body: exists f, Computable f ∧ Injective f ∧ forall a, p a ↔ q (f a)

@[inherit_doc OneOneReducible]
infixl:1000 " <=₁ " => OneOneReducible

中文:
定义 OneOneReducible
  签名: {α β} [Primcodable α] [Primcodable β] (p : α -> 命题) (q : β -> 命题)
  定义体: exists f, Computable f ∧ Injective f ∧ forall a, p a ↔ q (f a)

@[inherit_doc OneOneReducible]
infixl:1000 " <=₁ " => OneOneReducible

Depends on / 依赖: Computable, Injective
-/
def OneOneReducible {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -> Prop) :=
  exists f, Computable f ∧ Injective f ∧ forall a, p a ↔ q (f a)

@[inherit_doc OneOneReducible]
infixl:1000 " <=₁ " => OneOneReducible

/--
theorem `OneOneReducible.mk` / 定理 `OneOneReducible.mk`

English:
theorem OneOneReducible.mk
  statement: {α β} [Primcodable α] [Primcodable β] {f : α -> β} (q : β -> Prop)
  proof: ⟨f, h, i, fun _ => Iff.rfl⟩

@[refl]

中文:
定理 OneOneReducible.mk
  结论: {α β} [Primcodable α] [Primcodable β] {f : α -> β} (q : β -> 命题)
  证明: ⟨f, h, i, fun _ => Iff.rfl⟩

@[refl]

Depends on / 依赖: Iff.rfl
-/
theorem OneOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α -> β} (q : β -> Prop)
    (h : Computable f) (i : Injective f) : (fun a => q (f a)) <=₁ q :=
  ⟨f, h, i, fun _ => Iff.rfl⟩

@[refl]
/--
theorem `oneOneReducible_refl` / 定理 `oneOneReducible_refl`

English:
theorem oneOneReducible_refl
  given: {α} [Primcodable α] (p : α -> Prop)
  statement: p <=₁ p
  proof: ⟨id, Computable.id, injective_id, by simp⟩

@[trans]

中文:
定理 oneOneReducible_refl
  条件: {α} [Primcodable α] (p : α -> 命题)
  结论: p <=₁ p
  证明: ⟨id, Computable.id, injective_id, by simp⟩

@[trans]

Depends on / 依赖: Computable, Computable.id, injective_id
-/
theorem oneOneReducible_refl {α} [Primcodable α] (p : α -> Prop) : p <=₁ p :=
  ⟨id, Computable.id, injective_id, by simp⟩

@[trans]
/--
theorem `OneOneReducible.trans` / 定理 `OneOneReducible.trans`

English:
theorem OneOneReducible.trans
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> Prop}

中文:
定理 OneOneReducible.trans
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> 命题}
-/
theorem OneOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> Prop}
    {q : β -> Prop} {r : γ -> Prop} : p <=₁ q -> q <=₁ r -> p <=₁ r
  | ⟨f, c₁, i₁, h₁⟩, ⟨g, c₂, i₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, i₂.comp i₁, fun a =>
      ⟨fun h => by rw [comp_apply, ← h₂, ← h₁]; assumption, fun h => by rwa [h₁, h₂]⟩⟩

/--
theorem `OneOneReducible.to_many_one` / 定理 `OneOneReducible.to_many_one`

English:
theorem OneOneReducible.to_many_one
  statement: {α β} [Primcodable α] [Primcodable β] {p : α -> Prop}

中文:
定理 OneOneReducible.to_many_one
  结论: {α β} [Primcodable α] [Primcodable β] {p : α -> 命题}
-/
theorem OneOneReducible.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α -> Prop}
    {q : β -> Prop} : p <=₁ q -> p <=₀ q
  | ⟨f, c, _, h⟩ => ⟨f, c, h⟩

/--
theorem `OneOneReducible.of_equiv` / 定理 `OneOneReducible.of_equiv`

English:
theorem OneOneReducible.of_equiv
  statement: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β -> Prop)
  proof: OneOneReducible.mk _ h e.injective

中文:
定理 OneOneReducible.of_equiv
  结论: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β -> 命题)
  证明: OneOneReducible.mk _ h e.injective

Depends on / 依赖: OneOneReducible, OneOneReducible.mk, e.injective, injective
-/
theorem OneOneReducible.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β -> Prop)
    (h : Computable e) : (q ∘ e) <=₁ q :=
  OneOneReducible.mk _ h e.injective

/--
theorem `OneOneReducible.of_equiv_symm` / 定理 `OneOneReducible.of_equiv_symm`

English:
theorem OneOneReducible.of_equiv_symm
  statement: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
  proof: by
  convert! OneOneReducible.of_equiv _ h; funext; simp

中文:
定理 OneOneReducible.of_equiv_symm
  结论: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
  证明: by
  convert! OneOneReducible.of_equiv _ h; funext; simp

Depends on / 依赖: OneOneReducible, OneOneReducible.of_equiv, convert, of_equiv
-/
theorem OneOneReducible.of_equiv_symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
    (q : β -> Prop) (h : Computable e.symm) : q <=₁ (q ∘ e) := by
  convert! OneOneReducible.of_equiv _ h; funext; simp

/--
Instance `stdRefl_oneOneReducible` / 实例 `stdRefl_oneOneReducible`

English:
instance stdRefl_oneOneReducible
  signature: {α} [Primcodable α]
  body: oneOneReducible_refl

@[deprecated (since := "2026-03-27")] alias reflexive_oneOneReducible := stdRefl_oneOneReducible

中文:
实例 stdRefl_oneOneReducible
  签名: {α} [Primcodable α]
  定义体: oneOneReducible_refl

@[deprecated (since := "2026-03-27")] alias reflexive_oneOneReducible := stdRefl_oneOneReducible

Depends on / 依赖: oneOneReducible_refl
-/
instance stdRefl_oneOneReducible {α} [Primcodable α] : Std.Refl (@OneOneReducible α α _ _) where
  refl := oneOneReducible_refl

@[deprecated (since := "2026-03-27")] alias reflexive_oneOneReducible := stdRefl_oneOneReducible

/--
Instance `isTrans_oneOneReducible` / 实例 `isTrans_oneOneReducible`

English:
instance isTrans_oneOneReducible
  signature: {α} [Primcodable α]
  body: OneOneReducible.trans

@[deprecated (since := "2026-02-21")] alias transitive_oneOneReducible := isTrans_oneOneReducible

中文:
实例 isTrans_oneOneReducible
  签名: {α} [Primcodable α]
  定义体: OneOneReducible.trans

@[deprecated (since := "2026-02-21")] alias transitive_oneOneReducible := isTrans_oneOneReducible

Depends on / 依赖: OneOneReducible, OneOneReducible.trans
-/
instance isTrans_oneOneReducible {α} [Primcodable α] : IsTrans (α -> Prop) OneOneReducible where
  trans _ _ _ := OneOneReducible.trans

@[deprecated (since := "2026-02-21")] alias transitive_oneOneReducible := isTrans_oneOneReducible

namespace ComputablePred

variable {α : Type*} {β : Type*} [Primcodable α] [Primcodable β]

open Computable

/--
theorem `computable_of_manyOneReducible` / 定理 `computable_of_manyOneReducible`

English:
theorem computable_of_manyOneReducible
  statement: {p : α -> Prop} {q : β -> Prop} (h₁ : p <=₀ q)
  proof: by
  rcases h₁ with ⟨f, c, hf⟩
  rw [show p = fun a => q (f a) from Set.ext hf]
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩
  exact ⟨by infer_instance, by simpa using hg.comp c⟩

中文:
定理 computable_of_manyOneReducible
  结论: {p : α -> 命题} {q : β -> 命题} (h₁ : p <=₀ q)
  证明: by
  rcases h₁ with ⟨f, c, hf⟩
  rw [show p = fun a => q (f a) from Set.ext hf]
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩
  exact ⟨by infer_instance, by simpa using hg.comp c⟩

Depends on / 依赖: Set.ext, computable_iff, hg.comp, infer_instance
-/
theorem computable_of_manyOneReducible {p : α -> Prop} {q : β -> Prop} (h₁ : p <=₀ q)
    (h₂ : ComputablePred q) : ComputablePred p := by
  rcases h₁ with ⟨f, c, hf⟩
  rw [show p = fun a => q (f a) from Set.ext hf]
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩
  exact ⟨by infer_instance, by simpa using hg.comp c⟩

/--
theorem `computable_of_oneOneReducible` / 定理 `computable_of_oneOneReducible`

English:
theorem computable_of_oneOneReducible
  given: {p : α -> Prop} {q : β -> Prop} (h : p <=₁ q)
  proof: computable_of_manyOneReducible h.to_many_one

中文:
定理 computable_of_oneOneReducible
  条件: {p : α -> 命题} {q : β -> 命题} (h : p <=₁ q)
  证明: computable_of_manyOneReducible h.to_many_one

Depends on / 依赖: computable_of_manyOneReducible, h.to_many_one, to_many_one
-/
theorem computable_of_oneOneReducible {p : α -> Prop} {q : β -> Prop} (h : p <=₁ q) :
    ComputablePred q -> ComputablePred p :=
  computable_of_manyOneReducible h.to_many_one

end ComputablePred

/--
Definition of `ManyOneEquiv` / `ManyOneEquiv` 的定义

English:
definition ManyOneEquiv
  signature: {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -> Prop)
  body: p <=₀ q ∧ q <=₀ p

中文:
定义 ManyOneEquiv
  签名: {α β} [Primcodable α] [Primcodable β] (p : α -> 命题) (q : β -> 命题)
  定义体: p <=₀ q ∧ q <=₀ p
-/
def ManyOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -> Prop) :=
  p <=₀ q ∧ q <=₀ p

/--
Definition of `OneOneEquiv` / `OneOneEquiv` 的定义

English:
definition OneOneEquiv
  signature: {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -> Prop)
  body: p <=₁ q ∧ q <=₁ p

@[refl]

中文:
定义 OneOneEquiv
  签名: {α β} [Primcodable α] [Primcodable β] (p : α -> 命题) (q : β -> 命题)
  定义体: p <=₁ q ∧ q <=₁ p

@[refl]
-/
def OneOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α -> Prop) (q : β -> Prop) :=
  p <=₁ q ∧ q <=₁ p

@[refl]
/--
theorem `manyOneEquiv_refl` / 定理 `manyOneEquiv_refl`

English:
theorem manyOneEquiv_refl
  given: {α} [Primcodable α] (p : α -> Prop)
  statement: ManyOneEquiv p p
  proof: ⟨manyOneReducible_refl _, manyOneReducible_refl _⟩

@[symm]

中文:
定理 manyOneEquiv_refl
  条件: {α} [Primcodable α] (p : α -> 命题)
  结论: ManyOneEquiv p p
  证明: ⟨manyOneReducible_refl _, manyOneReducible_refl _⟩

@[symm]

Depends on / 依赖: manyOneReducible_refl
-/
theorem manyOneEquiv_refl {α} [Primcodable α] (p : α -> Prop) : ManyOneEquiv p p :=
  ⟨manyOneReducible_refl _, manyOneReducible_refl _⟩

@[symm]
/--
theorem `ManyOneEquiv.symm` / 定理 `ManyOneEquiv.symm`

English:
theorem ManyOneEquiv.symm
  given: {α β} [Primcodable α] [Primcodable β] {p : α -> Prop} {q : β -> Prop}
  proof: And.symm

@[trans]

中文:
定理 ManyOneEquiv.symm
  条件: {α β} [Primcodable α] [Primcodable β] {p : α -> 命题} {q : β -> 命题}
  证明: And.symm

@[trans]

Depends on / 依赖: And.symm
-/
theorem ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α -> Prop} {q : β -> Prop} :
    ManyOneEquiv p q -> ManyOneEquiv q p :=
  And.symm

@[trans]
/--
theorem `ManyOneEquiv.trans` / 定理 `ManyOneEquiv.trans`

English:
theorem ManyOneEquiv.trans
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> Prop}

中文:
定理 ManyOneEquiv.trans
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> 命题}
-/
theorem ManyOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> Prop}
    {q : β -> Prop} {r : γ -> Prop} : ManyOneEquiv p q -> ManyOneEquiv q r -> ManyOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩

/--
theorem `equivalence_of_manyOneEquiv` / 定理 `equivalence_of_manyOneEquiv`

English:
theorem equivalence_of_manyOneEquiv
  given: {α} [Primcodable α]
  statement: Equivalence (@ManyOneEquiv α α _ _)
  proof: ⟨manyOneEquiv_refl, fun {_ _} => ManyOneEquiv.symm, fun {_ _ _} => ManyOneEquiv.trans⟩

@[refl]

中文:
定理 equivalence_of_manyOneEquiv
  条件: {α} [Primcodable α]
  结论: 等价 (@ManyOneEquiv α α _ _)
  证明: ⟨manyOneEquiv_refl, fun {_ _} => ManyOneEquiv.symm, fun {_ _ _} => ManyOneEquiv.trans⟩

@[refl]

Depends on / 依赖: ManyOneEquiv, ManyOneEquiv.symm, ManyOneEquiv.trans, manyOneEquiv_refl
-/
theorem equivalence_of_manyOneEquiv {α} [Primcodable α] : Equivalence (@ManyOneEquiv α α _ _) :=
  ⟨manyOneEquiv_refl, fun {_ _} => ManyOneEquiv.symm, fun {_ _ _} => ManyOneEquiv.trans⟩

@[refl]
/--
theorem `oneOneEquiv_refl` / 定理 `oneOneEquiv_refl`

English:
theorem oneOneEquiv_refl
  given: {α} [Primcodable α] (p : α -> Prop)
  statement: OneOneEquiv p p
  proof: ⟨oneOneReducible_refl _, oneOneReducible_refl _⟩

@[symm]

中文:
定理 oneOneEquiv_refl
  条件: {α} [Primcodable α] (p : α -> 命题)
  结论: OneOneEquiv p p
  证明: ⟨oneOneReducible_refl _, oneOneReducible_refl _⟩

@[symm]

Depends on / 依赖: oneOneReducible_refl
-/
theorem oneOneEquiv_refl {α} [Primcodable α] (p : α -> Prop) : OneOneEquiv p p :=
  ⟨oneOneReducible_refl _, oneOneReducible_refl _⟩

@[symm]
/--
theorem `OneOneEquiv.symm` / 定理 `OneOneEquiv.symm`

English:
theorem OneOneEquiv.symm
  given: {α β} [Primcodable α] [Primcodable β] {p : α -> Prop} {q : β -> Prop}
  proof: And.symm

@[trans]

中文:
定理 OneOneEquiv.symm
  条件: {α β} [Primcodable α] [Primcodable β] {p : α -> 命题} {q : β -> 命题}
  证明: And.symm

@[trans]

Depends on / 依赖: And.symm
-/
theorem OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α -> Prop} {q : β -> Prop} :
    OneOneEquiv p q -> OneOneEquiv q p :=
  And.symm

@[trans]
/--
theorem `OneOneEquiv.trans` / 定理 `OneOneEquiv.trans`

English:
theorem OneOneEquiv.trans
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> Prop}

中文:
定理 OneOneEquiv.trans
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> 命题}
-/
theorem OneOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> Prop}
    {q : β -> Prop} {r : γ -> Prop} : OneOneEquiv p q -> OneOneEquiv q r -> OneOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩

/--
theorem `equivalence_of_oneOneEquiv` / 定理 `equivalence_of_oneOneEquiv`

English:
theorem equivalence_of_oneOneEquiv
  given: {α} [Primcodable α]
  statement: Equivalence (@OneOneEquiv α α _ _)
  proof: ⟨oneOneEquiv_refl, fun {_ _} => OneOneEquiv.symm, fun {_ _ _} => OneOneEquiv.trans⟩

中文:
定理 equivalence_of_oneOneEquiv
  条件: {α} [Primcodable α]
  结论: 等价 (@OneOneEquiv α α _ _)
  证明: ⟨oneOneEquiv_refl, fun {_ _} => OneOneEquiv.symm, fun {_ _ _} => OneOneEquiv.trans⟩

Depends on / 依赖: OneOneEquiv, OneOneEquiv.symm, OneOneEquiv.trans, oneOneEquiv_refl
-/
theorem equivalence_of_oneOneEquiv {α} [Primcodable α] : Equivalence (@OneOneEquiv α α _ _) :=
  ⟨oneOneEquiv_refl, fun {_ _} => OneOneEquiv.symm, fun {_ _ _} => OneOneEquiv.trans⟩

/--
theorem `OneOneEquiv.to_many_one` / 定理 `OneOneEquiv.to_many_one`

English:
theorem OneOneEquiv.to_many_one
  statement: {α β} [Primcodable α] [Primcodable β] {p : α -> Prop}

中文:
定理 OneOneEquiv.to_many_one
  结论: {α β} [Primcodable α] [Primcodable β] {p : α -> 命题}

Depends on / 依赖: Computable, e.symm
-/
theorem OneOneEquiv.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α -> Prop}
    {q : β -> Prop} : OneOneEquiv p q -> ManyOneEquiv p q
  | ⟨pq, qp⟩ => ⟨pq.to_many_one, qp.to_many_one⟩

/-- a computable bijection -/
nonrec def Equiv.Computable {α β} [Primcodable α] [Primcodable β] (e : α ≃ β) :=
  Computable e ∧ Computable e.symm

/--
theorem `Equiv.Computable.symm` / 定理 `Equiv.Computable.symm`

English:
theorem Equiv.Computable.symm
  given: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
  proof: And.symm

中文:
定理 等价.可计算.symm
  条件: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β}
  证明: And.symm

Depends on / 依赖: And.symm
-/
theorem Equiv.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} :
    e.Computable -> e.symm.Computable :=
  And.symm

/--
theorem `Equiv.Computable.trans` / 定理 `Equiv.Computable.trans`

English:
theorem Equiv.Computable.trans
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}

中文:
定理 等价.可计算.trans
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}
-/
theorem Equiv.Computable.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β}
    {e₂ : β ≃ γ} : e₁.Computable -> e₂.Computable -> (e₁.trans e₂).Computable
  | ⟨l₁, r₁⟩, ⟨l₂, r₂⟩ => ⟨l₂.comp l₁, r₁.comp r₂⟩

/--
theorem `Computable.eqv` / 定理 `Computable.eqv`

English:
theorem Computable.eqv
  given: (α) [Denumerable α]
  statement: (Denumerable.eqv α).Computable
  proof: ⟨Computable.encode, Computable.ofNat _⟩

中文:
定理 可计算.eqv
  条件: (α) [可枚举 α]
  结论: (可枚举.eqv α).可计算
  证明: ⟨Computable.encode, Computable.ofNat _⟩

Depends on / 依赖: Computable, Computable.encode, Computable.ofNat, encode
-/
theorem Computable.eqv (α) [Denumerable α] : (Denumerable.eqv α).Computable :=
  ⟨Computable.encode, Computable.ofNat _⟩

/--
theorem `Computable.equiv₂` / 定理 `Computable.equiv₂`

English:
theorem Computable.equiv₂
  given: (α β) [Denumerable α] [Denumerable β]
  proof: (Computable.eqv _).trans (Computable.eqv _).symm

中文:
定理 可计算.equiv₂
  条件: (α β) [可枚举 α] [可枚举 β]
  证明: (Computable.eqv _).trans (Computable.eqv _).symm

Depends on / 依赖: Computable, Computable.eqv
-/
theorem Computable.equiv₂ (α β) [Denumerable α] [Denumerable β] :
    (Denumerable.equiv₂ α β).Computable :=
  (Computable.eqv _).trans (Computable.eqv _).symm

/--
theorem `OneOneEquiv.of_equiv` / 定理 `OneOneEquiv.of_equiv`

English:
theorem OneOneEquiv.of_equiv
  statement: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
  proof: ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩

中文:
定理 OneOneEquiv.of_equiv
  结论: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.可计算)
  证明: ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩

Depends on / 依赖: OneOneReducible, OneOneReducible.of_equiv, OneOneReducible.of_equiv_symm, of_equiv, of_equiv_symm
-/
theorem OneOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : OneOneEquiv (p ∘ e) p :=
  ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩

/--
theorem `ManyOneEquiv.of_equiv` / 定理 `ManyOneEquiv.of_equiv`

English:
theorem ManyOneEquiv.of_equiv
  statement: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
  proof: (OneOneEquiv.of_equiv h).to_many_one

中文:
定理 ManyOneEquiv.of_equiv
  结论: {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.可计算)
  证明: (OneOneEquiv.of_equiv h).to_many_one

Depends on / 依赖: OneOneEquiv, OneOneEquiv.of_equiv, of_equiv, to_many_one
-/
theorem ManyOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable)
    {p} : ManyOneEquiv (p ∘ e) p :=
  (OneOneEquiv.of_equiv h).to_many_one

/--
theorem `ManyOneEquiv.le_congr_left` / 定理 `ManyOneEquiv.le_congr_left`

English:
theorem ManyOneEquiv.le_congr_left
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  proof: ⟨h.2.trans, h.1.trans⟩

中文:
定理 ManyOneEquiv.le_congr_left
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  证明: ⟨h.2.trans, h.1.trans⟩
-/
theorem ManyOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : ManyOneEquiv p q) : p <=₀ r ↔ q <=₀ r :=
  ⟨h.2.trans, h.1.trans⟩

/--
theorem `ManyOneEquiv.le_congr_right` / 定理 `ManyOneEquiv.le_congr_right`

English:
theorem ManyOneEquiv.le_congr_right
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  proof: ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩

中文:
定理 ManyOneEquiv.le_congr_right
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  证明: ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
-/
theorem ManyOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : ManyOneEquiv q r) : p <=₀ q ↔ p <=₀ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩

/--
theorem `OneOneEquiv.le_congr_left` / 定理 `OneOneEquiv.le_congr_left`

English:
theorem OneOneEquiv.le_congr_left
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  proof: ⟨h.2.trans, h.1.trans⟩

中文:
定理 OneOneEquiv.le_congr_left
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  证明: ⟨h.2.trans, h.1.trans⟩
-/
theorem OneOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : OneOneEquiv p q) : p <=₁ r ↔ q <=₁ r :=
  ⟨h.2.trans, h.1.trans⟩

/--
theorem `OneOneEquiv.le_congr_right` / 定理 `OneOneEquiv.le_congr_right`

English:
theorem OneOneEquiv.le_congr_right
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  proof: ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩

中文:
定理 OneOneEquiv.le_congr_right
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  证明: ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩
-/
theorem OneOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : OneOneEquiv q r) : p <=₁ q ↔ p <=₁ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩

/--
theorem `ManyOneEquiv.congr_left` / 定理 `ManyOneEquiv.congr_left`

English:
theorem ManyOneEquiv.congr_left
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  proof: and_congr h.le_congr_left h.le_congr_right

中文:
定理 ManyOneEquiv.congr_left
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  证明: and_congr h.le_congr_left h.le_congr_right

Depends on / 依赖: and_congr, h.le_congr_left, h.le_congr_right, le_congr_left, le_congr_right
-/
theorem ManyOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : ManyOneEquiv p q) :
    ManyOneEquiv p r ↔ ManyOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right

/--
theorem `ManyOneEquiv.congr_right` / 定理 `ManyOneEquiv.congr_right`

English:
theorem ManyOneEquiv.congr_right
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  proof: and_congr h.le_congr_right h.le_congr_left

中文:
定理 ManyOneEquiv.congr_right
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  证明: and_congr h.le_congr_right h.le_congr_left

Depends on / 依赖: and_congr, h.le_congr_left, h.le_congr_right, le_congr_left, le_congr_right
-/
theorem ManyOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : ManyOneEquiv q r) :
    ManyOneEquiv p q ↔ ManyOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left

/--
theorem `OneOneEquiv.congr_left` / 定理 `OneOneEquiv.congr_left`

English:
theorem OneOneEquiv.congr_left
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  proof: and_congr h.le_congr_left h.le_congr_right

中文:
定理 OneOneEquiv.congr_left
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  证明: and_congr h.le_congr_left h.le_congr_right

Depends on / 依赖: DFinsupp, DFinsupp.Lex.acc, InvImage, InvImage.accessible, accessible, and_congr, classical, h.le_congr_left, h.le_congr_right, le_congr_left, le_congr_right, lex_eq_invImage_dfinsupp_lex, toDFinsupp, toDFinsupp_support
-/
theorem OneOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : OneOneEquiv p q) :
    OneOneEquiv p r ↔ OneOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right

/--
theorem `OneOneEquiv.congr_right` / 定理 `OneOneEquiv.congr_right`

English:
theorem OneOneEquiv.congr_right
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  proof: and_congr h.le_congr_right h.le_congr_left

@[simp]

中文:
定理 OneOneEquiv.congr_right
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
  证明: and_congr h.le_congr_right h.le_congr_left

@[simp]

Depends on / 依赖: Lex.acc, and_congr, h.le_congr_left, h.le_congr_right, hr.apply, le_congr_left, le_congr_right
-/
theorem OneOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} (h : OneOneEquiv q r) :
    OneOneEquiv p q ↔ OneOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left

@[simp]
/--
theorem `ULower.down_computable` / 定理 `ULower.down_computable`

English:
theorem ULower.down_computable
  given: {α} [Primcodable α]
  statement: (ULower.equiv α).Computable
  proof: ⟨Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp⟩

中文:
定理 ULower.down_computable
  条件: {α} [Primcodable α]
  结论: (ULower.equiv α).可计算
  证明: ⟨Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp⟩

Depends on / 依赖: DFinsupp, DFinsupp.Lex.wellFounded, InvImage, InvImage.wf, Primrec, Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp, lex_eq_invImage_dfinsupp_lex, to_comp, ulower_down, ulower_up, wellFounded
-/
theorem ULower.down_computable {α} [Primcodable α] : (ULower.equiv α).Computable :=
  ⟨Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp⟩

/--
theorem `manyOneEquiv_up` / 定理 `manyOneEquiv_up`

English:
theorem manyOneEquiv_up
  given: {α} [Primcodable α] {p : α -> Prop}
  statement: ManyOneEquiv (p ∘ ULower.up) p
  proof: ManyOneEquiv.of_equiv ULower.down_computable.symm

local infixl:1001 " oplus' " => Sum.elim

中文:
定理 manyOneEquiv_up
  条件: {α} [Primcodable α] {p : α -> 命题}
  结论: ManyOneEquiv (p ∘ ULower.up) p
  证明: ManyOneEquiv.of_equiv ULower.down_computable.symm

local infixl:1001 " oplus' " => Sum.elim

Depends on / 依赖: Lex.wellFounded, ManyOneEquiv, ManyOneEquiv.of_equiv, ULower, ULower.down_computable.symm, down_computable, hN.wf, not_lt_zero, of_equiv, wellFounded
-/
theorem manyOneEquiv_up {α} [Primcodable α] {p : α -> Prop} : ManyOneEquiv (p ∘ ULower.up) p :=
  ManyOneEquiv.of_equiv ULower.down_computable.symm

local infixl:1001 " oplus' " => Sum.elim

open Nat.Primrec

/--
theorem `OneOneReducible.disjoin_left` / 定理 `OneOneReducible.disjoin_left`

English:
theorem OneOneReducible.disjoin_left
  statement: {α β} [Primcodable α] [Primcodable β] {p : α -> Prop}
  proof: ⟨Sum.inl, Computable.sumInl, fun _ _ => Sum.inl.inj_iff.1, fun _ => Iff.rfl⟩

中文:
定理 OneOneReducible.disjoin_left
  结论: {α β} [Primcodable α] [Primcodable β] {p : α -> 命题}
  证明: ⟨Sum.inl, Computable.sumInl, fun _ _ => Sum.inl.inj_iff.1, fun _ => Iff.rfl⟩

Depends on / 依赖: Computable, Computable.sumInl, Iff.rfl, Lex.wellFoundedLT, Sum.inl, Sum.inl.inj_iff, inj_iff, sumInl, wellFoundedLT
-/
theorem OneOneReducible.disjoin_left {α β} [Primcodable α] [Primcodable β] {p : α -> Prop}
    {q : β -> Prop} : p <=₁ p oplus' q :=
  ⟨Sum.inl, Computable.sumInl, fun _ _ => Sum.inl.inj_iff.1, fun _ => Iff.rfl⟩

/--
theorem `OneOneReducible.disjoin_right` / 定理 `OneOneReducible.disjoin_right`

English:
theorem OneOneReducible.disjoin_right
  statement: {α β} [Primcodable α] [Primcodable β] {p : α -> Prop}
  proof: ⟨Sum.inr, Computable.sumInr, fun _ _ => Sum.inr.inj_iff.1, fun _ => Iff.rfl⟩

中文:
定理 OneOneReducible.disjoin_right
  结论: {α β} [Primcodable α] [Primcodable β] {p : α -> 命题}
  证明: ⟨Sum.inr, Computable.sumInr, fun _ _ => Sum.inr.inj_iff.1, fun _ => Iff.rfl⟩

Depends on / 依赖: Computable, Computable.sumInr, Iff.rfl, Sum.inr, Sum.inr.inj_iff, inj_iff, sumInr
-/
theorem OneOneReducible.disjoin_right {α β} [Primcodable α] [Primcodable β] {p : α -> Prop}
    {q : β -> Prop} : q <=₁ p oplus' q :=
  ⟨Sum.inr, Computable.sumInr, fun _ _ => Sum.inr.inj_iff.1, fun _ => Iff.rfl⟩

/--
theorem `disjoin_manyOneReducible` / 定理 `disjoin_manyOneReducible`

English:
theorem disjoin_manyOneReducible
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]

中文:
定理 disjoin_manyOneReducible
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
-/
theorem disjoin_manyOneReducible {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ]
    {p : α -> Prop} {q : β -> Prop} {r : γ -> Prop} : p <=₀ r -> q <=₀ r -> (p oplus' q) <=₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨Sum.elim f g,
      Computable.id.sumCasesOn (c₁.comp Computable.snd).to₂ (c₂.comp Computable.snd).to₂,
      fun x => by cases x <;> [apply h₁; apply h₂]⟩

/--
theorem `disjoin_le` / 定理 `disjoin_le`

English:
theorem disjoin_le
  statement: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> Prop}
  proof: ⟨fun h =>
    ⟨OneOneReducible.disjoin_left.to_many_one.trans h,
      OneOneReducible.disjoin_right.to_many_one.trans h⟩,
    fun ⟨h₁, h₂⟩ => disjoin_manyOneReducible h₁ h₂⟩

中文:
定理 disjoin_le
  结论: {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> 命题}
  证明: ⟨fun h =>
    ⟨OneOneReducible.disjoin_left.to_many_one.trans h,
      OneOneReducible.disjoin_right.to_many_one.trans h⟩,
    fun ⟨h₁, h₂⟩ => disjoin_manyOneReducible h₁ h₂⟩

Depends on / 依赖: OneOneReducible, OneOneReducible.disjoin_left.to_many_one.trans, OneOneReducible.disjoin_right.to_many_one.trans, disjoin_left, disjoin_manyOneReducible, disjoin_right, to_many_one
-/
theorem disjoin_le {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α -> Prop}
    {q : β -> Prop} {r : γ -> Prop} : (p oplus' q) <=₀ r ↔ p <=₀ r ∧ q <=₀ r :=
  ⟨fun h =>
    ⟨OneOneReducible.disjoin_left.to_many_one.trans h,
      OneOneReducible.disjoin_right.to_many_one.trans h⟩,
    fun ⟨h₁, h₂⟩ => disjoin_manyOneReducible h₁ h₂⟩

variable {α : Type u} [Primcodable α] [Inhabited α] {β : Type v} [Primcodable β] [Inhabited β]

/--
Definition of `toNat` / `toNat` 的定义

English:
definition toNat
  signature: (p : Set α)
  body: { n | p ((Encodable.decode (α := α) n).getD default) }

@[simp]

中文:
定义 to自然数
  签名: (p : 集合 α)
  定义体: { n | p ((Encodable.decode (α := α) n).getD default) }

@[simp]

Depends on / 依赖: Encodable, Encodable.decode, decode
-/
def toNat (p : Set α) : Set Nat :=
  { n | p ((Encodable.decode (α := α) n).getD default) }

@[simp]
/--
theorem `toNat_manyOneReducible` / 定理 `toNat_manyOneReducible`

English:
theorem toNat_manyOneReducible
  given: {p : Set α}
  statement: toNat p <=₀ p
  proof: ⟨fun n => (Encodable.decode (α := α) n).getD default,
    Computable.option_getD Computable.decode (Computable.const _), fun _ => Iff.rfl⟩

@[simp]

中文:
定理 to自然数_manyOneReducible
  条件: {p : 集合 α}
  结论: to自然数 p <=₀ p
  证明: ⟨fun n => (Encodable.decode (α := α) n).getD default,
    Computable.option_getD Computable.decode (Computable.const _), fun _ => Iff.rfl⟩

@[simp]

Depends on / 依赖: Computable, Computable.const, Computable.decode, Computable.option_getD, Encodable, Encodable.decode, Iff.rfl, decode, option_getD
-/
theorem toNat_manyOneReducible {p : Set α} : toNat p <=₀ p :=
  ⟨fun n => (Encodable.decode (α := α) n).getD default,
    Computable.option_getD Computable.decode (Computable.const _), fun _ => Iff.rfl⟩

@[simp]
/--
theorem `manyOneReducible_toNat` / 定理 `manyOneReducible_toNat`

English:
theorem manyOneReducible_toNat
  given: {p : Set α}
  statement: p <=₀ toNat p
  proof: ⟨Encodable.encode, Computable.encode, by simp [toNat, Set.ofPred]⟩

@[simp]

中文:
定理 manyOneReducible_to自然数
  条件: {p : 集合 α}
  结论: p <=₀ to自然数 p
  证明: ⟨Encodable.encode, Computable.encode, by simp [toNat, Set.ofPred]⟩

@[simp]

Depends on / 依赖: Computable, Computable.encode, Encodable, Encodable.encode, Set.ofPred, encode, ofPred
-/
theorem manyOneReducible_toNat {p : Set α} : p <=₀ toNat p :=
  ⟨Encodable.encode, Computable.encode, by simp [toNat, Set.ofPred]⟩

@[simp]
/--
theorem `manyOneReducible_toNat_toNat` / 定理 `manyOneReducible_toNat_toNat`

English:
theorem manyOneReducible_toNat_toNat
  given: {p : Set α} {q : Set β}
  statement: toNat p <=₀ toNat q ↔ p <=₀ q
  proof: ⟨fun h => manyOneReducible_toNat.trans (h.trans toNat_manyOneReducible), fun h =>
    toNat_manyOneReducible.trans (h.trans manyOneReducible_toNat)⟩

@[simp]

中文:
定理 manyOneReducible_to自然数_to自然数
  条件: {p : 集合 α} {q : 集合 β}
  结论: to自然数 p <=₀ to自然数 q ↔ p <=₀ q
  证明: ⟨fun h => manyOneReducible_toNat.trans (h.trans toNat_manyOneReducible), fun h =>
    toNat_manyOneReducible.trans (h.trans manyOneReducible_toNat)⟩

@[simp]

Depends on / 依赖: h.trans, manyOneReducible_toNat, manyOneReducible_toNat.trans, toNat_manyOneReducible, toNat_manyOneReducible.trans
-/
theorem manyOneReducible_toNat_toNat {p : Set α} {q : Set β} : toNat p <=₀ toNat q ↔ p <=₀ q :=
  ⟨fun h => manyOneReducible_toNat.trans (h.trans toNat_manyOneReducible), fun h =>
    toNat_manyOneReducible.trans (h.trans manyOneReducible_toNat)⟩

@[simp]
/--
theorem `toNat_manyOneEquiv` / 定理 `toNat_manyOneEquiv`

English:
theorem toNat_manyOneEquiv
  given: {p : Set α}
  statement: ManyOneEquiv (toNat p) p
  proof: by simp [ManyOneEquiv]

@[simp]

中文:
定理 to自然数_manyOneEquiv
  条件: {p : 集合 α}
  结论: ManyOneEquiv (to自然数 p) p
  证明: by simp [ManyOneEquiv]

@[simp]

Depends on / 依赖: ManyOneEquiv
-/
theorem toNat_manyOneEquiv {p : Set α} : ManyOneEquiv (toNat p) p := by simp [ManyOneEquiv]

@[simp]
/--
theorem `manyOneEquiv_toNat` / 定理 `manyOneEquiv_toNat`

English:
theorem manyOneEquiv_toNat
  given: (p : Set α) (q : Set β)
  proof: by simp [ManyOneEquiv]

中文:
定理 manyOneEquiv_to自然数
  条件: (p : 集合 α) (q : 集合 β)
  证明: by simp [ManyOneEquiv]

Depends on / 依赖: ManyOneEquiv
-/
theorem manyOneEquiv_toNat (p : Set α) (q : Set β) :
    ManyOneEquiv (toNat p) (toNat q) ↔ ManyOneEquiv p q := by simp [ManyOneEquiv]

/--
Definition of `ManyOneDegree` / `ManyOneDegree` 的定义

English:
definition ManyOneDegree
  signature: : Type
  body: Quotient (⟨ManyOneEquiv, equivalence_of_manyOneEquiv⟩ : Setoid (Set Nat))

中文:
定义 ManyOneDegree
  签名: : 类型
  定义体: Quotient (⟨ManyOneEquiv, equivalence_of_manyOneEquiv⟩ : Setoid (Set Nat))

Depends on / 依赖: ManyOneEquiv, Quotient, Setoid, equivalence_of_manyOneEquiv
-/
def ManyOneDegree : Type :=
  Quotient (⟨ManyOneEquiv, equivalence_of_manyOneEquiv⟩ : Setoid (Set Nat))

namespace ManyOneDegree

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: (p : α -> Prop)
  body: Quotient.mk'' (toNat p)

@[elab_as_elim]

中文:
定义 of
  签名: (p : α -> 命题)
  定义体: Quotient.mk'' (toNat p)

@[elab_as_elim]

Depends on / 依赖: Quotient, Quotient.mk
-/
def of (p : α -> Prop) : ManyOneDegree :=
  Quotient.mk'' (toNat p)

@[elab_as_elim]
/--
theorem `ind_on` / 定理 `ind_on`

English:
theorem ind_on
  statement: {C : ManyOneDegree -> Prop} (d : ManyOneDegree)
  proof: Quotient.inductionOn' d h

中文:
定理 ind_on
  结论: {C : ManyOneDegree -> 命题} (d : ManyOneDegree)
  证明: Quotient.inductionOn' d h
-/
protected theorem ind_on {C : ManyOneDegree -> Prop} (d : ManyOneDegree)
    (h : forall p : Set Nat, C (of p)) : C d :=
  Quotient.inductionOn' d h

/--
Definition of `liftOn` / `liftOn` 的定义

English:
abbreviation liftOn
  signature: {φ} (d : ManyOneDegree) (f : Set Nat -> φ)
  body: Quotient.liftOn' d f h

@[simp]

中文:
缩写 liftOn
  签名: {φ} (d : ManyOneDegree) (f : 集合 自然数 -> φ)
  定义体: Quotient.liftOn' d f h

@[simp]
-/
protected abbrev liftOn {φ} (d : ManyOneDegree) (f : Set Nat -> φ)
    (h : forall p q, ManyOneEquiv p q -> f p = f q) : φ :=
  Quotient.liftOn' d f h

@[simp]
/--
theorem `liftOn_eq` / 定理 `liftOn_eq`

English:
theorem liftOn_eq
  statement: {φ} (p : Set Nat) (f : Set Nat -> φ)
  proof: rfl

中文:
定理 liftOn_eq
  结论: {φ} (p : 集合 自然数) (f : 集合 自然数 -> φ)
  证明: rfl
-/
protected theorem liftOn_eq {φ} (p : Set Nat) (f : Set Nat -> φ)
    (h : forall p q, ManyOneEquiv p q -> f p = f q) : (of p).liftOn f h = f p :=
  rfl

/-- Lifts a binary function on sets of natural numbers to many-one degrees. -/
@[reducible, simp]
/--
Definition of `liftOn₂` / `liftOn₂` 的定义

English:
definition liftOn₂
  signature: {φ} (d₁ d₂ : ManyOneDegree) (f : Set Nat -> Set Nat -> φ)
  body: d₁.liftOn (fun p => d₂.liftOn (f p) fun _ _ hq => h _ _ _ _ (by rfl) hq)
    (by
      intro p₁ p₂ hp
      induction d₂ using ManyOneDegree.ind_on
      apply h
      · assumption
      · rfl)

@[simp]

中文:
定义 liftOn₂
  签名: {φ} (d₁ d₂ : ManyOneDegree) (f : 集合 自然数 -> 集合 自然数 -> φ)
  定义体: d₁.liftOn (fun p => d₂.liftOn (f p) fun _ _ hq => h _ _ _ _ (by rfl) hq)
    (by
      intro p₁ p₂ hp
      induction d₂ using ManyOneDegree.ind_on
      apply h
      · assumption
      · rfl)

@[simp]
-/
protected def liftOn₂ {φ} (d₁ d₂ : ManyOneDegree) (f : Set Nat -> Set Nat -> φ)
    (h : forall p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ -> ManyOneEquiv q₁ q₂ -> f p₁ q₁ = f p₂ q₂) : φ :=
  d₁.liftOn (fun p => d₂.liftOn (f p) fun _ _ hq => h _ _ _ _ (by rfl) hq)
    (by
      intro p₁ p₂ hp
      induction d₂ using ManyOneDegree.ind_on
      apply h
      · assumption
      · rfl)

@[simp]
/--
theorem `liftOn₂_eq` / 定理 `liftOn₂_eq`

English:
theorem liftOn₂_eq
  statement: {φ} (p q : Set Nat) (f : Set Nat -> Set Nat -> φ)
  proof: rfl

中文:
定理 liftOn₂_eq
  结论: {φ} (p q : 集合 自然数) (f : 集合 自然数 -> 集合 自然数 -> φ)
  证明: rfl
-/
protected theorem liftOn₂_eq {φ} (p q : Set Nat) (f : Set Nat -> Set Nat -> φ)
    (h : forall p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ -> ManyOneEquiv q₁ q₂ -> f p₁ q₁ = f p₂ q₂) :
    (of p).liftOn₂ (of q) f h = f p q :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `of_eq_of` / 定理 `of_eq_of`

English:
theorem of_eq_of
  given: {p : α -> Prop} {q : β -> Prop}
  statement: of p = of q ↔ ManyOneEquiv p q
  proof: by
  rw [of]; rw [of]; rw [Quotient.eq'']
  simp

中文:
定理 of_eq_of
  条件: {p : α -> 命题} {q : β -> 命题}
  结论: of p = of q ↔ ManyOneEquiv p q
  证明: by
  rw [of]; rw [of]; rw [Quotient.eq'']
  simp

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem of_eq_of {p : α -> Prop} {q : β -> Prop} : of p = of q ↔ ManyOneEquiv p q := by
  rw [of]; rw [of]; rw [Quotient.eq'']
  simp

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited ManyOneDegree
  body: ⟨of (∅ : Set Nat)⟩

中文:
实例 instInhabited
  签名: : 可居 ManyOneDegree
  定义体: ⟨of (∅ : Set Nat)⟩
-/
instance instInhabited : Inhabited ManyOneDegree :=
  ⟨of (∅ : Set Nat)⟩

/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: : LE ManyOneDegree
  body: ⟨fun d₁ d₂ =>
    ManyOneDegree.liftOn₂ d₁ d₂ (· <=₀ ·) fun _p₁ _p₂ _q₁ _q₂ hp hq =>
      propext (hp.le_congr_left.trans hq.le_congr_right)⟩

@[simp]

中文:
实例 instLE
  签名: : LE ManyOneDegree
  定义体: ⟨fun d₁ d₂ =>
    ManyOneDegree.liftOn₂ d₁ d₂ (· <=₀ ·) fun _p₁ _p₂ _q₁ _q₂ hp hq =>
      propext (hp.le_congr_left.trans hq.le_congr_right)⟩

@[simp]

Depends on / 依赖: ManyOneDegree, ManyOneDegree.liftOn, hp.le_congr_left.trans, hq.le_congr_right, le_congr_left, le_congr_right, propext
-/
instance instLE : LE ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    ManyOneDegree.liftOn₂ d₁ d₂ (· <=₀ ·) fun _p₁ _p₂ _q₁ _q₂ hp hq =>
      propext (hp.le_congr_left.trans hq.le_congr_right)⟩

@[simp]
/--
theorem `of_le_of` / 定理 `of_le_of`

English:
theorem of_le_of
  given: {p : α -> Prop} {q : β -> Prop}
  statement: of p <= of q ↔ p <=₀ q
  proof: manyOneReducible_toNat_toNat

中文:
定理 of_le_of
  条件: {p : α -> 命题} {q : β -> 命题}
  结论: of p <= of q ↔ p <=₀ q
  证明: manyOneReducible_toNat_toNat

Depends on / 依赖: manyOneReducible_toNat_toNat
-/
theorem of_le_of {p : α -> Prop} {q : β -> Prop} : of p <= of q ↔ p <=₀ q :=
  manyOneReducible_toNat_toNat

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/--
theorem `le_refl` / 定理 `le_refl`

English:
theorem le_refl
  given: (d : ManyOneDegree)
  statement: d <= d
  proof: by
  induction d using ManyOneDegree.ind_on; simp; rfl

中文:
定理 le_refl
  条件: (d : ManyOneDegree)
  结论: d <= d
  证明: by
  induction d using ManyOneDegree.ind_on; simp; rfl
-/
private theorem le_refl (d : ManyOneDegree) : d <= d := by
  induction d using ManyOneDegree.ind_on; simp; rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
/--
theorem `le_antisymm` / 定理 `le_antisymm`

English:
theorem le_antisymm
  given: {d₁ d₂ : ManyOneDegree}
  statement: d₁ <= d₂ -> d₂ <= d₁ -> d₁ = d₂
  proof: by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  intro hp hq
  simp_all only [ManyOneEquiv, of_le_of, of_eq_of, true_and]

中文:
定理 le_antisymm
  条件: {d₁ d₂ : ManyOneDegree}
  结论: d₁ <= d₂ -> d₂ <= d₁ -> d₁ = d₂
  证明: by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  intro hp hq
  simp_all only [ManyOneEquiv, of_le_of, of_eq_of, true_and]
-/
private theorem le_antisymm {d₁ d₂ : ManyOneDegree} : d₁ <= d₂ -> d₂ <= d₁ -> d₁ = d₂ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  intro hp hq
  simp_all only [ManyOneEquiv, of_le_of, of_eq_of, true_and]

set_option backward.privateInPublic true in
/--
theorem `le_trans` / 定理 `le_trans`

English:
theorem le_trans
  given: {d₁ d₂ d₃ : ManyOneDegree}
  statement: d₁ <= d₂ -> d₂ <= d₃ -> d₁ <= d₃
  proof: by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  apply ManyOneReducible.trans

中文:
定理 le_trans
  条件: {d₁ d₂ d₃ : ManyOneDegree}
  结论: d₁ <= d₂ -> d₂ <= d₃ -> d₁ <= d₃
  证明: by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  apply ManyOneReducible.trans
-/
private theorem le_trans {d₁ d₂ d₃ : ManyOneDegree} : d₁ <= d₂ -> d₂ <= d₃ -> d₁ <= d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  apply ManyOneReducible.trans

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder ManyOneDegree where
  body: le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

中文:
实例 instPartialOrder
  签名: : 偏序 ManyOneDegree where
  定义体: le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

Depends on / 依赖: le_refl
-/
instance instPartialOrder : PartialOrder ManyOneDegree where
  le_refl := le_refl
  le_trans _ _ _ := le_trans
  le_antisymm _ _ := le_antisymm

/--
Instance `instAdd` / 实例 `instAdd`

English:
instance instAdd
  signature: : Add ManyOneDegree
  body: ⟨fun d₁ d₂ =>
    d₁.liftOn₂ d₂ (fun a b => of (a oplus' b))
      (by
        rintro a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩
        rw [of_eq_of]
        exact
          ⟨disjoin_manyOneReducible (hl₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hl₂.trans OneOneReducible.disjoin_right.to_m

中文:
实例 instAdd
  签名: : 加法 ManyOneDegree
  定义体: ⟨fun d₁ d₂ =>
    d₁.liftOn₂ d₂ (fun a b => of (a oplus' b))
      (by
        rintro a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩
        rw [of_eq_of]
        exact
          ⟨disjoin_manyOneReducible (hl₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hl₂.trans OneOneReducible.disjoin_right.to_m

Depends on / 依赖: OneOneReducible, OneOneReducible.disjoin_left.to_many_one, OneOneReducible.disjoin_right.to_many_one, disjoin_left, disjoin_manyOneReducible, disjoin_right, of_eq_of, to_many_one
-/
instance instAdd : Add ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    d₁.liftOn₂ d₂ (fun a b => of (a oplus' b))
      (by
        rintro a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩
        rw [of_eq_of]
        exact
          ⟨disjoin_manyOneReducible (hl₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hl₂.trans OneOneReducible.disjoin_right.to_many_one),
            disjoin_manyOneReducible (hr₁.trans OneOneReducible.disjoin_left.to_many_one)
              (hr₂.trans OneOneReducible.disjoin_right.to_many_one)⟩)⟩

@[simp]
/--
theorem `add_of` / 定理 `add_of`

English:
theorem add_of
  given: (p : Set α) (q : Set β)
  statement: of (p oplus' q) = of p + of q
  proof: of_eq_of.mpr
    ⟨disjoin_manyOneReducible
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_left.to_many_one)
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_right.to_many_one),
      disjoin_manyOneReducible
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_le

中文:
定理 add_of
  条件: (p : 集合 α) (q : 集合 β)
  结论: of (p oplus' q) = of p + of q
  证明: of_eq_of.mpr
    ⟨disjoin_manyOneReducible
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_left.to_many_one)
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_right.to_many_one),
      disjoin_manyOneReducible
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_le

Depends on / 依赖: OneOneReducible, OneOneReducible.disjoin_left.to_many_one, OneOneReducible.disjoin_right.to_many_one, disjoin_left, disjoin_manyOneReducible, disjoin_right, manyOneReducible_toNat, manyOneReducible_toNat.trans, of_eq_of, of_eq_of.mpr, toNat_manyOneReducible, toNat_manyOneReducible.trans, to_many_one
-/
theorem add_of (p : Set α) (q : Set β) : of (p oplus' q) = of p + of q :=
  of_eq_of.mpr
    ⟨disjoin_manyOneReducible
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_left.to_many_one)
        (manyOneReducible_toNat.trans OneOneReducible.disjoin_right.to_many_one),
      disjoin_manyOneReducible
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_left.to_many_one)
        (toNat_manyOneReducible.trans OneOneReducible.disjoin_right.to_many_one)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `add_le` / 定理 `add_le`

English:
theorem add_le
  given: {d₁ d₂ d₃ : ManyOneDegree}
  statement: d₁ + d₂ <= d₃ ↔ d₁ <= d₃ ∧ d₂ <= d₃
  proof: by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  simpa only [← add_of, of_le_of] using disjoin_le

@[simp]

中文:
定理 add_le
  条件: {d₁ d₂ d₃ : ManyOneDegree}
  结论: d₁ + d₂ <= d₃ ↔ d₁ <= d₃ ∧ d₂ <= d₃
  证明: by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  simpa only [← add_of, of_le_of] using disjoin_le

@[simp]
-/
protected theorem add_le {d₁ d₂ d₃ : ManyOneDegree} : d₁ + d₂ <= d₃ ↔ d₁ <= d₃ ∧ d₂ <= d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  simpa only [← add_of, of_le_of] using disjoin_le

@[simp]
/--
theorem `le_add_left` / 定理 `le_add_left`

English:
theorem le_add_left
  given: (d₁ d₂ : ManyOneDegree)
  statement: d₁ <= d₁ + d₂
  proof: (ManyOneDegree.add_le.1 (le_refl _)).1

@[simp]

中文:
定理 le_add_left
  条件: (d₁ d₂ : ManyOneDegree)
  结论: d₁ <= d₁ + d₂
  证明: (ManyOneDegree.add_le.1 (le_refl _)).1

@[simp]
-/
protected theorem le_add_left (d₁ d₂ : ManyOneDegree) : d₁ <= d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (le_refl _)).1

@[simp]
/--
theorem `le_add_right` / 定理 `le_add_right`

English:
theorem le_add_right
  given: (d₁ d₂ : ManyOneDegree)
  statement: d₂ <= d₁ + d₂
  proof: (ManyOneDegree.add_le.1 (le_refl _)).2

中文:
定理 le_add_right
  条件: (d₁ d₂ : ManyOneDegree)
  结论: d₂ <= d₁ + d₂
  证明: (ManyOneDegree.add_le.1 (le_refl _)).2
-/
protected theorem le_add_right (d₁ d₂ : ManyOneDegree) : d₂ <= d₁ + d₂ :=
  (ManyOneDegree.add_le.1 (le_refl _)).2

/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: : SemilatticeSup ManyOneDegree
  body: { ManyOneDegree.instPartialOrder with
    sup := (· + ·)
    le_sup_left := ManyOneDegree.le_add_left
    le_sup_right := ManyOneDegree.le_add_right
    sup_le := fun _ _ _ h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }

中文:
实例 instSemilatticeSup
  签名: : SemilatticeSup ManyOneDegree
  定义体: { ManyOneDegree.instPartialOrder with
    sup := (· + ·)
    le_sup_left := ManyOneDegree.le_add_left
    le_sup_right := ManyOneDegree.le_add_right
    sup_le := fun _ _ _ h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }

Depends on / 依赖: ManyOneDegree, ManyOneDegree.add_le, ManyOneDegree.instPartialOrder, ManyOneDegree.le_add_left, ManyOneDegree.le_add_right, add_le, instPartialOrder, le_add_left, le_add_right, le_sup_left, le_sup_right, sup_le
-/
instance instSemilatticeSup : SemilatticeSup ManyOneDegree :=
  { ManyOneDegree.instPartialOrder with
    sup := (· + ·)
    le_sup_left := ManyOneDegree.le_add_left
    le_sup_right := ManyOneDegree.le_add_right
    sup_le := fun _ _ _ h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }

end ManyOneDegree
