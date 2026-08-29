/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Logic.Equiv.Nat

/-!
# Countable types

In this file we provide basic instances of the `Countable` typeclass defined elsewhere.
-/

public section

assert_not_exists Monoid

universe u v w

open Function

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Countable Int
  body: Countable.of_equiv Nat Equiv.intEquivNat.symm

中文:
实例 :
  签名: Countable 整数
  定义体: Countable.of_equiv Nat Equiv.intEquivNat.symm

Depends on / 依赖: Countable, Countable.of_equiv, Equiv.intEquivNat.symm, intEquivNat, of_equiv
-/
instance : Countable Int :=
  Countable.of_equiv Nat Equiv.intEquivNat.symm

/-!
### Definition in terms of `Function.Embedding`
-/

section Embedding

variable {α : Sort u} {β : Sort v}

/--
theorem `countable_iff_nonempty_embedding` / 定理 `countable_iff_nonempty_embedding`

English:
theorem countable_iff_nonempty_embedding
  statement: Countable α ↔ Nonempty (α ↪ Nat)
  proof: ⟨fun ⟨⟨f, hf⟩⟩ => ⟨⟨f, hf⟩⟩, fun ⟨f⟩ => ⟨⟨f, f.2⟩⟩⟩

中文:
定理 countable_iff_nonempty_embedding
  结论: Countable α ↔ Nonempty (α ↪ 自然数)
  证明: ⟨fun ⟨⟨f, hf⟩⟩ => ⟨⟨f, hf⟩⟩, fun ⟨f⟩ => ⟨⟨f, f.2⟩⟩⟩
-/
theorem countable_iff_nonempty_embedding : Countable α ↔ Nonempty (α ↪ Nat) :=
  ⟨fun ⟨⟨f, hf⟩⟩ => ⟨⟨f, hf⟩⟩, fun ⟨f⟩ => ⟨⟨f, f.2⟩⟩⟩

/--
theorem `uncountable_iff_isEmpty_embedding` / 定理 `uncountable_iff_isEmpty_embedding`

English:
theorem uncountable_iff_isEmpty_embedding
  statement: Uncountable α ↔ IsEmpty (α ↪ Nat)
  proof: by
  rw [← not_countable_iff]; rw [countable_iff_nonempty_embedding]; rw [not_nonempty_iff]

中文:
定理 uncountable_iff_isEmpty_embedding
  结论: Uncountable α ↔ IsEmpty (α ↪ 自然数)
  证明: by
  rw [← not_countable_iff]; rw [countable_iff_nonempty_embedding]; rw [not_nonempty_iff]

Depends on / 依赖: countable_iff_nonempty_embedding, not_countable_iff, not_nonempty_iff
-/
theorem uncountable_iff_isEmpty_embedding : Uncountable α ↔ IsEmpty (α ↪ Nat) := by
  rw [← not_countable_iff]; rw [countable_iff_nonempty_embedding]; rw [not_nonempty_iff]

/--
theorem `nonempty_embedding_nat` / 定理 `nonempty_embedding_nat`

English:
theorem nonempty_embedding_nat
  given: (α) [Countable α]
  statement: Nonempty (α ↪ Nat)
  proof: countable_iff_nonempty_embedding.1 ‹_›

中文:
定理 nonempty_embedding_nat
  条件: (α) [Countable α]
  结论: Nonempty (α ↪ 自然数)
  证明: countable_iff_nonempty_embedding.1 ‹_›

Depends on / 依赖: countable_iff_nonempty_embedding
-/
theorem nonempty_embedding_nat (α) [Countable α] : Nonempty (α ↪ Nat) :=
  countable_iff_nonempty_embedding.1 ‹_›

/--
theorem `Function.Embedding.countable` / 定理 `Function.Embedding.countable`

English:
theorem Function.Embedding.countable
  given: [Countable β] (f : α ↪ β)
  statement: Countable α
  proof: f.injective.countable

中文:
定理 Function.Embedding.countable
  条件: [Countable β] (f : α ↪ β)
  结论: Countable α
  证明: f.injective.countable
-/
protected theorem Function.Embedding.countable [Countable β] (f : α ↪ β) : Countable α :=
  f.injective.countable

/--
lemma `Function.Embedding.uncountable` / 引理 `Function.Embedding.uncountable`

English:
lemma Function.Embedding.uncountable
  given: [Uncountable α] (f : α ↪ β)
  statement: Uncountable β
  proof: f.injective.uncountable

中文:
引理 Function.Embedding.uncountable
  条件: [Uncountable α] (f : α ↪ β)
  结论: Uncountable β
  证明: f.injective.uncountable
-/
protected lemma Function.Embedding.uncountable [Uncountable α] (f : α ↪ β) : Uncountable β :=
  f.injective.uncountable

end Embedding

/-!
### Operations on `Type*`s
-/

section type

variable {α : Type u} {β : Type v} {π : α -> Type w}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: α] [Countable β] : Countable (α oplus β)
  body: by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (Equiv.natSumNatEquivNat.injective.comp <| hf.sumMap hg).countable

中文:
实例 [Countable
  签名: α] [Countable β] : Countable (α oplus β)
  定义体: by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (Equiv.natSumNatEquivNat.injective.comp <| hf.sumMap hg).countable

Depends on / 依赖: Equiv.natSumNatEquivNat.injective.comp, countable, exists_injective_nat, hf.sumMap, injective, natSumNatEquivNat, sumMap
-/
instance [Countable α] [Countable β] : Countable (α oplus β) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (Equiv.natSumNatEquivNat.injective.comp <| hf.sumMap hg).countable

/--
Instance `Sum.uncountable_inl` / 实例 `Sum.uncountable_inl`

English:
instance Sum.uncountable_inl
  signature: [Uncountable α]
  body: inl_injective.uncountable

中文:
实例 Sum.uncountable_inl
  签名: [Uncountable α]
  定义体: inl_injective.uncountable

Depends on / 依赖: inl_injective, inl_injective.uncountable, uncountable
-/
instance Sum.uncountable_inl [Uncountable α] : Uncountable (α oplus β) :=
  inl_injective.uncountable

/--
Instance `Sum.uncountable_inr` / 实例 `Sum.uncountable_inr`

English:
instance Sum.uncountable_inr
  signature: [Uncountable β]
  body: inr_injective.uncountable

中文:
实例 Sum.uncountable_inr
  签名: [Uncountable β]
  定义体: inr_injective.uncountable

Depends on / 依赖: inr_injective, inr_injective.uncountable, uncountable
-/
instance Sum.uncountable_inr [Uncountable β] : Uncountable (α oplus β) :=
  inr_injective.uncountable

/--
Instance `Option.instCountable` / 实例 `Option.instCountable`

English:
instance Option.instCountable
  signature: [Countable α]
  body: Countable.of_equiv _ (Equiv.optionEquivSumPUnit.{0, _} α).symm

中文:
实例 Option.instCountable
  签名: [Countable α]
  定义体: Countable.of_equiv _ (Equiv.optionEquivSumPUnit.{0, _} α).symm

Depends on / 依赖: Countable, Countable.of_equiv, Equiv.optionEquivSumPUnit, of_equiv, optionEquivSumPUnit
-/
instance Option.instCountable [Countable α] : Countable (Option α) :=
  Countable.of_equiv _ (Equiv.optionEquivSumPUnit.{0, _} α).symm

/--
Instance `WithTop.instCountable` / 实例 `WithTop.instCountable`

English:
instance WithTop.instCountable
  signature: [Countable α]
  body: Option.instCountable

中文:
实例 WithTop.instCountable
  签名: [Countable α]
  定义体: Option.instCountable

Depends on / 依赖: Option.instCountable, instCountable
-/
instance WithTop.instCountable [Countable α] : Countable (WithTop α) := Option.instCountable
/--
Instance `WithBot.instCountable` / 实例 `WithBot.instCountable`

English:
instance WithBot.instCountable
  signature: [Countable α]
  body: Option.instCountable

中文:
实例 WithBot.instCountable
  签名: [Countable α]
  定义体: Option.instCountable

Depends on / 依赖: Option.instCountable, instCountable
-/
instance WithBot.instCountable [Countable α] : Countable (WithBot α) := Option.instCountable
/--
Instance `ENat.instCountable` / 实例 `ENat.instCountable`

English:
instance ENat.instCountable
  signature: : Countable Nat∞
  body: Option.instCountable

中文:
实例 ENat.instCountable
  签名: : Countable 自然数∞
  定义体: Option.instCountable

Depends on / 依赖: Option.instCountable, instCountable
-/
instance ENat.instCountable : Countable Nat∞ := Option.instCountable

/--
Instance `Option.instUncountable` / 实例 `Option.instUncountable`

English:
instance Option.instUncountable
  signature: [Uncountable α]
  body: Injective.uncountable fun _ _ => Option.some_inj.1

中文:
实例 Option.instUncountable
  签名: [Uncountable α]
  定义体: Injective.uncountable fun _ _ => Option.some_inj.1

Depends on / 依赖: Injective, Injective.uncountable, Option.some_inj, some_inj, uncountable
-/
instance Option.instUncountable [Uncountable α] : Uncountable (Option α) :=
  Injective.uncountable fun _ _ => Option.some_inj.1

/--
Instance `WithTop.instUncountable` / 实例 `WithTop.instUncountable`

English:
instance WithTop.instUncountable
  signature: [Uncountable α]
  body: Option.instUncountable

中文:
实例 WithTop.instUncountable
  签名: [Uncountable α]
  定义体: Option.instUncountable

Depends on / 依赖: Option.instUncountable, instUncountable
-/
instance WithTop.instUncountable [Uncountable α] : Uncountable (WithTop α) := Option.instUncountable
/--
Instance `WithBot.instUncountable` / 实例 `WithBot.instUncountable`

English:
instance WithBot.instUncountable
  signature: [Uncountable α]
  body: Option.instUncountable

中文:
实例 WithBot.instUncountable
  签名: [Uncountable α]
  定义体: Option.instUncountable

Depends on / 依赖: Option.instUncountable, instUncountable
-/
instance WithBot.instUncountable [Uncountable α] : Uncountable (WithBot α) := Option.instUncountable

/--
lemma `untopD_coe_enat` / 引理 `untopD_coe_enat`

English:
lemma untopD_coe_enat
  given: (d n : Nat)
  statement: WithTop.untopD d (n : Nat∞) = n
  proof: rfl

中文:
引理 untopD_coe_enat
  条件: (d n : 自然数)
  结论: WithTop.untopD d (n : 自然数∞) = n
  证明: rfl
-/
@[simp] lemma untopD_coe_enat (d n : Nat) : WithTop.untopD d (n : Nat∞) = n := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: α] [Countable β] : Countable (α × β)
  body: by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (Nat.pairEquiv.injective.comp <| hf.prodMap hg).countable

中文:
实例 [Countable
  签名: α] [Countable β] : Countable (α × β)
  定义体: by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (Nat.pairEquiv.injective.comp <| hf.prodMap hg).countable

Depends on / 依赖: Nat.pairEquiv.injective.comp, countable, exists_injective_nat, hf.prodMap, injective, pairEquiv, prodMap
-/
instance [Countable α] [Countable β] : Countable (α × β) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  rcases exists_injective_nat β with ⟨g, hg⟩
  exact (Nat.pairEquiv.injective.comp <| hf.prodMap hg).countable

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Uncountable
  signature: α] [Nonempty β] : Uncountable (α × β)
  body: by
  inhabit β
  exact (Prod.mk_left_injective default).uncountable

中文:
实例 [Uncountable
  签名: α] [Nonempty β] : Uncountable (α × β)
  定义体: by
  inhabit β
  exact (Prod.mk_left_injective default).uncountable

Depends on / 依赖: Prod.mk_left_injective, inhabit, mk_left_injective, uncountable
-/
instance [Uncountable α] [Nonempty β] : Uncountable (α × β) := by
  inhabit β
  exact (Prod.mk_left_injective default).uncountable

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] [Uncountable β] : Uncountable (α × β)
  body: by
  inhabit α
  exact (Prod.mk_right_injective default).uncountable

中文:
实例 [Nonempty
  签名: α] [Uncountable β] : Uncountable (α × β)
  定义体: by
  inhabit α
  exact (Prod.mk_right_injective default).uncountable

Depends on / 依赖: Prod.mk_right_injective, inhabit, mk_right_injective, uncountable
-/
instance [Nonempty α] [Uncountable β] : Uncountable (α × β) := by
  inhabit α
  exact (Prod.mk_right_injective default).uncountable

/--
lemma `countable_left_of_prod_of_nonempty` / 引理 `countable_left_of_prod_of_nonempty`

English:
lemma countable_left_of_prod_of_nonempty
  given: [Nonempty β] (h : Countable (α × β))
  statement: Countable α
  proof: by
  contrapose! h
  infer_instance

中文:
引理 countable_left_of_prod_of_nonempty
  条件: [Nonempty β] (h : Countable (α × β))
  结论: Countable α
  证明: by
  contrapose! h
  infer_instance

Depends on / 依赖: contrapose, infer_instance
-/
lemma countable_left_of_prod_of_nonempty [Nonempty β] (h : Countable (α × β)) : Countable α := by
  contrapose! h
  infer_instance

/--
lemma `countable_right_of_prod_of_nonempty` / 引理 `countable_right_of_prod_of_nonempty`

English:
lemma countable_right_of_prod_of_nonempty
  given: [Nonempty α] (h : Countable (α × β))
  statement: Countable β
  proof: by
  contrapose! h
  infer_instance

中文:
引理 countable_right_of_prod_of_nonempty
  条件: [Nonempty α] (h : Countable (α × β))
  结论: Countable β
  证明: by
  contrapose! h
  infer_instance

Depends on / 依赖: contrapose, infer_instance
-/
lemma countable_right_of_prod_of_nonempty [Nonempty α] (h : Countable (α × β)) : Countable β := by
  contrapose! h
  infer_instance

/--
lemma `countable_prod_swap` / 引理 `countable_prod_swap`

English:
lemma countable_prod_swap
  given: [Countable (α × β)]
  statement: Countable (β × α)
  proof: Countable.of_equiv _ (Equiv.prodComm α β)

中文:
引理 countable_prod_swap
  条件: [Countable (α × β)]
  结论: Countable (β × α)
  证明: Countable.of_equiv _ (Equiv.prodComm α β)

Depends on / 依赖: Countable, Countable.of_equiv, Equiv.prodComm, of_equiv, prodComm
-/
lemma countable_prod_swap [Countable (α × β)] : Countable (β × α) :=
  Countable.of_equiv _ (Equiv.prodComm α β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: α] [forall a, Countable (π a)] : Countable (Sigma π)
  body: by
  rcases exists_injective_nat α with ⟨f, hf⟩
  choose g hg using fun a => exists_injective_nat (π a)
  exact ((Equiv.sigmaEquivProd Nat Nat).injective.comp <| hf.sigma_map hg).countable

中文:
实例 [Countable
  签名: α] [对任意 a, Countable (π a)] : Countable (Sigma π)
  定义体: by
  rcases exists_injective_nat α with ⟨f, hf⟩
  choose g hg using fun a => exists_injective_nat (π a)
  exact ((Equiv.sigmaEquivProd Nat Nat).injective.comp <| hf.sigma_map hg).countable

Depends on / 依赖: Equiv.sigmaEquivProd, countable, exists_injective_nat, hf.sigma_map, injective, injective.comp, sigmaEquivProd, sigma_map
-/
instance [Countable α] [forall a, Countable (π a)] : Countable (Sigma π) := by
  rcases exists_injective_nat α with ⟨f, hf⟩
  choose g hg using fun a => exists_injective_nat (π a)
  exact ((Equiv.sigmaEquivProd Nat Nat).injective.comp <| hf.sigma_map hg).countable

/--
lemma `Sigma.uncountable` / 引理 `Sigma.uncountable`

English:
lemma Sigma.uncountable
  given: (a : α) [Uncountable (π a)]
  statement: Uncountable (Sigma π)
  proof: (sigma_mk_injective (i := a)).uncountable

中文:
引理 Sigma.uncountable
  条件: (a : α) [Uncountable (π a)]
  结论: Uncountable (Sigma π)
  证明: (sigma_mk_injective (i := a)).uncountable

Depends on / 依赖: sigma_mk_injective, uncountable
-/
lemma Sigma.uncountable (a : α) [Uncountable (π a)] : Uncountable (Sigma π) :=
  (sigma_mk_injective (i := a)).uncountable

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] [forall a, Uncountable (π a)] : Uncountable (Sigma π)
  body: by
  inhabit α; exact Sigma.uncountable default

中文:
实例 [Nonempty
  签名: α] [对任意 a, Uncountable (π a)] : Uncountable (Sigma π)
  定义体: by
  inhabit α; exact Sigma.uncountable default
-/
instance [Nonempty α] [forall a, Uncountable (π a)] : Uncountable (Sigma π) := by
  inhabit α; exact Sigma.uncountable default

instance (priority := 500) SetCoe.countable [Countable α] (s : Set α) : Countable s :=
  Subtype.countable

end type

section sort

variable {α : Sort u} {β : Sort v} {π : α -> Sort w}


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: α] [Countable β] : Countable (α oplus' β)
  body: Countable.of_equiv (PLift α oplus PLift β) (Equiv.plift.sumPSum Equiv.plift)

中文:
实例 [Countable
  签名: α] [Countable β] : Countable (α oplus' β)
  定义体: Countable.of_equiv (PLift α oplus PLift β) (Equiv.plift.sumPSum Equiv.plift)
-/
instance [Countable α] [Countable β] : Countable (α oplus' β) :=
  Countable.of_equiv (PLift α oplus PLift β) (Equiv.plift.sumPSum Equiv.plift)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: α] [Countable β] : Countable (PProd α β)
  body: Countable.of_equiv (PLift α × PLift β) (Equiv.plift.prodPProd Equiv.plift)

中文:
实例 [Countable
  签名: α] [Countable β] : Countable (PProd α β)
  定义体: Countable.of_equiv (PLift α × PLift β) (Equiv.plift.prodPProd Equiv.plift)

Depends on / 依赖: Countable, Countable.of_equiv, Equiv.plift, Equiv.plift.prodPProd, of_equiv, prodPProd
-/
instance [Countable α] [Countable β] : Countable (PProd α β) :=
  Countable.of_equiv (PLift α × PLift β) (Equiv.plift.prodPProd Equiv.plift)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Countable
  signature: α] [forall a, Countable (π a)] : Countable (PSigma π)
  body: Countable.of_equiv (Σ a : PLift α, PLift (π a.down)) (Equiv.psigmaEquivSigmaPLift π).symm

中文:
实例 [Countable
  签名: α] [对任意 a, Countable (π a)] : Countable (PSigma π)
  定义体: Countable.of_equiv (Σ a : PLift α, PLift (π a.down)) (Equiv.psigmaEquivSigmaPLift π).symm

Depends on / 依赖: Countable, Countable.of_equiv, Equiv.psigmaEquivSigmaPLift, a.down, of_equiv, psigmaEquivSigmaPLift
-/
instance [Countable α] [forall a, Countable (π a)] : Countable (PSigma π) :=
  Countable.of_equiv (Σ a : PLift α, PLift (π a.down)) (Equiv.psigmaEquivSigmaPLift π).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: α] [forall a, Countable (π a)] : Countable (forall a, π a)
  body: by
  have (n : Nat) : Countable (Fin n -> Nat) := by
    induction n with
    | zero => infer_instance
    | succ n ihn => exact Countable.of_equiv (Nat × (Fin n -> Nat)) (Fin.consEquiv fun _ => Nat)
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  have f := fun a => (nonempty_embedding_nat (π a))

中文:
实例 [Finite
  签名: α] [对任意 a, Countable (π a)] : Countable (对任意 a, π a)
  定义体: by
  have (n : Nat) : Countable (Fin n -> Nat) := by
    induction n with
    | zero => infer_instance
    | succ n ihn => exact Countable.of_equiv (Nat × (Fin n -> Nat)) (Fin.consEquiv fun _ => Nat)
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  have f := fun a => (nonempty_embedding_nat (π a))

Depends on / 依赖: Countable, Countable.of_equiv, Embedding, Embedding.piCongrRight, Equiv.piCongrLeft, Fin.consEquiv, Finite, Finite.exists_equiv_fin, consEquiv, countable, exists_equiv_fin, infer_instance, nonempty_embedding_nat, of_equiv, piCongrLeft, piCongrRight, toEmbedding
-/
instance [Finite α] [forall a, Countable (π a)] : Countable (forall a, π a) := by
  have (n : Nat) : Countable (Fin n -> Nat) := by
    induction n with
    | zero => infer_instance
    | succ n ihn => exact Countable.of_equiv (Nat × (Fin n -> Nat)) (Fin.consEquiv fun _ => Nat)
  rcases Finite.exists_equiv_fin α with ⟨n, ⟨e⟩⟩
  have f := fun a => (nonempty_embedding_nat (π a)).some
  exact ((Embedding.piCongrRight f).trans (Equiv.piCongrLeft' _ e).toEmbedding).countable

end sort
