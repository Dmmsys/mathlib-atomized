/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.Group.AddChar

/-!
# Direct sum of additive characters

This file defines the direct sum of additive characters.
-/

@[expose] public section

open Function
open scoped DirectSum

variable {ι R : Type*} {G : ι → Type*} [DecidableEq ι] [∀ i, AddCommGroup (G i)] [CommMonoid R]

namespace AddChar
section DirectSum

/-- Direct sum of additive characters. -/
@[simps!]
/-
**AddChar.directSum** 是 Mathlib 中的一个定义，位于命名空间 `AddChar`。
形式化陈述：directSum (ψ : forall i, AddChar (G i) R) : AddChar (⨁ i, G i) R
参数：ψ : forall i, AddChar (G i) R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Direct sum of additive characters.
-/
def directSum (ψ : ∀ i, AddChar (G i) R) : AddChar (⨁ i, G i) R :=
  toAddMonoidHomEquiv.symm <| DirectSum.toAddMonoid fun i ↦ toAddMonoidHomEquiv (ψ i)
/-
**AddChar.directSum_injective** 是 Mathlib 中的一个引理，位于命名空间 `AddChar`。
形式化陈述：directSum_injective : Injective (directSum : (forall i, AddChar (G i) R) -
> AddChar (⨁ i, G i) R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用引理 `DirectSum.toAddMonoid_injective`：toAddMonoid_injective : Injective (toAd
dMonoid : (forall i, β i ->+ γ) -> (⨁ i, β i) ->+ γ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
-/
lemma directSum_injective :
    Injective (directSum : (∀ i, AddChar (G i) R) → AddChar (⨁ i, G i) R) := by
  refine toAddMonoidHomEquiv.symm.injective.comp <| DirectSum.toAddMonoid_injective.comp ?_
  rintro ψ χ h
  simpa [funext_iff] using h

end DirectSum
end AddChar

