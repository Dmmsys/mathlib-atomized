/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.GroupWithZero.ProdHom
public import Mathlib.Algebra.Order.Group.Equiv
public import Mathlib.Algebra.Order.Monoid.Lex
public import Mathlib.Algebra.Order.Hom.MonoidWithZero
public import Mathlib.Data.Prod.Lex

/-!
# Order homomorphisms for products of linearly ordered groups with zero

This file defines order homomorphisms for products of linearly ordered groups with zero,
which is identified with the `WithZero` of the lexicographic product of the units of the groups.

The product of linearly ordered groups with zero `WithZero (αˣ ×ₗ βˣ)` is a
linearly ordered group with zero itself with natural inclusions but only one projection.
One has to work with the lexicographic product of the units `αˣ ×ₗ βˣ` since otherwise,
the plain product `αˣ × βˣ` would not be linearly ordered.

## TODO

Create the "LinOrdCommGrpWithZero" category.

-/

@[expose] public section

namespace MonoidWithZeroHom

variable {M₀ N₀ : Type*}

set_option backward.isDefEq.respectTransparency false in
/-
**MonoidWithZeroHom.inl_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：inl_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder 
N₀] [DecidablePred fun x : M₀ => x = 0] : Monotone (inl M₀ N₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `WithZero.map'_mono`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOneClass β] {f : α
 →* β}, …
· 使用引理 `MonoidHom.inl_mono`：inl_mono : Monotone (MonoidHom.inl α β)
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
-/
lemma inl_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] : Monotone (inl M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inl_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]
/-
**MonoidWithZeroHom.inl_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`
。
形式化陈述：inl_strictMono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Par
tialOrder N₀] [DecidablePred fun x : M₀ => x = 0] : StrictMono (inl M₀ N₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用引理 `MonoidWithZeroHom.inl_mono`：inl_mono [LinearOrderedCommGroupWithZero M₀]
 [GroupWithZero N₀] [Preorder N₀] [DecidablePred fun x : M₀ => x = 0] : Monotone
 (inl M₀ N₀)
· 使用引理 `MonoidWithZeroHom.inl_injective`：inl_injective [DecidablePred fun x : G₀
 => x = 0] : Function.Injective (inl G₀ H₀)
-/
lemma inl_strictMono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [PartialOrder N₀]
    [DecidablePred fun x : M₀ ↦ x = 0] : StrictMono (inl M₀ N₀) :=
  inl_mono.strictMono_of_injective inl_injective

set_option backward.isDefEq.respectTransparency false in
/-
**MonoidWithZeroHom.inr_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：inr_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero 
N₀] [DecidablePred fun x : N₀ => x = 0] : Monotone (inr M₀ N₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `WithZero.map'_mono`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] [inst_2 : MulOneClass α]   [inst_3 : MulOneClass β] {f : α
 →* β}, …
· 使用引理 `MonoidHom.inr_mono`：inr_mono : Monotone (MonoidHom.inr α β)
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
-/
lemma inr_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ ↦ x = 0] : Monotone (inr M₀ N₀) := by
  refine (WithZero.map'_mono MonoidHom.inr_mono).comp ?_
  intro x y
  obtain rfl | ⟨x, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  obtain rfl | ⟨y, rfl⟩ := GroupWithZero.eq_zero_or_unit y <;>
  · simp [WithZero.withZeroUnitsEquiv]
/-
**MonoidWithZeroHom.inr_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`
。
形式化陈述：inr_strictMono [GroupWithZero M₀] [PartialOrder M₀] [LinearOrderedCommGrou
pWithZero N₀] [DecidablePred fun x : N₀ => x = 0] : StrictMono (inr M₀ N₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用引理 `MonoidWithZeroHom.inr_mono`：inr_mono [GroupWithZero M₀] [Preorder M₀] [L
inearOrderedCommGroupWithZero N₀] [DecidablePred fun x : N₀ => x = 0] : Monotone
 (inr M₀ N₀)
· 使用引理 `MonoidWithZeroHom.inr_injective`：inr_injective [DecidablePred fun x : H₀
 => x = 0] : Function.Injective (inr G₀ H₀)
-/
lemma inr_strictMono [GroupWithZero M₀] [PartialOrder M₀] [LinearOrderedCommGroupWithZero N₀]
    [DecidablePred fun x : N₀ ↦ x = 0] : StrictMono (inr M₀ N₀) :=
  inr_mono.strictMono_of_injective inr_injective
/-
**MonoidWithZeroHom.fst_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：fst_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder 
N₀] : Monotone (fst M₀ N₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithZero.forall`：∀ {α : Type u} {p : WithZero α → Prop}, (∀ (x : WithZer
o α), p x) ↔ p 0 ∧ ∀ (a : α), p ↑a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MonoidWithZeroHom.fst_apply_coe`：∀ {G₀ : Type u_1} {H₀ : Type u_2} [inst
 : GroupWithZero G₀] [inst_1 : GroupWithZero H₀] (x : G₀ˣ × H₀ˣ),   (MonoidWithZ
eroHom.fst G₀ H₀) ↑x …
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma fst_mono [LinearOrderedCommGroupWithZero M₀] [GroupWithZero N₀] [Preorder N₀] :
    Monotone (fst M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp +contextual [WithZero.forall, Prod.le_def]
/-
**MonoidWithZeroHom.snd_mono** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：snd_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero 
N₀] : Monotone (snd M₀ N₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `WithZero.forall`：∀ {α : Type u} {p : WithZero α → Prop}, (∀ (x : WithZer
o α), p x) ↔ p 0 ∧ ∀ (a : α), p ↑a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `WithZero.instIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α], IsBotZeroCl
ass (WithZero α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MonoidWithZeroHom.snd_apply_coe`：∀ {G₀ : Type u_1} {H₀ : Type u_2} [inst
 : GroupWithZero G₀] [inst_1 : GroupWithZero H₀] (x : G₀ˣ × H₀ˣ),   (MonoidWithZ
eroHom.snd G₀ H₀) ↑x …
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma snd_mono [GroupWithZero M₀] [Preorder M₀] [LinearOrderedCommGroupWithZero N₀] :
    Monotone (snd M₀ N₀) := by
  refine WithZero.forall.mpr ?_
  simp [WithZero.forall, Prod.le_def]

end MonoidWithZeroHom

namespace LinearOrderedCommGroupWithZero

variable (α β : Type*) [LinearOrderedCommGroupWithZero α] [LinearOrderedCommGroupWithZero β]

open MonoidWithZeroHom

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
M to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def inl : α →*₀o WithZero (αˣ ×ₗ βˣ) where
  __ := (WithZero.map' (toLexMulEquiv ..).toMonoidHom).comp (inl α β)
  monotone' := by simpa using (WithZero.map'_mono (Prod.Lex.toLex_mono)).comp inl_mono

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given linearly ordered groups with zero M, N, the natural inclusion ordered homomorphism from
N to `WithZero (Mˣ ×ₗ Nˣ)`, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def inr : β →*₀o WithZero (αˣ ×ₗ βˣ) where
  __ := (WithZero.map' (toLexMulEquiv ..).toMonoidHom).comp (inr α β)
  monotone' := by simpa using (WithZero.map'_mono (Prod.Lex.toLex_mono)).comp inr_mono

set_option backward.isDefEq.respectTransparency.types false in
/-- Given linearly ordered groups with zero M, N, the natural projection ordered homomorphism from
`WithZero (Mˣ ×ₗ Nˣ)` to M, which is the linearly ordered group with zero that can be identified
as their product. -/
@[simps!]
nonrec def fst : WithZero (αˣ ×ₗ βˣ) →*₀o α where
  __ := (fst α β).comp (WithZero.map' (toLexMulEquiv (αˣ × βˣ)).symm.toMonoidHom)
  monotone' := by
    -- this can't rely on `Monotone.comp` since `ofLex` is not monotone
    intro x y
    cases x <;>
    cases y
    · simp
    · simp
    · simp
    · simpa using Prod.Lex.monotone_fst _ _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LinearOrderedCommGroupWithZero.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `LinearO
rderedCommGroupWithZero`。
形式化陈述：fst_comp_inl : (fst _ _).comp (inl α β) = .id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderMonoidWithZeroHom.ext`：ext (h : forall a, f a = g a) : f = g
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `LinearOrderedCommGroupWithZero.inl_apply`：∀ (α : Type u_1) (β : Type u_2
) [inst : LinearOrderedCommGroupWithZero α] [inst_1 : LinearOrderedCommGroupWith
Zero β]   (a : α),   (LinearOr…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `LinearOrderedCommGroupWithZero.fst_apply`：∀ (α : Type u_1) (β : Type u_2
) [inst : LinearOrderedCommGroupWithZero α] [inst_1 : LinearOrderedCommGroupWith
Zero β]   (a : WithZero (Lex (…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.inl_apply_unit`：inl_apply_unit [DecidablePred fun x : 
G₀ => x = 0] (x : G₀ˣ) : inl G₀ H₀ x = ((x, (1 : H₀ˣ)) : WithZero (G₀ˣ × H₀ˣ))
· 使用定理 `MonoidWithZeroHom.fst_apply_coe`：∀ {G₀ : Type u_1} {H₀ : Type u_2} [inst
 : GroupWithZero G₀] [inst_1 : GroupWithZero H₀] (x : G₀ˣ × H₀ˣ),   (MonoidWithZ
eroHom.fst G₀ H₀) ↑x …
-/
theorem fst_comp_inl : (fst _ _).comp (inl α β) = .id α := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp

variable {α β}

set_option backward.isDefEq.respectTransparency false in
/-
**LinearOrderedCommGroupWithZero.inl_eq_coe_inl** 是 Mathlib 中的一个引理，位于命名空间 `Linea
rOrderedCommGroupWithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inl_eq_coe_inlₗ {m : α} (hm : m ≠ 0) :
    inl α β m = OrderMonoidHom.inlₗ αˣ βˣ (Units.mk0 _ hm) := by
  lift m to αˣ using isUnit_iff_ne_zero.mpr hm
  simp

set_option backward.isDefEq.respectTransparency false in
/-
**LinearOrderedCommGroupWithZero.inr_eq_coe_inr** 是 Mathlib 中的一个引理，位于命名空间 `Linea
rOrderedCommGroupWithZero`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inr_eq_coe_inrₗ {n : β} (hn : n ≠ 0) :
    inr α β n = OrderMonoidHom.inrₗ αˣ βˣ (Units.mk0 _ hn) := by
  lift n to βˣ using isUnit_iff_ne_zero.mpr hn
  simp
/-
**LinearOrderedCommGroupWithZero.inl_mul_inr_eq_coe_toLex** 是 Mathlib 中的一个定理，位于命
名空间 `LinearOrderedCommGroupWithZero`。
形式化陈述：inl_mul_inr_eq_coe_toLex {m : α} {n : β} (hm : m != 0) (hn : n != 0) : inl
 α β m * inr α β n = toLex (Units.mk0 _ hm, Units.mk0 _ hn)
参数：hm : m != 0；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearOrderedCommGroupWithZero.inl_eq_coe_inlₗ`：inl_eq_coe_inlₗ {m : α} 
(hm : m != 0) : inl α β m = OrderMonoidHom.inlₗ αˣ βˣ (Units.mk0 _ hm)
· 使用引理 `LinearOrderedCommGroupWithZero.inr_eq_coe_inrₗ`：inr_eq_coe_inrₗ {n : β} 
(hn : n != 0) : inr α β n = OrderMonoidHom.inrₗ αˣ βˣ (Units.mk0 _ hn)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.coe_mul`：∀ {α : Type u_1} [inst : Mul α] (a b : α), ↑(a * b) = 
↑a * ↑b
· 使用定理 `OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex`：inlₗ_mul_inrₗ_eq_toLex (m : α) (n
 : β) : inlₗ α β m * inrₗ α β n = toLex (m, n)
-/
theorem inl_mul_inr_eq_coe_toLex {m : α} {n : β} (hm : m ≠ 0) (hn : n ≠ 0) :
    inl α β m * inr α β n = toLex (Units.mk0 _ hm, Units.mk0 _ hn) := by
  rw [inl_eq_coe_inlₗ hm, inr_eq_coe_inrₗ hn,
      ← WithZero.coe_mul, OrderMonoidHom.inlₗ_mul_inrₗ_eq_toLex]

end LinearOrderedCommGroupWithZero

