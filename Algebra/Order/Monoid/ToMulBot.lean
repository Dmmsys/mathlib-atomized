/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop

/-!
Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/

@[expose] public section


universe u

variable {α : Type u}

namespace WithZero

variable [Add α]

/--
Definition of `toMulBot` / `toMulBot` 的定义

English:
definition toMulBot
  signature: : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α)
  body: MulEquiv.refl _

@[simp]

中文:
定义 toMulBot
  签名: : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α)
  定义体: MulEquiv.refl _

@[simp]

Depends on / 依赖: MulEquiv, MulEquiv.refl
-/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _

@[simp]
/--
theorem `toMulBot_zero` / 定理 `toMulBot_zero`

English:
theorem toMulBot_zero
  statement: toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥
  proof: rfl

@[simp]

中文:
定理 toMulBot_zero
  结论: toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥
  证明: rfl

@[simp]
-/
theorem toMulBot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl

@[simp]
/--
theorem `toMulBot_coe` / 定理 `toMulBot_coe`

English:
theorem toMulBot_coe
  given: (x : Multiplicative α)
  proof: rfl

@[simp]

中文:
定理 toMulBot_coe
  条件: (x : Multiplicative α)
  证明: rfl

@[simp]
-/
theorem toMulBot_coe (x : Multiplicative α) :
    toMulBot ↑x = Multiplicative.ofAdd (↑x.toAdd : WithBot α) :=
  rfl

@[simp]
/--
theorem `toMulBot_symm_bot` / 定理 `toMulBot_symm_bot`

English:
theorem toMulBot_symm_bot
  statement: toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0
  proof: rfl

@[simp]

中文:
定理 toMulBot_symm_bot
  结论: toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0
  证明: rfl

@[simp]
-/
theorem toMulBot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl

@[simp]
/--
theorem `toMulBot_coe_ofAdd` / 定理 `toMulBot_coe_ofAdd`

English:
theorem toMulBot_coe_ofAdd
  given: (x : α)
  proof: rfl

中文:
定理 toMulBot_coe_ofAdd
  条件: (x : α)
  证明: rfl
-/
theorem toMulBot_coe_ofAdd (x : α) :
    toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl

variable [Preorder α] (a b : WithZero (Multiplicative α))

/--
theorem `toMulBot_strictMono` / 定理 `toMulBot_strictMono`

English:
theorem toMulBot_strictMono
  statement: StrictMono (@toMulBot α _)
  proof: fun _ _ => id

@[simp]

中文:
定理 toMulBot_strictMono
  结论: StrictMono (@toMulBot α _)
  证明: fun _ _ => id

@[simp]
-/
theorem toMulBot_strictMono : StrictMono (@toMulBot α _) := fun _ _ => id

@[simp]
/--
theorem `toMulBot_le` / 定理 `toMulBot_le`

English:
theorem toMulBot_le
  statement: toMulBot a <= toMulBot b ↔ a <= b
  proof: Iff.rfl

@[simp]

中文:
定理 toMulBot_le
  结论: toMulBot a <= toMulBot b ↔ a <= b
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem toMulBot_le : toMulBot a <= toMulBot b ↔ a <= b :=
  Iff.rfl

@[simp]
/--
theorem `toMulBot_lt` / 定理 `toMulBot_lt`

English:
theorem toMulBot_lt
  statement: toMulBot a < toMulBot b ↔ a < b
  proof: Iff.rfl

中文:
定理 toMulBot_lt
  结论: toMulBot a < toMulBot b ↔ a < b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem toMulBot_lt : toMulBot a < toMulBot b ↔ a < b :=
  Iff.rfl

end WithZero
