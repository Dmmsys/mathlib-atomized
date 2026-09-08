/-
Copyright (c) 2021 Peter Nelson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Nelson, Yaël Dillies
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Order
public import Mathlib.Data.Set.Finite.Basic  -- shake: keep (IsAtomic α), cf. lean#13417
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Atoms

import Mathlib.Data.Finite.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Order structures on finite types

This file provides order instances on fintypes.

## Computable instances

On a `Fintype`, we can construct
* an `OrderBot` from `SemilatticeInf`.
* an `OrderTop` from `SemilatticeSup`.
* a `BoundedOrder` from `Lattice`.

Those are marked as `def` to avoid defeqness issues.

## Completion instances

Those instances are noncomputable because the definitions of `sSup` and `sInf` use `Set.toFinset`
and set membership is undecidable in general.

On a `Fintype`, we can promote:
* a `Lattice` to a `CompleteLattice`.
* a `DistribLattice` to a `CompleteDistribLattice`.
* a `LinearOrder` to a `CompleteLinearOrder`.
* a `BooleanAlgebra` to a `CompleteAtomicBooleanAlgebra`.

Those are marked as `def` to avoid typeclass loops.

## Concrete instances

We provide a few instances for concrete types:
* `Fin.completeLinearOrder`
* `Bool.completeLinearOrder`
* `Bool.completeBooleanAlgebra`
-/

public section


open Finset

namespace Fintype

variable {ι α : Type*} [Fintype ι] [Fintype α]

section Nonempty

variable (α) [Nonempty α]

-- See note [reducible non-instances]
/-- Constructs the `⊥` of a finite nonempty `SemilatticeInf`. -/
/-
**Fintype.toOrderBot** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toOrderBot [SemilatticeInf α] : OrderBot α where bot
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty

--- 原说明 ---
Constructs the `⊥` of a finite nonempty `SemilatticeInf`.
-/
abbrev toOrderBot [SemilatticeInf α] : OrderBot α where
  bot := univ.inf' univ_nonempty id
  bot_le a := inf'_le _ <| mem_univ a

-- See note [reducible non-instances]
/-- Constructs the `⊤` of a finite nonempty `SemilatticeSup` -/
/-
**Fintype.toOrderTop** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toOrderTop [SemilatticeSup α] : OrderTop α where top
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.univ_nonempty`：univ_nonempty [Nonempty α] : (univ : Finset α).Non
empty

--- 原说明 ---
Constructs the `⊤` of a finite nonempty `SemilatticeSup`
-/
abbrev toOrderTop [SemilatticeSup α] : OrderTop α where
  top := univ.sup' univ_nonempty id
  le_top a := le_sup' id <| mem_univ a

-- See note [reducible non-instances]
/-- Constructs the `⊤` and `⊥` of a finite nonempty `Lattice`. -/
/-
**Fintype.toBoundedOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toBoundedOrder [Lattice α] : BoundedOrder α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs the `⊤` and `⊥` of a finite nonempty `Lattice`.
-/
abbrev toBoundedOrder [Lattice α] : BoundedOrder α :=
  { toOrderBot α, toOrderTop α with }

end Nonempty

section BoundedOrder

variable (α)

open scoped Classical in
-- See note [reducible non-instances]
/-- A finite bounded lattice is complete. -/
/-
**Fintype.toCompleteLattice** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toCompleteLattice [Lattice α] [BoundedOrder α] : CompleteLattice α where _
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite bounded lattice is complete.
-/
noncomputable abbrev toCompleteLattice [Lattice α] [BoundedOrder α] : CompleteLattice α where
  __ := ‹Lattice α›
  __ := ‹BoundedOrder α›
  sSup := fun s => s.toFinset.sup id
  sInf := fun s => s.toFinset.inf id
  isLUB_sSup s := Set.coe_toFinset s ▸ Finset.isLUB_sup_id
  isGLB_sInf s := Set.coe_toFinset s ▸ Finset.isGLB_inf_id

attribute [local instance] toCompleteLattice in
-- See note [reducible non-instances]
/-- A finite bounded distributive lattice is completely distributive. -/
/-
**Fintype.toCompleteDistribLatticeMinimalAxioms** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fin
type`。
形式化陈述：toCompleteDistribLatticeMinimalAxioms [DistribLattice α] [BoundedOrder α] 
: CompleteDistribLattice.MinimalAxioms α where iInf_sup_le_sup_sInf
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite bounded distributive lattice is completely distributive.
-/
noncomputable abbrev toCompleteDistribLatticeMinimalAxioms [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice.MinimalAxioms α where
  iInf_sup_le_sup_sInf := fun a s => by
    convert! (Finset.inf_sup_distrib_left s.toFinset id a).ge using 1
    rw [Finset.inf_eq_iInf]
    simp_rw [Set.mem_toFinset]
    rfl
  inf_sSup_le_iSup_inf := fun a s => by
    convert! (Finset.sup_inf_distrib_left s.toFinset id a).le using 1
    rw [Finset.sup_eq_iSup]
    simp_rw [Set.mem_toFinset]
    rfl

attribute [local instance] toCompleteLattice in
-- See note [reducible non-instances]
/-- A finite bounded distributive lattice is completely distributive. -/
/-
**Fintype.toCompleteDistribLattice** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toCompleteDistribLattice [DistribLattice α] [BoundedOrder α] : CompleteDis
tribLattice α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite bounded distributive lattice is completely distributive.
-/
noncomputable abbrev toCompleteDistribLattice [DistribLattice α] [BoundedOrder α] :
    CompleteDistribLattice α := .ofMinimalAxioms (toCompleteDistribLatticeMinimalAxioms _)

-- See note [reducible non-instances]
/-- A finite bounded linear order is complete.

If the `α` is already a `BiheytingAlgebra`, then prefer to construct this instance manually using
`Fintype.toCompleteLattice` instead, to avoid creating a diamond with
`LinearOrder.toBiheytingAlgebra`. -/
/-
**Fintype.toCompleteLinearOrder** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toCompleteLinearOrder [LinearOrder α] [BoundedOrder α] : CompleteLinearOrd
er α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BiheytingAlgebra.sdiff_le_iff`：∀ {α : Type u_4} [self : BiheytingAlgebra
 α] (a b c : α), a \ b ≤ c ↔ a ≤ b ⊔ c
· 使用定理 `BiheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : BiheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a
· 使用定理 `LinearOrder.le_total`：∀ {α : Type u_2} [self : LinearOrder α] (a b : α),
 a ≤ b ∨ b ≤ a
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b

--- 原说明 ---
A finite bounded linear order is complete.

If the `α` is already a `BiheytingAlgebra`, then prefer to construct this instan
ce manually using
`Fintype.toCompleteLattice` instead, to avoid creating a diamond with
`LinearOrder.toBiheytingAlgebra`.
-/
noncomputable abbrev toCompleteLinearOrder
    [LinearOrder α] [BoundedOrder α] : CompleteLinearOrder α :=
  { toCompleteLattice α, ‹LinearOrder α›, LinearOrder.toBiheytingAlgebra _ with }

-- See note [reducible non-instances]
/-- A finite Boolean algebra is complete. -/
/-
**Fintype.toCompleteBooleanAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toCompleteBooleanAlgebra [BooleanAlgebra α] : CompleteBooleanAlgebra α whe
re __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BooleanAlgebra.le_top`：∀ {α : Type u} [self : BooleanAlgebra α] (a : α),
 a ≤ ⊤
· 使用定理 `BooleanAlgebra.bot_le`：∀ {α : Type u} [self : BooleanAlgebra α] (a : α),
 ⊥ ≤ a
· 使用定理 `BooleanAlgebra.inf_compl_le_bot`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), x ⊓ xᶜ ≤ ⊥
· 使用定理 `BooleanAlgebra.top_le_sup_compl`：∀ {α : Type u} [self : BooleanAlgebra α
] (x : α), ⊤ ≤ x ⊔ xᶜ
· 使用定理 `BooleanAlgebra.sdiff_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y :
 α), x \ y = x ⊓ yᶜ
· 使用定理 `BooleanAlgebra.himp_eq`：∀ {α : Type u} [self : BooleanAlgebra α] (x y : 
α), x ⇨ y = y ⊔ xᶜ

--- 原说明 ---
A finite Boolean algebra is complete.
-/
noncomputable abbrev toCompleteBooleanAlgebra [BooleanAlgebra α] : CompleteBooleanAlgebra α where
  __ := ‹BooleanAlgebra α›
  __ := Fintype.toCompleteDistribLattice α

-- See note [reducible non-instances]
/-- A finite Boolean algebra is complete and atomic. -/
/-
**Fintype.toCompleteAtomicBooleanAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toCompleteAtomicBooleanAlgebra [BooleanAlgebra α] : CompleteAtomicBooleanA
lgebra α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A finite Boolean algebra is complete and atomic.
-/
noncomputable abbrev toCompleteAtomicBooleanAlgebra [BooleanAlgebra α] :
    CompleteAtomicBooleanAlgebra α :=
  (toCompleteBooleanAlgebra α).toCompleteAtomicBooleanAlgebra

end BoundedOrder

section Nonempty

variable (α) [Nonempty α]

-- See note [reducible non-instances]
/-- A nonempty finite lattice is complete. If the lattice is already a `BoundedOrder`, then use
`Fintype.toCompleteLattice` instead, as this gives definitional equality for `⊥` and `⊤`. -/
/-
**Fintype.toCompleteLatticeOfNonempty** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toCompleteLatticeOfNonempty [Lattice α] : CompleteLattice α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonempty finite lattice is complete. If the lattice is already a `BoundedOrder
`, then use
`Fintype.toCompleteLattice` instead, as this gives definitional equality for `⊥`
 and `⊤`.
-/
noncomputable abbrev toCompleteLatticeOfNonempty [Lattice α] : CompleteLattice α :=
  @toCompleteLattice _ _ _ <| toBoundedOrder α

-- See note [reducible non-instances]
/-- A nonempty finite linear order is complete. If the linear order is already a `BoundedOrder`,
then use `Fintype.toCompleteLinearOrder` instead, as this gives definitional equality for `⊥` and
`⊤`. -/
/-
**Fintype.toCompleteLinearOrderOfNonempty** 是 Mathlib 中的一个缩写定义，位于命名空间 `Fintype`。
形式化陈述：toCompleteLinearOrderOfNonempty [LinearOrder α] : CompleteLinearOrder α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonempty finite linear order is complete. If the linear order is already a `Bo
undedOrder`,
then use `Fintype.toCompleteLinearOrder` instead, as this gives definitional equ
ality for `⊥` and
`⊤`.
-/
noncomputable abbrev toCompleteLinearOrderOfNonempty [LinearOrder α] : CompleteLinearOrder α :=
  @toCompleteLinearOrder _ _ _ <| toBoundedOrder α

end Nonempty

end Fintype

/-! ### Concrete instances -/

/-
**Fin.completeLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Fin.completeLinearOrder {n : Nat} [NeZero n] : CompleteLinearOrder (Fin n)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Concrete instances
-/
noncomputable instance Fin.completeLinearOrder {n : ℕ} [NeZero n] : CompleteLinearOrder (Fin n) :=
  Fintype.toCompleteLinearOrder _
/-
**Bool.completeBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.completeBooleanAlgebra : CompleteBooleanAlgebra Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Bool.completeBooleanAlgebra : CompleteBooleanAlgebra Bool :=
  Fintype.toCompleteBooleanAlgebra _
/-
**Bool.completeLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.completeLinearOrder : CompleteLinearOrder Bool where __
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BiheytingAlgebra.sdiff_le_iff`：∀ {α : Type u_4} [self : BiheytingAlgebra
 α] (a b c : α), a \ b ≤ c ↔ a ≤ b ⊔ c
· 使用定理 `BiheytingAlgebra.top_sdiff`：∀ {α : Type u_4} [self : BiheytingAlgebra α]
 (a : α), ⊤ \ a = ￢a
· 使用定理 `LinearOrder.le_total`：∀ {α : Type u_2} [self : LinearOrder α] (a b : α),
 a ≤ b ∨ b ≤ a
· 使用定理 `LinearOrder.compare_eq_compareOfLessAndEq`：∀ {α : Type u_2} [self : Line
arOrder α] (a b : α), compare a b = compareOfLessAndEq a b
-/
noncomputable instance Bool.completeLinearOrder : CompleteLinearOrder Bool where
  __ := Fintype.toCompleteLattice _
  __ : BiheytingAlgebra Bool := inferInstance
  __ : LinearOrder Bool := inferInstance
/-
**Bool.completeAtomicBooleanAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Bool.completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Bool
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance Bool.completeAtomicBooleanAlgebra : CompleteAtomicBooleanAlgebra Bool :=
  Fintype.toCompleteAtomicBooleanAlgebra _

/-! ### Directed Orders -/

section DirectedOrders

variable {ι : Sort*} {α : Type*} {r : α → α → Prop} [IsTrans α r] {γ : Type*} [Nonempty γ]
  {f : γ → α} [Finite ι]

/-
**Directed.finite_set_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Directed.finite_set_le (D : Directed r f) {s : Set γ} (hs : s.Finite) : ex
ists z, forall i in s, r (f i) (f z)
参数：D : Directed r f；hs : s.Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.mem_toFinset`：∀ {α : Type u} {s : Set α} {a : α} (hs : s.Fini
te), a ∈ hs.toFinset ↔ a ∈ s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Directed.finset_le`：Directed.finset_le {r : α -> α -> Prop} [IsTrans α r
] {ι} [hι : Nonempty ι] {f : ι -> α} (D : Directed r f) (s : Finset ι) : exists 
z, foral…
-/
theorem Directed.finite_set_le (D : Directed r f) {s : Set γ} (hs : s.Finite) :
    ∃ z, ∀ i ∈ s, r (f i) (f z) := by
  convert! D.finset_le hs.toFinset using 3; rw [Set.Finite.mem_toFinset]
/-
**Directed.finite_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Directed.finite_le {ι κ : Sort*} [Nonempty ι] [Finite κ] {f : ι -> α} (hf 
: Directed r f) (g : κ -> ι) : exists z, forall i, r (f (g i)) (f z)
参数：hf : Directed r f；g : κ -> ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Directed.finite_set_le`：Directed.finite_set_le (D : Directed r f) {s : S
et γ} (hs : s.Finite) : exists z, forall i in s, r (f i) (f z)
· 使用定理 `PLift.instNonempty_mathlib`：∀ {α : Sort u} [Nonempty α], Nonempty (PLift
 α)
· 使用定理 `Directed.comp_of_surjective`：∀ {α : Type u_1} {ι : Sort u_3} {κ : Sort u
_4} {r : α → α → Prop} {f : ι → κ},   Function.Surjective f → ∀ {g : κ → α}, Dir
ected r g → Direc…
· 使用定理 `PLift.down_surjective`：down_surjective : Surjective (@down α)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
-/
lemma Directed.finite_le {ι κ : Sort*} [Nonempty ι] [Finite κ] {f : ι → α} (hf : Directed r f)
    (g : κ → ι) : ∃ z, ∀ i, r (f (g i)) (f z) := by
  simpa using
    (hf.comp_of_surjective PLift.down_surjective).finite_set_le (Set.finite_range (PLift.up ∘ g))

variable [Nonempty α] [Preorder α]
/-
**Finite.exists_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.exists_le [IsDirectedOrder α] (f : ι -> α) : exists M, forall i, f 
i <= M
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Directed.finite_le`：Directed.finite_le {ι κ : Sort*} [Nonempty ι] [Finit
e κ] {f : ι -> α} (hf : Directed r f) (g : κ -> ι) : exists z, forall i, r (f (g
 i)) (f …
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `directed_id`：directed_id [IsDirected α r] : Directed r id
-/
theorem Finite.exists_le [IsDirectedOrder α] (f : ι → α) : ∃ M, ∀ i, f i ≤ M :=
  directed_id.finite_le _
/-
**Finite.exists_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.exists_ge [IsCodirectedOrder α] (f : ι -> α) : exists M, forall i, 
M <= f i
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Directed.finite_le`：Directed.finite_le {ι κ : Sort*} [Nonempty ι] [Finit
e κ] {f : ι -> α} (hf : Directed r f) (g : κ -> ι) : exists z, forall i, r (f (g
 i)) (f …
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `directed_id`：directed_id [IsDirected α r] : Directed r id
-/
theorem Finite.exists_ge [IsCodirectedOrder α] (f : ι → α) : ∃ M, ∀ i, M ≤ f i :=
  directed_id.finite_le (r := (· ≥ ·)) _
/-
**Set.Finite.exists_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.exists_le [IsDirectedOrder α] {s : Set α} (hs : s.Finite) : exi
sts M, forall i in s, i <= M
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Directed.finite_set_le`：Directed.finite_set_le (D : Directed r f) {s : S
et γ} (hs : s.Finite) : exists z, forall i in s, r (f i) (f z)
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `directed_id`：directed_id [IsDirected α r] : Directed r id
-/
theorem Set.Finite.exists_le [IsDirectedOrder α] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, i ≤ M :=
  directed_id.finite_set_le hs
/-
**Set.Finite.exists_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.Finite.exists_ge [IsCodirectedOrder α] {s : Set α} (hs : s.Finite) : e
xists M, forall i in s, M <= i
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Directed.finite_set_le`：Directed.finite_set_le (D : Directed r f) {s : S
et γ} (hs : s.Finite) : exists z, forall i in s, r (f i) (f z)
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
· 使用定理 `directed_id`：directed_id [IsDirected α r] : Directed r id
-/
theorem Set.Finite.exists_ge [IsCodirectedOrder α] {s : Set α} (hs : s.Finite) :
    ∃ M, ∀ i ∈ s, M ≤ i :=
  directed_id.finite_set_le (r := (· ≥ ·)) hs

@[simp]
/-
**Finite.bddAbove_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.bddAbove_range [IsDirectedOrder α] (f : ι -> α) : BddAbove (Set.ran
ge f)
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_le`：Finite.exists_le [IsDirectedOrder α] (f : ι -> α) : ex
ists M, forall i, f i <= M
-/
theorem Finite.bddAbove_range [IsDirectedOrder α] (f : ι → α) : BddAbove (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_le f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

@[simp]
/-
**Finite.bddBelow_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.bddBelow_range [IsCodirectedOrder α] (f : ι -> α) : BddBelow (Set.r
ange f)
参数：f : ι -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.exists_ge`：Finite.exists_ge [IsCodirectedOrder α] (f : ι -> α) : 
exists M, forall i, M <= f i
-/
theorem Finite.bddBelow_range [IsCodirectedOrder α] (f : ι → α) : BddBelow (Set.range f) := by
  obtain ⟨M, hM⟩ := Finite.exists_ge f
  refine ⟨M, fun a ha => ?_⟩
  obtain ⟨b, rfl⟩ := ha
  exact hM b

end DirectedOrders

section
variable {ι : Sort*} {α : Type*} [CompleteLattice α] {s : Set α} {a : α} {f : ι → α}

/-
**le_iSup_iff_of_directed** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_iSup_iff_of_directed [Nonempty ι] [Finite ι] (hf : Directed (· <= ·) f)
 : a <= ⨆ i, f i ↔ exists i, a <= f i where mp ha
参数：hf : Directed (· <= ·) f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Directed.finite_le`：Directed.finite_le {ι κ : Sort*} [Nonempty ι] [Finit
e κ] {f : ι -> α} (hf : Directed r f) (g : κ -> ι) : exists z, forall i, r (f (g
 i)) (f …
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `le_iSup_of_le`：le_iSup_of_le (i : ι) (h : a <= f i) : a <= iSup f
-/
lemma le_iSup_iff_of_directed [Nonempty ι] [Finite ι] (hf : Directed (· ≤ ·) f) :
    a ≤ ⨆ i, f i ↔ ∃ i, a ≤ f i where
  mp ha := by obtain ⟨i, hi⟩ := hf.finite_le id; exact ⟨i, ha.trans <| iSup_le hi⟩
  mpr := by rintro ⟨i, hai⟩; exact le_iSup_of_le i hai
/-
**le_sSup_iff_of_directedOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_sSup_iff_of_directedOn (hs : s.Nonempty) (hs' : s.Finite) (hs'' : Direc
tedOn (· <= ·) s) : a <= sSup s ↔ exists b in s, a <= b
参数：hs : s.Nonempty；hs' : s.Finite；hs'' : DirectedOn (· <= ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用引理 `le_iSup_iff_of_directed`：le_iSup_iff_of_directed [Nonempty ι] [Finite ι]
 (hf : Directed (· <= ·) f) : a <= ⨆ i, f i ↔ exists i, a <= f i where mp ha
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_sSup_iff_of_directedOn (hs : s.Nonempty) (hs' : s.Finite) (hs'' : DirectedOn (· ≤ ·) s) :
    a ≤ sSup s ↔ ∃ b ∈ s, a ≤ b := by
  have := hs.to_subtype
  have := hs'.to_subtype
  simp [sSup_eq_iSup', le_iSup_iff_of_directed hs''.directed_val]

end

namespace Set
variable {ι : Sort*} {α : Type*} {S : Set (Set α)} {s : Set α} {f : ι → Set α}

/-
**Set.subset_iUnion_iff_of_directed** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_iUnion_iff_of_directed [Nonempty ι] [Finite ι] (hf : Directed (· <=
 ·) f) : s subseteq ⋃ i, f i ↔ exists i, s subseteq f i
参数：hf : Directed (· <= ·) f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_iSup_iff_of_directed`：le_iSup_iff_of_directed [Nonempty ι] [Finite ι]
 (hf : Directed (· <= ·) f) : a <= ⨆ i, f i ↔ exists i, a <= f i where mp ha
-/
lemma subset_iUnion_iff_of_directed [Nonempty ι] [Finite ι] (hf : Directed (· ≤ ·) f) :
    s ⊆ ⋃ i, f i ↔ ∃ i, s ⊆ f i := le_iSup_iff_of_directed hf
/-
**Set.subset_sUnion_iff_of_directed** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：subset_sUnion_iff_of_directed (hS : S.Nonempty) (hS' : S.Finite) (hS'' : D
irectedOn (· <= ·) S) : s subseteq sSup S ↔ exists t in S, s subseteq t
参数：hS : S.Nonempty；hS' : S.Finite；hS'' : DirectedOn (· <= ·) S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_sSup_iff_of_directedOn`：le_sSup_iff_of_directedOn (hs : s.Nonempty) (
hs' : s.Finite) (hs'' : DirectedOn (· <= ·) s) : a <= sSup s ↔ exists b in s, a 
<= b
-/
lemma subset_sUnion_iff_of_directed (hS : S.Nonempty) (hS' : S.Finite)
    (hS'' : DirectedOn (· ≤ ·) S) : s ⊆ sSup S ↔ ∃ t ∈ S, s ⊆ t :=
  le_sSup_iff_of_directedOn hS hS' hS''

end Set

/-!
### Suprema and infima over finite types

We state simplified versions of `le_ciSup_if_le` and `ciSup_mono` when the indexing type
is finite. This avoids having to explicitly use `Finite.bddAbove_range`.

Similarly for `ciInf`.
-/

section ciSup

namespace Finite

section CCL

variable {α ι ι' : Type*} [Finite ι] [Finite ι'] [ConditionallyCompleteLattice α]

/-
**Finite.le_ciSup_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : a <= f c) : a <= iSup f
参数：c : ι；h : a <= f c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_ciSup_of_le`：le_ciSup_of_le {f : ι -> α} (H : BddAbove (range f)) (c 
: ι) (h : a <= f c) : a <= iSup f
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
lemma le_ciSup_of_le {a : α} {f : ι → α} (c : ι) (h : a ≤ f c) : a ≤ iSup f :=
  _root_.le_ciSup_of_le (bddAbove_range f) c h
/-
**Finite.ciInf_le_of_le** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：ciInf_le_of_le {a : α} {f : ι -> α} (c : ι) (h : f c <= a) : iInf f <= a
参数：c : ι；h : f c <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_le_of_le`：ciInf_le_of_le {f : ι -> α} (H : BddBelow (range f)) (c 
: ι) (h : f c <= a) : iInf f <= a
· 使用定理 `Finite.bddBelow_range`：Finite.bddBelow_range [IsCodirectedOrder α] (f : 
ι -> α) : BddBelow (Set.range f)
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
-/
lemma ciInf_le_of_le {a : α} {f : ι → α} (c : ι) (h : f c ≤ a) : iInf f ≤ a :=
  _root_.ciInf_le_of_le (bddBelow_range f) c h
/-
**Finite.ciSup_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：ciSup_mono {f g : ι -> α} (H : forall (x : ι), f x <= g x) : iSup f <= iSu
p g
参数：H : forall (x : ι), f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciSup_mono`：ciSup_mono {f g : ι -> α} (B : BddAbove (range g)) (H : fora
ll x, f x <= g x) : iSup f <= iSup g
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
lemma ciSup_mono {f g : ι → α} (H : ∀ (x : ι), f x ≤ g x) : iSup f ≤ iSup g :=
  _root_.ciSup_mono (bddAbove_range g) H
/-
**Finite.ciInf_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：ciInf_mono {f g : ι -> α} (H : forall (x : ι), f x <= g x) : iInf f <= iIn
f g
参数：H : forall (x : ι), f x <= g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ciInf_mono`：ciInf_mono {f g : ι -> α} (B : BddBelow (range f)) (H : fora
ll x, f x <= g x) : iInf f <= iInf g
· 使用定理 `Finite.bddBelow_range`：Finite.bddBelow_range [IsCodirectedOrder α] (f : 
ι -> α) : BddBelow (Set.range f)
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `SemilatticeInf.instIsCodirectedOrder`：∀ {α : Type u_1} [inst : Semilatti
ceInf α], IsCodirectedOrder α
-/
lemma ciInf_mono {f g : ι → α} (H : ∀ (x : ι), f x ≤ g x) : iInf f ≤ iInf g :=
  _root_.ciInf_mono (bddBelow_range f) H
/-
**Finite.le_ciSup** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：le_ciSup (f : ι -> α) (i : ι) : f i <= ⨆ j, f j
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma le_ciSup (f : ι → α) (i : ι) : f i ≤ ⨆ j, f j :=
  le_ciSup_of_le i le_rfl
/-
**Finite.ciInf_le** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：ciInf_le (f : ι -> α) (i : ι) : ⨅ j, f j <= f i
参数：f : ι -> α；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.le_ciSup`：le_ciSup (f : ι -> α) (i : ι) : f i <= ⨆ j, f j
-/
lemma ciInf_le (f : ι → α) (i : ι) : ⨅ j, f j ≤ f i :=
  le_ciSup (α := αᵒᵈ) f i
/-
**Finite.ciSup_sup** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：ciSup_sup [Nonempty ι] {f : ι -> α} {a : α} : (⨆ i, f i) ⊔ a = ⨆ i, f i ⊔ 
a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `sup_le_sup_right`：sup_le_sup_right (h₁ : a <= b) (c) : a ⊔ c <= b ⊔ c
· 使用引理 `Finite.le_ciSup`：le_ciSup (f : ι -> α) (i : ι) : f i <= ⨆ j, f j
-/
lemma ciSup_sup [Nonempty ι] {f : ι → α} {a : α} :
    (⨆ i, f i) ⊔ a = ⨆ i, f i ⊔ a := by
  refine le_antisymm (sup_le ?_ ?_) <| ciSup_le fun i ↦ sup_le_sup_right (le_ciSup f i) a
  · exact ciSup_le fun i ↦ le_ciSup_of_le i le_sup_left
  · exact le_ciSup_of_le (Classical.arbitrary ι) le_sup_right
/-
**Finite.ciInf_inf** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：ciInf_inf [Nonempty ι] {f : ι -> α} {a : α} : (⨅ i, f i) ⊓ a = ⨅ i, f i ⊓ 
a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.ciSup_sup`：ciSup_sup [Nonempty ι] {f : ι -> α} {a : α} : (⨆ i, f 
i) ⊔ a = ⨆ i, f i ⊔ a
-/
lemma ciInf_inf [Nonempty ι] {f : ι → α} {a : α} :
    (⨅ i, f i) ⊓ a = ⨅ i, f i ⊓ a :=
  ciSup_sup (α := αᵒᵈ) ..
/-
**Finite.ciSup_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：ciSup_prod (f : ι × ι' -> α) : ⨆ a, f a = ⨆ i, ⨆ i', f (i, i')
参数：f : ι × ι' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ciSup_prod`：ciSup_prod {f : β × γ -> α} (hf : BddAbove (Set.range f)) : 
⨆ p, f p = ⨆ b, ⨆ c, f (b, c)
· 使用定理 `Finite.bddAbove_range`：Finite.bddAbove_range [IsDirectedOrder α] (f : ι 
-> α) : BddAbove (Set.range f)
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `supSet_to_nonempty`：∀ (α : Type u_1) [SupSet α], Nonempty α
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
-/
lemma ciSup_prod (f : ι × ι' → α) :
    ⨆ a, f a = ⨆ i, ⨆ i', f (i, i') :=
  _root_.ciSup_prod (bddAbove_range f)
/-
**Finite.ciInf_prod** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：ciInf_prod (f : ι × ι' -> α) : ⨅ a, f a = ⨅ i, ⨅ i', f (i, i')
参数：f : ι × ι' -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.ciSup_prod`：ciSup_prod (f : ι × ι' -> α) : ⨆ a, f a = ⨆ i, ⨆ i', 
f (i, i')
-/
lemma ciInf_prod (f : ι × ι' → α) :
    ⨅ a, f a = ⨅ i, ⨅ i', f (i, i') :=
  ciSup_prod (α := αᵒᵈ) f

end CCL

section CCLO

variable {α β ι : Type*} [ConditionallyCompleteLinearOrder α] [ConditionallyCompleteLattice β]
  [Finite ι] [Nonempty ι]

/-
**Finite.map_iSup_of_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：map_iSup_of_monotoneOn {s : Set α} {f : ι -> α} {g : α -> β} (hg : Monoton
eOn g s) (hs : forall i, f i in s) : g (⨆ i, f i) = ⨆ i, g (f i)
参数：hg : MonotoneOn g s；hs : forall i, f i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_ciSup_of_finite`：exists_eq_ciSup_of_finite [Nonempty ι] [Finit
e ι] {f : ι -> α} : exists i, f i = ⨆ i, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finite.le_ciSup_of_le`：le_ciSup_of_le {a : α} {f : ι -> α} (c : ι) (h : 
a <= f c) : a <= iSup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `ciSup_le`：ciSup_le [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, f x 
<= c) : iSup f <= c
· 使用引理 `Finite.le_ciSup`：le_ciSup (f : ι -> α) (i : ι) : f i <= ⨆ j, f j
-/
lemma map_iSup_of_monotoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : MonotoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨆ i, f i) = ⨆ i, g (f i) := by
  obtain ⟨j, hj⟩ : ∃ j, f j = ⨆ i, f i := exists_eq_ciSup_of_finite
  rw [← hj]
  exact le_antisymm (le_ciSup_of_le j le_rfl) <|
    ciSup_le fun i ↦ hg (hs i) (hs j) (hj ▸ le_ciSup f i)
/-
**Finite.map_iInf_of_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：map_iInf_of_monotoneOn {s : Set α} {f : ι -> α} {g : α -> β} (hg : Monoton
eOn g s) (hs : forall i, f i in s) : g (⨅ i, f i) = ⨅ i, g (f i)
参数：hg : MonotoneOn g s；hs : forall i, f i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.map_iSup_of_monotoneOn`：map_iSup_of_monotoneOn {s : Set α} {f : ι
 -> α} {g : α -> β} (hg : MonotoneOn g s) (hs : forall i, f i in s) : g (⨆ i, f 
i) = ⨆ i, g (f i)
-/
lemma map_iInf_of_monotoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : MonotoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨅ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotoneOn (α := αᵒᵈ) (β := βᵒᵈ) (fun _ hi _ hj h ↦ hg hj hi h) hs
/-
**Finite.map_iSup_of_antitoneOn** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：map_iSup_of_antitoneOn {s : Set α} {f : ι -> α} {g : α -> β} (hg : Antiton
eOn g s) (hs : forall i, f i in s) : g (⨆ i, f i) = ⨅ i, g (f i)
参数：hg : AntitoneOn g s；hs : forall i, f i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.map_iSup_of_monotoneOn`：map_iSup_of_monotoneOn {s : Set α} {f : ι
 -> α} {g : α -> β} (hg : MonotoneOn g s) (hs : forall i, f i in s) : g (⨆ i, f 
i) = ⨆ i, g (f i)
-/
lemma map_iSup_of_antitoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : AntitoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨆ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotoneOn (β := βᵒᵈ) hg hs
/-
**Finite.map_iInf_of_antitoneOn** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：map_iInf_of_antitoneOn {s : Set α} {f : ι -> α} {g : α -> β} (hg : Antiton
eOn g s) (hs : forall i, f i in s) : g (⨅ i, f i) = ⨆ i, g (f i)
参数：hg : AntitoneOn g s；hs : forall i, f i in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.map_iInf_of_monotoneOn`：map_iInf_of_monotoneOn {s : Set α} {f : ι
 -> α} {g : α -> β} (hg : MonotoneOn g s) (hs : forall i, f i in s) : g (⨅ i, f 
i) = ⨅ i, g (f i)
-/
lemma map_iInf_of_antitoneOn {s : Set α} {f : ι → α} {g : α → β} (hg : AntitoneOn g s)
    (hs : ∀ i, f i ∈ s) :
    g (⨅ i, f i) = ⨆ i, g (f i) :=
  map_iInf_of_monotoneOn (β := βᵒᵈ) hg hs
/-
**Finite.map_iSup_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：map_iSup_of_monotone (f : ι -> α) {g : α -> β} (hg : Monotone g) : g (⨆ i,
 f i) = ⨆ i, g (f i)
参数：f : ι -> α；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.map_iSup_of_monotoneOn`：map_iSup_of_monotoneOn {s : Set α} {f : ι
 -> α} {g : α -> β} (hg : MonotoneOn g s) (hs : forall i, f i in s) : g (⨆ i, f 
i) = ⨆ i, g (f i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `monotoneOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β}, MonotoneOn f Set.univ ↔ Monotone f
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
lemma map_iSup_of_monotone (f : ι → α) {g : α → β} (hg : Monotone g) :
    g (⨆ i, f i) = ⨆ i, g (f i) :=
  map_iSup_of_monotoneOn (monotoneOn_univ.mpr hg) (fun i ↦ Set.mem_univ (f i))
/-
**Finite.map_iInf_of_monotone** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：map_iInf_of_monotone (f : ι -> α) {g : α -> β} (hg : Monotone g) : g (⨅ i,
 f i) = ⨅ i, g (f i)
参数：f : ι -> α；hg : Monotone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.map_iSup_of_monotone`：map_iSup_of_monotone (f : ι -> α) {g : α ->
 β} (hg : Monotone g) : g (⨆ i, f i) = ⨆ i, g (f i)
-/
lemma map_iInf_of_monotone (f : ι → α) {g : α → β} (hg : Monotone g) :
    g (⨅ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotone (α := αᵒᵈ) (β := βᵒᵈ) f fun _ _ h ↦ hg h
/-
**Finite.map_iSup_of_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：map_iSup_of_antitone (f : ι -> α) {g : α -> β} (hg : Antitone g) : g (⨆ i,
 f i) = ⨅ i, g (f i)
参数：f : ι -> α；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.map_iSup_of_monotone`：map_iSup_of_monotone (f : ι -> α) {g : α ->
 β} (hg : Monotone g) : g (⨆ i, f i) = ⨆ i, g (f i)
-/
lemma map_iSup_of_antitone (f : ι → α) {g : α → β} (hg : Antitone g) :
    g (⨆ i, f i) = ⨅ i, g (f i) :=
  map_iSup_of_monotone (β := βᵒᵈ) f hg
/-
**Finite.map_iInf_of_antitone** 是 Mathlib 中的一个引理，位于命名空间 `Finite`。
形式化陈述：map_iInf_of_antitone (f : ι -> α) {g : α -> β} (hg : Antitone g) : g (⨅ i,
 f i) = ⨆ i, g (f i)
参数：f : ι -> α；hg : Antitone g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finite.map_iInf_of_monotone`：map_iInf_of_monotone (f : ι -> α) {g : α ->
 β} (hg : Monotone g) : g (⨅ i, f i) = ⨅ i, g (f i)
-/
lemma map_iInf_of_antitone (f : ι → α) {g : α → β} (hg : Antitone g) :
    g (⨅ i, f i) = ⨆ i, g (f i) :=
  map_iInf_of_monotone (β := βᵒᵈ) f hg

end CCLO

end Finite

end ciSup

