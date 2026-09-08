/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.Bounded
public import Mathlib.Order.Hom.Lattice
public import Mathlib.Order.SymmDiff

/-!
# Bounded lattice homomorphisms

This file defines bounded lattice homomorphisms.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `SupBotHom`: Finitary supremum homomorphisms. Maps which preserve `⊔` and `⊥`.
* `InfTopHom`: Finitary infimum homomorphisms. Maps which preserve `⊓` and `⊤`.
* `BoundedLatticeHom`: Bounded lattice homomorphisms. Maps which preserve `⊤`, `⊥`, `⊔` and `⊓`.

## Typeclasses

* `SupBotHomClass`
* `InfTopHomClass`
* `BoundedLatticeHomClass`

## TODO

Do we need more intersections between `BotHom`, `TopHom` and lattice homomorphisms?
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/-- The type of finitary supremum-preserving homomorphisms from `α` to `β`. -/
/-
**SupBotHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Max α] → [Max β] → [Bot α] → [Bot β] → 
Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of finitary supremum-preserving homomorphisms from `α` to `β`.
-/
structure SupBotHom (α β : Type*) [Max α] [Max β] [Bot α] [Bot β]
  extends SupHom α β, BotHom α β where

/-- The type of finitary infimum-preserving homomorphisms from `α` to `β`. -/
@[to_dual]
/-
**InfTopHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Min α] → [Min β] → [Top α] → [Top β] → 
Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of finitary infimum-preserving homomorphisms from `α` to `β`.
-/
structure InfTopHom (α β : Type*) [Min α] [Min β] [Top α] [Top β]
  extends InfHom α β, TopHom α β where

attribute [nolint docBlame] SupBotHom.toBotHom InfTopHom.toTopHom

/-- The type of bounded lattice homomorphisms from `α` to `β`. -/
/-
**BoundedLatticeHom** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：BoundedLatticeHom (α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α] [
BoundedOrder β] extends LatticeHom α β, InfTopHom α β, SupBotHom α β where  attr
ibute [nolint docBlame] BoundedLatticeHom.toInfTopHom BoundedLatticeHom.toSupBot
Hom  attribute [to_dual self (reorder
参数：α β : Type*。
继承自：LatticeHom α β, InfTopHom α β, SupBotHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bounded lattice homomorphisms from `α` to `β`.
-/
structure BoundedLatticeHom (α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
  [BoundedOrder β] extends LatticeHom α β, InfTopHom α β, SupBotHom α β where

attribute [nolint docBlame] BoundedLatticeHom.toInfTopHom BoundedLatticeHom.toSupBotHom

attribute [to_dual self (reorder := map_top' map_bot')] BoundedLatticeHom.mk
attribute [to_dual existing] BoundedLatticeHom.toInfTopHom BoundedLatticeHom.map_top'

section

/-- `SupBotHomClass F α β` states that `F` is a type of finitary supremum-preserving morphisms.

You should extend this class when you extend `SupBotHom`. -/
/-
**SupBotHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [Max α] → [Max β] → [Bo
t α] → [Bot β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SupBotHomClass F α β` states that `F` is a type of finitary supremum-preserving
 morphisms.

You should extend this class when you extend `SupBotHom`.
-/
class SupBotHomClass (F α β : Type*) [Max α] [Max β] [Bot α] [Bot β] [FunLike F α β] : Prop
  extends SupHomClass F α β where
  /-- A `SupBotHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

/-- `InfTopHomClass F α β` states that `F` is a type of finitary infimum-preserving morphisms.

You should extend this class when you extend `SupBotHom`. -/
@[to_dual]
/-
**InfTopHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [Min α] → [Min β] → [To
p α] → [Top β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`InfTopHomClass F α β` states that `F` is a type of finitary infimum-preserving 
morphisms.

You should extend this class when you extend `SupBotHom`.
-/
class InfTopHomClass (F α β : Type*) [Min α] [Min β] [Top α] [Top β] [FunLike F α β] : Prop
  extends InfHomClass F α β where
  /-- An `InfTopHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤

/-- `BoundedLatticeHomClass F α β` states that `F` is a type of bounded lattice morphisms.

You should extend this class when you extend `BoundedLatticeHom`. -/
/-
**BoundedLatticeHomClass** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：BoundedLatticeHomClass (F α β : Type*) [Lattice α] [Lattice β] [BoundedOrd
er α] [BoundedOrder β] [FunLike F α β] : Prop extends LatticeHomClass F α β wher
e /-- A `BoundedLatticeHomClass` morphism preserves the top element. -/ map_top 
(f : F) : f ⊤ = ⊤ /-- A `BoundedLatticeHomClass` morphism preserves the bottom e
lement. -/ map_bot (f : F) : f ⊥ = ⊥  attribute [to_dual self (reorder
参数：F α β : Type*。
继承自：LatticeHomClass F α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BoundedLatticeHomClass F α β` states that `F` is a type of bounded lattice morp
hisms.

You should extend this class when you extend `BoundedLatticeHom`.
-/
class BoundedLatticeHomClass (F α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
    [BoundedOrder β] [FunLike F α β] : Prop
  extends LatticeHomClass F α β where
  /-- A `BoundedLatticeHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- A `BoundedLatticeHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

attribute [to_dual self (reorder := map_top map_bot)] BoundedLatticeHomClass.mk
attribute [to_dual existing] BoundedLatticeHomClass.map_bot

end

section Hom

variable [FunLike F α β]

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) SupBotHomClass.toBotHomClass [Max α] [Max β] [Bot α]
    [Bot β] [SupBotHomClass F α β] : BotHomClass F α β :=
  { ‹SupBotHomClass F α β› with }

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BoundedLatticeHomClass.toSupBotHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    SupBotHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BoundedLatticeHomClass.toBoundedOrderHomClass [Lattice α]
    [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    BoundedOrderHomClass F α β :=
{ show OrderHomClass F α β from inferInstance, ‹BoundedLatticeHomClass F α β› with }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toSupBotHomClass [SemilatticeSup α] [OrderBot α]
    [SemilatticeSup β] [OrderBot β] [OrderIsoClass F α β] : SupBotHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toBotHomClass with }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toBoundedLatticeHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [OrderIsoClass F α β] :
    BoundedLatticeHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass, OrderIsoClass.toBoundedOrderHomClass with }

end Equiv

section BoundedLattice

variable [Lattice α] [Lattice β] [FunLike F α β]

@[to_dual]
/-
**Disjoint.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.map [OrderBot α] [OrderBot β] [BotHomClass F α β] [InfHomClass F 
α β] {a b : α} (f : F) (h : Disjoint a b) : Disjoint (f a) (f b)
参数：f : F；h : Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `BotHomClass.map_bot`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Bot α} {inst_1 : Bot β}   {inst_2 : FunLike F α β} [se
lf : BotH…
-/
theorem Disjoint.map [OrderBot α] [OrderBot β] [BotHomClass F α β] [InfHomClass F α β] {a b : α}
    (f : F) (h : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff, ← map_inf, h.eq_bot, map_bot]
/-
**IsCompl.map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompl.map [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α 
β] {a b : α} (f : F) (h : IsCompl a b) : IsCompl (f a) (f b)
参数：f : F；h : IsCompl a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.map`：Disjoint.map [OrderBot α] [OrderBot β] [BotHomClass F α β]
 [InfHomClass F α β] {a b : α} (f : F) (h : Disjoint a b) : Disjoint (f a) (f b)
· 使用定理 `SupBotHomClass.toBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Max α] [inst_2 : Max β] [inst_3 : Bot α]  
 [inst_4 : Bot β] …
· 使用定理 `BoundedLatticeHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Codisjoint.map`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : L
attice α] [inst_1 : Lattice β] [inst_2 : FunLike F α β]   [inst_3 : OrderTop α] 
[ins…
· 使用定理 `InfTopHomClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Min α] [inst_2 : Min β] [inst_3 : Top α]  
 [inst_4 : Top β] …
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
theorem IsCompl.map [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] {a b : α}
    (f : F) (h : IsCompl a b) : IsCompl (f a) (f b) :=
  ⟨h.1.map _, h.2.map _⟩

end BoundedLattice

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [FunLike F α β] [BoundedLatticeHomClass F α β]
variable (f : F)

/-- Special case of `map_compl` for Boolean algebras. -/
/-
**map_compl'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_compl' (a : α) : f aᶜ = (f a)ᶜ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `IsCompl.map`：IsCompl.map [BoundedOrder α] [BoundedOrder β] [BoundedLatti
ceHomClass F α β] {a b : α} (f : F) (h : IsCompl a b) : IsCompl (f a) (f b)
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ

--- 原说明 ---
Special case of `map_compl` for Boolean algebras.
-/
theorem map_compl' (a : α) : f aᶜ = (f a)ᶜ :=
  (isCompl_compl.map _).compl_eq.symm

/-- Special case of `map_sdiff` for Boolean algebras. -/
/-
**map_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_sdiff' (a b : α) : f (a \ b) = f a \ f b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sdiff_eq`：sdiff_eq : x \ y = x ⊓ yᶜ
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `map_compl'`：map_compl' (a : α) : f aᶜ = (f a)ᶜ

--- 原说明 ---
Special case of `map_sdiff` for Boolean algebras.
-/
theorem map_sdiff' (a b : α) : f (a \ b) = f a \ f b := by
  rw [sdiff_eq, sdiff_eq, map_inf, map_compl']

open scoped symmDiff in
/-- Special case of `map_symmDiff` for Boolean algebras. -/
/-
**map_symmDiff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_symmDiff' (a b : α) : f (a ∆ b) = f a ∆ f b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `symmDiff.eq_1`：∀ {α : Type u_2} [inst : Max α] [inst_1 : SDiff α] (a b :
 α), symmDiff a b = a \ b ⊔ b \ a
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `map_sdiff'`：map_sdiff' (a b : α) : f (a \ b) = f a \ f b

--- 原说明 ---
Special case of `map_symmDiff` for Boolean algebras.
-/
theorem map_symmDiff' (a b : α) : f (a ∆ b) = f a ∆ f b := by
  rw [symmDiff, symmDiff, map_sup, map_sdiff', map_sdiff']

end BooleanAlgebra

variable [FunLike F α β]

@[to_dual]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Max α] [Max β] [Bot α] [Bot β] [SupBotHomClass F α β] : CoeTC F (SupBotHom α β) :=
  ⟨fun f => ⟨f, map_bot f⟩⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    CoeTC F (BoundedLatticeHom α β) :=
  ⟨fun f =>
    { (f : LatticeHom α β) with
      toFun := f
      map_top' := map_top f
      map_bot' := map_bot f }⟩

/-! ### Finitary supremum homomorphisms -/

namespace SupBotHom

variable [Max α] [Bot α]

section Sup

variable [Max β] [Bot β] [Max γ] [Bot γ] [Max δ] [Bot δ]

@[to_dual]
/-
**SupBotHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupBotHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (SupBotHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

@[to_dual]
/-
**SupBotHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupBotHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SupBotHomClass (SupBotHom α β) α β where
  map_sup f := f.map_sup'
  map_bot f := f.map_bot'

@[to_dual]
/-
**SupBotHom.toFun_eq_coe** 是 Mathlib 中的一个引理，位于命名空间 `SupBotHom`。
形式化陈述：toFun_eq_coe (f : SupBotHom α β) : f.toFun = f
参数：f : SupBotHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toFun_eq_coe (f : SupBotHom α β) : f.toFun = f := rfl
/-
**SupBotHom.coe_toSupHom** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1 : Bot α] [inst_2 : 
Max β] [inst_3 : Bot β] (f : SupBotHom α β),   ⇑f.toSupHom = ⇑f
参数：f : SupBotHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma coe_toSupHom (f : SupBotHom α β) : ⇑f.toSupHom = f := rfl
/-
**SupBotHom.coe_toBotHom** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1 : Bot α] [inst_2 : 
Max β] [inst_3 : Bot β] (f : SupBotHom α β),   ⇑f.toBotHom = ⇑f
参数：f : SupBotHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma coe_toBotHom (f : SupBotHom α β) : ⇑f.toBotHom = f := rfl
/-
**SupBotHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1 : Bot α] [inst_2 : 
Max β] [inst_3 : Bot β] (f : SupHom α β)   (hf : f.toFun ⊥ = ⊥), ⇑{ toSupHom := 
f, map_bot' := hf } = ⇑f
参数：f : SupHom α β；hf : f.toFun ⊥ = ⊥。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] lemma coe_mk (f : SupHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[to_dual (attr := ext)]
/-
**SupBotHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：ext {f g : SupBotHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : SupBotHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SupBotHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual /--
Copy of an `InfTopHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
/-
**SupBotHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `SupBotHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Max α] →       [inst_1 : B
ot α] →         [inst_2 : Max β] → [inst_3 : Bot β] → (f : SupBotHom α β) → (f' 
: α → β) → f' = ⇑f → SupBotHom α β
参数：f : SupBotHom α β；f' : α → β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BotHom.map_bot'`：∀ {α : Type u_6} {β : Type u_7} [inst : Bot α] [inst_1 
: Bot β] (self : BotHom α β), self.toFun ⊥ = ⊥
-/
protected def copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : SupBotHom α β :=
  { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }

@[to_dual (attr := simp)]
/-
**SupBotHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：coe_copy (f : SupBotHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) =
 f'
参数：f : SupBotHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : SupBotHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
/-
**SupBotHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：copy_eq (f : SupBotHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : SupBotHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : SupBotHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `SupBotHom`. -/
@[to_dual (attr := simps!) /-- `id` as an `InfTopHom`. -/]
/-
**SupBotHom.id** 是 Mathlib 中的一个定义，位于命名空间 `SupBotHom`。
形式化陈述：(α : Type u_2) → [inst : Max α] → [inst_1 : Bot α] → SupBotHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `SupBotHom`.
-/
protected def id : SupBotHom α α :=
  ⟨SupHom.id α, rfl⟩

@[to_dual]
/-
**SupBotHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupBotHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (SupBotHom α α) :=
  ⟨SupBotHom.id α⟩

@[to_dual (attr := simp, norm_cast)]
/-
**SupBotHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：coe_id : ⇑(SupBotHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(SupBotHom.id α) = id :=
  rfl

variable {α}

@[to_dual]
/-
**SupBotHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：id_apply (a : α) : SupBotHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : SupBotHom.id α a = a :=
  rfl

/-- Composition of `SupBotHom`s as a `SupBotHom`. -/
@[to_dual /-- Composition of `InfTopHom`s as an `InfTopHom`. -/]
/-
**SupBotHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `SupBotHom`。
形式化陈述：comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ
参数：f : SupBotHom β γ；g : SupBotHom α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BotHom.map_bot'`：∀ {α : Type u_6} {β : Type u_7} [inst : Bot α] [inst_1 
: Bot β] (self : BotHom α β), self.toFun ⊥ = ⊥

--- 原说明 ---
Composition of `SupBotHom`s as a `SupBotHom`.
-/
def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }

@[to_dual (attr := simp)]
/-
**SupBotHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：coe_comp (f : SupBotHom β γ) (g : SupBotHom α β) : (f.comp g : α -> γ) = f
 ∘ g
参数：f : SupBotHom β γ；g : SupBotHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : SupBotHom β γ) (g : SupBotHom α β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a 
= f (g a)
参数：f : SupBotHom β γ；g : SupBotHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：comp_assoc (f : SupBotHom γ δ) (g : SupBotHom β γ) (h : SupBotHom α β) : (
f.comp g).comp h = f.comp (g.comp h)
参数：f : SupBotHom γ δ；g : SupBotHom β γ；h : SupBotHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : SupBotHom γ δ) (g : SupBotHom β γ) (h : SupBotHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
/-
**SupBotHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1 : Bot α] [inst_2 : 
Max β] [inst_3 : Bot β] (f : SupBotHom α β),   f.comp (SupBotHom.id α) = f
参数：f : SupBotHom α β；SupBotHom.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] theorem comp_id (f : SupBotHom α β) : f.comp (SupBotHom.id α) = f := rfl
/-
**SupBotHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Max α] [inst_1 : Bot α] [inst_2 : 
Max β] [inst_3 : Bot β] (f : SupBotHom α β),   (SupBotHom.id β).comp f = f
参数：f : SupBotHom α β；SupBotHom.id β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] theorem id_comp (f : SupBotHom α β) : (SupBotHom.id β).comp f = f := rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：cancel_right {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective 
f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupBotHom.ext`：ext {f g : SupBotHom α β} (h : forall a, f a = g a) : f =
 g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem cancel_right {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]
/-
**SupBotHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：cancel_left {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g)
 : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupBotHom.ext`：ext {f g : SupBotHom α β} (h : forall a, f a = g a) : f =
 g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SupBotHom.comp_apply`：comp_apply (f : SupBotHom β γ) (g : SupBotHom α β)
 (a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => SupBotHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Sup

variable [SemilatticeSup β] [OrderBot β]

@[to_dual]
/-
**SupBotHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupBotHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (SupBotHom α β) :=
  ⟨fun f g => { f.toBotHom ⊔ g.toBotHom with toSupHom := f.toSupHom ⊔ g.toSupHom }⟩

@[to_dual]
/-
**SupBotHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupBotHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (SupBotHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]
/-
**SupBotHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupBotHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup (SupBotHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ ↦ rfl

@[to_dual]
/-
**SupBotHom.** 是 Mathlib 中的一个实例，位于命名空间 `SupBotHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderBot (SupBotHom α β) where
  bot := ⟨⊥, rfl⟩
  bot_le _ _ := bot_le

@[to_dual (attr := simp)]
/-
**SupBotHom.coe_sup** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：coe_sup (f g : SupBotHom α β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
参数：f g : SupBotHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sup (f g : SupBotHom α β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：coe_bot : ⇑(⊥ : SupBotHom α β) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_bot : ⇑(⊥ : SupBotHom α β) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.sup_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：sup_apply (f g : SupBotHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a
参数：f g : SupBotHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_apply (f g : SupBotHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.bot_apply** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：bot_apply (a : α) : (⊥ : SupBotHom α β) a = ⊥
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_apply (a : α) : (⊥ : SupBotHom α β) a = ⊥ :=
  rfl

/-- `Subtype.val` as a `SupBotHom`. -/
@[to_dual (rename := Pbot → Ptop, Psup → Pinf) /-- `Subtype.val` as an `InfTopHom`. -/]
/-
**SupBotHom.subtypeVal** 是 Mathlib 中的一个定义，位于命名空间 `SupBotHom`。
形式化陈述：subtypeVal {P : β -> Prop} (Pbot : P ⊥) (Psup : forall ⦃x y : β⦄, P x -> P
 y -> P (x ⊔ y)) : letI
参数：Pbot : P ⊥；Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subtype.val` as a `SupBotHom`.
-/
def subtypeVal {P : β → Prop}
    (Pbot : P ⊥) (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    letI := Subtype.orderBot Pbot
    letI := Subtype.semilatticeSup Psup
    SupBotHom {x : β // P x} β :=
  letI := Subtype.orderBot Pbot
  letI := Subtype.semilatticeSup Psup
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_bot Pbot])

@[to_dual (attr := simp) (rename := Pbot → Ptop, Psup → Pinf)]
/-
**SupBotHom.subtypeVal_apply** 是 Mathlib 中的一个引理，位于命名空间 `SupBotHom`。
形式化陈述：subtypeVal_apply {P : β -> Prop} (Pbot : P ⊥) (Psup : forall ⦃x y : β⦄, P 
x -> P y -> P (x ⊔ y)) (x : {x : β // P x}) : subtypeVal Pbot Psup x = x
参数：Pbot : P ⊥；Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)；x : {x : β // P x
}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_apply {P : β → Prop}
    (Pbot : P ⊥) (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) (x : {x : β // P x}) :
    subtypeVal Pbot Psup x = x := rfl

@[to_dual (attr := simp) (rename := Pbot → Ptop, Psup → Pinf)]
/-
**SupBotHom.subtypeVal_coe** 是 Mathlib 中的一个引理，位于命名空间 `SupBotHom`。
形式化陈述：subtypeVal_coe {P : β -> Prop} (Pbot : P ⊥) (Psup : forall ⦃x y : β⦄, P x 
-> P y -> P (x ⊔ y)) : ⇑(subtypeVal Pbot Psup) = Subtype.val
参数：Pbot : P ⊥；Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_coe {P : β → Prop}
    (Pbot : P ⊥) (Psup : ∀ ⦃x y : β⦄, P x → P y → P (x ⊔ y)) :
    ⇑(subtypeVal Pbot Psup) = Subtype.val := rfl

end SupBotHom

/-! ### Bounded lattice homomorphisms -/

namespace BoundedLatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

/-- Reinterpret a `BoundedLatticeHom` as a `BoundedOrderHom`. -/
/-
**BoundedLatticeHom.toBoundedOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `BoundedLatticeH
om`。
形式化陈述：toBoundedOrderHom (f : BoundedLatticeHom α β) : BoundedOrderHom α β
参数：f : BoundedLatticeHom α β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLatticeHom.map_top'`：∀ {α : Type u_6} {β : Type u_7} [inst : Latt
ice α] [inst_1 : Lattice β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Bounde…
· 使用定理 `BoundedLatticeHom.map_bot'`：∀ {α : Type u_6} {β : Type u_7} [inst : Latt
ice α] [inst_1 : Lattice β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Bounde…

--- 原说明 ---
Reinterpret a `BoundedLatticeHom` as a `BoundedOrderHom`.
-/
def toBoundedOrderHom (f : BoundedLatticeHom α β) : BoundedOrderHom α β :=
  { f, (f.toLatticeHom : α →o β) with }
/-
**BoundedLatticeHom.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `BoundedLatticeHom`。
形式化陈述：instFunLike : FunLike (BoundedLatticeHom α β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (BoundedLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
/-
**BoundedLatticeHom.instBoundedLatticeHomClass** 是 Mathlib 中的一个实例，位于命名空间 `Bounde
dLatticeHom`。
形式化陈述：instBoundedLatticeHomClass : BoundedLatticeHomClass (BoundedLatticeHom α β
) α β where map_sup f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHom.map_sup'`：∀ {α : Type u_6} {β : Type u_7} [inst : Max α] [inst_1 
: Max β] (self : SupHom α β) (a b : α),   self.toFun (a ⊔ b) = self.toFun a ⊔ se
lf.to…
· 使用定理 `LatticeHom.map_inf'`：∀ {α : Type u_6} {β : Type u_7} [inst : Lattice α] 
[inst_1 : Lattice β] (self : LatticeHom α β) (a b : α),   self.toFun (a ⊓ b) = s
elf.toFun…
· 使用定理 `BoundedLatticeHom.map_top'`：∀ {α : Type u_6} {β : Type u_7} [inst : Latt
ice α] [inst_1 : Lattice β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Bounde…
· 使用定理 `BoundedLatticeHom.map_bot'`：∀ {α : Type u_6} {β : Type u_7} [inst : Latt
ice α] [inst_1 : Lattice β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Bounde…
-/
instance instBoundedLatticeHomClass : BoundedLatticeHomClass (BoundedLatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'
/-
**BoundedLatticeHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] [i
nst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β] (f : BoundedLatticeHom α β),
 f.toFun = ⇑f
参数：f : BoundedLatticeHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toFun_eq_coe (f : BoundedLatticeHom α β) : f.toFun = f := rfl
/-
**BoundedLatticeHom.coe_toLatticeHom** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHo
m`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] [i
nst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β] (f : BoundedLatticeHom α β),
 ⇑f.toLatticeHom = ⇑f
参数：f : BoundedLatticeHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toLatticeHom (f : BoundedLatticeHom α β) : ⇑f.toLatticeHom = f := rfl
@[to_dual (attr := simp)]
/-
**BoundedLatticeHom.coe_toSupBotHom** 是 Mathlib 中的一个引理，位于命名空间 `BoundedLatticeHom
`。
形式化陈述：coe_toSupBotHom (f : BoundedLatticeHom α β) : ⇑f.toSupBotHom = f
参数：f : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_toSupBotHom (f : BoundedLatticeHom α β) : ⇑f.toSupBotHom = f := rfl
/-
**BoundedLatticeHom.coe_toBoundedOrderHom** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatt
iceHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] [i
nst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β] (f : BoundedLatticeHom α β),
 ⇑f.toBoundedOrderHom = ⇑f
参数：f : BoundedLatticeHom α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toBoundedOrderHom (f : BoundedLatticeHom α β) : ⇑f.toBoundedOrderHom = f := rfl
/-
**BoundedLatticeHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] [i
nst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β] (f : LatticeHom α β) (hf : f
.toFun ⊤ = ⊤) (hf' : f.toFun ⊥ = ⊥),   ⇑{ toLatticeHom := f, map_top' := hf, map
_bot' := hf' } = ⇑f
参数：f : LatticeHom α β；hf : f.toFun ⊤ = ⊤；hf' : f.toFun ⊥ = ⊥。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_mk (f : LatticeHom α β) (hf hf') : ⇑(mk f hf hf') = f := rfl

@[ext]
/-
**BoundedLatticeHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：ext {f g : BoundedLatticeHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : BoundedLatticeHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `BoundedLatticeHom` with a new `toFun` equal to the old one. Useful to fix
definitional equalities. -/
/-
**BoundedLatticeHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `BoundedLatticeHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Lattice α] →       [inst_1
 : Lattice β] →         [inst_2 : BoundedOrder α] →           [inst_3 : BoundedO
rder β] → (f : BoundedLatticeHom α β) → (f' : α → β) → f' = ⇑f → BoundedLatticeH
om α β
参数：f : BoundedLatticeHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `BoundedLatticeHom` with a new `toFun` equal to the old one. Useful to
 fix
definitional equalities.
-/
protected def copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : BoundedLatticeHom α β :=
  { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }

@[simp]
/-
**BoundedLatticeHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：coe_copy (f : BoundedLatticeHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy
 f' h) = f'
参数：f : BoundedLatticeHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**BoundedLatticeHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：copy_eq (f : BoundedLatticeHom α β) (f' : α -> β) (h : f' = f) : f.copy f'
 h = f
参数：f : BoundedLatticeHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : BoundedLatticeHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `BoundedLatticeHom`. -/
/-
**BoundedLatticeHom.id** 是 Mathlib 中的一个定义，位于命名空间 `BoundedLatticeHom`。
形式化陈述：(α : Type u_2) → [inst : Lattice α] → [inst_1 : BoundedOrder α] → BoundedL
atticeHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `BoundedLatticeHom`.
-/
protected def id : BoundedLatticeHom α α :=
  { LatticeHom.id α, BoundedOrderHom.id α with }
/-
**BoundedLatticeHom.** 是 Mathlib 中的一个实例，位于命名空间 `BoundedLatticeHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (BoundedLatticeHom α α) :=
  ⟨BoundedLatticeHom.id α⟩

@[simp, norm_cast]
/-
**BoundedLatticeHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：coe_id : ⇑(BoundedLatticeHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(BoundedLatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**BoundedLatticeHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：id_apply (a : α) : BoundedLatticeHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : BoundedLatticeHom.id α a = a :=
  rfl

/-- Composition of `BoundedLatticeHom`s as a `BoundedLatticeHom`. -/
/-
**BoundedLatticeHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `BoundedLatticeHom`。
形式化陈述：comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatt
iceHom α γ
参数：f : BoundedLatticeHom β γ；g : BoundedLatticeHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `BoundedLatticeHom`s as a `BoundedLatticeHom`.
-/
def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }

@[simp]
/-
**BoundedLatticeHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：coe_comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : (f.comp
 g : α -> γ) = f ∘ g
参数：f : BoundedLatticeHom β γ；g : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
/-
**BoundedLatticeHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α)
 : (f.comp g) a = f (g a)
参数：f : BoundedLatticeHom β γ；g : BoundedLatticeHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
-- `simp`-normal form of `coe_comp_lattice_hom`
/-
**BoundedLatticeHom.coe_comp_lattice_hom'** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatt
iceHom`。
形式化陈述：coe_comp_lattice_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α
 β) : (⟨(f : SupHom β γ).comp g, map_inf (f.comp g)⟩ : LatticeHom α γ) = (f : La
tticeHom β γ).comp g
参数：f : BoundedLatticeHom β γ；g : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
-/
theorem coe_comp_lattice_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (⟨(f : SupHom β γ).comp g, map_inf (f.comp g)⟩ : LatticeHom α γ) =
      (f : LatticeHom β γ).comp g :=
  rfl
/-
**BoundedLatticeHom.coe_comp_lattice_hom** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatti
ceHom`。
形式化陈述：coe_comp_lattice_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α 
β) : (f.comp g : LatticeHom α γ) = (f : LatticeHom β γ).comp g
参数：f : BoundedLatticeHom β γ；g : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLatticeHomClass.toLatticeHomClass`：∀ {F : Type u_6} {α : Type u_7
} {β : Type u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : BoundedOrder 
α}   {inst_3 : BoundedOrder β}…
-/
theorem coe_comp_lattice_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : LatticeHom α γ) = (f : LatticeHom β γ).comp g :=
  rfl

@[to_dual (attr := simp)]
-- `simp`-normal form of `coe_comp_sup_hom`
/-
**BoundedLatticeHom.coe_comp_sup_hom'** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeH
om`。
形式化陈述：coe_comp_sup_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) 
: ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g
参数：f : BoundedLatticeHom β γ；g : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
-/
theorem coe_comp_sup_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g :=
  rfl

@[to_dual]
/-
**BoundedLatticeHom.coe_comp_sup_hom** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHo
m`。
形式化陈述：coe_comp_sup_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
 (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g
参数：f : BoundedLatticeHom β γ；g : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
-/
theorem coe_comp_sup_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl

@[simp]
/-
**BoundedLatticeHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：comp_assoc (f : BoundedLatticeHom γ δ) (g : BoundedLatticeHom β γ) (h : Bo
undedLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : BoundedLatticeHom γ δ；g : BoundedLatticeHom β γ；h : BoundedLatticeHom α β
。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : BoundedLatticeHom γ δ) (g : BoundedLatticeHom β γ)
    (h : BoundedLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl
/-
**BoundedLatticeHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] [i
nst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β] (f : BoundedLatticeHom α β),
 f.comp (BoundedLatticeHom.id α) = f
参数：f : BoundedLatticeHom α β；BoundedLatticeHom.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem comp_id (f : BoundedLatticeHom α β) : f.comp (BoundedLatticeHom.id α) = f := rfl
/-
**BoundedLatticeHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Lattice α] [inst_1 : Lattice β] [i
nst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β] (f : BoundedLatticeHom α β),
 (BoundedLatticeHom.id β).comp f = f
参数：f : BoundedLatticeHom α β；BoundedLatticeHom.id β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem id_comp (f : BoundedLatticeHom α β) : (BoundedLatticeHom.id β).comp f = f := rfl

@[simp]
/-
**BoundedLatticeHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：cancel_right {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β} (
hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLatticeHom.ext`：ext {f g : BoundedLatticeHom α β} (h : forall a, 
f a = g a) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
-/
theorem cancel_right {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => BoundedLatticeHom.ext <| hf.forall.2 <| DFunLike.ext_iff.1 h,
    fun h => congr_arg₂ _ h rfl⟩

@[simp]
/-
**BoundedLatticeHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：cancel_left {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (h
g : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLatticeHom.ext`：ext {f g : BoundedLatticeHom α β} (h : forall a, 
f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BoundedLatticeHom.comp_apply`：comp_apply (f : BoundedLatticeHom β γ) (g 
: BoundedLatticeHom α β) (a : α) : (f.comp g) a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/-- `Subtype.val` as a `BoundedLatticeHom`. -/
@[to_dual self (reorder := Pbot Ptop, Psup Pinf)]
/-
**BoundedLatticeHom.subtypeVal** 是 Mathlib 中的一个定义，位于命名空间 `BoundedLatticeHom`。
形式化陈述：subtypeVal {P : β -> Prop} (Pbot : P ⊥) (Ptop : P ⊤) (Psup : forall ⦃x y⦄,
 P x -> P y -> P (x ⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) : letI
参数：Pbot : P ⊥；Ptop : P ⊤；Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)；Pinf : for
all ⦃x y⦄, P x -> P y -> P (x ⊓ y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subtype.val` as a `BoundedLatticeHom`.
-/
def subtypeVal {P : β → Prop} (Pbot : P ⊥) (Ptop : P ⊤)
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    letI := Subtype.lattice Psup Pinf
    letI := Subtype.boundedOrder Pbot Ptop
    BoundedLatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  letI := Subtype.boundedOrder Pbot Ptop
  .mk (.subtypeVal Psup Pinf) (by simp [Subtype.coe_top Ptop]) (by simp [Subtype.coe_bot Pbot])

@[simp]
/-
**BoundedLatticeHom.subtypeVal_apply** 是 Mathlib 中的一个引理，位于命名空间 `BoundedLatticeHo
m`。
形式化陈述：subtypeVal_apply {P : β -> Prop} (Pbot : P ⊥) (Ptop : P ⊤) (Psup : forall 
⦃x y⦄, P x -> P y -> P (x ⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) (
x : {x : β // P x}) : subtypeVal Pbot Ptop Psup Pinf x = x
参数：Pbot : P ⊥；Ptop : P ⊤；Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)；Pinf : for
all ⦃x y⦄, P x -> P y -> P (x ⊓ y)；x : {x : β // P x}。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_apply {P : β → Prop}
    (Pbot : P ⊥) (Ptop : P ⊤) (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y))
    (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) (x : {x : β // P x}) :
    subtypeVal Pbot Ptop Psup Pinf x = x := rfl

@[simp]
/-
**BoundedLatticeHom.subtypeVal_coe** 是 Mathlib 中的一个引理，位于命名空间 `BoundedLatticeHom`
。
形式化陈述：subtypeVal_coe {P : β -> Prop} (Pbot : P ⊥) (Ptop : P ⊤) (Psup : forall ⦃x
 y⦄, P x -> P y -> P (x ⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) : ⇑
(subtypeVal Pbot Ptop Psup Pinf) = Subtype.val
参数：Pbot : P ⊥；Ptop : P ⊤；Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)；Pinf : for
all ⦃x y⦄, P x -> P y -> P (x ⊓ y)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma subtypeVal_coe {P : β → Prop} (Pbot : P ⊥) (Ptop : P ⊤)
    (Psup : ∀ ⦃x y⦄, P x → P y → P (x ⊔ y)) (Pinf : ∀ ⦃x y⦄, P x → P y → P (x ⊓ y)) :
    ⇑(subtypeVal Pbot Ptop Psup Pinf) = Subtype.val := rfl

end BoundedLatticeHom

/-! ### Dual homs -/

namespace SupBotHom

variable [Max α] [Bot α] [Max β] [Bot β] [Max γ] [Bot γ]

/-- Reinterpret a finitary supremum homomorphism as a finitary infimum homomorphism between the dual
lattices. -/
@[to_dual /--
Reinterpret a finitary infimum homomorphism as a finitary supremum homomorphism between the dual
lattices. -/]
/-
**SupBotHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `SupBotHom`。
形式化陈述：dual : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SupBotHom.map_bot'`：∀ {α : Type u_6} {β : Type u_7} [inst : Max α] [inst
_1 : Max β] [inst_2 : Bot α] [inst_3 : Bot β]   (self : SupBotHom α β), self.toF
un ⊥ = ⊥
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def dual : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨SupHom.dual f.toSupHom, f.map_bot'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩
/-
**SupBotHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：∀ {α : Type u_2} [inst : Max α] [inst_1 : Bot α], SupBotHom.dual (SupBotHo
m.id α) = InfTopHom.id αᵒᵈ
参数：SupBotHom.id α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_dual (attr := simp)] theorem dual_id : SupBotHom.dual (SupBotHom.id α) = InfTopHom.id _ := rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：dual_comp (g : SupBotHom β γ) (f : SupBotHom α β) : SupBotHom.dual (g.comp
 f) = (SupBotHom.dual g).comp (SupBotHom.dual f)
参数：g : SupBotHom β γ；f : SupBotHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : SupBotHom β γ) (f : SupBotHom α β) :
    SupBotHom.dual (g.comp f) = (SupBotHom.dual g).comp (SupBotHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：symm_dual_id : SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id : SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α :=
  rfl

@[to_dual (attr := simp)]
/-
**SupBotHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `SupBotHom`。
形式化陈述：symm_dual_comp (g : InfTopHom βᵒᵈ γᵒᵈ) (f : InfTopHom αᵒᵈ βᵒᵈ) : SupBotHom
.dual.symm (g.comp f) = (SupBotHom.dual.symm g).comp (SupBotHom.dual.symm f)
参数：g : InfTopHom βᵒᵈ γᵒᵈ；f : InfTopHom αᵒᵈ βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_comp (g : InfTopHom βᵒᵈ γᵒᵈ) (f : InfTopHom αᵒᵈ βᵒᵈ) :
    SupBotHom.dual.symm (g.comp f) =
      (SupBotHom.dual.symm g).comp (SupBotHom.dual.symm f) :=
  rfl

end SupBotHom

namespace BoundedLatticeHom

variable [Lattice α] [BoundedOrder α] [Lattice β] [BoundedOrder β] [Lattice γ] [BoundedOrder γ]

/-- Reinterpret a bounded lattice homomorphism as a bounded lattice homomorphism between the dual
bounded lattices. -/
@[simps!]
/-
**BoundedLatticeHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `BoundedLatticeHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : Lattice α] →       [inst_1
 : BoundedOrder α] →         [inst_2 : Lattice β] → [inst_3 : BoundedOrder β] → 
BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLatticeHom.map_bot'`：∀ {α : Type u_6} {β : Type u_7} [inst : Latt
ice α] [inst_1 : Lattice β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Bounde…
· 使用定理 `BoundedLatticeHom.map_top'`：∀ {α : Type u_6} {β : Type u_7} [inst : Latt
ice α] [inst_1 : Lattice β] [inst_2 : BoundedOrder α]   [inst_3 : BoundedOrder β
] (self : Bounde…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret a bounded lattice homomorphism as a bounded lattice homomorphism bet
ween the dual
bounded lattices.
-/
protected def dual : BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨LatticeHom.dual f.toLatticeHom, f.map_bot', f.map_top'⟩
  invFun f := ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩

@[simp]
/-
**BoundedLatticeHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：dual_id : BoundedLatticeHom.dual (BoundedLatticeHom.id α) = BoundedLattice
Hom.id _
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_id : BoundedLatticeHom.dual (BoundedLatticeHom.id α) = BoundedLatticeHom.id _ :=
  rfl

@[simp]
/-
**BoundedLatticeHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：dual_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) : Bounde
dLatticeHom.dual (g.comp f) = (BoundedLatticeHom.dual g).comp (BoundedLatticeHom
.dual f)
参数：g : BoundedLatticeHom β γ；f : BoundedLatticeHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    BoundedLatticeHom.dual (g.comp f) =
      (BoundedLatticeHom.dual g).comp (BoundedLatticeHom.dual f) :=
  rfl

@[simp]
/-
**BoundedLatticeHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`。
形式化陈述：symm_dual_id : BoundedLatticeHom.dual.symm (BoundedLatticeHom.id _) = Boun
dedLatticeHom.id α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id :
    BoundedLatticeHom.dual.symm (BoundedLatticeHom.id _) = BoundedLatticeHom.id α :=
  rfl

@[simp]
/-
**BoundedLatticeHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `BoundedLatticeHom`
。
形式化陈述：symm_dual_comp (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ 
βᵒᵈ) : BoundedLatticeHom.dual.symm (g.comp f) = (BoundedLatticeHom.dual.symm g).
comp (BoundedLatticeHom.dual.symm f)
参数：g : BoundedLatticeHom βᵒᵈ γᵒᵈ；f : BoundedLatticeHom αᵒᵈ βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_comp (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ βᵒᵈ) :
    BoundedLatticeHom.dual.symm (g.comp f) =
      (BoundedLatticeHom.dual.symm g).comp (BoundedLatticeHom.dual.symm f) :=
  rfl

end BoundedLatticeHom

