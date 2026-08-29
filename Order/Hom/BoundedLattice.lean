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

/--
Definition of `SupBotHom` / `SupBotHom` 的定义

English:
structure SupBotHom
  parameters: (α β : Type*) [Max α] [Max β] [Bot α] [Bot β]
  extends: SupHom α β, BotHom α β
  (no additional axioms)

中文:
结构 SupBot态射
  参数: (α β : 类型) [最大值 α] [最大值 β] [底元素 α] [底元素 β]
  继承: 并态射 α β, 底元素态射 α β
  (无附加公理)
-/
structure SupBotHom (α β : Type*) [Max α] [Max β] [Bot α] [Bot β]
  extends SupHom α β, BotHom α β where

/-- The type of finitary infimum-preserving homomorphisms from `α` to `β`. -/
@[to_dual]
/--
Definition of `InfTopHom` / `InfTopHom` 的定义

English:
structure InfTopHom
  parameters: (α β : Type*) [Min α] [Min β] [Top α] [Top β]
  extends: InfHom α β, TopHom α β
  (no additional axioms)

中文:
结构 InfTop态射
  参数: (α β : 类型) [最小值 α] [最小值 β] [顶元素 α] [顶元素 β]
  继承: 交态射 α β, 顶元素态射 α β
  (无附加公理)
-/
structure InfTopHom (α β : Type*) [Min α] [Min β] [Top α] [Top β]
  extends InfHom α β, TopHom α β where

attribute [nolint docBlame] SupBotHom.toBotHom InfTopHom.toTopHom

/--
Definition of `BoundedLatticeHom` / `BoundedLatticeHom` 的定义

English:
structure BoundedLatticeHom
  parameters: (α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
  extends: LatticeHom α β, InfTopHom α β, SupBotHom α β
  (no additional axioms)

中文:
结构 有界格态射
  参数: (α β : 类型) [格 α] [格 β] [有界序 α]
  继承: 格态射 α β, InfTop态射 α β, SupBot态射 α β
  (无附加公理)

Depends on / 依赖: BoundedLatticeHom, BoundedLatticeHom.mk, map_bot, map_top
-/
structure BoundedLatticeHom (α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
  [BoundedOrder β] extends LatticeHom α β, InfTopHom α β, SupBotHom α β where

attribute [nolint docBlame] BoundedLatticeHom.toInfTopHom BoundedLatticeHom.toSupBotHom

attribute [to_dual self (reorder := map_top' map_bot')] BoundedLatticeHom.mk
attribute [to_dual existing] BoundedLatticeHom.toInfTopHom BoundedLatticeHom.map_top'

section

/--
Definition of `SupBotHomClass` / `SupBotHomClass` 的定义

English:
class SupBotHomClass
  parameters: (F α β : Type*) [Max α] [Max β] [Bot α] [Bot β] [FunLike F α β]
  extends: SupHomClass F α β
  axioms and operations (1):
    - map_bot((f : F)) : f ⊥ = ⊥

中文:
类 SupBot态射类
  参数: (F α β : 类型) [最大值 α] [最大值 β] [底元素 α] [底元素 β] [函数状 F α β]
  继承: 并态射类 F α β
  公理与运算 (1 个):
    - map_bot((f : F)) : f ⊥ = ⊥
-/
class SupBotHomClass (F α β : Type*) [Max α] [Max β] [Bot α] [Bot β] [FunLike F α β] : Prop
  extends SupHomClass F α β where
  /-- A `SupBotHomClass` morphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥

/-- `InfTopHomClass F α β` states that `F` is a type of finitary infimum-preserving morphisms.

You should extend this class when you extend `SupBotHom`. -/
@[to_dual]
/--
Definition of `InfTopHomClass` / `InfTopHomClass` 的定义

English:
class InfTopHomClass
  parameters: (F α β : Type*) [Min α] [Min β] [Top α] [Top β] [FunLike F α β]
  extends: InfHomClass F α β
  axioms and operations (1):
    - map_top((f : F)) : f ⊤ = ⊤

中文:
类 InfTop态射类
  参数: (F α β : 类型) [最小值 α] [最小值 β] [顶元素 α] [顶元素 β] [函数状 F α β]
  继承: 交态射类 F α β
  公理与运算 (1 个):
    - map_top((f : F)) : f ⊤ = ⊤
-/
class InfTopHomClass (F α β : Type*) [Min α] [Min β] [Top α] [Top β] [FunLike F α β] : Prop
  extends InfHomClass F α β where
  /-- An `InfTopHomClass` morphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤

/--
Definition of `BoundedLatticeHomClass` / `BoundedLatticeHomClass` 的定义

English:
class BoundedLatticeHomClass
  parameters: (F α β : Type*) [Lattice α] [Lattice β] [BoundedOrder α]
  extends: LatticeHomClass F α β
  axioms and operations (2):
    - map_top((f : F)) : f ⊤ = ⊤
    - map_bot((f : F)) : f ⊥ = ⊥

中文:
类 有界格态射类
  参数: (F α β : 类型) [格 α] [格 β] [有界序 α]
  继承: 格态射类 F α β
  公理与运算 (2 个):
    - map_top((f : F)) : f ⊤ = ⊤
    - map_bot((f : F)) : f ⊥ = ⊥

Depends on / 依赖: BoundedLatticeHomClass, BoundedLatticeHomClass.mk, map_bot, map_top
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
instance (priority := 100) SupBotHomClass.toBotHomClass [Max α] [Max β] [Bot α]
    [Bot β] [SupBotHomClass F α β] : BotHomClass F α β :=
  { ‹SupBotHomClass F α β› with }

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) BoundedLatticeHomClass.toSupBotHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    SupBotHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with }

-- See note [lower instance priority]
instance (priority := 100) BoundedLatticeHomClass.toBoundedOrderHomClass [Lattice α]
    [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
    BoundedOrderHomClass F α β :=
{ show OrderHomClass F α β from inferInstance, ‹BoundedLatticeHomClass F α β› with }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) OrderIsoClass.toSupBotHomClass [SemilatticeSup α] [OrderBot α]
    [SemilatticeSup β] [OrderBot β] [OrderIsoClass F α β] : SupBotHomClass F α β :=
  { OrderIsoClass.toSupHomClass, OrderIsoClass.toBotHomClass with }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBoundedLatticeHomClass [Lattice α] [Lattice β]
    [BoundedOrder α] [BoundedOrder β] [OrderIsoClass F α β] :
    BoundedLatticeHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass, OrderIsoClass.toBoundedOrderHomClass with }

end Equiv

section BoundedLattice

variable [Lattice α] [Lattice β] [FunLike F α β]

@[to_dual]
/--
theorem `Disjoint.map` / 定理 `Disjoint.map`

English:
theorem Disjoint.map
  statement: [OrderBot α] [OrderBot β] [BotHomClass F α β] [InfHomClass F α β] {a b : α}
  proof: by
  rw [disjoint_iff]; rw [← map_inf]; rw [h.eq_bot]; rw [map_bot]

中文:
定理 Disjoint.map
  结论: [有底序 α] [有底序 β] [底元素态射类 F α β] [交态射类 F α β] {a b : α}
  证明: by
  rw [disjoint_iff]; rw [← map_inf]; rw [h.eq_bot]; rw [map_bot]

Depends on / 依赖: disjoint_iff, eq_bot, h.eq_bot, map_bot, map_inf
-/
theorem Disjoint.map [OrderBot α] [OrderBot β] [BotHomClass F α β] [InfHomClass F α β] {a b : α}
    (f : F) (h : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff]; rw [← map_inf]; rw [h.eq_bot]; rw [map_bot]

/--
theorem `IsCompl.map` / 定理 `IsCompl.map`

English:
theorem IsCompl.map
  statement: [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] {a b : α}
  proof: ⟨h.1.map _, h.2.map _⟩

中文:
定理 是补集.map
  结论: [有界序 α] [有界序 β] [有界格态射类 F α β] {a b : α}
  证明: ⟨h.1.map _, h.2.map _⟩
-/
theorem IsCompl.map [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] {a b : α}
    (f : F) (h : IsCompl a b) : IsCompl (f a) (f b) :=
  ⟨h.1.map _, h.2.map _⟩

end BoundedLattice

section BooleanAlgebra

variable [BooleanAlgebra α] [BooleanAlgebra β] [FunLike F α β] [BoundedLatticeHomClass F α β]
variable (f : F)

/--
theorem `map_compl'` / 定理 `map_compl'`

English:
theorem map_compl'
  given: (a : α)
  statement: f aᶜ = (f a)ᶜ
  proof: (isCompl_compl.map _).compl_eq.symm

中文:
定理 map_compl'
  条件: (a : α)
  结论: f aᶜ = (f a)ᶜ
  证明: (isCompl_compl.map _).compl_eq.symm

Depends on / 依赖: compl_eq, compl_eq.symm, isCompl_compl, isCompl_compl.map
-/
theorem map_compl' (a : α) : f aᶜ = (f a)ᶜ :=
  (isCompl_compl.map _).compl_eq.symm

/--
theorem `map_sdiff'` / 定理 `map_sdiff'`

English:
theorem map_sdiff'
  given: (a b : α)
  statement: f (a \ b) = f a \ f b
  proof: by
  rw [sdiff_eq]; rw [sdiff_eq]; rw [map_inf]; rw [map_compl']

中文:
定理 map_sdiff'
  条件: (a b : α)
  结论: f (a \ b) = f a \ f b
  证明: by
  rw [sdiff_eq]; rw [sdiff_eq]; rw [map_inf]; rw [map_compl']

Depends on / 依赖: map_compl, map_inf, sdiff_eq
-/
theorem map_sdiff' (a b : α) : f (a \ b) = f a \ f b := by
  rw [sdiff_eq]; rw [sdiff_eq]; rw [map_inf]; rw [map_compl']

open scoped symmDiff in
/--
theorem `map_symmDiff'` / 定理 `map_symmDiff'`

English:
theorem map_symmDiff'
  given: (a b : α)
  statement: f (a ∆ b) = f a ∆ f b
  proof: by
  rw [symmDiff]; rw [symmDiff]; rw [map_sup]; rw [map_sdiff']; rw [map_sdiff']

中文:
定理 map_symmDiff'
  条件: (a b : α)
  结论: f (a ∆ b) = f a ∆ f b
  证明: by
  rw [symmDiff]; rw [symmDiff]; rw [map_sup]; rw [map_sdiff']; rw [map_sdiff']

Depends on / 依赖: map_sdiff, map_sup, symmDiff
-/
theorem map_symmDiff' (a b : α) : f (a ∆ b) = f a ∆ f b := by
  rw [symmDiff]; rw [symmDiff]; rw [map_sup]; rw [map_sdiff']; rw [map_sdiff']

end BooleanAlgebra

variable [FunLike F α β]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Max
  signature: α] [Max β] [Bot α] [Bot β] [SupBotHomClass F α β] : CoeTC F (SupBotHom α β)
  body: ⟨fun f => ⟨f, map_bot f⟩⟩

中文:
实例 [最大值
  签名: α] [最大值 β] [底元素 α] [底元素 β] [SupBot态射类 F α β] : CoeTC F (SupBot态射 α β)
  定义体: ⟨fun f => ⟨f, map_bot f⟩⟩

Depends on / 依赖: map_bot
-/
instance [Max α] [Max β] [Bot α] [Bot β] [SupBotHomClass F α β] : CoeTC F (SupBotHom α β) :=
  ⟨fun f => ⟨f, map_bot f⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Lattice
  signature: α] [Lattice β] [BoundedOrder α] [BoundedOrder β] [BoundedLatticeHomClass F α β] :
  body: ⟨fun f =>
    { (f : LatticeHom α β) with
      toFun := f
      map_top' := map_top f
      map_bot' := map_bot f }⟩

中文:
实例 [格
  签名: α] [格 β] [有界序 α] [有界序 β] [有界格态射类 F α β] :
  定义体: ⟨fun f =>
    { (f : LatticeHom α β) with
      toFun := f
      map_top' := map_top f
      map_bot' := map_bot f }⟩

Depends on / 依赖: LatticeHom, map_bot, map_top
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
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (SupBotHom α β) α β
  body: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

@[to_dual]

中文:
实例 :
  签名: 函数状 (SupBot态射 α β) α β
  定义体: f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

@[to_dual]

Depends on / 依赖: f.toFun
-/
instance : FunLike (SupBotHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupBotHomClass (SupBotHom α β) α β
  body: f.map_sup'
  map_bot f := f.map_bot'

@[to_dual]

中文:
实例 :
  签名: SupBot态射类 (SupBot态射 α β) α β
  定义体: f.map_sup'
  map_bot f := f.map_bot'

@[to_dual]

Depends on / 依赖: f.map_sup, map_sup
-/
instance : SupBotHomClass (SupBotHom α β) α β where
  map_sup f := f.map_sup'
  map_bot f := f.map_bot'

@[to_dual]
/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (f : SupBotHom α β)
  statement: f.toFun = f
  proof: rfl

中文:
引理 toFun_eq_coe
  条件: (f : SupBot态射 α β)
  结论: f.toFun = f
  证明: rfl
-/
lemma toFun_eq_coe (f : SupBotHom α β) : f.toFun = f := rfl

/--
lemma `coe_toSupHom` / 引理 `coe_toSupHom`

English:
lemma coe_toSupHom
  given: (f : SupBotHom α β)
  statement: ⇑f.toSupHom = f
  proof: rfl

中文:
引理 coe_toSupHom
  条件: (f : SupBot态射 α β)
  结论: ⇑f.toSupHom = f
  证明: rfl
-/
@[to_dual (attr := simp)] lemma coe_toSupHom (f : SupBotHom α β) : ⇑f.toSupHom = f := rfl
/--
lemma `coe_toBotHom` / 引理 `coe_toBotHom`

English:
lemma coe_toBotHom
  given: (f : SupBotHom α β)
  statement: ⇑f.toBotHom = f
  proof: rfl

中文:
引理 coe_toBotHom
  条件: (f : SupBot态射 α β)
  结论: ⇑f.toBotHom = f
  证明: rfl
-/
@[to_dual (attr := simp)] lemma coe_toBotHom (f : SupBotHom α β) : ⇑f.toBotHom = f := rfl
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : SupHom α β) (hf)
  statement: ⇑(mk f hf) = f
  proof: rfl

@[to_dual (attr := ext)]

中文:
引理 coe_mk
  条件: (f : 并态射 α β) (hf)
  结论: ⇑(mk f hf) = f
  证明: rfl

@[to_dual (attr := ext)]
-/
@[to_dual (attr := simp)] lemma coe_mk (f : SupHom α β) (hf) : ⇑(mk f hf) = f := rfl

@[to_dual (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : SupBotHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : SupBot态射 α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : SupBotHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `SupBotHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
@[to_dual /--
Copy of an `InfTopHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/]
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : SupBotHom α β) (f' : α -> β) (h : f' = f)
  body: { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }

@[to_dual (attr := simp)]

中文:
定义 copy
  签名: (f : SupBot态射 α β) (f' : α -> β) (h : f' = f)
  定义体: { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }

@[to_dual (attr := simp)]
-/
protected def copy (f : SupBotHom α β) (f' : α -> β) (h : f' = f) : SupBotHom α β :=
  { f.toBotHom.copy f' h with toSupHom := f.toSupHom.copy f' h }

@[to_dual (attr := simp)]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : SupBotHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

@[to_dual]

中文:
定理 coe_copy
  条件: (f : SupBot态射 α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl

@[to_dual]
-/
theorem coe_copy (f : SupBotHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

@[to_dual]
/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : SupBotHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : SupBot态射 α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : SupBotHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `SupBotHom`. -/
@[to_dual (attr := simps!) /-- `id` as an `InfTopHom`. -/]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : SupBotHom α α
  body: ⟨SupHom.id α, rfl⟩

@[to_dual]

中文:
定义 id
  签名: : SupBot态射 α α
  定义体: ⟨SupHom.id α, rfl⟩

@[to_dual]
-/
protected def id : SupBotHom α α :=
  ⟨SupHom.id α, rfl⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (SupBotHom α α)
  body: ⟨SupBotHom.id α⟩

@[to_dual (attr := simp, norm_cast)]

中文:
实例 :
  签名: 可居 (SupBot态射 α α)
  定义体: ⟨SupBotHom.id α⟩

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: SupBotHom, SupBotHom.id
-/
instance : Inhabited (SupBotHom α α) :=
  ⟨SupBotHom.id α⟩

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(SupBotHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(SupBot态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(SupBotHom.id α) = id :=
  rfl

variable {α}

@[to_dual]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: SupBotHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: SupBot态射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : SupBotHom.id α a = a :=
  rfl

/-- Composition of `SupBotHom`s as a `SupBotHom`. -/
@[to_dual /-- Composition of `InfTopHom`s as an `InfTopHom`. -/]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : SupBotHom β γ) (g : SupBotHom α β)
  body: { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }

@[to_dual (attr := simp)]

中文:
定义 comp
  签名: (f : SupBot态射 β γ) (g : SupBot态射 α β)
  定义体: { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }

@[to_dual (attr := simp)]

Depends on / 依赖: f.toBotHom.comp, f.toSupHom.comp, g.toBotHom, g.toSupHom, toBotHom, toSupHom
-/
def comp (f : SupBotHom β γ) (g : SupBotHom α β) : SupBotHom α γ :=
  { f.toSupHom.comp g.toSupHom, f.toBotHom.comp g.toBotHom with }

@[to_dual (attr := simp)]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : SupBotHom β γ) (g : SupBotHom α β)
  statement: (f.comp g : α -> γ) = f ∘ g
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_comp
  条件: (f : SupBot态射 β γ) (g : SupBot态射 α β)
  结论: (f.comp g : α -> γ) = f ∘ g
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_comp (f : SupBotHom β γ) (g : SupBotHom α β) : (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : SupBotHom β γ) (g : SupBotHom α β) (a : α)
  statement: (f.comp g) a = f (g a)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 comp_apply
  条件: (f : SupBot态射 β γ) (g : SupBot态射 α β) (a : α)
  结论: (f.comp g) a = f (g a)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem comp_apply (f : SupBotHom β γ) (g : SupBotHom α β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : SupBotHom γ δ) (g : SupBotHom β γ) (h : SupBotHom α β)
  proof: rfl

中文:
定理 comp_assoc
  条件: (f : SupBot态射 γ δ) (g : SupBot态射 β γ) (h : SupBot态射 α β)
  证明: rfl
-/
theorem comp_assoc (f : SupBotHom γ δ) (g : SupBotHom β γ) (h : SupBotHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : SupBotHom α β)
  statement: f.comp (SupBotHom.id α) = f
  proof: rfl

中文:
定理 comp_id
  条件: (f : SupBot态射 α β)
  结论: f.comp (SupBot态射.id α) = f
  证明: rfl
-/
@[to_dual (attr := simp)] theorem comp_id (f : SupBotHom α β) : f.comp (SupBotHom.id α) = f := rfl

/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : SupBotHom α β)
  statement: (SupBotHom.id β).comp f = f
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 id_comp
  条件: (f : SupBot态射 α β)
  结论: (SupBot态射.id β).comp f = f
  证明: rfl

@[to_dual (attr := simp)]
-/
@[to_dual (attr := simp)] theorem id_comp (f : SupBotHom α β) : (SupBotHom.id β).comp f = f := rfl

@[to_dual (attr := simp)]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective f)
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]

中文:
定理 cancel_right
  条件: {g₁ g₂ : SupBot态射 β γ} {f : SupBot态射 α β} (hf : 满射 f)
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : SupBotHom β γ} {f : SupBotHom α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, fun h => congr_arg₂ _ h rfl⟩

@[to_dual (attr := simp)]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g)
  proof: ⟨fun h => SupBotHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : SupBot态射 β γ} {f₁ f₂ : SupBot态射 α β} (hg : 单射 g)
  证明: ⟨fun h => SupBotHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: SupBotHom, SupBotHom.ext, comp_apply, congr_arg
-/
theorem cancel_left {g : SupBotHom β γ} {f₁ f₂ : SupBotHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => SupBotHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end Sup

variable [SemilatticeSup β] [OrderBot β]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (SupBotHom α β)
  body: ⟨fun f g => { f.toBotHom ⊔ g.toBotHom with toSupHom := f.toSupHom ⊔ g.toSupHom }⟩

@[to_dual]

中文:
实例 :
  签名: 最大值 (SupBot态射 α β)
  定义体: ⟨fun f g => { f.toBotHom ⊔ g.toBotHom with toSupHom := f.toSupHom ⊔ g.toSupHom }⟩

@[to_dual]

Depends on / 依赖: f.toBotHom, f.toSupHom, g.toBotHom, g.toSupHom, toBotHom, toSupHom
-/
instance : Max (SupBotHom α β) :=
  ⟨fun f g => { f.toBotHom ⊔ g.toBotHom with toSupHom := f.toSupHom ⊔ g.toSupHom }⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (SupBotHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]

中文:
实例 :
  签名: 偏序 (SupBot态射 α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (SupBotHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SemilatticeSup (SupBotHom α β)
  body: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual]

中文:
实例 :
  签名: SemilatticeSup (SupBot态射 α β)
  定义体: DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual]

Depends on / 依赖: DFunLike, DFunLike.coe_injective.semilatticeSup, coe_injective, semilatticeSup
-/
instance : SemilatticeSup (SupBotHom α β) :=
  DFunLike.coe_injective.semilatticeSup _ .rfl .rfl fun _ _ => rfl

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (SupBotHom α β)
  body: ⟨⊥, rfl⟩
  bot_le _ _ := bot_le

@[to_dual (attr := simp)]

中文:
实例 :
  签名: 有底序 (SupBot态射 α β)
  定义体: ⟨⊥, rfl⟩
  bot_le _ _ := bot_le

@[to_dual (attr := simp)]
-/
instance : OrderBot (SupBotHom α β) where
  bot := ⟨⊥, rfl⟩
  bot_le _ _ := bot_le

@[to_dual (attr := simp)]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (f g : SupBotHom α β)
  statement: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_sup
  条件: (f g : SupBot态射 α β)
  结论: ⇑(f ⊔ g) = ⇑f ⊔ ⇑g
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_sup (f g : SupBotHom α β) : ⇑(f ⊔ g) = ⇑f ⊔ ⇑g :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ⇑(⊥ : SupBotHom α β) = ⊥
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_bot
  结论: ⇑(⊥ : SupBot态射 α β) = ⊥
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_bot : ⇑(⊥ : SupBotHom α β) = ⊥ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `sup_apply` / 定理 `sup_apply`

English:
theorem sup_apply
  given: (f g : SupBotHom α β) (a : α)
  statement: (f ⊔ g) a = f a ⊔ g a
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 sup_apply
  条件: (f g : SupBot态射 α β) (a : α)
  结论: (f ⊔ g) a = f a ⊔ g a
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem sup_apply (f g : SupBotHom α β) (a : α) : (f ⊔ g) a = f a ⊔ g a :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `bot_apply` / 定理 `bot_apply`

English:
theorem bot_apply
  given: (a : α)
  statement: (⊥ : SupBotHom α β) a = ⊥
  proof: rfl

中文:
定理 bot_apply
  条件: (a : α)
  结论: (⊥ : SupBot态射 α β) a = ⊥
  证明: rfl
-/
theorem bot_apply (a : α) : (⊥ : SupBotHom α β) a = ⊥ :=
  rfl

/-- `Subtype.val` as a `SupBotHom`. -/
@[to_dual (rename := Pbot -> Ptop, Psup -> Pinf) /-- `Subtype.val` as an `InfTopHom`. -/]
/--
Definition of `subtypeVal` / `subtypeVal` 的定义

English:
definition subtypeVal
  signature: {P : β -> Prop}
  body: Subtype.orderBot Pbot
    letI := Subtype.semilatticeSup Psup
    SupBotHom {x : β // P x} β :=
  letI := Subtype.orderBot Pbot
  letI := Subtype.semilatticeSup Psup
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_bot Pbot])

@[to_dual (attr := simp) (rename := Pbot -> Ptop, Psup -> Pinf)]

中文:
定义 subtypeVal
  签名: {P : β -> 命题}
  定义体: Subtype.orderBot Pbot
    letI := Subtype.semilatticeSup Psup
    SupBotHom {x : β // P x} β :=
  letI := Subtype.orderBot Pbot
  letI := Subtype.semilatticeSup Psup
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_bot Pbot])

@[to_dual (attr := simp) (rename := Pbot -> Ptop, Psup -> Pinf)]

Depends on / 依赖: Subtype, Subtype.orderBot, orderBot
-/
def subtypeVal {P : β -> Prop}
    (Pbot : P ⊥) (Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)) :
    letI := Subtype.orderBot Pbot
    letI := Subtype.semilatticeSup Psup
    SupBotHom {x : β // P x} β :=
  letI := Subtype.orderBot Pbot
  letI := Subtype.semilatticeSup Psup
  .mk (SupHom.subtypeVal Psup) (by simp [Subtype.coe_bot Pbot])

@[to_dual (attr := simp) (rename := Pbot -> Ptop, Psup -> Pinf)]
/--
lemma `subtypeVal_apply` / 引理 `subtypeVal_apply`

English:
lemma subtypeVal_apply
  statement: {P : β -> Prop}
  proof: rfl

@[to_dual (attr := simp) (rename := Pbot -> Ptop, Psup -> Pinf)]

中文:
引理 subtypeVal_apply
  结论: {P : β -> 命题}
  证明: rfl

@[to_dual (attr := simp) (rename := Pbot -> Ptop, Psup -> Pinf)]
-/
lemma subtypeVal_apply {P : β -> Prop}
    (Pbot : P ⊥) (Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)) (x : {x : β // P x}) :
    subtypeVal Pbot Psup x = x := rfl

@[to_dual (attr := simp) (rename := Pbot -> Ptop, Psup -> Pinf)]
/--
lemma `subtypeVal_coe` / 引理 `subtypeVal_coe`

English:
lemma subtypeVal_coe
  statement: {P : β -> Prop}
  proof: rfl

中文:
引理 subtypeVal_coe
  结论: {P : β -> 命题}
  证明: rfl
-/
lemma subtypeVal_coe {P : β -> Prop}
    (Pbot : P ⊥) (Psup : forall ⦃x y : β⦄, P x -> P y -> P (x ⊔ y)) :
    ⇑(subtypeVal Pbot Psup) = Subtype.val := rfl

end SupBotHom

/-! ### Bounded lattice homomorphisms -/

namespace BoundedLatticeHom

variable [Lattice α] [Lattice β] [Lattice γ] [Lattice δ] [BoundedOrder α] [BoundedOrder β]
  [BoundedOrder γ] [BoundedOrder δ]

/--
Definition of `toBoundedOrderHom` / `toBoundedOrderHom` 的定义

English:
definition toBoundedOrderHom
  signature: (f : BoundedLatticeHom α β)
  body: { f, (f.toLatticeHom : α ->o β) with }

中文:
定义 toBoundedOrderHom
  签名: (f : 有界格态射 α β)
  定义体: { f, (f.toLatticeHom : α ->o β) with }

Depends on / 依赖: f.toLatticeHom, toLatticeHom
-/
def toBoundedOrderHom (f : BoundedLatticeHom α β) : BoundedOrderHom α β :=
  { f, (f.toLatticeHom : α ->o β) with }

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (BoundedLatticeHom α β) α β where
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

中文:
实例 instFunLike
  签名: : 函数状 (有界格态射 α β) α β where
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (BoundedLatticeHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

/--
Instance `instBoundedLatticeHomClass` / 实例 `instBoundedLatticeHomClass`

English:
instance instBoundedLatticeHomClass
  signature: : BoundedLatticeHomClass (BoundedLatticeHom α β) α β where
  body: f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

中文:
实例 instBoundedLatticeHomClass
  签名: : 有界格态射类 (有界格态射 α β) α β where
  定义体: f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

Depends on / 依赖: f.map_sup, map_sup
-/
instance instBoundedLatticeHomClass : BoundedLatticeHomClass (BoundedLatticeHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_bot f := f.map_bot'

/--
lemma `toFun_eq_coe` / 引理 `toFun_eq_coe`

English:
lemma toFun_eq_coe
  given: (f : BoundedLatticeHom α β)
  statement: f.toFun = f
  proof: rfl

中文:
引理 toFun_eq_coe
  条件: (f : 有界格态射 α β)
  结论: f.toFun = f
  证明: rfl
-/
@[simp] lemma toFun_eq_coe (f : BoundedLatticeHom α β) : f.toFun = f := rfl

/--
lemma `coe_toLatticeHom` / 引理 `coe_toLatticeHom`

English:
lemma coe_toLatticeHom
  given: (f : BoundedLatticeHom α β)
  statement: ⇑f.toLatticeHom = f
  proof: rfl
@[to_dual (attr := simp)]

中文:
引理 coe_toLatticeHom
  条件: (f : 有界格态射 α β)
  结论: ⇑f.toLatticeHom = f
  证明: rfl
@[to_dual (attr := simp)]
-/
@[simp] lemma coe_toLatticeHom (f : BoundedLatticeHom α β) : ⇑f.toLatticeHom = f := rfl
@[to_dual (attr := simp)]
/--
lemma `coe_toSupBotHom` / 引理 `coe_toSupBotHom`

English:
lemma coe_toSupBotHom
  given: (f : BoundedLatticeHom α β)
  statement: ⇑f.toSupBotHom = f
  proof: rfl

中文:
引理 coe_toSupBotHom
  条件: (f : 有界格态射 α β)
  结论: ⇑f.toSupBotHom = f
  证明: rfl
-/
lemma coe_toSupBotHom (f : BoundedLatticeHom α β) : ⇑f.toSupBotHom = f := rfl
/--
lemma `coe_toBoundedOrderHom` / 引理 `coe_toBoundedOrderHom`

English:
lemma coe_toBoundedOrderHom
  given: (f : BoundedLatticeHom α β)
  statement: ⇑f.toBoundedOrderHom = f
  proof: rfl

中文:
引理 coe_toBoundedOrderHom
  条件: (f : 有界格态射 α β)
  结论: ⇑f.toBoundedOrderHom = f
  证明: rfl
-/
@[simp] lemma coe_toBoundedOrderHom (f : BoundedLatticeHom α β) : ⇑f.toBoundedOrderHom = f := rfl
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (f : LatticeHom α β) (hf hf')
  statement: ⇑(mk f hf hf') = f
  proof: rfl

@[ext]

中文:
引理 coe_mk
  条件: (f : 格态射 α β) (hf hf')
  结论: ⇑(mk f hf hf') = f
  证明: rfl

@[ext]
-/
@[simp] lemma coe_mk (f : LatticeHom α β) (hf hf') : ⇑(mk f hf hf') = f := rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : BoundedLatticeHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : 有界格态射 α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : BoundedLatticeHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : BoundedLatticeHom α β) (f' : α -> β) (h : f' = f)
  body: { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }

@[simp]

中文:
定义 copy
  签名: (f : 有界格态射 α β) (f' : α -> β) (h : f' = f)
  定义体: { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }

@[simp]
-/
protected def copy (f : BoundedLatticeHom α β) (f' : α -> β) (h : f' = f) : BoundedLatticeHom α β :=
  { f.toLatticeHom.copy f' h, f.toBoundedOrderHom.copy f' h with }

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : BoundedLatticeHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : 有界格态射 α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : BoundedLatticeHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : BoundedLatticeHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : 有界格态射 α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : BoundedLatticeHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : BoundedLatticeHom α α
  body: { LatticeHom.id α, BoundedOrderHom.id α with }

中文:
定义 id
  签名: : 有界格态射 α α
  定义体: { LatticeHom.id α, BoundedOrderHom.id α with }
-/
protected def id : BoundedLatticeHom α α :=
  { LatticeHom.id α, BoundedOrderHom.id α with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (BoundedLatticeHom α α)
  body: ⟨BoundedLatticeHom.id α⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 可居 (有界格态射 α α)
  定义体: ⟨BoundedLatticeHom.id α⟩

@[simp, norm_cast]

Depends on / 依赖: BoundedLatticeHom, BoundedLatticeHom.id
-/
instance : Inhabited (BoundedLatticeHom α α) :=
  ⟨BoundedLatticeHom.id α⟩

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(BoundedLatticeHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(有界格态射.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(BoundedLatticeHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: BoundedLatticeHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: 有界格态射.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : BoundedLatticeHom.id α a = a :=
  rfl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β)
  body: { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }

@[simp]

中文:
定义 comp
  签名: (f : 有界格态射 β γ) (g : 有界格态射 α β)
  定义体: { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }

@[simp]

Depends on / 依赖: f.toBoundedOrderHom.comp, f.toLatticeHom.comp, g.toBoundedOrderHom, g.toLatticeHom, toBoundedOrderHom, toLatticeHom
-/
def comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) : BoundedLatticeHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom, f.toBoundedOrderHom.comp g.toBoundedOrderHom with }

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : 有界格态射 β γ) (g : 有界格态射 α β)
  证明: rfl

@[simp]
-/
theorem coe_comp (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : α -> γ) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : 有界格态射 β γ) (g : 有界格态射 α β) (a : α)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) (a : α) :
    (f.comp g) a = f (g a) :=
  rfl

@[simp]
-- `simp`-normal form of `coe_comp_lattice_hom`
/--
theorem `coe_comp_lattice_hom'` / 定理 `coe_comp_lattice_hom'`

English:
theorem coe_comp_lattice_hom'
  given: (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β)
  proof: rfl

中文:
定理 coe_comp_lattice_hom'
  条件: (f : 有界格态射 β γ) (g : 有界格态射 α β)
  证明: rfl
-/
theorem coe_comp_lattice_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (⟨(f : SupHom β γ).comp g, map_inf (f.comp g)⟩ : LatticeHom α γ) =
      (f : LatticeHom β γ).comp g :=
  rfl

/--
theorem `coe_comp_lattice_hom` / 定理 `coe_comp_lattice_hom`

English:
theorem coe_comp_lattice_hom
  given: (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_comp_lattice_hom
  条件: (f : 有界格态射 β γ) (g : 有界格态射 α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_comp_lattice_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : LatticeHom α γ) = (f : LatticeHom β γ).comp g :=
  rfl

@[to_dual (attr := simp)]
-- `simp`-normal form of `coe_comp_sup_hom`
/--
theorem `coe_comp_sup_hom'` / 定理 `coe_comp_sup_hom'`

English:
theorem coe_comp_sup_hom'
  given: (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β)
  proof: rfl

@[to_dual]

中文:
定理 coe_comp_sup_hom'
  条件: (f : 有界格态射 β γ) (g : 有界格态射 α β)
  证明: rfl

@[to_dual]
-/
theorem coe_comp_sup_hom' (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    ⟨f ∘ g, map_sup (f.comp g)⟩ = (f : SupHom β γ).comp g :=
  rfl

@[to_dual]
/--
theorem `coe_comp_sup_hom` / 定理 `coe_comp_sup_hom`

English:
theorem coe_comp_sup_hom
  given: (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β)
  proof: rfl

@[simp]

中文:
定理 coe_comp_sup_hom
  条件: (f : 有界格态射 β γ) (g : 有界格态射 α β)
  证明: rfl

@[simp]
-/
theorem coe_comp_sup_hom (f : BoundedLatticeHom β γ) (g : BoundedLatticeHom α β) :
    (f.comp g : SupHom α γ) = (f : SupHom β γ).comp g :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: (f : BoundedLatticeHom γ δ) (g : BoundedLatticeHom β γ)
  proof: rfl

中文:
定理 comp_assoc
  结论: (f : 有界格态射 γ δ) (g : 有界格态射 β γ)
  证明: rfl
-/
theorem comp_assoc (f : BoundedLatticeHom γ δ) (g : BoundedLatticeHom β γ)
    (h : BoundedLatticeHom α β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : BoundedLatticeHom α β)
  statement: f.comp (BoundedLatticeHom.id α) = f
  proof: rfl

中文:
定理 comp_id
  条件: (f : 有界格态射 α β)
  结论: f.comp (有界格态射.id α) = f
  证明: rfl
-/
@[simp] theorem comp_id (f : BoundedLatticeHom α β) : f.comp (BoundedLatticeHom.id α) = f := rfl

/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : BoundedLatticeHom α β)
  statement: (BoundedLatticeHom.id β).comp f = f
  proof: rfl

@[simp]

中文:
定理 id_comp
  条件: (f : 有界格态射 α β)
  结论: (有界格态射.id β).comp f = f
  证明: rfl

@[simp]
-/
@[simp] theorem id_comp (f : BoundedLatticeHom α β) : (BoundedLatticeHom.id β).comp f = f := rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  statement: {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β}
  proof: ⟨fun h => BoundedLatticeHom.ext hf.forall.2 DFunLike.ext_iff.1 h,
    fun h => congr_arg₂ _ h rfl⟩

@[simp]

中文:
定理 cancel_right
  结论: {g₁ g₂ : 有界格态射 β γ} {f : 有界格态射 α β}
  证明: ⟨fun h => BoundedLatticeHom.ext hf.forall.2 DFunLike.ext_iff.1 h,
    fun h => congr_arg₂ _ h rfl⟩

@[simp]

Depends on / 依赖: BoundedLatticeHom, BoundedLatticeHom.ext, DFunLike, DFunLike.ext_iff, ext_iff, hf.forall
-/
theorem cancel_right {g₁ g₂ : BoundedLatticeHom β γ} {f : BoundedLatticeHom α β}
    (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => BoundedLatticeHom.ext hf.forall.2 DFunLike.ext_iff.1 h,
    fun h => congr_arg₂ _ h rfl⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (hg : Injective g)
  proof: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: {g : 有界格态射 β γ} {f₁ f₂ : 有界格态射 α β} (hg : 单射 g)
  证明: ⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: comp_apply, congr_arg
-/
theorem cancel_left {g : BoundedLatticeHom β γ} {f₁ f₂ : BoundedLatticeHom α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

/-- `Subtype.val` as a `BoundedLatticeHom`. -/
@[to_dual self (reorder := Pbot Ptop, Psup Pinf)]
/--
Definition of `subtypeVal` / `subtypeVal` 的定义

English:
definition subtypeVal
  signature: {P : β -> Prop} (Pbot : P ⊥) (Ptop : P ⊤)
  body: Subtype.lattice Psup Pinf
    letI := Subtype.boundedOrder Pbot Ptop
    BoundedLatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  letI := Subtype.boundedOrder Pbot Ptop
  .mk (.subtypeVal Psup Pinf) (by simp [Subtype.coe_top Ptop]) (by simp [Subtype.coe_bot Pbot])

@[simp]

中文:
定义 subtypeVal
  签名: {P : β -> 命题} (Pbot : P ⊥) (Ptop : P ⊤)
  定义体: Subtype.lattice Psup Pinf
    letI := Subtype.boundedOrder Pbot Ptop
    BoundedLatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  letI := Subtype.boundedOrder Pbot Ptop
  .mk (.subtypeVal Psup Pinf) (by simp [Subtype.coe_top Ptop]) (by simp [Subtype.coe_bot Pbot])

@[simp]

Depends on / 依赖: Subtype, Subtype.lattice, lattice
-/
def subtypeVal {P : β -> Prop} (Pbot : P ⊥) (Ptop : P ⊤)
    (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) :
    letI := Subtype.lattice Psup Pinf
    letI := Subtype.boundedOrder Pbot Ptop
    BoundedLatticeHom {x : β // P x} β :=
  letI := Subtype.lattice Psup Pinf
  letI := Subtype.boundedOrder Pbot Ptop
  .mk (.subtypeVal Psup Pinf) (by simp [Subtype.coe_top Ptop]) (by simp [Subtype.coe_bot Pbot])

@[simp]
/--
lemma `subtypeVal_apply` / 引理 `subtypeVal_apply`

English:
lemma subtypeVal_apply
  statement: {P : β -> Prop}
  proof: rfl

@[simp]

中文:
引理 subtypeVal_apply
  结论: {P : β -> 命题}
  证明: rfl

@[simp]
-/
lemma subtypeVal_apply {P : β -> Prop}
    (Pbot : P ⊥) (Ptop : P ⊤) (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y))
    (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) (x : {x : β // P x}) :
    subtypeVal Pbot Ptop Psup Pinf x = x := rfl

@[simp]
/--
lemma `subtypeVal_coe` / 引理 `subtypeVal_coe`

English:
lemma subtypeVal_coe
  statement: {P : β -> Prop} (Pbot : P ⊥) (Ptop : P ⊤)
  proof: rfl

中文:
引理 subtypeVal_coe
  结论: {P : β -> 命题} (Pbot : P ⊥) (Ptop : P ⊤)
  证明: rfl
-/
lemma subtypeVal_coe {P : β -> Prop} (Pbot : P ⊥) (Ptop : P ⊤)
    (Psup : forall ⦃x y⦄, P x -> P y -> P (x ⊔ y)) (Pinf : forall ⦃x y⦄, P x -> P y -> P (x ⊓ y)) :
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
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ where
  body: ⟨SupHom.dual f.toSupHom, f.map_bot'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩

中文:
定义 dual
  签名: : SupBot态射 α β ≃ InfTop态射 αᵒᵈ βᵒᵈ where
  定义体: ⟨SupHom.dual f.toSupHom, f.map_bot'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩

Depends on / 依赖: SupHom, SupHom.dual, f.map_bot, f.toSupHom, map_bot, toSupHom
-/
def dual : SupBotHom α β ≃ InfTopHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨SupHom.dual f.toSupHom, f.map_bot'⟩
  invFun f := ⟨SupHom.dual.symm f.toInfHom, f.map_top'⟩

/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: SupBotHom.dual (SupBotHom.id α) = InfTopHom.id _
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 dual_id
  结论: SupBot态射.dual (SupBot态射.id α) = InfTop态射.id _
  证明: rfl

@[to_dual (attr := simp)]
-/
@[to_dual (attr := simp)] theorem dual_id : SupBotHom.dual (SupBotHom.id α) = InfTopHom.id _ := rfl

@[to_dual (attr := simp)]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : SupBotHom β γ) (f : SupBotHom α β)
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 dual_comp
  条件: (g : SupBot态射 β γ) (f : SupBot态射 α β)
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem dual_comp (g : SupBotHom β γ) (f : SupBotHom α β) :
    SupBotHom.dual (g.comp f) = (SupBotHom.dual g).comp (SupBotHom.dual f) :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  statement: SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 symm_dual_id
  结论: SupBot态射.dual.symm (InfTop态射.id _) = SupBot态射.id α
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem symm_dual_id : SupBotHom.dual.symm (InfTopHom.id _) = SupBotHom.id α :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : InfTopHom βᵒᵈ γᵒᵈ) (f : InfTopHom αᵒᵈ βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : InfTop态射 βᵒᵈ γᵒᵈ) (f : InfTop态射 αᵒᵈ βᵒᵈ)
  证明: rfl
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
/--
Definition of `dual` / `dual` 的定义

English:
definition dual
  signature: : BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ where
  body: ⟨LatticeHom.dual f.toLatticeHom, f.map_bot', f.map_top'⟩
  invFun f := ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩

@[simp]

中文:
定义 dual
  签名: : 有界格态射 α β ≃ 有界格态射 αᵒᵈ βᵒᵈ where
  定义体: ⟨LatticeHom.dual f.toLatticeHom, f.map_bot', f.map_top'⟩
  invFun f := ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩

@[simp]
-/
protected def dual : BoundedLatticeHom α β ≃ BoundedLatticeHom αᵒᵈ βᵒᵈ where
  toFun f := ⟨LatticeHom.dual f.toLatticeHom, f.map_bot', f.map_top'⟩
  invFun f := ⟨LatticeHom.dual.symm f.toLatticeHom, f.map_bot', f.map_top'⟩

@[simp]
/--
theorem `dual_id` / 定理 `dual_id`

English:
theorem dual_id
  statement: BoundedLatticeHom.dual (BoundedLatticeHom.id α) = BoundedLatticeHom.id _
  proof: rfl

@[simp]

中文:
定理 dual_id
  结论: 有界格态射.dual (有界格态射.id α) = 有界格态射.id _
  证明: rfl

@[simp]
-/
theorem dual_id : BoundedLatticeHom.dual (BoundedLatticeHom.id α) = BoundedLatticeHom.id _ :=
  rfl

@[simp]
/--
theorem `dual_comp` / 定理 `dual_comp`

English:
theorem dual_comp
  given: (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β)
  proof: rfl

@[simp]

中文:
定理 dual_comp
  条件: (g : 有界格态射 β γ) (f : 有界格态射 α β)
  证明: rfl

@[simp]
-/
theorem dual_comp (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
    BoundedLatticeHom.dual (g.comp f) =
      (BoundedLatticeHom.dual g).comp (BoundedLatticeHom.dual f) :=
  rfl

@[simp]
/--
theorem `symm_dual_id` / 定理 `symm_dual_id`

English:
theorem symm_dual_id
  proof: rfl

@[simp]

中文:
定理 symm_dual_id
  证明: rfl

@[simp]
-/
theorem symm_dual_id :
    BoundedLatticeHom.dual.symm (BoundedLatticeHom.id _) = BoundedLatticeHom.id α :=
  rfl

@[simp]
/--
theorem `symm_dual_comp` / 定理 `symm_dual_comp`

English:
theorem symm_dual_comp
  given: (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ βᵒᵈ)
  proof: rfl

中文:
定理 symm_dual_comp
  条件: (g : 有界格态射 βᵒᵈ γᵒᵈ) (f : 有界格态射 αᵒᵈ βᵒᵈ)
  证明: rfl
-/
theorem symm_dual_comp (g : BoundedLatticeHom βᵒᵈ γᵒᵈ) (f : BoundedLatticeHom αᵒᵈ βᵒᵈ) :
    BoundedLatticeHom.dual.symm (g.comp f) =
      (BoundedLatticeHom.dual.symm g).comp (BoundedLatticeHom.dual.symm f) :=
  rfl

end BoundedLatticeHom
