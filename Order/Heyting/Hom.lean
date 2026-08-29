/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Hom.BoundedLattice

/-!
# Heyting algebra morphisms

A Heyting homomorphism between two Heyting algebras is a bounded lattice homomorphism that preserves
Heyting implication.

We use the `DFunLike` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `HeytingHom`: Heyting homomorphisms.
* `CoheytingHom`: Co-Heyting homomorphisms.
* `BiheytingHom`: Bi-Heyting homomorphisms.

## Typeclasses

* `HeytingHomClass`
* `CoheytingHomClass`
* `BiheytingHomClass`
-/

@[expose] public section


open Function

variable {F α β γ δ : Type*}

/--
Definition of `HeytingHom` / `HeytingHom` 的定义

English:
structure HeytingHom
  parameters: (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β]
  axioms and operations (2):
    - map_bot' : toFun ⊥ = ⊥
    - map_himp' : forall a b, toFun (a ⇨ b) = toFun a ⇨ toFun b

中文:
结构 HeytingHom
  参数: (α β : 类型) [HeytingAlgebra α] [HeytingAlgebra β]
  公理与运算 (2 个):
    - map_bot' : toFun ⊥ = ⊥
    - map_himp' : 对任意 a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
-/
structure HeytingHom (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a Heyting homomorphism preserves the bottom element. -/
  protected map_bot' : toFun ⊥ = ⊥
  /-- The proposition that a Heyting homomorphism preserves the Heyting implication. -/
  protected map_himp' : forall a b, toFun (a ⇨ b) = toFun a ⇨ toFun b

/--
Definition of `CoheytingHom` / `CoheytingHom` 的定义

English:
structure CoheytingHom
  parameters: (α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β]
  axioms and operations (2):
    - map_top' : toFun ⊤ = ⊤
    - map_sdiff' : forall a b, toFun (a \ b) = toFun a \ toFun b

中文:
结构 CoheytingHom
  参数: (α β : 类型) [CoheytingAlgebra α] [CoheytingAlgebra β]
  公理与运算 (2 个):
    - map_top' : toFun ⊤ = ⊤
    - map_sdiff' : 对任意 a b, toFun (a \ b) = toFun a \ toFun b
-/
structure CoheytingHom (α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a co-Heyting homomorphism preserves the top element. -/
  protected map_top' : toFun ⊤ = ⊤
  /-- The proposition that a co-Heyting homomorphism preserves the difference operation. -/
  protected map_sdiff' : forall a b, toFun (a \ b) = toFun a \ toFun b

/--
Definition of `BiheytingHom` / `BiheytingHom` 的定义

English:
structure BiheytingHom
  parameters: (α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β]
  axioms and operations (2):
    - map_himp' : forall a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
    - map_sdiff' : forall a b, toFun (a \ b) = toFun a \ toFun b

中文:
结构 BiheytingHom
  参数: (α β : 类型) [BiheytingAlgebra α] [BiheytingAlgebra β]
  公理与运算 (2 个):
    - map_himp' : 对任意 a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
    - map_sdiff' : 对任意 a b, toFun (a \ b) = toFun a \ toFun b
-/
structure BiheytingHom (α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a bi-Heyting homomorphism preserves the Heyting implication. -/
  protected map_himp' : forall a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
  /-- The proposition that a bi-Heyting homomorphism preserves the difference operation. -/
  protected map_sdiff' : forall a b, toFun (a \ b) = toFun a \ toFun b

/--
Definition of `HeytingHomClass` / `HeytingHomClass` 的定义

English:
class HeytingHomClass
  parameters: (F α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] [FunLike F α β]
  extends: LatticeHomClass F α β
  axioms and operations (2):
    - map_bot((f : F)) : f ⊥ = ⊥
    - map_himp((f : F)) : forall a b, f (a ⇨ b) = f a ⇨ f b

中文:
类 HeytingHomClass
  参数: (F α β : 类型) [HeytingAlgebra α] [HeytingAlgebra β] [FunLike F α β]
  继承: LatticeHomClass F α β
  公理与运算 (2 个):
    - map_bot((f : F)) : f ⊥ = ⊥
    - map_himp((f : F)) : 对任意 a b, f (a ⇨ b) = f a ⇨ f b
-/
class HeytingHomClass (F α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] [FunLike F α β] : Prop
    extends LatticeHomClass F α β where
  /-- The proposition that a Heyting homomorphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥
  /-- The proposition that a Heyting homomorphism preserves the Heyting implication. -/
  map_himp (f : F) : forall a b, f (a ⇨ b) = f a ⇨ f b

/--
Definition of `CoheytingHomClass` / `CoheytingHomClass` 的定义

English:
class CoheytingHomClass
  parameters: (F α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] [FunLike F α β]
  extends: LatticeHomClass F α β
  axioms and operations (2):
    - map_top((f : F)) : f ⊤ = ⊤
    - map_sdiff((f : F)) : forall a b, f (a \ b) = f a \ f b

中文:
类 CoheytingHomClass
  参数: (F α β : 类型) [CoheytingAlgebra α] [CoheytingAlgebra β] [FunLike F α β]
  继承: LatticeHomClass F α β
  公理与运算 (2 个):
    - map_top((f : F)) : f ⊤ = ⊤
    - map_sdiff((f : F)) : 对任意 a b, f (a \ b) = f a \ f b
-/
class CoheytingHomClass (F α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] [FunLike F α β] :
    Prop
  extends LatticeHomClass F α β where
  /-- The proposition that a co-Heyting homomorphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- The proposition that a co-Heyting homomorphism preserves the difference operation. -/
  map_sdiff (f : F) : forall a b, f (a \ b) = f a \ f b

/--
Definition of `BiheytingHomClass` / `BiheytingHomClass` 的定义

English:
class BiheytingHomClass
  parameters: (F α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] [FunLike F α β]
  extends: LatticeHomClass F α β
  axioms and operations (2):
    - map_himp((f : F)) : forall a b, f (a ⇨ b) = f a ⇨ f b
    - map_sdiff((f : F)) : forall a b, f (a \ b) = f a \ f b

中文:
类 BiheytingHomClass
  参数: (F α β : 类型) [BiheytingAlgebra α] [BiheytingAlgebra β] [FunLike F α β]
  继承: LatticeHomClass F α β
  公理与运算 (2 个):
    - map_himp((f : F)) : 对任意 a b, f (a ⇨ b) = f a ⇨ f b
    - map_sdiff((f : F)) : 对任意 a b, f (a \ b) = f a \ f b
-/
class BiheytingHomClass (F α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] [FunLike F α β] :
    Prop
  extends LatticeHomClass F α β where
  /-- The proposition that a bi-Heyting homomorphism preserves the Heyting implication. -/
  map_himp (f : F) : forall a b, f (a ⇨ b) = f a ⇨ f b
  /-- The proposition that a bi-Heyting homomorphism preserves the difference operation. -/
  map_sdiff (f : F) : forall a b, f (a \ b) = f a \ f b

export HeytingHomClass (map_himp)

export CoheytingHomClass (map_sdiff)

attribute [simp] map_himp map_sdiff

section Hom

variable [FunLike F α β]

/-! This section passes in some instances implicitly. See note [implicit instance arguments] -/

-- See note [lower instance priority]
instance (priority := 100) HeytingHomClass.toBoundedLatticeHomClass [HeytingAlgebra α]
    {_ : HeytingAlgebra β} [HeytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹HeytingHomClass F α β› with
    map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }

-- See note [lower instance priority]
instance (priority := 100) CoheytingHomClass.toBoundedLatticeHomClass [CoheytingAlgebra α]
    {_ : CoheytingAlgebra β} [CoheytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹CoheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, map_sdiff] }

-- See note [lower instance priority]
instance (priority := 100) BiheytingHomClass.toHeytingHomClass [BiheytingAlgebra α]
    {_ : BiheytingAlgebra β} [BiheytingHomClass F α β] : HeytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, BiheytingHomClass.map_sdiff] }

-- See note [lower instance priority]
instance (priority := 100) BiheytingHomClass.toCoheytingHomClass [BiheytingAlgebra α]
    {_ : BiheytingAlgebra β} [BiheytingHomClass F α β] : CoheytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toHeytingHomClass [HeytingAlgebra α]
    {_ : HeytingAlgebra β} [OrderIsoClass F α β] : HeytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toCoheytingHomClass [CoheytingAlgebra α]
    {_ : CoheytingAlgebra β} [OrderIsoClass F α β] : CoheytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toBiheytingHomClass [BiheytingAlgebra α]
    {_ : BiheytingAlgebra β} [OrderIsoClass F α β] : BiheytingHomClass F α β :=
  { OrderIsoClass.toLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }

end Equiv

variable [FunLike F α β]

/--
Instance `BoundedLatticeHomClass.toBiheytingHomClass` / 实例 `BoundedLatticeHomClass.toBiheytingHomClass`

English:
instance BoundedLatticeHomClass.toBiheytingHomClass
  signature: [BooleanAlgebra α] [BooleanAlgebra β]
  body: { ‹BoundedLatticeHomClass F α β› with
    map_himp := fun f a b => by rw [himp_eq, himp_eq, map_sup, (isCompl_compl.map _).compl_eq]
    map_sdiff := fun f a b => by rw [sdiff_eq, sdiff_eq, map_inf, (isCompl_compl.map _).compl_eq] }

中文:
实例 BoundedLatticeHomClass.toBiheytingHomClass
  签名: [布尔eanAlgebra α] [布尔eanAlgebra β]
  定义体: { ‹BoundedLatticeHomClass F α β› with
    map_himp := fun f a b => by rw [himp_eq, himp_eq, map_sup, (isCompl_compl.map _).compl_eq]
    map_sdiff := fun f a b => by rw [sdiff_eq, sdiff_eq, map_inf, (isCompl_compl.map _).compl_eq] }

Depends on / 依赖: BoundedLatticeHomClass, compl_eq, himp_eq, isCompl_compl, isCompl_compl.map, map_himp, map_inf, map_sdiff, map_sup, sdiff_eq
-/
instance BoundedLatticeHomClass.toBiheytingHomClass [BooleanAlgebra α] [BooleanAlgebra β]
    [BoundedLatticeHomClass F α β] : BiheytingHomClass F α β :=
  { ‹BoundedLatticeHomClass F α β› with
    map_himp := fun f a b => by rw [himp_eq, himp_eq, map_sup, (isCompl_compl.map _).compl_eq]
    map_sdiff := fun f a b => by rw [sdiff_eq, sdiff_eq, map_inf, (isCompl_compl.map _).compl_eq] }

section HeytingAlgebra

open scoped symmDiff

variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] (f : F)

@[simp]
/--
theorem `map_compl` / 定理 `map_compl`

English:
theorem map_compl
  given: (a : α)
  statement: f aᶜ = (f a)ᶜ
  proof: by rw [← himp_bot, ← himp_bot, map_himp, map_bot]

@[simp]

中文:
定理 map_compl
  条件: (a : α)
  结论: f aᶜ = (f a)ᶜ
  证明: by rw [← himp_bot, ← himp_bot, map_himp, map_bot]

@[simp]

Depends on / 依赖: himp_bot, map_bot, map_himp
-/
theorem map_compl (a : α) : f aᶜ = (f a)ᶜ := by rw [← himp_bot, ← himp_bot, map_himp, map_bot]

@[simp]
/--
theorem `map_bihimp` / 定理 `map_bihimp`

English:
theorem map_bihimp
  given: (a b : α)
  statement: f (a ⇔ b) = f a ⇔ f b
  proof: by simp_rw [bihimp, map_inf, map_himp]

中文:
定理 map_bihimp
  条件: (a b : α)
  结论: f (a ⇔ b) = f a ⇔ f b
  证明: by simp_rw [bihimp, map_inf, map_himp]

Depends on / 依赖: bihimp, map_himp, map_inf, simp_rw
-/
theorem map_bihimp (a b : α) : f (a ⇔ b) = f a ⇔ f b := by simp_rw [bihimp, map_inf, map_himp]

end HeytingAlgebra

section CoheytingAlgebra

open scoped symmDiff

variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] (f : F)

@[simp]
/--
theorem `map_hnot` / 定理 `map_hnot`

English:
theorem map_hnot
  given: (a : α)
  statement: f (￢a) = ￢f a
  proof: by rw [← top_sdiff', ← top_sdiff', map_sdiff, map_top]

@[simp]

中文:
定理 map_hnot
  条件: (a : α)
  结论: f (￢a) = ￢f a
  证明: by rw [← top_sdiff', ← top_sdiff', map_sdiff, map_top]

@[simp]

Depends on / 依赖: map_sdiff, map_top, top_sdiff
-/
theorem map_hnot (a : α) : f (￢a) = ￢f a := by rw [← top_sdiff', ← top_sdiff', map_sdiff, map_top]

@[simp]
/--
theorem `map_symmDiff` / 定理 `map_symmDiff`

English:
theorem map_symmDiff
  given: (a b : α)
  statement: f (a ∆ b) = f a ∆ f b
  proof: by simp_rw [symmDiff, map_sup, map_sdiff]

中文:
定理 map_symmDiff
  条件: (a b : α)
  结论: f (a ∆ b) = f a ∆ f b
  证明: by simp_rw [symmDiff, map_sup, map_sdiff]

Depends on / 依赖: map_sdiff, map_sup, simp_rw, symmDiff
-/
theorem map_symmDiff (a b : α) : f (a ∆ b) = f a ∆ f b := by simp_rw [symmDiff, map_sup, map_sdiff]

end CoheytingAlgebra

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [HeytingAlgebra
  signature: α] [HeytingAlgebra β] [HeytingHomClass F α β] : CoeTC F (HeytingHom α β)
  body: ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_bot' := map_bot f
      map_himp' := map_himp f }⟩

中文:
实例 [HeytingAlgebra
  签名: α] [HeytingAlgebra β] [HeytingHomClass F α β] : CoeTC F (HeytingHom α β)
  定义体: ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_bot' := map_bot f
      map_himp' := map_himp f }⟩

Depends on / 依赖: map_bot, map_himp, map_inf, map_sup
-/
instance [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] : CoeTC F (HeytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_bot' := map_bot f
      map_himp' := map_himp f }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CoheytingAlgebra
  signature: α] [CoheytingAlgebra β] [CoheytingHomClass F α β] :
  body: ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_top' := map_top f
      map_sdiff' := map_sdiff f }⟩

中文:
实例 [CoheytingAlgebra
  签名: α] [CoheytingAlgebra β] [CoheytingHomClass F α β] :
  定义体: ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_top' := map_top f
      map_sdiff' := map_sdiff f }⟩

Depends on / 依赖: map_inf, map_sdiff, map_sup, map_top
-/
instance [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] :
    CoeTC F (CoheytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_top' := map_top f
      map_sdiff' := map_sdiff f }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [BiheytingAlgebra
  signature: α] [BiheytingAlgebra β] [BiheytingHomClass F α β] :
  body: ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_himp' := map_himp f
      map_sdiff' := map_sdiff f }⟩

中文:
实例 [BiheytingAlgebra
  签名: α] [BiheytingAlgebra β] [BiheytingHomClass F α β] :
  定义体: ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_himp' := map_himp f
      map_sdiff' := map_sdiff f }⟩

Depends on / 依赖: map_himp, map_inf, map_sdiff, map_sup
-/
instance [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingHomClass F α β] :
    CoeTC F (BiheytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_himp' := map_himp f
      map_sdiff' := map_sdiff f }⟩

namespace HeytingHom

variable [HeytingAlgebra α] [HeytingAlgebra β] [HeytingAlgebra γ] [HeytingAlgebra δ]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (HeytingHom α β) α β where
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

中文:
实例 instFunLike
  签名: : FunLike (HeytingHom α β) α β where
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance instFunLike : FunLike (HeytingHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

/--
Instance `instHeytingHomClass` / 实例 `instHeytingHomClass`

English:
instance instHeytingHomClass
  signature: : HeytingHomClass (HeytingHom α β) α β where
  body: f.map_sup'
  map_inf f := f.map_inf'
  map_bot f := f.map_bot'
  map_himp := HeytingHom.map_himp'

中文:
实例 instHeytingHomClass
  签名: : HeytingHomClass (HeytingHom α β) α β where
  定义体: f.map_sup'
  map_inf f := f.map_inf'
  map_bot f := f.map_bot'
  map_himp := HeytingHom.map_himp'

Depends on / 依赖: f.map_sup, map_sup
-/
instance instHeytingHomClass : HeytingHomClass (HeytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_bot f := f.map_bot'
  map_himp := HeytingHom.map_himp'

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : HeytingHom α β}
  statement: f.toFun = ⇑f
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: {f : HeytingHom α β}
  结论: f.toFun = ⇑f
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe {f : HeytingHom α β} : f.toFun = ⇑f :=
  rfl

@[simp]
/--
theorem `toFun_eq_coe_aux` / 定理 `toFun_eq_coe_aux`

English:
theorem toFun_eq_coe_aux
  given: {f : HeytingHom α β}
  statement: (↑f.toLatticeHom) = ⇑f
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe_aux
  条件: {f : HeytingHom α β}
  结论: (↑f.toLatticeHom) = ⇑f
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe_aux {f : HeytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : HeytingHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : HeytingHom α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : HeytingHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : HeytingHom α β) (f' : α -> β) (h : f' = f)
  body: f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_bot' := by simpa only [h] using map_bot f
  map_himp' := by simpa only [h] using map_himp f

@[simp]

中文:
定义 copy
  签名: (f : HeytingHom α β) (f' : α -> β) (h : f' = f)
  定义体: f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_bot' := by simpa only [h] using map_bot f
  map_himp' := by simpa only [h] using map_himp f

@[simp]
-/
protected def copy (f : HeytingHom α β) (f' : α -> β) (h : f' = f) : HeytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_bot' := by simpa only [h] using map_bot f
  map_himp' := by simpa only [h] using map_himp f

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : HeytingHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : HeytingHom α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : HeytingHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : HeytingHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : HeytingHom α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : HeytingHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : HeytingHom α α
  body: { BotHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_himp' := fun _ _ => rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : HeytingHom α α
  定义体: { BotHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_himp' := fun _ _ => rfl }

@[simp, norm_cast]
-/
protected def id : HeytingHom α α :=
  { BotHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_himp' := fun _ _ => rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(HeytingHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(HeytingHom.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(HeytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: HeytingHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: HeytingHom.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : HeytingHom.id α a = a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (HeytingHom α α)
  body: ⟨HeytingHom.id _⟩

中文:
实例 :
  签名: Inhabited (HeytingHom α α)
  定义体: ⟨HeytingHom.id _⟩

Depends on / 依赖: HeytingHom, HeytingHom.id
-/
instance : Inhabited (HeytingHom α α) :=
  ⟨HeytingHom.id _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (HeytingHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 :
  签名: PartialOrder (HeytingHom α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (HeytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : HeytingHom β γ) (g : HeytingHom α β)
  body: { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_bot' := by simp
    map_himp' := fun a b => by simp }

中文:
定义 comp
  签名: (f : HeytingHom β γ) (g : HeytingHom α β)
  定义体: { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_bot' := by simp
    map_himp' := fun a b => by simp }

Depends on / 依赖: f.toLatticeHom.comp, g.toLatticeHom, map_bot, map_himp, toLatticeHom
-/
def comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_bot' := by simp
    map_himp' := fun a b => by simp }

variable {f f₁ f₂ : HeytingHom α β} {g g₁ g₂ : HeytingHom β γ}

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : HeytingHom β γ) (g : HeytingHom α β)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : HeytingHom β γ) (g : HeytingHom α β)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : HeytingHom β γ) (g : HeytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : HeytingHom β γ) (g : HeytingHom α β) (a : α)
  statement: f.comp g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : HeytingHom β γ) (g : HeytingHom α β) (a : α)
  结论: f.comp g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : HeytingHom β γ) (g : HeytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : HeytingHom α β)
  statement: f.comp (HeytingHom.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : HeytingHom α β)
  结论: f.comp (HeytingHom.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : HeytingHom α β) : f.comp (HeytingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : HeytingHom α β)
  statement: (HeytingHom.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : HeytingHom α β)
  结论: (HeytingHom.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : HeytingHom α β) : (HeytingHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: (hf : Surjective f)
  statement: g₁.comp f = g₂.comp f ↔ g₁ = g₂
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

中文:
定理 cancel_right
  条件: (hf : Surjective f)
  结论: g₁.comp f = g₂.comp f ↔ g₁ = g₂
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: (hg : Injective g)
  statement: g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
  proof: ⟨fun h => HeytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: (hg : Injective g)
  结论: g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
  证明: ⟨fun h => HeytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: HeytingHom, HeytingHom.ext, comp_apply, congr_arg
-/
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => HeytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end HeytingHom

namespace CoheytingHom

variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingAlgebra γ] [CoheytingAlgebra δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (CoheytingHom α β) α β
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

中文:
实例 :
  签名: FunLike (CoheytingHom α β) α β
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (CoheytingHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoheytingHomClass (CoheytingHom α β) α β
  body: f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_sdiff := CoheytingHom.map_sdiff'

中文:
实例 :
  签名: CoheytingHomClass (CoheytingHom α β) α β
  定义体: f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_sdiff := CoheytingHom.map_sdiff'

Depends on / 依赖: f.map_sup, map_sup
-/
instance : CoheytingHomClass (CoheytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_sdiff := CoheytingHom.map_sdiff'

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : CoheytingHom α β}
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: {f : CoheytingHom α β}
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe {f : CoheytingHom α β} : f.toFun = (f : α -> β) :=
  rfl

@[simp]
/--
theorem `toFun_eq_coe_aux` / 定理 `toFun_eq_coe_aux`

English:
theorem toFun_eq_coe_aux
  given: {f : CoheytingHom α β}
  statement: (↑f.toLatticeHom) = ⇑f
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe_aux
  条件: {f : CoheytingHom α β}
  结论: (↑f.toLatticeHom) = ⇑f
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe_aux {f : CoheytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : CoheytingHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : CoheytingHom α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : CoheytingHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : CoheytingHom α β) (f' : α -> β) (h : f' = f)
  body: f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_top' := by simpa only [h] using map_top f
  map_sdiff' := by simpa only [h] using map_sdiff f

@[simp]

中文:
定义 copy
  签名: (f : CoheytingHom α β) (f' : α -> β) (h : f' = f)
  定义体: f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_top' := by simpa only [h] using map_top f
  map_sdiff' := by simpa only [h] using map_sdiff f

@[simp]
-/
protected def copy (f : CoheytingHom α β) (f' : α -> β) (h : f' = f) : CoheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_top' := by simpa only [h] using map_top f
  map_sdiff' := by simpa only [h] using map_sdiff f

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : CoheytingHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : CoheytingHom α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : CoheytingHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : CoheytingHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : CoheytingHom α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : CoheytingHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : CoheytingHom α α
  body: { TopHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_sdiff' := fun _ _ => rfl }

@[simp, norm_cast]

中文:
定义 id
  签名: : CoheytingHom α α
  定义体: { TopHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_sdiff' := fun _ _ => rfl }

@[simp, norm_cast]
-/
protected def id : CoheytingHom α α :=
  { TopHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_sdiff' := fun _ _ => rfl }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(CoheytingHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(CoheytingHom.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(CoheytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: CoheytingHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: CoheytingHom.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : CoheytingHom.id α a = a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (CoheytingHom α α)
  body: ⟨CoheytingHom.id _⟩

中文:
实例 :
  签名: Inhabited (CoheytingHom α α)
  定义体: ⟨CoheytingHom.id _⟩

Depends on / 依赖: CoheytingHom, CoheytingHom.id
-/
instance : Inhabited (CoheytingHom α α) :=
  ⟨CoheytingHom.id _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (CoheytingHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 :
  签名: PartialOrder (CoheytingHom α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (CoheytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : CoheytingHom β γ) (g : CoheytingHom α β)
  body: { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_top' := by simp
    map_sdiff' := fun a b => by simp }

中文:
定义 comp
  签名: (f : CoheytingHom β γ) (g : CoheytingHom α β)
  定义体: { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_top' := by simp
    map_sdiff' := fun a b => by simp }

Depends on / 依赖: f.toLatticeHom.comp, g.toLatticeHom, map_sdiff, map_top, toLatticeHom
-/
def comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : CoheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_top' := by simp
    map_sdiff' := fun a b => by simp }

variable {f f₁ f₂ : CoheytingHom α β} {g g₁ g₂ : CoheytingHom β γ}

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : CoheytingHom β γ) (g : CoheytingHom α β)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : CoheytingHom β γ) (g : CoheytingHom α β)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α)
  statement: f.comp g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α)
  结论: f.comp g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : CoheytingHom γ δ) (g : CoheytingHom β γ) (h : CoheytingHom α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : CoheytingHom γ δ) (g : CoheytingHom β γ) (h : CoheytingHom α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : CoheytingHom γ δ) (g : CoheytingHom β γ) (h : CoheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : CoheytingHom α β)
  statement: f.comp (CoheytingHom.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : CoheytingHom α β)
  结论: f.comp (CoheytingHom.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : CoheytingHom α β) : f.comp (CoheytingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : CoheytingHom α β)
  statement: (CoheytingHom.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : CoheytingHom α β)
  结论: (CoheytingHom.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : CoheytingHom α β) : (CoheytingHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: (hf : Surjective f)
  statement: g₁.comp f = g₂.comp f ↔ g₁ = g₂
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

中文:
定理 cancel_right
  条件: (hf : Surjective f)
  结论: g₁.comp f = g₂.comp f ↔ g₁ = g₂
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: (hg : Injective g)
  statement: g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
  proof: ⟨fun h => CoheytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: (hg : Injective g)
  结论: g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
  证明: ⟨fun h => CoheytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: CoheytingHom, CoheytingHom.ext, comp_apply, congr_arg
-/
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => CoheytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end CoheytingHom

namespace BiheytingHom

variable [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingAlgebra γ] [BiheytingAlgebra δ]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (BiheytingHom α β) α β
  body: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

中文:
实例 :
  签名: FunLike (BiheytingHom α β) α β
  定义体: f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

Depends on / 依赖: f.toFun
-/
instance : FunLike (BiheytingHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BiheytingHomClass (BiheytingHom α β) α β
  body: f.map_sup'
  map_inf f := f.map_inf'
  map_himp f := f.map_himp'
  map_sdiff f := f.map_sdiff'

中文:
实例 :
  签名: BiheytingHomClass (BiheytingHom α β) α β
  定义体: f.map_sup'
  map_inf f := f.map_inf'
  map_himp f := f.map_himp'
  map_sdiff f := f.map_sdiff'

Depends on / 依赖: MulPosMono, MulPosMono.toMulPosStrictMono, f.map_sup, map_sup, toMulPosStrictMono
-/
instance : BiheytingHomClass (BiheytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_himp f := f.map_himp'
  map_sdiff f := f.map_sdiff'

/--
theorem `toFun_eq_coe` / 定理 `toFun_eq_coe`

English:
theorem toFun_eq_coe
  given: {f : BiheytingHom α β}
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[simp]

中文:
定理 toFun_eq_coe
  条件: {f : BiheytingHom α β}
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[simp]
-/
theorem toFun_eq_coe {f : BiheytingHom α β} : f.toFun = (f : α -> β) :=
  rfl

@[simp]
/--
theorem `toFun_eq_coe_aux` / 定理 `toFun_eq_coe_aux`

English:
theorem toFun_eq_coe_aux
  given: {f : BiheytingHom α β}
  statement: (↑f.toLatticeHom) = ⇑f
  proof: rfl

@[ext]

中文:
定理 toFun_eq_coe_aux
  条件: {f : BiheytingHom α β}
  结论: (↑f.toLatticeHom) = ⇑f
  证明: rfl

@[ext]
-/
theorem toFun_eq_coe_aux {f : BiheytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : BiheytingHom α β} (h : forall a, f a = g a)
  statement: f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: {f g : BiheytingHom α β} (h : 对任意 a, f a = g a)
  结论: f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : BiheytingHom α β} (h : forall a, f a = g a) : f = g :=
  DFunLike.ext f g h

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (f : BiheytingHom α β) (f' : α -> β) (h : f' = f)
  body: f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_himp' := by simpa only [h] using map_himp f
  map_sdiff' := by simpa only [h] using map_sdiff f

@[simp]

中文:
定义 copy
  签名: (f : BiheytingHom α β) (f' : α -> β) (h : f' = f)
  定义体: f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_himp' := by simpa only [h] using map_himp f
  map_sdiff' := by simpa only [h] using map_sdiff f

@[simp]

Depends on / 依赖: Ideal.dvdNotUnit_iff_lt, WellFoundedGT, convert, dvdNotUnit_iff_lt, this.wf
-/
protected def copy (f : BiheytingHom α β) (f' : α -> β) (h : f' = f) : BiheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_himp' := by simpa only [h] using map_himp f
  map_sdiff' := by simpa only [h] using map_sdiff f

@[simp]
/--
theorem `coe_copy` / 定理 `coe_copy`

English:
theorem coe_copy
  given: (f : BiheytingHom α β) (f' : α -> β) (h : f' = f)
  statement: ⇑(f.copy f' h) = f'
  proof: rfl

中文:
定理 coe_copy
  条件: (f : BiheytingHom α β) (f' : α -> β) (h : f' = f)
  结论: ⇑(f.copy f' h) = f'
  证明: rfl
-/
theorem coe_copy (f : BiheytingHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl

/--
theorem `copy_eq` / 定理 `copy_eq`

English:
theorem copy_eq
  given: (f : BiheytingHom α β) (f' : α -> β) (h : f' = f)
  statement: f.copy f' h = f
  proof: DFunLike.ext' h

中文:
定理 copy_eq
  条件: (f : BiheytingHom α β) (f' : α -> β) (h : f' = f)
  结论: f.copy f' h = f
  证明: DFunLike.ext' h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem copy_eq (f : BiheytingHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : BiheytingHom α α
  body: { HeytingHom.id _, CoheytingHom.id _ with toLatticeHom := LatticeHom.id _ }

@[simp, norm_cast]

中文:
定义 id
  签名: : BiheytingHom α α
  定义体: { HeytingHom.id _, CoheytingHom.id _ with toLatticeHom := LatticeHom.id _ }

@[simp, norm_cast]
-/
protected def id : BiheytingHom α α :=
  { HeytingHom.id _, CoheytingHom.id _ with toLatticeHom := LatticeHom.id _ }

@[simp, norm_cast]
/--
theorem `coe_id` / 定理 `coe_id`

English:
theorem coe_id
  statement: ⇑(BiheytingHom.id α) = id
  proof: rfl

中文:
定理 coe_id
  结论: ⇑(BiheytingHom.id α) = id
  证明: rfl
-/
theorem coe_id : ⇑(BiheytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
/--
theorem `id_apply` / 定理 `id_apply`

English:
theorem id_apply
  given: (a : α)
  statement: BiheytingHom.id α a = a
  proof: rfl

中文:
定理 id_apply
  条件: (a : α)
  结论: BiheytingHom.id α a = a
  证明: rfl
-/
theorem id_apply (a : α) : BiheytingHom.id α a = a :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (BiheytingHom α α)
  body: ⟨BiheytingHom.id _⟩

中文:
实例 :
  签名: Inhabited (BiheytingHom α α)
  定义体: ⟨BiheytingHom.id _⟩

Depends on / 依赖: BiheytingHom, BiheytingHom.id
-/
instance : Inhabited (BiheytingHom α α) :=
  ⟨BiheytingHom.id _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (BiheytingHom α β)
  body: PartialOrder.lift _ DFunLike.coe_injective

中文:
实例 :
  签名: PartialOrder (BiheytingHom α β)
  定义体: PartialOrder.lift _ DFunLike.coe_injective

Depends on / 依赖: DFunLike, DFunLike.coe_injective, PartialOrder, PartialOrder.lift, coe_injective
-/
instance : PartialOrder (BiheytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (f : BiheytingHom β γ) (g : BiheytingHom α β)
  body: { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_himp' := fun a b => by simp
    map_sdiff' := fun a b => by simp }

中文:
定义 comp
  签名: (f : BiheytingHom β γ) (g : BiheytingHom α β)
  定义体: { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_himp' := fun a b => by simp
    map_sdiff' := fun a b => by simp }

Depends on / 依赖: f.toLatticeHom.comp, g.toLatticeHom, map_himp, map_sdiff, toLatticeHom
-/
def comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : BiheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_himp' := fun a b => by simp
    map_sdiff' := fun a b => by simp }

variable {f f₁ f₂ : BiheytingHom α β} {g g₁ g₂ : BiheytingHom β γ}

@[simp]
/--
theorem `coe_comp` / 定理 `coe_comp`

English:
theorem coe_comp
  given: (f : BiheytingHom β γ) (g : BiheytingHom α β)
  statement: ⇑(f.comp g) = f ∘ g
  proof: rfl

@[simp]

中文:
定理 coe_comp
  条件: (f : BiheytingHom β γ) (g : BiheytingHom α β)
  结论: ⇑(f.comp g) = f ∘ g
  证明: rfl

@[simp]
-/
theorem coe_comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α)
  statement: f.comp g a = f (g a)
  proof: rfl

@[simp]

中文:
定理 comp_apply
  条件: (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α)
  结论: f.comp g a = f (g a)
  证明: rfl

@[simp]
-/
theorem comp_apply (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (f : BiheytingHom γ δ) (g : BiheytingHom β γ) (h : BiheytingHom α β)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (f : BiheytingHom γ δ) (g : BiheytingHom β γ) (h : BiheytingHom α β)
  证明: rfl

@[simp]
-/
theorem comp_assoc (f : BiheytingHom γ δ) (g : BiheytingHom β γ) (h : BiheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : BiheytingHom α β)
  statement: f.comp (BiheytingHom.id α) = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (f : BiheytingHom α β)
  结论: f.comp (BiheytingHom.id α) = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem comp_id (f : BiheytingHom α β) : f.comp (BiheytingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : BiheytingHom α β)
  statement: (BiheytingHom.id β).comp f = f
  proof: ext fun _ => rfl

@[simp]

中文:
定理 id_comp
  条件: (f : BiheytingHom α β)
  结论: (BiheytingHom.id β).comp f = f
  证明: ext fun _ => rfl

@[simp]
-/
theorem id_comp (f : BiheytingHom α β) : (BiheytingHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/--
theorem `cancel_right` / 定理 `cancel_right`

English:
theorem cancel_right
  given: (hf : Surjective f)
  statement: g₁.comp f = g₂.comp f ↔ g₁ = g₂
  proof: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

中文:
定理 cancel_right
  条件: (hf : Surjective f)
  结论: g₁.comp f = g₂.comp f ↔ g₁ = g₂
  证明: ⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, congr_arg, ext_iff, hf.forall
-/
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
⟨fun h => ext hf.forall.2 DFunLike.ext_iff.1 h, congr_arg (fun a => comp a f)⟩

@[simp]
/--
theorem `cancel_left` / 定理 `cancel_left`

English:
theorem cancel_left
  given: (hg : Injective g)
  statement: g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
  proof: ⟨fun h => BiheytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

中文:
定理 cancel_left
  条件: (hg : Injective g)
  结论: g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
  证明: ⟨fun h => BiheytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

Depends on / 依赖: BiheytingHom, BiheytingHom.ext, comp_apply, congr_arg
-/
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
⟨fun h => BiheytingHom.ext fun a => hg by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end BiheytingHom
