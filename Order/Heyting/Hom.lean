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

/-- The type of Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that preserve
Heyting implication. -/
/-
**HeytingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [HeytingAlgebra α] → [HeytingAlgebra β] 
→ Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms
 that preserve
Heyting implication.
-/
structure HeytingHom (α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a Heyting homomorphism preserves the bottom element. -/
  protected map_bot' : toFun ⊥ = ⊥
  /-- The proposition that a Heyting homomorphism preserves the Heyting implication. -/
  protected map_himp' : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b

/-- The type of co-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that
preserve difference. -/
/-
**CoheytingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [CoheytingAlgebra α] → [CoheytingAlgebra
 β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of co-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphi
sms that
preserve difference.
-/
structure CoheytingHom (α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a co-Heyting homomorphism preserves the top element. -/
  protected map_top' : toFun ⊤ = ⊤
  /-- The proposition that a co-Heyting homomorphism preserves the difference operation. -/
  protected map_sdiff' : ∀ a b, toFun (a \ b) = toFun a \ toFun b

/-- The type of bi-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphisms that
preserve Heyting implication and difference. -/
/-
**BiheytingHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [BiheytingAlgebra α] → [BiheytingAlgebra
 β] → Type (max u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of bi-Heyting homomorphisms from `α` to `β`. Bounded lattice homomorphi
sms that
preserve Heyting implication and difference.
-/
structure BiheytingHom (α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] extends
  LatticeHom α β where
  /-- The proposition that a bi-Heyting homomorphism preserves the Heyting implication. -/
  protected map_himp' : ∀ a b, toFun (a ⇨ b) = toFun a ⇨ toFun b
  /-- The proposition that a bi-Heyting homomorphism preserves the difference operation. -/
  protected map_sdiff' : ∀ a b, toFun (a \ b) = toFun a \ toFun b

/-- `HeytingHomClass F α β` states that `F` is a type of Heyting homomorphisms.

You should extend this class when you extend `HeytingHom`. -/
/-
**HeytingHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [HeytingAlgebra α] → [H
eytingAlgebra β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HeytingHomClass F α β` states that `F` is a type of Heyting homomorphisms.

You should extend this class when you extend `HeytingHom`.
-/
class HeytingHomClass (F α β : Type*) [HeytingAlgebra α] [HeytingAlgebra β] [FunLike F α β] : Prop
    extends LatticeHomClass F α β where
  /-- The proposition that a Heyting homomorphism preserves the bottom element. -/
  map_bot (f : F) : f ⊥ = ⊥
  /-- The proposition that a Heyting homomorphism preserves the Heyting implication. -/
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b

/-- `CoheytingHomClass F α β` states that `F` is a type of co-Heyting homomorphisms.

You should extend this class when you extend `CoheytingHom`. -/
/-
**CoheytingHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [CoheytingAlgebra α] → 
[CoheytingAlgebra β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`CoheytingHomClass F α β` states that `F` is a type of co-Heyting homomorphisms.

You should extend this class when you extend `CoheytingHom`.
-/
class CoheytingHomClass (F α β : Type*) [CoheytingAlgebra α] [CoheytingAlgebra β] [FunLike F α β] :
    Prop
  extends LatticeHomClass F α β where
  /-- The proposition that a co-Heyting homomorphism preserves the top element. -/
  map_top (f : F) : f ⊤ = ⊤
  /-- The proposition that a co-Heyting homomorphism preserves the difference operation. -/
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b

/-- `BiheytingHomClass F α β` states that `F` is a type of bi-Heyting homomorphisms.

You should extend this class when you extend `BiheytingHom`. -/
/-
**BiheytingHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : Type u_7) → (β : Type u_8) → [BiheytingAlgebra α] → 
[BiheytingAlgebra β] → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`BiheytingHomClass F α β` states that `F` is a type of bi-Heyting homomorphisms.

You should extend this class when you extend `BiheytingHom`.
-/
class BiheytingHomClass (F α β : Type*) [BiheytingAlgebra α] [BiheytingAlgebra β] [FunLike F α β] :
    Prop
  extends LatticeHomClass F α β where
  /-- The proposition that a bi-Heyting homomorphism preserves the Heyting implication. -/
  map_himp (f : F) : ∀ a b, f (a ⇨ b) = f a ⇨ f b
  /-- The proposition that a bi-Heyting homomorphism preserves the difference operation. -/
  map_sdiff (f : F) : ∀ a b, f (a \ b) = f a \ f b

export HeytingHomClass (map_himp)

export CoheytingHomClass (map_sdiff)

attribute [simp] map_himp map_sdiff

section Hom

variable [FunLike F α β]

/-! This section passes in some instances implicitly. See note [implicit instance arguments] -/

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) HeytingHomClass.toBoundedLatticeHomClass [HeytingAlgebra α]
    {_ : HeytingAlgebra β} [HeytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹HeytingHomClass F α β› with
    map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) CoheytingHomClass.toBoundedLatticeHomClass [CoheytingAlgebra α]
    {_ : CoheytingAlgebra β} [CoheytingHomClass F α β] : BoundedLatticeHomClass F α β :=
  { ‹CoheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, map_sdiff] }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BiheytingHomClass.toHeytingHomClass [BiheytingAlgebra α]
    {_ : BiheytingAlgebra β} [BiheytingHomClass F α β] : HeytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_bot := fun f => by rw [← @sdiff_self α _ ⊤, ← sdiff_self, BiheytingHomClass.map_sdiff] }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) BiheytingHomClass.toCoheytingHomClass [BiheytingAlgebra α]
    {_ : BiheytingAlgebra β} [BiheytingHomClass F α β] : CoheytingHomClass F α β :=
  { ‹BiheytingHomClass F α β› with
    map_top := fun f => by rw [← @himp_self α _ ⊥, ← himp_self, map_himp] }

end Hom

section Equiv

variable [EquivLike F α β]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toHeytingHomClass [HeytingAlgebra α]
    {_ : HeytingAlgebra β} [OrderIsoClass F α β] : HeytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_himp := fun f a b =>
      eq_of_forall_le_iff fun c => by
        simp only [← map_inv_le_iff, le_himp_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toCoheytingHomClass [CoheytingAlgebra α]
    {_ : CoheytingAlgebra β} [OrderIsoClass F α β] : CoheytingHomClass F α β :=
  { OrderIsoClass.toBoundedLatticeHomClass with
    map_sdiff := fun f a b =>
      eq_of_forall_ge_iff fun c => by
        simp only [← le_map_inv_iff, sdiff_le_iff]
        rw [← OrderIsoClass.map_le_map_iff f]
        simp }

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
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

/-
**BoundedLatticeHomClass.toBiheytingHomClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：BoundedLatticeHomClass.toBiheytingHomClass [BooleanAlgebra α] [BooleanAlge
bra β] [BoundedLatticeHomClass F α β] : BiheytingHomClass F α β
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedLatticeHomClass.toLatticeHomClass`：∀ {F : Type u_6} {α : Type u_7
} {β : Type u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : BoundedOrder 
α}   {inst_3 : BoundedOrder β}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `himp_eq`：himp_eq : x ⇨ y = y ⊔ xᶜ
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `IsCompl.compl_eq`：IsCompl.compl_eq (h : IsCompl a b) : aᶜ = b
· 使用定理 `IsCompl.map`：IsCompl.map [BoundedOrder α] [BoundedOrder β] [BoundedLatti
ceHomClass F α β] {a b : α} (f : F) (h : IsCompl a b) : IsCompl (f a) (f b)
· 使用定理 `isCompl_compl`：isCompl_compl : IsCompl x xᶜ
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
/-
**map_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_compl (a : α) : f aᶜ = (f a)ᶜ
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `himp_bot`：himp_bot (a : α) : a ⇨ ⊥ = aᶜ
· 使用定理 `HeytingHomClass.map_himp`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8}
 {inst : HeytingAlgebra α} {inst_1 : HeytingAlgebra β}   {inst_2 : FunLike F α β
} [self : Heyt…
· 使用定理 `BotHomClass.map_bot`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Bot α} {inst_1 : Bot β}   {inst_2 : FunLike F α β} [se
lf : BotH…
· 使用定理 `SupBotHomClass.toBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Max α] [inst_2 : Max β] [inst_3 : Bot α]  
 [inst_4 : Bot β] …
· 使用定理 `BoundedLatticeHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `HeytingHomClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2
} {β : Type u_3} [inst : FunLike F α β] [inst_1 : HeytingAlgebra α] {x : Heyting
Algebra β}   [HeytingHomClass …
-/
theorem map_compl (a : α) : f aᶜ = (f a)ᶜ := by rw [← himp_bot, ← himp_bot, map_himp, map_bot]

@[simp]
/-
**map_bihimp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_bihimp (a b : α) : f (a ⇔ b) = f a ⇔ f b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `InfHomClass.map_inf`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Min α} {inst_1 : Min β} {inst_2 : FunLike F α β}   [self : InfHomClass F α β
] (f : F)…
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `HeytingHomClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u_2
} {β : Type u_3} [inst : FunLike F α β] [inst_1 : HeytingAlgebra α] {x : Heyting
Algebra β}   [HeytingHomClass …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `HeytingHomClass.map_himp`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8}
 {inst : HeytingAlgebra α} {inst_1 : HeytingAlgebra β}   {inst_2 : FunLike F α β
} [self : Heyt…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_bihimp (a b : α) : f (a ⇔ b) = f a ⇔ f b := by simp_rw [bihimp, map_inf, map_himp]

end HeytingAlgebra

section CoheytingAlgebra

open scoped symmDiff

variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] (f : F)

@[simp]
/-
**map_hnot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_hnot (a : α) : f (￢a) = ￢f a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_sdiff'`：∀ {α : Type u_2} [inst : CoheytingAlgebra α] (a : α), ⊤ \ a 
= ￢a
· 使用定理 `CoheytingHomClass.map_sdiff`：∀ {F : Type u_6} {α : Type u_7} {β : Type u
_8} {inst : CoheytingAlgebra α} {inst_1 : CoheytingAlgebra β}   {inst_2 : FunLik
e F α β} [self : …
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
· 使用定理 `InfTopHomClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : FunLike F α β] [inst_1 : Min α] [inst_2 : Min β] [inst_3 : Top α]  
 [inst_4 : Top β] …
· 使用定理 `BoundedLatticeHomClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `CoheytingHomClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u
_2} {β : Type u_3} [inst : FunLike F α β] [inst_1 : CoheytingAlgebra α]   {x : C
oheytingAlgebra β} [CoheytingHom…
-/
theorem map_hnot (a : α) : f (￢a) = ￢f a := by rw [← top_sdiff', ← top_sdiff', map_sdiff, map_top]

@[simp]
/-
**map_symmDiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_symmDiff (a b : α) : f (a ∆ b) = f a ∆ f b
参数：a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SupHomClass.map_sup`：∀ {F : Type u_6} {α : Type u_7} {β : Type u_8} {ins
t : Max α} {inst_1 : Max β} {inst_2 : FunLike F α β}   [self : SupHomClass F α β
] (f : F)…
· 使用定理 `SupBotHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Max α} {inst_1 : Max β} {inst_2 : Bot α} {inst_3 : Bot β}   {inst_4
 : FunLike F α β} …
· 使用定理 `BoundedLatticeHomClass.toSupBotHomClass`：∀ {F : Type u_1} {α : Type u_2}
 {β : Type u_3} [inst : FunLike F α β] [inst_1 : Lattice α] [inst_2 : Lattice β]
   [inst_3 : BoundedOrder α] …
· 使用定理 `CoheytingHomClass.toBoundedLatticeHomClass`：∀ {F : Type u_1} {α : Type u
_2} {β : Type u_3} [inst : FunLike F α β] [inst_1 : CoheytingAlgebra α]   {x : C
oheytingAlgebra β} [CoheytingHom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CoheytingHomClass.map_sdiff`：∀ {F : Type u_6} {α : Type u_7} {β : Type u
_8} {inst : CoheytingAlgebra α} {inst_1 : CoheytingAlgebra β}   {inst_2 : FunLik
e F α β} [self : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_symmDiff (a b : α) : f (a ∆ b) = f a ∆ f b := by simp_rw [symmDiff, map_sup, map_sdiff]

end CoheytingAlgebra

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [HeytingAlgebra α] [HeytingAlgebra β] [HeytingHomClass F α β] : CoeTC F (HeytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_bot' := map_bot f
      map_himp' := map_himp f }⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingHomClass F α β] :
    CoeTC F (CoheytingHom α β) :=
  ⟨fun f =>
    { toFun := f
      map_sup' := map_sup f
      map_inf' := map_inf f
      map_top' := map_top f
      map_sdiff' := map_sdiff f }⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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

/-
**HeytingHom.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `HeytingHom`。
形式化陈述：instFunLike : FunLike (HeytingHom α β) α β where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (HeytingHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
/-
**HeytingHom.instHeytingHomClass** 是 Mathlib 中的一个实例，位于命名空间 `HeytingHom`。
形式化陈述：instHeytingHomClass : HeytingHomClass (HeytingHom α β) α β where map_sup f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SupHom.map_sup'`：∀ {α : Type u_6} {β : Type u_7} [inst : Max α] [inst_1 
: Max β] (self : SupHom α β) (a b : α),   self.toFun (a ⊔ b) = self.toFun a ⊔ se
lf.to…
· 使用定理 `LatticeHom.map_inf'`：∀ {α : Type u_6} {β : Type u_7} [inst : Lattice α] 
[inst_1 : Lattice β] (self : LatticeHom α β) (a b : α),   self.toFun (a ⊓ b) = s
elf.toFun…
· 使用定理 `HeytingHom.map_bot'`：∀ {α : Type u_6} {β : Type u_7} [inst : HeytingAlge
bra α] [inst_1 : HeytingAlgebra β] (self : HeytingHom α β),   self.toFun ⊥ = ⊥
· 使用定理 `HeytingHom.map_himp'`：∀ {α : Type u_6} {β : Type u_7} [inst : HeytingAlg
ebra α] [inst_1 : HeytingAlgebra β] (self : HeytingHom α β) (a b : α),   self.to
Fun (a ⇨ b…
-/
instance instHeytingHomClass : HeytingHomClass (HeytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_bot f := f.map_bot'
  map_himp := HeytingHom.map_himp'
/-
**HeytingHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：toFun_eq_coe {f : HeytingHom α β} : f.toFun = ⇑f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : HeytingHom α β} : f.toFun = ⇑f :=
  rfl

@[simp]
/-
**HeytingHom.toFun_eq_coe_aux** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：toFun_eq_coe_aux {f : HeytingHom α β} : (↑f.toLatticeHom) = ⇑f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe_aux {f : HeytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
/-
**HeytingHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：ext {f g : HeytingHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : HeytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `HeytingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**HeytingHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `HeytingHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : HeytingAlgebra α] →       
[inst_1 : HeytingAlgebra β] → (f : HeytingHom α β) → (f' : α → β) → f' = ⇑f → He
ytingHom α β
参数：f : HeytingHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `HeytingHom` with a new `toFun` equal to the old one. Useful to fix de
finitional
equalities.
-/
protected def copy (f : HeytingHom α β) (f' : α → β) (h : f' = f) : HeytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_bot' := by simpa only [h] using map_bot f
  map_himp' := by simpa only [h] using map_himp f

@[simp]
/-
**HeytingHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：coe_copy (f : HeytingHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h) 
= f'
参数：f : HeytingHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : HeytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**HeytingHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：copy_eq (f : HeytingHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : HeytingHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : HeytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `HeytingHom`. -/
/-
**HeytingHom.id** 是 Mathlib 中的一个定义，位于命名空间 `HeytingHom`。
形式化陈述：(α : Type u_2) → [inst : HeytingAlgebra α] → HeytingHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `HeytingHom`.
-/
protected def id : HeytingHom α α :=
  { BotHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_himp' := fun _ _ => rfl }

@[simp, norm_cast]
/-
**HeytingHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：coe_id : ⇑(HeytingHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(HeytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**HeytingHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：id_apply (a : α) : HeytingHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : HeytingHom.id α a = a :=
  rfl
/-
**HeytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `HeytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (HeytingHom α α) :=
  ⟨HeytingHom.id _⟩
/-
**HeytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `HeytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (HeytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

/-- Composition of `HeytingHom`s as a `HeytingHom`. -/
/-
**HeytingHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `HeytingHom`。
形式化陈述：comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ
参数：f : HeytingHom β γ；g : HeytingHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `HeytingHom`s as a `HeytingHom`.
-/
def comp (f : HeytingHom β γ) (g : HeytingHom α β) : HeytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_bot' := by simp
    map_himp' := fun a b => by simp }

variable {f f₁ f₂ : HeytingHom α β} {g g₁ g₂ : HeytingHom β γ}

@[simp]
/-
**HeytingHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：coe_comp (f : HeytingHom β γ) (g : HeytingHom α β) : ⇑(f.comp g) = f ∘ g
参数：f : HeytingHom β γ；g : HeytingHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : HeytingHom β γ) (g : HeytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/-
**HeytingHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：comp_apply (f : HeytingHom β γ) (g : HeytingHom α β) (a : α) : f.comp g a 
= f (g a)
参数：f : HeytingHom β γ；g : HeytingHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : HeytingHom β γ) (g : HeytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
/-
**HeytingHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：comp_assoc (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β) 
: (f.comp g).comp h = f.comp (g.comp h)
参数：f : HeytingHom γ δ；g : HeytingHom β γ；h : HeytingHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : HeytingHom γ δ) (g : HeytingHom β γ) (h : HeytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**HeytingHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：comp_id (f : HeytingHom α β) : f.comp (HeytingHom.id α) = f
参数：f : HeytingHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HeytingHom.ext`：ext {f g : HeytingHom α β} (h : forall a, f a = g a) : f
 = g
-/
theorem comp_id (f : HeytingHom α β) : f.comp (HeytingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**HeytingHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：id_comp (f : HeytingHom α β) : (HeytingHom.id β).comp f = f
参数：f : HeytingHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HeytingHom.ext`：ext {f g : HeytingHom α β} (h : forall a, f a = g a) : f
 = g
-/
theorem id_comp (f : HeytingHom α β) : (HeytingHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**HeytingHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HeytingHom.ext`：ext {f g : HeytingHom α β} (h : forall a, f a = g a) : f
 = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
/-
**HeytingHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `HeytingHom`。
形式化陈述：cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HeytingHom.ext`：ext {f g : HeytingHom α β} (h : forall a, f a = g a) : f
 = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HeytingHom.comp_apply`：comp_apply (f : HeytingHom β γ) (g : HeytingHom α
 β) (a : α) : f.comp g a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => HeytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end HeytingHom

namespace CoheytingHom

variable [CoheytingAlgebra α] [CoheytingAlgebra β] [CoheytingAlgebra γ] [CoheytingAlgebra δ]

/-
**CoheytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `CoheytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (CoheytingHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
/-
**CoheytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `CoheytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoheytingHomClass (CoheytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_top f := f.map_top'
  map_sdiff := CoheytingHom.map_sdiff'
/-
**CoheytingHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：toFun_eq_coe {f : CoheytingHom α β} : f.toFun = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : CoheytingHom α β} : f.toFun = (f : α → β) :=
  rfl

@[simp]
/-
**CoheytingHom.toFun_eq_coe_aux** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：toFun_eq_coe_aux {f : CoheytingHom α β} : (↑f.toLatticeHom) = ⇑f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe_aux {f : CoheytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
/-
**CoheytingHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：ext {f g : CoheytingHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : CoheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `CoheytingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**CoheytingHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `CoheytingHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : CoheytingAlgebra α] →     
  [inst_1 : CoheytingAlgebra β] → (f : CoheytingHom α β) → (f' : α → β) → f' = ⇑
f → CoheytingHom α β
参数：f : CoheytingHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `CoheytingHom` with a new `toFun` equal to the old one. Useful to fix 
definitional
equalities.
-/
protected def copy (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : CoheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_top' := by simpa only [h] using map_top f
  map_sdiff' := by simpa only [h] using map_sdiff f

@[simp]
/-
**CoheytingHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：coe_copy (f : CoheytingHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h
) = f'
参数：f : CoheytingHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**CoheytingHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：copy_eq (f : CoheytingHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = 
f
参数：f : CoheytingHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : CoheytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `CoheytingHom`. -/
/-
**CoheytingHom.id** 是 Mathlib 中的一个定义，位于命名空间 `CoheytingHom`。
形式化陈述：(α : Type u_2) → [inst : CoheytingAlgebra α] → CoheytingHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `CoheytingHom`.
-/
protected def id : CoheytingHom α α :=
  { TopHom.id _ with
    toLatticeHom := LatticeHom.id _
    map_sdiff' := fun _ _ => rfl }

@[simp, norm_cast]
/-
**CoheytingHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：coe_id : ⇑(CoheytingHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(CoheytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**CoheytingHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：id_apply (a : α) : CoheytingHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : CoheytingHom.id α a = a :=
  rfl
/-
**CoheytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `CoheytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (CoheytingHom α α) :=
  ⟨CoheytingHom.id _⟩
/-
**CoheytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `CoheytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (CoheytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

/-- Composition of `CoheytingHom`s as a `CoheytingHom`. -/
/-
**CoheytingHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `CoheytingHom`。
形式化陈述：comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : CoheytingHom α γ
参数：f : CoheytingHom β γ；g : CoheytingHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `CoheytingHom`s as a `CoheytingHom`.
-/
def comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : CoheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_top' := by simp
    map_sdiff' := fun a b => by simp }

variable {f f₁ f₂ : CoheytingHom α β} {g g₁ g₂ : CoheytingHom β γ}

@[simp]
/-
**CoheytingHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：coe_comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : ⇑(f.comp g) = f ∘
 g
参数：f : CoheytingHom β γ；g : CoheytingHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : CoheytingHom β γ) (g : CoheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/-
**CoheytingHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：comp_apply (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α) : f.comp 
g a = f (g a)
参数：f : CoheytingHom β γ；g : CoheytingHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : CoheytingHom β γ) (g : CoheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
/-
**CoheytingHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：comp_assoc (f : CoheytingHom γ δ) (g : CoheytingHom β γ) (h : CoheytingHom
 α β) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : CoheytingHom γ δ；g : CoheytingHom β γ；h : CoheytingHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : CoheytingHom γ δ) (g : CoheytingHom β γ) (h : CoheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**CoheytingHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：comp_id (f : CoheytingHom α β) : f.comp (CoheytingHom.id α) = f
参数：f : CoheytingHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoheytingHom.ext`：ext {f g : CoheytingHom α β} (h : forall a, f a = g a)
 : f = g
-/
theorem comp_id (f : CoheytingHom α β) : f.comp (CoheytingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**CoheytingHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：id_comp (f : CoheytingHom α β) : (CoheytingHom.id β).comp f = f
参数：f : CoheytingHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoheytingHom.ext`：ext {f g : CoheytingHom α β} (h : forall a, f a = g a)
 : f = g
-/
theorem id_comp (f : CoheytingHom α β) : (CoheytingHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**CoheytingHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoheytingHom.ext`：ext {f g : CoheytingHom α β} (h : forall a, f a = g a)
 : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
/-
**CoheytingHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `CoheytingHom`。
形式化陈述：cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CoheytingHom.ext`：ext {f g : CoheytingHom α β} (h : forall a, f a = g a)
 : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CoheytingHom.comp_apply`：comp_apply (f : CoheytingHom β γ) (g : Coheytin
gHom α β) (a : α) : f.comp g a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => CoheytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end CoheytingHom

namespace BiheytingHom

variable [BiheytingAlgebra α] [BiheytingAlgebra β] [BiheytingAlgebra γ] [BiheytingAlgebra δ]

/-
**BiheytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `BiheytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (BiheytingHom α β) α β where
  coe f := f.toFun
  coe_injective f g h := by obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := f; obtain ⟨⟨⟨_, _⟩, _⟩, _⟩ := g; congr
/-
**BiheytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `BiheytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BiheytingHomClass (BiheytingHom α β) α β where
  map_sup f := f.map_sup'
  map_inf f := f.map_inf'
  map_himp f := f.map_himp'
  map_sdiff f := f.map_sdiff'
/-
**BiheytingHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：toFun_eq_coe {f : BiheytingHom α β} : f.toFun = (f : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : BiheytingHom α β} : f.toFun = (f : α → β) :=
  rfl

@[simp]
/-
**BiheytingHom.toFun_eq_coe_aux** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：toFun_eq_coe_aux {f : BiheytingHom α β} : (↑f.toLatticeHom) = ⇑f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe_aux {f : BiheytingHom α β} : (↑f.toLatticeHom) = ⇑f :=
  rfl

@[ext]
/-
**BiheytingHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：ext {f g : BiheytingHom α β} (h : forall a, f a = g a) : f = g
参数：h : forall a, f a = g a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : BiheytingHom α β} (h : ∀ a, f a = g a) : f = g :=
  DFunLike.ext f g h

/-- Copy of a `BiheytingHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**BiheytingHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `BiheytingHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     [inst : BiheytingAlgebra α] →     
  [inst_1 : BiheytingAlgebra β] → (f : BiheytingHom α β) → (f' : α → β) → f' = ⇑
f → BiheytingHom α β
参数：f : BiheytingHom α β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `BiheytingHom` with a new `toFun` equal to the old one. Useful to fix 
definitional
equalities.
-/
protected def copy (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : BiheytingHom α β where
  toFun := f'
  map_sup' := by simpa only [h] using map_sup f
  map_inf' := by simpa only [h] using map_inf f
  map_himp' := by simpa only [h] using map_himp f
  map_sdiff' := by simpa only [h] using map_sdiff f

@[simp]
/-
**BiheytingHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：coe_copy (f : BiheytingHom α β) (f' : α -> β) (h : f' = f) : ⇑(f.copy f' h
) = f'
参数：f : BiheytingHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : ⇑(f.copy f' h) = f' :=
  rfl
/-
**BiheytingHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：copy_eq (f : BiheytingHom α β) (f' : α -> β) (h : f' = f) : f.copy f' h = 
f
参数：f : BiheytingHom α β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : BiheytingHom α β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h

variable (α)

/-- `id` as a `BiheytingHom`. -/
/-
**BiheytingHom.id** 是 Mathlib 中的一个定义，位于命名空间 `BiheytingHom`。
形式化陈述：(α : Type u_2) → [inst : BiheytingAlgebra α] → BiheytingHom α α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`id` as a `BiheytingHom`.
-/
protected def id : BiheytingHom α α :=
  { HeytingHom.id _, CoheytingHom.id _ with toLatticeHom := LatticeHom.id _ }

@[simp, norm_cast]
/-
**BiheytingHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：coe_id : ⇑(BiheytingHom.id α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(BiheytingHom.id α) = id :=
  rfl

variable {α}

@[simp]
/-
**BiheytingHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：id_apply (a : α) : BiheytingHom.id α a = a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (a : α) : BiheytingHom.id α a = a :=
  rfl
/-
**BiheytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `BiheytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (BiheytingHom α α) :=
  ⟨BiheytingHom.id _⟩
/-
**BiheytingHom.** 是 Mathlib 中的一个实例，位于命名空间 `BiheytingHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (BiheytingHom α β) :=
  PartialOrder.lift _ DFunLike.coe_injective

/-- Composition of `BiheytingHom`s as a `BiheytingHom`. -/
/-
**BiheytingHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `BiheytingHom`。
形式化陈述：comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : BiheytingHom α γ
参数：f : BiheytingHom β γ；g : BiheytingHom α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of `BiheytingHom`s as a `BiheytingHom`.
-/
def comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : BiheytingHom α γ :=
  { f.toLatticeHom.comp g.toLatticeHom with
    toFun := f ∘ g
    map_himp' := fun a b => by simp
    map_sdiff' := fun a b => by simp }

variable {f f₁ f₂ : BiheytingHom α β} {g g₁ g₂ : BiheytingHom β γ}

@[simp]
/-
**BiheytingHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：coe_comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : ⇑(f.comp g) = f ∘
 g
参数：f : BiheytingHom β γ；g : BiheytingHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : BiheytingHom β γ) (g : BiheytingHom α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
/-
**BiheytingHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：comp_apply (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α) : f.comp 
g a = f (g a)
参数：f : BiheytingHom β γ；g : BiheytingHom α β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : BiheytingHom β γ) (g : BiheytingHom α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
/-
**BiheytingHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：comp_assoc (f : BiheytingHom γ δ) (g : BiheytingHom β γ) (h : BiheytingHom
 α β) : (f.comp g).comp h = f.comp (g.comp h)
参数：f : BiheytingHom γ δ；g : BiheytingHom β γ；h : BiheytingHom α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : BiheytingHom γ δ) (g : BiheytingHom β γ) (h : BiheytingHom α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
/-
**BiheytingHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：comp_id (f : BiheytingHom α β) : f.comp (BiheytingHom.id α) = f
参数：f : BiheytingHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BiheytingHom.ext`：ext {f g : BiheytingHom α β} (h : forall a, f a = g a)
 : f = g
-/
theorem comp_id (f : BiheytingHom α β) : f.comp (BiheytingHom.id α) = f :=
  ext fun _ => rfl

@[simp]
/-
**BiheytingHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：id_comp (f : BiheytingHom α β) : (BiheytingHom.id β).comp f = f
参数：f : BiheytingHom α β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BiheytingHom.ext`：ext {f g : BiheytingHom α β} (h : forall a, f a = g a)
 : f = g
-/
theorem id_comp (f : BiheytingHom α β) : (BiheytingHom.id β).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**BiheytingHom.cancel_right** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂
参数：hf : Surjective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BiheytingHom.ext`：ext {f g : BiheytingHom α β} (h : forall a, f a = g a)
 : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_right (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| DFunLike.ext_iff.1 h, congr_arg (fun a ↦ comp a f)⟩

@[simp]
/-
**BiheytingHom.cancel_left** 是 Mathlib 中的一个定理，位于命名空间 `BiheytingHom`。
形式化陈述：cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂
参数：hg : Injective g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BiheytingHom.ext`：ext {f g : BiheytingHom α β} (h : forall a, f a = g a)
 : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `BiheytingHom.comp_apply`：comp_apply (f : BiheytingHom β γ) (g : Biheytin
gHom α β) (a : α) : f.comp g a = f (g a)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem cancel_left (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => BiheytingHom.ext fun a => hg <| by rw [← comp_apply, h, comp_apply], congr_arg _⟩

end BiheytingHom

