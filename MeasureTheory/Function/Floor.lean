/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurability of `⌊x⌋` etc

In this file we prove that `Int.floor`, `Int.ceil`, `Int.fract`, `Nat.floor`, and `Nat.ceil` are
measurable under some assumptions on the (semi)ring.
-/

public section


open Set

section FloorRing

variable {α R : Type*} [MeasurableSpace α] [Ring R] [LinearOrder R] [FloorRing R]
  [TopologicalSpace R] [OrderTopology R] [MeasurableSpace R]

/-
**Int.measurable_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.measurable_floor [OpensMeasurableSpace R] : Measurable (Int.floor : R 
-> Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_countable`：measurable_to_countable [MeasurableSpace α] [Co
untable α] [MeasurableSpace β] {f : β -> α} (h : forall y, MeasurableSet (f ⁻¹' 
{f y})) : Mea…
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.preimage_floor_singleton`：preimage_floor_singleton (m : Int) : (floo
r : R -> Int) ⁻¹' {m} = Ico (m : R) (m + 1)
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem Int.measurable_floor [OpensMeasurableSpace R] : Measurable (Int.floor : R → ℤ) :=
  measurable_to_countable fun x => by
    simpa only [Int.preimage_floor_singleton] using measurableSet_Ico

@[fun_prop]
/-
**Measurable.floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.floor [OpensMeasurableSpace R] {f : α -> R} (hf : Measurable f)
 : Measurable fun x => ⌊f x⌋
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Int.measurable_floor`：Int.measurable_floor [OpensMeasurableSpace R] : Me
asurable (Int.floor : R -> Int)
-/
theorem Measurable.floor [OpensMeasurableSpace R] {f : α → R} (hf : Measurable f) :
    Measurable fun x => ⌊f x⌋ :=
  Int.measurable_floor.comp hf
/-
**Int.measurable_ceil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Int.measurable_ceil [OpensMeasurableSpace R] : Measurable (Int.ceil : R ->
 Int)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_countable`：measurable_to_countable [MeasurableSpace α] [Co
untable α] [MeasurableSpace β] {f : β -> α} (h : forall y, MeasurableSet (f ⁻¹' 
{f y})) : Mea…
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.preimage_ceil_singleton`：preimage_ceil_singleton (m : Int) : (ceil :
 R -> Int) ⁻¹' {m} = Ioc ((m : R) - 1) m
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem Int.measurable_ceil [OpensMeasurableSpace R] : Measurable (Int.ceil : R → ℤ) :=
  measurable_to_countable fun x => by
    simpa only [Int.preimage_ceil_singleton] using measurableSet_Ioc

@[fun_prop]
/-
**Measurable.ceil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.ceil [OpensMeasurableSpace R] {f : α -> R} (hf : Measurable f) 
: Measurable fun x => ⌈f x⌉
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Int.measurable_ceil`：Int.measurable_ceil [OpensMeasurableSpace R] : Meas
urable (Int.ceil : R -> Int)
-/
theorem Measurable.ceil [OpensMeasurableSpace R] {f : α → R} (hf : Measurable f) :
    Measurable fun x => ⌈f x⌉ :=
  Int.measurable_ceil.comp hf
/-
**measurable_fract** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurable_fract [IsStrictOrderedRing R] [BorelSpace R] : Measurable (Int.
fract : R -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.preimage_fract`：preimage_fract (s : Set R) : fract ⁻¹' s = ⋃ m : Int
, (fun x => x - (m : R)) ⁻¹' (s inter Ico (0 : R) 1)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `Measurable.sub_const`：∀ {G : Type u_2} {α : Type u_3} [inst : Measurable
Space G] [inst_1 : Sub G] {m : MeasurableSpace α} {f : α → G}   [MeasurableSub G
], Measura…
· 使用定理 `ContinuousSub.measurableSub`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Sub γ]   [ContinuousSub 
γ], MeasurableSub…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `measurable_id`：measurable_id {_ : MeasurableSpace α} : Measurable (@id α
)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem measurable_fract [IsStrictOrderedRing R] [BorelSpace R] :
    Measurable (Int.fract : R → R) := by
  intro s hs
  rw [Int.preimage_fract]
  exact MeasurableSet.iUnion fun z => measurable_id.sub_const _ (hs.inter measurableSet_Ico)

@[fun_prop]
/-
**Measurable.fract** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.fract [IsStrictOrderedRing R] [BorelSpace R] {f : α -> R} (hf :
 Measurable f) : Measurable fun x => Int.fract (f x)
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `measurable_fract`：measurable_fract [IsStrictOrderedRing R] [BorelSpace R
] : Measurable (Int.fract : R -> R)
-/
theorem Measurable.fract [IsStrictOrderedRing R] [BorelSpace R] {f : α → R} (hf : Measurable f) :
    Measurable fun x => Int.fract (f x) :=
  measurable_fract.comp hf
/-
**MeasurableSet.image_fract** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MeasurableSet.image_fract [IsStrictOrderedRing R] [BorelSpace R] {s : Set 
R} (hs : MeasurableSet s) : MeasurableSet (Int.fract '' s)
参数：hs : MeasurableSet s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.image_fract`：image_fract (s : Set R) : fract '' s = ⋃ m : Int, (fun 
x : R => x - m) '' s inter Ico 0 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Set.image_add_right'`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {
b : α}, (fun x => x + -b) '' t = (fun x => x + b) ⁻¹' t
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableInt`：Countable ℤ
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasurableAdd.measurable_add_const`：∀ {M : Type u_2} {inst : MeasurableS
pace M} {inst_1 : Add M} [self : MeasurableAdd M] (c : M), Measurable fun x => x
 + c
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `measurableSet_Ico`：measurableSet_Ico [ClosedIciTopology α] : MeasurableS
et (Ico a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
-/
theorem MeasurableSet.image_fract [IsStrictOrderedRing R] [BorelSpace R]
    {s : Set R} (hs : MeasurableSet s) :
    MeasurableSet (Int.fract '' s) := by
  simp only [Int.image_fract, sub_eq_add_neg, image_add_right']
  exact MeasurableSet.iUnion fun m => (measurable_add_const _ hs).inter measurableSet_Ico

end FloorRing

section FloorSemiring

variable {α R : Type*} [MeasurableSpace α] [Semiring R] [LinearOrder R] [FloorSemiring R]
  [TopologicalSpace R] [OrderTopology R] [MeasurableSpace R] [OpensMeasurableSpace R] {f : α → R}

/-
**Nat.measurable_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.measurable_floor [IsStrictOrderedRing R] : Measurable (Nat.floor : R -
> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_countable`：measurable_to_countable [MeasurableSpace α] [Co
untable α] [MeasurableSpace β] {f : β -> α} (h : forall y, MeasurableSet (f ⁻¹' 
{f y})) : Mea…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.preimage_floor_zero`：preimage_floor_zero : (floor : R -> Nat) ⁻¹' {0
} = Iio 1
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Nat.preimage_floor_of_ne_zero`：preimage_floor_of_ne_zero {n : Nat} (hn :
 n != 0) : (floor : R -> Nat) ⁻¹' {n} = Ico (n : R) (n + 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Nat.measurable_floor [IsStrictOrderedRing R] : Measurable (Nat.floor : R → ℕ) :=
  measurable_to_countable fun n => by
    rcases eq_or_ne ⌊n⌋₊ 0 with h | h <;> simp [h, Nat.preimage_floor_of_ne_zero, -floor_eq_zero]

@[fun_prop]
/-
**Measurable.nat_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.nat_floor [IsStrictOrderedRing R] (hf : Measurable f) : Measura
ble fun x => ⌊f x⌋₊
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Nat.measurable_floor`：Nat.measurable_floor [IsStrictOrderedRing R] : Mea
surable (Nat.floor : R -> Nat)
-/
theorem Measurable.nat_floor [IsStrictOrderedRing R] (hf : Measurable f) :
    Measurable fun x => ⌊f x⌋₊ :=
  Nat.measurable_floor.comp hf
/-
**Nat.measurable_ceil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Nat.measurable_ceil : Measurable (Nat.ceil : R -> Nat)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `measurable_to_countable`：measurable_to_countable [MeasurableSpace α] [Co
untable α] [MeasurableSpace β] {f : β -> α} (h : forall y, MeasurableSet (f ⁻¹' 
{f y})) : Mea…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.preimage_ceil_zero`：preimage_ceil_zero : (Nat.ceil : R -> Nat) ⁻¹' {
0} = Iic 0
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Nat.preimage_ceil_of_ne_zero`：preimage_ceil_of_ne_zero (hn : n != 0) : (
Nat.ceil : R -> Nat) ⁻¹' {n} = Ioc (↑(n - 1) : R) n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem Nat.measurable_ceil : Measurable (Nat.ceil : R → ℕ) :=
  measurable_to_countable fun n => by
    rcases eq_or_ne ⌈n⌉₊ 0 with h | h <;> simp_all [Nat.preimage_ceil_of_ne_zero, -ceil_eq_zero]

@[fun_prop]
/-
**Measurable.nat_ceil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Measurable.nat_ceil (hf : Measurable f) : Measurable fun x => ⌈f x⌉₊
参数：hf : Measurable f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Measurable.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {x : Mea
surableSpace α} {x_1 : MeasurableSpace β}   {x_2 : MeasurableSpace γ} {g : β → γ
} {f …
· 使用定理 `Nat.measurable_ceil`：Nat.measurable_ceil : Measurable (Nat.ceil : R -> N
at)
-/
theorem Measurable.nat_ceil (hf : Measurable f) : Measurable fun x => ⌈f x⌉₊ :=
  Nat.measurable_ceil.comp hf

end FloorSemiring

