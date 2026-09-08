/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Notation.Lemmas
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Ring.Pi

/-!
# Pi instances for ordered groups and monoids

This file defines instances for ordered group, monoid, and related structures on Pi types.
-/

@[expose] public section

variable {I α β γ : Type*}

-- The indexing type
variable {f : I → Type*}

namespace Pi

/-- The product of a family of ordered commutative monoids is an ordered commutative monoid. -/
@[to_additive
      /-- The product of a family of ordered additive commutative monoids is
an ordered additive commutative monoid. -/]
/-
**Pi.isOrderedMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isOrderedMonoid {ι : Type*} {Z : ι -> Type*} [forall i, CommMonoid (Z i)] 
[forall i, Preorder (Z i)] [forall i, IsOrderedMonoid (Z i)] : IsOrderedMonoid (
forall i, Z i) where mul_le_mul_left _ _ w _
参数：Z i；Z i；Z i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
-/
instance isOrderedMonoid {ι : Type*} {Z : ι → Type*} [∀ i, CommMonoid (Z i)]
    [∀ i, Preorder (Z i)] [∀ i, IsOrderedMonoid (Z i)] :
    IsOrderedMonoid (∀ i, Z i) where
  mul_le_mul_left _ _ w _ := fun i => mul_le_mul_left (w i) _

@[to_additive]
/-
**Pi.existsMulOfLe** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：existsMulOfLe {ι : Type*} {α : ι -> Type*} [forall i, LE (α i)] [forall i,
 Mul (α i)] [forall i, ExistsMulOfLE (α i)] : ExistsMulOfLE (forall i, α i)
参数：α i；α i；α i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
instance existsMulOfLe {ι : Type*} {α : ι → Type*} [∀ i, LE (α i)] [∀ i, Mul (α i)]
    [∀ i, ExistsMulOfLE (α i)] : ExistsMulOfLE (∀ i, α i) :=
  ⟨fun h =>
    ⟨fun i => (exists_mul_of_le <| h i).choose,
      funext fun i => (exists_mul_of_le <| h i).choose_spec⟩⟩

/-- The product of a family of canonically ordered monoids is a canonically ordered monoid. -/
@[to_additive
      /-- The product of a family of canonically ordered additive monoids is
a canonically ordered additive monoid. -/]
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι : Type*} {Z : ι → Type*} [∀ i, Monoid (Z i)] [∀ i, PartialOrder (Z i)]
    [∀ i, CanonicallyOrderedMul (Z i)] :
    CanonicallyOrderedMul (∀ i, Z i) where
  __ := Pi.existsMulOfLe
  le_mul_self _ _ := fun _ => le_mul_self
  le_self_mul _ _ := fun _ => le_self_mul

@[to_additive]
/-
**Pi.isOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isOrderedCancelMonoid [forall i, CommMonoid <| f i] [forall i, Preorder <|
 f i] [forall i, IsOrderedCancelMonoid <| f i] : IsOrderedCancelMonoid (forall i
 : I, f i) where le_of_mul_le_mul_left _ _ _ h i
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLE`：∀ {α : Type u_2} [inst : CommM
onoid α] [inst_1 : Preorder α] [IsOrderedCancelMonoid α], MulLeftReflectLE α
-/
instance isOrderedCancelMonoid [∀ i, CommMonoid <| f i] [∀ i, Preorder <| f i]
    [∀ i, IsOrderedCancelMonoid <| f i] :
    IsOrderedCancelMonoid (∀ i : I, f i) where
  le_of_mul_le_mul_left _ _ _ h i := le_of_mul_le_mul_left' (h i)
/-
**Pi.isOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
形式化陈述：isOrderedRing [forall i, Semiring (f i)] [forall i, PartialOrder (f i)] [f
orall i, IsOrderedRing (f i)] : IsOrderedRing (forall i, f i) where add_le_add_l
eft _ _ hab _
参数：f i；f i；f i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
-/
instance isOrderedRing [∀ i, Semiring (f i)] [∀ i, PartialOrder (f i)] [∀ i, IsOrderedRing (f i)] :
    IsOrderedRing (∀ i, f i) where
  add_le_add_left _ _ hab _ := fun _ => add_le_add_left (hab _) _
  zero_le_one := fun i => zero_le_one (α := f i)
  mul_le_mul_of_nonneg_left _ hc _ _ hab := fun _ => mul_le_mul_of_nonneg_left (hab _) <| hc _
  mul_le_mul_of_nonneg_right _ hc _ _ hab := fun _ => mul_le_mul_of_nonneg_right (hab _) <| hc _

end Pi

namespace Function
section const
variable (β) [One α] [Preorder α] {a : α}

@[to_additive const_nonneg_of_nonneg]
/-
**Function.one_le_const_of_one_le** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：one_le_const_of_one_le (ha : 1 <= a) : 1 <= const β a
参数：ha : 1 <= a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_le_const_of_one_le (ha : 1 ≤ a) : 1 ≤ const β a := fun _ => ha

@[to_additive]
/-
**Function.const_le_one_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_le_one_of_le_one (ha : a <= 1) : const β a <= 1
参数：ha : a <= 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_le_one_of_le_one (ha : a ≤ 1) : const β a ≤ 1 := fun _ => ha

variable {β} [Nonempty β]

@[to_additive (attr := simp) const_nonneg]
/-
**Function.one_le_const** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：one_le_const : 1 <= const β a ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.const_le_const`：const_le_const : const β a <= const β b ↔ a <= 
b
-/
theorem one_le_const : 1 ≤ const β a ↔ 1 ≤ a :=
  const_le_const

@[to_additive (attr := simp) const_pos]
/-
**Function.one_lt_const** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：one_lt_const : 1 < const β a ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.const_lt_const`：const_lt_const : const β a < const β b ↔ a < b
-/
theorem one_lt_const : 1 < const β a ↔ 1 < a :=
  const_lt_const

@[to_additive (attr := simp)]
/-
**Function.const_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_le_one : const β a <= 1 ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.const_le_const`：const_le_const : const β a <= const β b ↔ a <= 
b
-/
theorem const_le_one : const β a ≤ 1 ↔ a ≤ 1 :=
  const_le_const

@[to_additive (attr := simp) const_neg']
/-
**Function.const_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：const_lt_one : const β a < 1 ↔ a < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.const_lt_const`：const_lt_const : const β a < const β b ↔ a < b
-/
theorem const_lt_one : const β a < 1 ↔ a < 1 :=
  const_lt_const

end const

section extend
variable [One γ] [LE γ] {f : α → β} {g : α → γ} {e : β → γ}

/-
**Function.one_le_extend** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : One γ] [inst_1 : LE
 γ] {f : α → β} {g : α → γ} {e : β → γ},   1 ≤ g → 1 ≤ e → 1 ≤ Function.extend f
 g e
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `one_le_dite`：one_le_dite [LE α] (ha : forall h, 1 <= a h) (hb : forall h
, 1 <= b h) : 1 <= dite p a b
-/
@[to_additive extend_nonneg] lemma one_le_extend (hg : 1 ≤ g) (he : 1 ≤ e) : 1 ≤ extend f g e :=
  fun _b ↦ by classical exact one_le_dite (fun _ ↦ hg _) (fun _ ↦ he _)
/-
**Function.extend_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : One γ] [inst_1 : LE
 γ] {f : α → β} {g : α → γ} {e : β → γ},   g ≤ 1 → e ≤ 1 → Function.extend f g e
 ≤ 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `dite_le_one`：dite_le_one [LE α] (ha : forall h, a h <= 1) (hb : forall h
, b h <= 1) : dite p a b <= 1
-/
@[to_additive] lemma extend_le_one (hg : g ≤ 1) (he : e ≤ 1) : extend f g e ≤ 1 :=
  fun _b ↦ by classical exact dite_le_one (fun _ ↦ hg _) (fun _ ↦ he _)

end extend
end Function

namespace Pi
variable {ι : Type*} {α : ι → Type*} [DecidableEq ι] [∀ i, One (α i)] [∀ i, Preorder (α i)] {i : ι}
  {a b : α i}

@[to_additive (attr := simp, gcongr)]
/-
**Pi.mulSingle_le_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_le_mulSingle : mulSingle i a <= mulSingle i b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulSingle_le_mulSingle : mulSingle i a ≤ mulSingle i b ↔ a ≤ b := by
  simp [mulSingle]

@[to_additive (attr := simp) single_nonneg]
/-
**Pi.one_le_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：one_le_mulSingle : 1 <= mulSingle i a ↔ 1 <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_le_mulSingle : 1 ≤ mulSingle i a ↔ 1 ≤ a := by simp [mulSingle]

@[to_additive (attr := simp) single_pos]
/-
**Pi.one_lt_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：one_lt_mulSingle : 1 < mulSingle i a ↔ 1 < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_lt_mulSingle : 1 < mulSingle i a ↔ 1 < a := by simp [mulSingle]

@[to_additive (attr := simp)]
/-
**Pi.mulSingle_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSingle_le_one : mulSingle i a <= 1 ↔ a <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulSingle_le_one : mulSingle i a ≤ 1 ↔ a ≤ 1 := by simp [mulSingle]

end Pi

-- Porting note: Tactic code not ported yet
-- namespace Tactic

-- open Function

-- variable (ι) [Zero α] {a : α}

-- private theorem function_const_nonneg_of_pos [Preorder α] (ha : 0 < a) : 0 ≤ const ι a :=
--   const_nonneg_of_nonneg _ ha.le

-- variable [Nonempty ι]

-- private theorem function_const_ne_zero : a ≠ 0 → const ι a ≠ 0 :=
--   const_ne_zero.2

-- private theorem function_const_pos [Preorder α] : 0 < a → 0 < const ι a :=
--   const_pos.2

-- /-- Extension for the `positivity` tactic: `Function.const` is positive/nonnegative/nonzero if
-- its input is. -/
-- @[positivity]
-- unsafe def positivity_const : expr → tactic strictness
--   | q(Function.const $(ι) $(a)) => do
--     let strict_a ← core a
--     match strict_a with
--       | positive p =>
--         positive <$> to_expr ``(function_const_pos $(ι) $(p)) <|>
--           nonnegative <$> to_expr ``(function_const_nonneg_of_pos $(ι) $(p))
--       | nonnegative p => nonnegative <$> to_expr ``(const_nonneg_of_nonneg $(ι) $(p))
--       | nonzero p => nonzero <$> to_expr ``(function_const_ne_zero $(ι) $(p))
--   | e =>
--     pp e >>= fail ∘ format.bracket "The expression `" "` is not of the form `Function.const ι a`"

-- end Tactic

