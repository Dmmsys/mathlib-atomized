/-
Copyright (c) 2019 Abhimanyu Pallavi Sudhir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abhimanyu Pallavi Sudhir, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Order.Filter.Ring
public import Mathlib.Order.Filter.Ultrafilter.Defs

/-!
# Ultraproducts

If `φ` is an ultrafilter, then the space of germs of functions `f : α → β` at `φ` is called
the *ultraproduct*. In this file we prove properties of ultraproducts that rely on `φ` being an
ultrafilter. Definitions and properties that work for any filter should go to `Order.Filter.Germ`.

## Tags

ultrafilter, ultraproduct
-/

@[expose] public section


universe u v

variable {α : Type u} {β : Type v} {φ : Ultrafilter α}

namespace Filter

local notation3 "∀* "(...)", "r:(scoped p => Filter.Eventually p (Ultrafilter.toFilter φ)) => r

namespace Germ

open Ultrafilter

local notation "β*" => Germ (φ : Filter α) β

/-
**Filter.Germ.instGroupWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instGroupWithZero [GroupWithZero β] : GroupWithZero β* where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroupWithZero [GroupWithZero β] : GroupWithZero β* where
  __ := instDivInvMonoid
  __ := instMonoidWithZero
  mul_inv_cancel f := inductionOn f fun f hf ↦ coe_eq.2 <| (φ.em fun y ↦ f y = 0).elim
    (fun H ↦ (hf <| coe_eq.2 H).elim) fun H ↦ H.mono fun _ ↦ mul_inv_cancel₀
  inv_zero := coe_eq.2 <| by simp only [Function.comp_def, inv_zero, EventuallyEq.rfl]
/-
**Filter.Germ.instDivisionSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instDivisionSemiring [DivisionSemiring β] : DivisionSemiring β* where toSe
miring
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionSemiring [DivisionSemiring β] : DivisionSemiring β* where
  toSemiring := instSemiring
  __ := instGroupWithZero
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
/-
**Filter.Germ.instDivisionRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instDivisionRing [DivisionRing β] : DivisionRing β* where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionRing [DivisionRing β] : DivisionRing β* where
  __ := instRing
  __ := instDivisionSemiring
  qsmul := _
  qsmul_def := fun _ _ => rfl
/-
**Filter.Germ.instSemifield** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instSemifield [Semifield β] : Semifield β* where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemifield [Semifield β] : Semifield β* where
  __ := instCommSemiring
  __ := instDivisionSemiring
/-
**Filter.Germ.instField** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instField [Field β] : Field β* where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instField [Field β] : Field β* where
  __ := instCommRing
  __ := instDivisionRing
/-
**Filter.Germ.coe_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_lt [Preorder β] {f g : α -> β} : (f : β*) < g ↔ forall* x, f x < g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem coe_lt [Preorder β] {f g : α → β} : (f : β*) < g ↔ ∀* x, f x < g x := by
  simp only [lt_iff_le_not_ge, eventually_and, coe_le, eventually_not, EventuallyLE]
/-
**Filter.Germ.coe_pos** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_pos [Preorder β] [Zero β] {f : α -> β} : 0 < (f : β*) ↔ forall* x, 0 <
 f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.coe_lt`：coe_lt [Preorder β] {f g : α -> β} : (f : β*) < g ↔ 
forall* x, f x < g x
-/
theorem coe_pos [Preorder β] [Zero β] {f : α → β} : 0 < (f : β*) ↔ ∀* x, 0 < f x :=
  coe_lt
/-
**Filter.Germ.const_lt** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_lt [Preorder β] {x y : β} : x < y -> (↑x : β*) < ↑y
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Germ.coe_lt`：coe_lt [Preorder β] {f g : α -> β} : (f : β*) < g ↔ 
forall* x, f x < g x
· 使用定理 `Filter.Germ.liftRel_const`：liftRel_const {r : β -> γ -> Prop} {x : β} {y
 : γ} (h : r x y) : LiftRel r (↑x : Germ l β) ↑y
-/
theorem const_lt [Preorder β] {x y : β} : x < y → (↑x : β*) < ↑y :=
  coe_lt.mpr ∘ liftRel_const

@[simp, norm_cast]
/-
**Filter.Germ.const_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_lt_iff [Preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.Germ.coe_lt`：coe_lt [Preorder β] {f g : α -> β} : (f : β*) < g ↔ 
forall* x, f x < g x
· 使用定理 `Filter.Germ.liftRel_const_iff`：liftRel_const_iff [NeBot l] {r : β -> γ -
> Prop} {x : β} {y : γ} : LiftRel r (↑x : Germ l β) ↑y ↔ r x y
-/
theorem const_lt_iff [Preorder β] {x y : β} : (↑x : β*) < ↑y ↔ x < y :=
  coe_lt.trans liftRel_const_iff
/-
**Filter.Germ.lt_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：lt_def [Preorder β] : ((· < ·) : β* -> β* -> Prop) = LiftRel (· < ·)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.Germ.coe_lt`：coe_lt [Preorder β] {f g : α -> β} : (f : β*) < g ↔ 
forall* x, f x < g x
-/
theorem lt_def [Preorder β] : ((· < ·) : β* → β* → Prop) = LiftRel (· < ·) := by
  ext ⟨f⟩ ⟨g⟩
  exact coe_lt
/-
**Filter.Germ.total** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：total [LE β] [@Std.Total β (· <= ·)] : @Std.Total β* (· <= ·)
参数：· <= ·。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn₂`：inductionOn₂ (f : Germ l β) (g : Germ l γ) {p 
: Germ l β -> Germ l γ -> Prop} (h : forall (f : α -> β) (g : α -> γ), p f g) : 
p f g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ultrafilter.eventually_or`：eventually_or : (forallᶠ x in f, p x ∨ q x) ↔
 (forallᶠ x in f, p x) ∨ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a
-/
instance total [LE β] [@Std.Total β (· ≤ ·)] : @Std.Total β* (· ≤ ·) :=
  ⟨fun f g =>
    inductionOn₂ f g fun _f _g => eventually_or.1 <| Eventually.of_forall fun _x => total_of _ _ _⟩

open scoped Classical in
/-- If `φ` is an ultrafilter then the ultraproduct is a linear order. -/
/-
**Filter.Germ.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instLinearOrder [LinearOrder β] : LinearOrder β*
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `φ` is an ultrafilter then the ultraproduct is a linear order.
-/
noncomputable instance instLinearOrder [LinearOrder β] : LinearOrder β* :=
  Lattice.toLinearOrder _
/-
**Filter.Germ.instIsStrictOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instIsStrictOrderedRing [Semiring β] [PartialOrder β] [IsStrictOrderedRing
 β] : IsStrictOrderedRing β* where mul_lt_mul_of_pos_left x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.instIsOrderedAddCancelMonoid`：∀ {α : Type u_1} {β : Type u_2
} {l : Filter α} [inst : AddCommMonoid β] [inst_1 : Preorder β]   [IsOrderedCanc
elAddMonoid β], IsOrderedCance…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} {
inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], Nontrivial R
· 使用定理 `Filter.Germ.inductionOn`：inductionOn (f : Germ l β) {p : Germ l β -> Pro
p} (h : forall f : α -> β, p f) : p f
· 使用定理 `Filter.Germ.inductionOn₂`：inductionOn₂ (f : Germ l β) (g : Germ l γ) {p 
: Germ l β -> Germ l γ -> Prop} (h : forall (f : α -> β) (g : α -> γ), p f g) : 
p f g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Germ.coe_lt`：coe_lt [Preorder β] {f g : α -> β} : (f : β*) < g ↔ 
forall* x, f x < g x
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `mul_lt_mul_of_pos_left`：mul_lt_mul_of_pos_left [PosMulStrictMono α] (hbc
 : b < c) (ha : 0 < a) : a * b < a * c
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
instance instIsStrictOrderedRing [Semiring β] [PartialOrder β] [IsStrictOrderedRing β] :
    IsStrictOrderedRing β* where
  mul_lt_mul_of_pos_left x := inductionOn x fun _f hf y z ↦ inductionOn₂ y z fun _g _h hgh ↦
    coe_lt.2 <| (coe_lt.1 hf).mp <| (coe_lt.1 hgh).mono fun _a ↦ mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right x := inductionOn x fun _f hf y z ↦ inductionOn₂ y z fun _g _h hgh ↦
    coe_lt.2 <| (coe_lt.1 hf).mp <| (coe_lt.1 hgh).mono fun _a ↦ mul_lt_mul_of_pos_right
/-
**Filter.Germ.max_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：max_def [LinearOrder β] (x y : β*) : max x y = map₂ max x y
参数：x y : β*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn₂`：inductionOn₂ (f : Germ l β) (g : Germ l γ) {p 
: Germ l β -> Germ l γ -> Prop} (h : forall (f : α -> β) (g : α -> γ), p f g) : 
p f g
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用定理 `Filter.Germ.map₂_coe`：map₂_coe (op : β -> γ -> δ) (f : α -> β) (g : α ->
 γ) : map₂ op (f : Germ l β) g = fun x => op (f x) (g x)
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `max_eq_left`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, b ≤ a → 
max a b = a
-/
theorem max_def [LinearOrder β] (x y : β*) : max x y = map₂ max x y :=
  inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [max_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_right hi).symm
    · rw [max_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (max_eq_left hi).symm
/-
**Filter.Germ.min_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：min_def [K : LinearOrder β] (x y : β*) : min x y = map₂ min x y
参数：x y : β*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn₂`：inductionOn₂ (f : Germ l β) (g : Germ l γ) {p 
: Germ l β -> Germ l γ -> Prop} (h : forall (f : α -> β) (g : α -> γ), p f g) : 
p f g
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `min_eq_left`：min_eq_left (h : a <= b) : min a b = a
· 使用定理 `Filter.Germ.map₂_coe`：map₂_coe (op : β -> γ -> δ) (f : α -> β) (g : α ->
 γ) : map₂ op (f : Germ l β) g = fun x => op (f x) (g x)
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `min_eq_right`：min_eq_right (h : b <= a) : min a b = b
-/
theorem min_def [K : LinearOrder β] (x y : β*) : min x y = map₂ min x y :=
  inductionOn₂ x y fun a b => by
    rcases le_total (a : β*) b with h | h
    · rw [min_eq_left h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_left hi).symm
    · rw [min_eq_right h, map₂_coe, coe_eq]
      exact h.mono fun i hi => (min_eq_right hi).symm
/-
**Filter.Germ.abs_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：abs_def [AddCommGroup β] [LinearOrder β] (x : β*) : |x| = map abs x
参数：x : β*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn`：inductionOn (f : Germ l β) {p : Germ l β -> Pro
p} (h : forall f : α -> β, p f) : p f
-/
theorem abs_def [AddCommGroup β] [LinearOrder β] (x : β*) :
    |x| = map abs x :=
  inductionOn x fun _a => rfl

@[simp]
/-
**Filter.Germ.const_max** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_max [LinearOrder β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y
参数：x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Germ.max_def`：max_def [LinearOrder β] (x y : β*) : max x y = map₂
 max x y
· 使用定理 `Filter.Germ.map₂_const`：map₂_const (l : Filter α) (b : β) (c : γ) (f : β
 -> γ -> δ) : map₂ f (↑b : Germ l β) ↑c = ↑(f b c)
-/
theorem const_max [LinearOrder β] (x y : β) : (↑(max x y : β) : β*) = max ↑x ↑y := by
  rw [max_def, map₂_const]

@[simp]
/-
**Filter.Germ.const_min** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_min [LinearOrder β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y
参数：x y : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Germ.min_def`：min_def [K : LinearOrder β] (x y : β*) : min x y = 
map₂ min x y
· 使用定理 `Filter.Germ.map₂_const`：map₂_const (l : Filter α) (b : β) (c : γ) (f : β
 -> γ -> δ) : map₂ f (↑b : Germ l β) ↑c = ↑(f b c)
-/
theorem const_min [LinearOrder β] (x y : β) : (↑(min x y : β) : β*) = min ↑x ↑y := by
  rw [min_def, map₂_const]

@[simp]
/-
**Filter.Germ.const_abs** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_abs [AddCommGroup β] [LinearOrder β] (x : β) : (↑|x| : β*) = |↑x|
参数：x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.Germ.abs_def`：abs_def [AddCommGroup β] [LinearOrder β] (x : β*) :
 |x| = map abs x
· 使用定理 `Filter.Germ.map_const`：map_const (l : Filter α) (a : β) (f : β -> γ) : (
↑a : Germ l β).map f = ↑(f a)
-/
theorem const_abs [AddCommGroup β] [LinearOrder β] (x : β) :
    (↑|x| : β*) = |↑x| := by
  rw [abs_def, map_const]

end Germ

end Filter

