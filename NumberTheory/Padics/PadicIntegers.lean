/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis, Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# p-adic integers

This file defines the `p`-adic integers `ℤ_[p]` as the subtype of `ℚ_[p]` with norm `≤ 1`.
We show that `ℤ_[p]`
* is complete,
* is nonarchimedean,
* is a normed ring,
* is a local ring, and
* is a discrete valuation ring.

The relation between `ℤ_[p]` and `ZMod p` is established in another file.

## Important definitions

* `PadicInt` : the type of `p`-adic integers

## Notation

We introduce the notation `ℤ_[p]` for the `p`-adic integers.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

Coercions into `ℤ_[p]` are set up to work with the `norm_cast` tactic.

## References

* [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
* [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
* <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, p-adic integer
-/

@[expose] public section


open Padic Metric IsLocalRing

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

/-- The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`. -/
/-
**PadicInt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：PadicInt : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-adic integers `ℤ_[p]` are the `p`-adic numbers with norm `≤ 1`.
-/
def PadicInt : Type := {x : ℚ_[p] // ‖x‖ ≤ 1}

/-- The ring of `p`-adic integers. -/
notation "ℤ_[" p "]" => PadicInt p

namespace PadicInt
variable {p} {x y : ℤ_[p]}

/-! ### Ring structure and coercion to `ℚ_[p]` -/

/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Ring structure and coercion to `ℚ_[p]`
-/
instance : Coe ℤ_[p] ℚ_[p] :=
  ⟨Subtype.val⟩
/-
**PadicInt.ext** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：ext {x y : Int_[p]} : (x : Rat_[p]) = y -> x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem ext {x y : ℤ_[p]} : (x : ℚ_[p]) = y → x = y :=
  Subtype.ext

variable (p)

/-- The `p`-adic integers as a subring of `ℚ_[p]`. -/
/-
**PadicInt.subring** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：subring : Subring Rat_[p] where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-adic integers as a subring of `ℚ_[p]`.
-/
def subring : Subring ℚ_[p] where
  carrier := { x : ℚ_[p] | ‖x‖ ≤ 1 }
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' hx hy := (Padic.nonarchimedean _ _).trans <| max_le_iff.2 ⟨hx, hy⟩
  mul_mem' hx hy := (padicNormE.mul _ _).trans_le <| mul_le_one₀ hx (norm_nonneg _) hy
  neg_mem' hx := (norm_neg _).trans_le hx

@[simp]
/-
**PadicInt.mem_subring_iff** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：mem_subring_iff {x : Rat_[p]} : x in subring p ↔ ‖x‖ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_subring_iff {x : ℚ_[p]} : x ∈ subring p ↔ ‖x‖ ≤ 1 := Iff.rfl

variable {p}
/-
**PadicInt.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
形式化陈述：instCommRing : CommRing Int_[p]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing : CommRing ℤ_[p] := inferInstanceAs <| CommRing (subring p)
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited ℤ_[p] := ⟨0⟩

@[simp]
/-
**PadicInt.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：mk_zero {h} : (⟨0, h⟩ : Int_[p]) = (0 : Int_[p])
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zero {h} : (⟨0, h⟩ : ℤ_[p]) = (0 : ℤ_[p]) := rfl

@[simp, norm_cast]
/-
**PadicInt.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_add (z1 z2 : Int_[p]) : ((z1 + z2 : Int_[p]) : Rat_[p]) = z1 + z2
参数：z1 z2 : Int_[p]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (z1 z2 : ℤ_[p]) : ((z1 + z2 : ℤ_[p]) : ℚ_[p]) = z1 + z2 := rfl

@[simp, norm_cast]
/-
**PadicInt.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_mul (z1 z2 : Int_[p]) : ((z1 * z2 : Int_[p]) : Rat_[p]) = z1 * z2
参数：z1 z2 : Int_[p]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (z1 z2 : ℤ_[p]) : ((z1 * z2 : ℤ_[p]) : ℚ_[p]) = z1 * z2 := rfl

@[simp, norm_cast]
/-
**PadicInt.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_neg (z1 : Int_[p]) : ((-z1 : Int_[p]) : Rat_[p]) = -z1
参数：z1 : Int_[p]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (z1 : ℤ_[p]) : ((-z1 : ℤ_[p]) : ℚ_[p]) = -z1 := rfl

@[simp, norm_cast]
/-
**PadicInt.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_sub (z1 z2 : Int_[p]) : ((z1 - z2 : Int_[p]) : Rat_[p]) = z1 - z2
参数：z1 z2 : Int_[p]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (z1 z2 : ℤ_[p]) : ((z1 - z2 : ℤ_[p]) : ℚ_[p]) = z1 - z2 := rfl

@[simp, norm_cast]
/-
**PadicInt.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_one : ((1 : Int_[p]) : Rat_[p]) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : ℤ_[p]) : ℚ_[p]) = 1 := rfl

@[simp, norm_cast]
/-
**PadicInt.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_zero : ((0 : Int_[p]) : Rat_[p]) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : ℤ_[p]) : ℚ_[p]) = 0 := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PadicInt.coe_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {x : ℤ_[p]}, ↑x = 0 ↔ x = 0
参数：Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PadicInt.coe_zero`：coe_zero : ((0 : Int_[p]) : Rat_[p]) = 0
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma coe_eq_zero : (x : ℚ_[p]) = 0 ↔ x = 0 := by rw [← coe_zero, Subtype.coe_inj]
/-
**PadicInt.coe_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：coe_ne_zero : (x : Rat_[p]) != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `PadicInt.coe_eq_zero`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {x : ℤ_[p]}, ↑
x = 0 ↔ x = 0
-/
lemma coe_ne_zero : (x : ℚ_[p]) ≠ 0 ↔ x ≠ 0 := coe_eq_zero.not

@[simp, norm_cast]
/-
**PadicInt.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_natCast (n : Nat) : ((n : Int_[p]) : Rat_[p]) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast (n : ℕ) : ((n : ℤ_[p]) : ℚ_[p]) = n := rfl

@[simp, norm_cast]
/-
**PadicInt.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_intCast (z : Int) : ((z : Int_[p]) : Rat_[p]) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast (z : ℤ) : ((z : ℤ_[p]) : ℚ_[p]) = z := rfl

/-- The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism. -/
@[simps!]
/-
**PadicInt.Coe.ringHom** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt.Coe`。
形式化陈述：{p : ℕ} → [hp : Fact (Nat.Prime p)] → ℤ_[p] →+* ℚ_[p]
参数：Nat.Prime p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coercion from `ℤ_[p]` to `ℚ_[p]` as a ring homomorphism.
-/
def Coe.ringHom : ℤ_[p] →+* ℚ_[p] := (subring p).subtype

@[simp, norm_cast]
/-
**PadicInt.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：coe_pow (x : Int_[p]) (n : Nat) : (↑(x ^ n) : Rat_[p]) = (↑x : Rat_[p]) ^ 
n
参数：x : Int_[p]；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (x : ℤ_[p]) (n : ℕ) : (↑(x ^ n) : ℚ_[p]) = (↑x : ℚ_[p]) ^ n := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PadicInt.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：mk_coe (k : Int_[p]) : (⟨k, k.2⟩ : Int_[p]) = k
参数：k : Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_coe (k : ℤ_[p]) : (⟨k, k.2⟩ : ℤ_[p]) = k := by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**PadicInt.coe_sum** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：coe_sum {α : Type*} (s : Finset α) (f : α -> Int_[p]) : (((∑ z in s, f z) 
: Int_[p]) : Rat_[p]) = ∑ z in s, (f z : Rat_[p])
参数：s : Finset α；f : α -> Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_sum {α : Type*} (s : Finset α) (f : α → ℤ_[p]) :
    (((∑ z ∈ s, f z) : ℤ_[p]) : ℚ_[p]) = ∑ z ∈ s, (f z : ℚ_[p]) := by
  simp [← Coe.ringHom_apply, map_sum PadicInt.Coe.ringHom f s]

open Topology in
/-
**PadicInt.isOpenEmbedding_coe** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：isOpenEmbedding_coe : IsOpenEmbedding ((↑) : Int_[p] -> Rat_[p])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_eq_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), dist a b = ‖a - b‖
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `IsUltrametricDist.isOpen_closedBall`：isOpen_closedBall {r : Real} (hr : 
r != 0) : IsOpen (closedBall x r)
· 使用定理 `Padic.instIsUltrametricDist`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], IsUl
trametricDist ℚ_[p]
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
lemma isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℤ_[p] → ℚ_[p]) := by
  refine (?_ : IsOpen {y : ℚ_[p] | ‖y‖ ≤ 1}).isOpenEmbedding_subtypeVal
  simpa only [Metric.closedBall, dist_eq_norm_sub, sub_zero] using
    IsUltrametricDist.isOpen_closedBall (0 : ℚ_[p]) one_ne_zero

/-- The inverse of a `p`-adic integer with norm equal to `1` is also a `p`-adic integer.
Otherwise, the inverse is defined to be `0`. -/
/-
**PadicInt.inv** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：{p : ℕ} → [hp : Fact (Nat.Prime p)] → ℤ_[p] → ℤ_[p]
参数：Nat.Prime p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a `p`-adic integer with norm equal to `1` is also a `p`-adic inte
ger.
Otherwise, the inverse is defined to be `0`.
-/
def inv : ℤ_[p] → ℤ_[p]
  | ⟨k, _⟩ => if h : ‖k‖ = 1 then ⟨k⁻¹, by simp [h]⟩ else 0

set_option backward.isDefEq.respectTransparency false in
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CharZero ℤ_[p] where
  cast_injective m n h :=
    Nat.cast_injective (R := ℚ_[p]) (by rw [Subtype.ext_iff] at h; norm_cast at h)

@[norm_cast]
/-
**PadicInt.intCast_eq** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：intCast_eq (z1 z2 : Int) : (z1 : Int_[p]) = z2 ↔ z1 = z2
参数：z1 z2 : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.instCharZero`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], CharZero ℤ_[
p]
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem intCast_eq (z1 z2 : ℤ) : (z1 : ℤ_[p]) = z2 ↔ z1 = z2 := by simp

set_option backward.isDefEq.respectTransparency false in
/-- A sequence of integers that is Cauchy with respect to the `p`-adic norm converges to a `p`-adic
integer. -/
/-
**PadicInt.ofIntSeq** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：ofIntSeq (seq : Nat -> Int) (h : IsCauSeq (padicNorm p) fun n => seq n) : 
Int_[p]
参数：seq : Nat -> Int；h : IsCauSeq (padicNorm p) fun n => seq n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `padicNorm.instIsAbsoluteValueRat`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], I
sAbsoluteValue (padicNorm p)

--- 原说明 ---
A sequence of integers that is Cauchy with respect to the `p`-adic norm converge
s to a `p`-adic
integer.
-/
def ofIntSeq (seq : ℕ → ℤ) (h : IsCauSeq (padicNorm p) fun n => seq n) : ℤ_[p] :=
  ⟨⟦⟨_, h⟩⟧,
    show ↑(PadicSeq.norm _) ≤ (1 : ℝ) by
      rw [PadicSeq.norm]
      split_ifs with hne <;> norm_cast
      apply padicNorm.of_int⟩

/-! ### Instances

We now show that `ℤ_[p]` is a
* complete metric space
* normed ring
* integral domain
-/

variable (p)

/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace ℤ_[p] := inferInstanceAs <| MetricSpace (Subtype _)
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsUltrametricDist ℤ_[p] := IsUltrametricDist.subtype _
/-
**PadicInt.completeSpace** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
形式化陈述：completeSpace : CompleteSpace Int_[p]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_le`：isClosed_le [TopologicalSpace β] {f g : β -> α} (hf : Conti
nuous f) (hg : Continuous g) : IsClosed { b | f b <= g b }
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Padic.instCompleteSpace`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], CompleteSp
ace ℚ_[p]
-/
instance completeSpace : CompleteSpace ℤ_[p] :=
  have : IsClosed { x : ℚ_[p] | ‖x‖ ≤ 1 } := isClosed_le continuous_norm continuous_const
  this.completeSpace_coe
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Norm ℤ_[p] := ⟨fun z => ‖(z : ℚ_[p])‖⟩

variable {p} in
/-
**PadicInt.norm_def** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_def {z : Int_[p]} : ‖z‖ = ‖(z : Rat_[p])‖
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_def {z : ℤ_[p]} : ‖z‖ = ‖(z : ℚ_[p])‖ := rfl
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormedCommRing ℤ_[p] where
  dist_eq := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    exact dist_eq_norm_neg_add x y
  norm_mul_le := by simp [norm_def]
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormOneClass ℤ_[p] :=
  ⟨norm_def.trans norm_one⟩
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NormMulClass ℤ_[p] := ⟨fun x y ↦ by simp [norm_def]⟩
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDomain ℤ_[p] := NoZeroDivisors.to_isDomain _

variable {p}

/-! ### Norm -/

/-
**PadicInt.norm_le_one** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
参数：z : Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
### Norm
-/
theorem norm_le_one (z : ℤ_[p]) : ‖z‖ ≤ 1 := z.2
/-
**PadicInt.nonarchimedean** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：nonarchimedean (q r : Int_[p]) : ‖q + r‖ <= max ‖q‖ ‖r‖
参数：q r : Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.nonarchimedean`：nonarchimedean (q r : Rat_[p]) : ‖q + r‖ <= max ‖q
‖ ‖r‖
-/
theorem nonarchimedean (q r : ℤ_[p]) : ‖q + r‖ ≤ max ‖q‖ ‖r‖ := Padic.nonarchimedean _ _
/-
**PadicInt.norm_add_eq_max_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_add_eq_max_of_ne {q r : Int_[p]} : ‖q‖ != ‖r‖ -> ‖q + r‖ = max ‖q‖ ‖r
‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.add_eq_max_of_ne`：add_eq_max_of_ne {q r : Rat_[p]} (h : ‖q‖ != ‖r‖
) : ‖q + r‖ = max ‖q‖ ‖r‖
-/
theorem norm_add_eq_max_of_ne {q r : ℤ_[p]} : ‖q‖ ≠ ‖r‖ → ‖q + r‖ = max ‖q‖ ‖r‖ :=
  Padic.add_eq_max_of_ne
/-
**PadicInt.norm_eq_of_norm_add_lt_right** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_eq_of_norm_add_lt_right {z1 z2 : Int_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z
1‖ = ‖z2‖
参数：h : ‖z1 + z2‖ < ‖z2‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_add_eq_max_of_ne`：norm_add_eq_max_of_ne {q r : Int_[p]} : 
‖q‖ != ‖r‖ -> ‖q + r‖ = max ‖q‖ ‖r‖
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
-/
theorem norm_eq_of_norm_add_lt_right {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z2‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_right) h
/-
**PadicInt.norm_eq_of_norm_add_lt_left** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_eq_of_norm_add_lt_left {z1 z2 : Int_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1
‖ = ‖z2‖
参数：h : ‖z1 + z2‖ < ‖z1‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_add_eq_max_of_ne`：norm_add_eq_max_of_ne {q r : Int_[p]} : 
‖q‖ != ‖r‖ -> ‖q + r‖ = max ‖q‖ ‖r‖
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
-/
theorem norm_eq_of_norm_add_lt_left {z1 z2 : ℤ_[p]} (h : ‖z1 + z2‖ < ‖z1‖) : ‖z1‖ = ‖z2‖ :=
  by_contra fun hne =>
    not_lt_of_ge (by rw [norm_add_eq_max_of_ne hne]; apply le_max_left) h

@[simp]
/-
**PadicInt.padic_norm_e_of_padicInt** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：padic_norm_e_of_padicInt (z : Int_[p]) : ‖(z : Rat_[p])‖ = ‖z‖
参数：z : Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem padic_norm_e_of_padicInt (z : ℤ_[p]) : ‖(z : ℚ_[p])‖ = ‖z‖ := by simp [norm_def]
/-
**PadicInt.norm_intCast_eq_padic_norm** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_intCast_eq_padic_norm (z : Int) : ‖(z : Int_[p])‖ = ‖(z : Rat_[p])‖
参数：z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_intCast_eq_padic_norm (z : ℤ) : ‖(z : ℤ_[p])‖ = ‖(z : ℚ_[p])‖ := by simp [norm_def]

@[simp]
/-
**PadicInt.norm_eq_padic_norm** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_eq_padic_norm {q : Rat_[p]} (hq : ‖q‖ <= 1) : @norm Int_[p] _ ⟨q, hq⟩
 = ‖q‖
参数：hq : ‖q‖ <= 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_eq_padic_norm {q : ℚ_[p]} (hq : ‖q‖ ≤ 1) : @norm ℤ_[p] _ ⟨q, hq⟩ = ‖q‖ := rfl

@[simp]
/-
**PadicInt.norm_p** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_p : ‖(p : Int_[p])‖ = (p : Real)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.norm_p`：norm_p : ‖(p : Rat_[p])‖ = (p : Real)⁻¹
-/
theorem norm_p : ‖(p : ℤ_[p])‖ = (p : ℝ)⁻¹ := Padic.norm_p
/-
**PadicInt.norm_p_pow** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_p_pow (n : Nat) : ‖(p : Int_[p]) ^ n‖ = (p : Real) ^ (-n : Int)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `PadicInt.instNormOneClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormOneC
lass ℤ_[p]
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PadicInt.norm_p`：norm_p : ‖(p : Int_[p])‖ = (p : Real)⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_p_pow (n : ℕ) : ‖(p : ℤ_[p]) ^ n‖ = (p : ℝ) ^ (-n : ℤ) := by simp

@[simp]
/-
**PadicInt.one_le_norm_iff** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：one_le_norm_iff {x : Int_[p]} : 1 <= ‖x‖ ↔ ‖x‖ = 1
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma one_le_norm_iff {x : ℤ_[p]} :
    1 ≤ ‖x‖ ↔ ‖x‖ = 1 := by
  simp [le_antisymm_iff, ← padic_norm_e_of_padicInt, x.prop]

@[simp]
/-
**PadicInt.norm_natCast_p_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：norm_natCast_p_sub_one : ‖((p - 1 : Nat) : Int_[p])‖ = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Padic.norm_natCast_p_sub_one`：norm_natCast_p_sub_one : ‖((p - 1 : Nat) :
 Rat_[p])‖ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_natCast_p_sub_one :
    ‖((p - 1 : ℕ) : ℤ_[p])‖ = 1 := by
  simp [norm_def]
/-
**PadicInt.cauSeq_to_rat_cauSeq** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def cauSeq_to_rat_cauSeq (f : CauSeq ℤ_[p] norm) : CauSeq ℚ_[p] fun a => ‖a‖ :=
  ⟨fun n => f n, fun _ hε => by simpa [norm, norm_def] using f.cauchy hε⟩

variable (p)
/-
**PadicInt.complete** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
形式化陈述：complete : CauSeq.IsComplete Int_[p] norm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `Padic.padicNormE_lim_le`：padicNormE_lim_le {f : CauSeq Rat_[p] norm} {a 
: Real} (ha : 0 < a) (hf : forall i, ‖f i‖ <= a) : ‖f.lim‖ <= a
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `PadicInt.norm_le_one`：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CauSeq.equiv_lim`：equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s)
-/
instance complete : CauSeq.IsComplete ℤ_[p] norm :=
  ⟨fun f =>
    have hqn : ‖CauSeq.lim (cauSeq_to_rat_cauSeq f)‖ ≤ 1 :=
      padicNormE_lim_le zero_lt_one fun _ => norm_le_one _
    ⟨⟨_, hqn⟩, fun ε => by
      simpa [norm, norm_def] using! CauSeq.equiv_lim (cauSeq_to_rat_cauSeq f) ε⟩⟩
/-
**PadicInt.exists_pow_neg_lt** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：exists_pow_neg_lt {ε : Real} (hε : 0 < ε) : exists k : Nat, (p : Real) ^ (
-(k : Int)) < ε
参数：hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `inv_lt_inv₀`：inv_lt_inv₀ (ha : 0 < a) (hb : 0 < b) : a⁻¹ < b⁻¹ ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `zpow_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialO
rder G₀] [PosMulReflectLT G₀] {a : G₀}   [ZeroLEOneClass G₀], 0 < a → ∀ (n : ℤ…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
-/
theorem exists_pow_neg_lt {ε : ℝ} (hε : 0 < ε) : ∃ k : ℕ, (p : ℝ) ^ (-(k : ℤ)) < ε := by
  obtain ⟨k, hk⟩ := exists_nat_gt ε⁻¹
  use k
  rw [← inv_lt_inv₀ hε (zpow_pos _ _)]
  · rw [zpow_neg, inv_inv, zpow_natCast]
    apply lt_of_lt_of_le hk
    norm_cast
    apply le_of_lt
    convert! Nat.lt_pow_self _ using 1
    exact hp.1.one_lt
  · exact mod_cast hp.1.pos
/-
**PadicInt.exists_pow_neg_lt_rat** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：exists_pow_neg_lt_rat {ε : Rat} (hε : 0 < ε) : exists k : Nat, (p : Rat) ^
 (-(k : Int)) < ε
参数：hε : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PadicInt.exists_pow_neg_lt`：exists_pow_neg_lt {ε : Real} (hε : 0 < ε) : 
exists k : Nat, (p : Real) ^ (-(k : Int)) < ε
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem exists_pow_neg_lt_rat {ε : ℚ} (hε : 0 < ε) : ∃ k : ℕ, (p : ℚ) ^ (-(k : ℤ)) < ε := by
  obtain ⟨k, hk⟩ := @exists_pow_neg_lt p _ ε (mod_cast hε)
  use k
  rw [show (p : ℝ) = (p : ℚ) by simp] at hk
  exact mod_cast hk

variable {p}
/-
**PadicInt.norm_int_lt_one_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_int_lt_one_iff_dvd (k : Int) : ‖(k : Int_[p])‖ < 1 ↔ (p : Int) ∣ k
参数：k : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.norm_intCast_lt_one_iff`：norm_intCast_lt_one_iff {k : Int} : ‖(k :
 Rat_[p])‖ < 1 ↔ ↑p ∣ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_intCast_eq_padic_norm`：norm_intCast_eq_padic_norm (z : Int
) : ‖(z : Int_[p])‖ = ‖(z : Rat_[p])‖
-/
theorem norm_int_lt_one_iff_dvd (k : ℤ) : ‖(k : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ < 1 ↔ ↑p ∣ k by rwa [norm_intCast_eq_padic_norm]
  Padic.norm_intCast_lt_one_iff
/-
**PadicInt.norm_int_le_pow_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_int_le_pow_iff_dvd {k : Int} {n : Nat} : ‖(k : Int_[p])‖ <= (p : Real
) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.norm_int_le_pow_iff_dvd`：norm_int_le_pow_iff_dvd (k : Int) (n : Na
t) : ‖(k : Rat_[p])‖ <= (p : Real) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PadicInt.norm_intCast_eq_padic_norm`：norm_intCast_eq_padic_norm (z : Int
) : ‖(z : Int_[p])‖ = ‖(z : Rat_[p])‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
-/
theorem norm_int_le_pow_iff_dvd {k : ℤ} {n : ℕ} :
    ‖(k : ℤ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k :=
  suffices ‖(k : ℚ_[p])‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ (p ^ n : ℤ) ∣ k by
    simpa [norm_intCast_eq_padic_norm]
  Padic.norm_int_le_pow_iff_dvd _ _

@[simp]
/-
**PadicInt.norm_natCast_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：norm_natCast_eq_one_iff {n : Nat} : ‖(n : Int_[p])‖ = 1 ↔ p.Coprime n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_def`：norm_def {z : Int_[p]} : ‖z‖ = ‖(z : Rat_[p])‖
· 使用定理 `PadicInt.coe_natCast`：coe_natCast (n : Nat) : ((n : Int_[p]) : Rat_[p]) 
= n
· 使用引理 `Padic.norm_natCast_eq_one_iff`：norm_natCast_eq_one_iff {n : Nat} : ‖(n :
 Rat_[p])‖ = 1 ↔ p.Coprime n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma norm_natCast_eq_one_iff {n : ℕ} :
    ‖(n : ℤ_[p])‖ = 1 ↔ p.Coprime n := by
  rw [norm_def, coe_natCast, Padic.norm_natCast_eq_one_iff]

@[simp]
/-
**PadicInt.norm_natCast_lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：norm_natCast_lt_one_iff {n : Nat} : ‖(n : Int_[p])‖ < 1 ↔ p ∣ n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_def`：norm_def {z : Int_[p]} : ‖z‖ = ‖(z : Rat_[p])‖
· 使用定理 `PadicInt.coe_natCast`：coe_natCast (n : Nat) : ((n : Int_[p]) : Rat_[p]) 
= n
· 使用引理 `Padic.norm_natCast_lt_one_iff`：norm_natCast_lt_one_iff {n : Nat} : ‖(n :
 Rat_[p])‖ < 1 ↔ p ∣ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma norm_natCast_lt_one_iff {n : ℕ} :
    ‖(n : ℤ_[p])‖ < 1 ↔ p ∣ n := by
  rw [norm_def, coe_natCast, Padic.norm_natCast_lt_one_iff]

@[simp]
/-
**PadicInt.norm_intCast_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：norm_intCast_eq_one_iff {z : Int} : ‖(z : Int_[p])‖ = 1 ↔ IsCoprime z p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_def`：norm_def {z : Int_[p]} : ‖z‖ = ‖(z : Rat_[p])‖
· 使用定理 `PadicInt.coe_intCast`：coe_intCast (z : Int) : ((z : Int_[p]) : Rat_[p]) 
= z
· 使用引理 `Padic.norm_intCast_eq_one_iff`：norm_intCast_eq_one_iff {z : Int} : ‖(z :
 Rat_[p])‖ = 1 ↔ IsCoprime z p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma norm_intCast_eq_one_iff {z : ℤ} :
    ‖(z : ℤ_[p])‖ = 1 ↔ IsCoprime z p := by
  rw [norm_def, coe_intCast, Padic.norm_intCast_eq_one_iff]

@[simp]
/-
**PadicInt.norm_intCast_lt_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：norm_intCast_lt_one_iff {z : Int} : ‖(z : Int_[p])‖ < 1 ↔ (p : Int) ∣ z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_def`：norm_def {z : Int_[p]} : ‖z‖ = ‖(z : Rat_[p])‖
· 使用定理 `PadicInt.coe_intCast`：coe_intCast (z : Int) : ((z : Int_[p]) : Rat_[p]) 
= z
· 使用定理 `Padic.norm_intCast_lt_one_iff`：norm_intCast_lt_one_iff {k : Int} : ‖(k :
 Rat_[p])‖ < 1 ↔ ↑p ∣ k
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma norm_intCast_lt_one_iff {z : ℤ} :
    ‖(z : ℤ_[p])‖ < 1 ↔ (p : ℤ) ∣ z := by
  rw [norm_def, coe_intCast, Padic.norm_intCast_lt_one_iff]

/-! ### Valuation on `ℤ_[p]` -/

/-
**PadicInt.valuation_coe_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：valuation_coe_nonneg : 0 <= (x : Rat_[p]).valuation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.valuation_zero`：valuation_zero : valuation (0 : Rat_[p]) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `neg_nonpos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, -a ≤ 0 ↔ 0 ≤ a
· 使用定理 `zpow_le_one_iff_right₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [ins
t_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G₀]   {n : 
ℤ}, 1 < a → …
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PadicInt.coe_ne_zero`：coe_ne_zero : (x : Rat_[p]) != 0 ↔ x != 0

--- 原说明 ---
### Valuation on `ℤ_[p]`
-/
lemma valuation_coe_nonneg : 0 ≤ (x : ℚ_[p]).valuation := by
  obtain rfl | hx := eq_or_ne x 0
  · simp
  have := x.2
  rwa [Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx, zpow_le_one_iff_right₀, neg_nonpos]
    at this
  exact mod_cast hp.out.one_lt

/-- `PadicInt.valuation` lifts the `p`-adic valuation on `ℚ` to `ℤ_[p]`. -/
/-
**PadicInt.valuation** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：valuation (x : Int_[p]) : Nat
参数：x : Int_[p]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PadicInt.valuation` lifts the `p`-adic valuation on `ℚ` to `ℤ_[p]`.
-/
def valuation (x : ℤ_[p]) : ℕ := (x : ℚ_[p]).valuation.toNat
/-
**PadicInt.valuation_coe** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℤ_[p]), (↑x).valuation = ↑x.valua
tion
参数：Nat.Prime p；x : ℤ_[p]；↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ofNat_toNat`：∀ (a : ℤ), ↑a.toNat = max a 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma valuation_coe (x : ℤ_[p]) : (x : ℚ_[p]).valuation = x.valuation := by
  simp [valuation, valuation_coe_nonneg]
/-
**PadicInt.valuation_zero** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], PadicInt.valuation 0 = 0
参数：Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.valuation_zero`：valuation_zero : valuation (0 : Rat_[p]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma valuation_zero : valuation (0 : ℤ_[p]) = 0 := by simp [valuation]
/-
**PadicInt.valuation_one** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], PadicInt.valuation 1 = 0
参数：Nat.Prime p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Padic.valuation_one`：valuation_one : valuation (1 : Rat_[p]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma valuation_one : valuation (1 : ℤ_[p]) = 0 := by simp [valuation]
/-
**PadicInt.valuation_p** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], (↑p).valuation = 1
参数：Nat.Prime p；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Padic.valuation_natCast`：valuation_natCast (n : Nat) : valuation (n : Ra
t_[p]) = padicValNat p n
· 使用定理 `padicValNat_self`：padicValNat_self [Fact p.Prime] : padicValNat p p = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma valuation_p : valuation (p : ℤ_[p]) = 1 := by simp [valuation]
/-
**PadicInt.le_valuation_add** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：le_valuation_add (hxy : x + y != 0) : min x.valuation y.valuation <= (x + 
y).valuation
参数：hxy : x + y != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_min`：cast_min {α} [Semiring α] [LinearOrder α] [IsStrictOrdered
Ring α] (m n : Nat) : (↑(min m n : Nat) : α) = min (m : α) n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Padic.le_valuation_add`：le_valuation_add {x y : Rat_[p]} (hxy : x + y !=
 0) : min x.valuation y.valuation <= (x + y).valuation
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PadicInt.coe_ne_zero`：coe_ne_zero : (x : Rat_[p]) != 0 ↔ x != 0
-/
lemma le_valuation_add (hxy : x + y ≠ 0) : min x.valuation y.valuation ≤ (x + y).valuation := by
  zify; simpa [← valuation_coe] using Padic.le_valuation_add <| coe_ne_zero.2 hxy
/-
**PadicInt.valuation_mul** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {x y : ℤ_[p]}, x ≠ 0 → y ≠ 0 → (x * y)
.valuation = x.valuation + y.valuation
参数：Nat.Prime p；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Padic.valuation_mul`：valuation_mul {x y : Rat_[p]} (hx : x != 0) (hy : y
 != 0) : (x * y).valuation = x.valuation + y.valuation
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PadicInt.coe_ne_zero`：coe_ne_zero : (x : Rat_[p]) != 0 ↔ x != 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma valuation_mul (hx : x ≠ 0) (hy : y ≠ 0) :
    (x * y).valuation = x.valuation + y.valuation := by
  zify; simp [← valuation_coe, Padic.valuation_mul (coe_ne_zero.2 hx) (coe_ne_zero.2 hy)]

@[simp]
/-
**PadicInt.valuation_pow** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：valuation_pow (x : Int_[p]) (n : Nat) : (x ^ n).valuation = n * x.valuatio
n
参数：x : Int_[p]；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Padic.valuation_pow`：valuation_pow (x : Rat_[p]) : forall n : Nat, (x ^ 
n).valuation = n * x.valuation | 0 => by simp | n + 1 => by obtain rfl | hx
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma valuation_pow (x : ℤ_[p]) (n : ℕ) : (x ^ n).valuation = n * x.valuation := by
  zify; simp [← valuation_coe]
/-
**PadicInt.norm_eq_zpow_neg_valuation** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：norm_eq_zpow_neg_valuation {x : Int_[p]} (hx : x != 0) : ‖x‖ = p ^ (-x.val
uation : Int)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `PadicInt.coe_ne_zero`：coe_ne_zero : (x : Rat_[p]) != 0 ↔ x != 0
· 使用定理 `PadicInt.valuation_coe`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (x : ℤ_[p]),
 (↑x).valuation = ↑x.valuation
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_eq_zpow_neg_valuation {x : ℤ_[p]} (hx : x ≠ 0) : ‖x‖ = p ^ (-x.valuation : ℤ) := by
  simp [norm_def, Padic.norm_eq_zpow_neg_valuation <| coe_ne_zero.2 hx]

-- TODO: Do we really need this lemma?
@[simp]
/-
**PadicInt.valuation_p_pow_mul** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：valuation_p_pow_mul (n : Nat) (c : Int_[p]) (hc : c != 0) : ((p : Int_[p])
 ^ n * c).valuation = n + c.valuation
参数：n : Nat；c : Int_[p]；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.valuation_mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {x y : ℤ_[p]
}, x ≠ 0 → y ≠ 0 → (x * y).valuation = x.valuation + y.valuation
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `PadicInt.instCharZero`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], CharZero ℤ_[
p]
· 使用引理 `PadicInt.valuation_pow`：valuation_pow (x : Int_[p]) (n : Nat) : (x ^ n).
valuation = n * x.valuation
· 使用定理 `PadicInt.valuation_p`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], (↑p).valuatio
n = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem valuation_p_pow_mul (n : ℕ) (c : ℤ_[p]) (hc : c ≠ 0) :
    ((p : ℤ_[p]) ^ n * c).valuation = n + c.valuation := by
  rw [valuation_mul (NeZero.ne _) hc, valuation_pow, valuation_p, mul_one]

section Units

/-! ### Units of `ℤ_[p]` -/

set_option backward.isDefEq.respectTransparency false in
/-
**PadicInt.mul_inv** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：mul_inv : forall {z : Int_[p]}, ‖z‖ = 1 -> z * z.inv = 1 | ⟨k, _⟩, h => by
 have hk : k != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zero_ne_one'`：zero_ne_one' [One α] [NeZero (1 : α)] : (0 : α) != 1
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `PadicInt.norm_eq_padic_norm`：norm_eq_padic_norm {q : Rat_[p]} (hq : ‖q‖ 
<= 1) : @norm Int_[p] _ ⟨q, hq⟩ = ‖q‖
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Units of `ℤ_[p]`
-/
theorem mul_inv : ∀ {z : ℤ_[p]}, ‖z‖ = 1 → z * z.inv = 1
  | ⟨k, _⟩, h => by
    have hk : k ≠ 0 := fun h' => zero_ne_one' ℚ_[p] (by simp [h'] at h)
    unfold PadicInt.inv
    rw [norm_eq_padic_norm] at h
    dsimp only
    rw [dif_pos h]
    apply Subtype.ext_iff.2
    simp [mul_inv_cancel₀ hk]
/-
**PadicInt.inv_mul** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：inv_mul {z : Int_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1
参数：hz : ‖z‖ = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `PadicInt.mul_inv`：mul_inv : forall {z : Int_[p]}, ‖z‖ = 1 -> z * z.inv =
 1 | ⟨k, _⟩, h => by have hk : k != 0
-/
theorem inv_mul {z : ℤ_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1 := by rw [mul_comm, mul_inv hz]
/-
**PadicInt.isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：isUnit_iff {z : Int_[p]} : IsUnit z ↔ ‖z‖ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isUnit_iff_dvd_one`：isUnit_iff_dvd_one {x : α} : IsUnit x ↔ x ∣ 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `PadicInt.norm_le_one`：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `PadicInt.instNormOneClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormOneC
lass ℤ_[p]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `PadicInt.mul_inv`：mul_inv : forall {z : Int_[p]}, ‖z‖ = 1 -> z * z.inv =
 1 | ⟨k, _⟩, h => by have hk : k != 0
· 使用定理 `PadicInt.inv_mul`：inv_mul {z : Int_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1
-/
theorem isUnit_iff {z : ℤ_[p]} : IsUnit z ↔ ‖z‖ = 1 :=
  ⟨fun h => by
    rcases isUnit_iff_dvd_one.1 h with ⟨w, eq⟩
    refine le_antisymm (norm_le_one _) ?_
    have := mul_le_mul_of_nonneg_left (norm_le_one w) (norm_nonneg z)
    rwa [mul_one, ← norm_mul, ← eq, norm_one] at this, fun h =>
    ⟨⟨z, z.inv, mul_inv h, inv_mul h⟩, rfl⟩⟩
/-
**PadicInt.norm_lt_one_add** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_lt_one_add {z1 z2 : Int_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1) : ‖z1 
+ z2‖ < 1
参数：hz1 : ‖z1‖ < 1；hz2 : ‖z2‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `PadicInt.nonarchimedean`：nonarchimedean (q r : Int_[p]) : ‖q + r‖ <= max
 ‖q‖ ‖r‖
· 使用定理 `max_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, b < a → c <
 a → max b c < a
-/
theorem norm_lt_one_add {z1 z2 : ℤ_[p]} (hz1 : ‖z1‖ < 1) (hz2 : ‖z2‖ < 1) : ‖z1 + z2‖ < 1 :=
  lt_of_le_of_lt (nonarchimedean _ _) (max_lt hz1 hz2)
/-
**PadicInt.norm_lt_one_mul** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_lt_one_mul {z1 z2 : Int_[p]} (hz2 : ‖z2‖ < 1) : ‖z1 * z2‖ < 1
参数：hz2 : ‖z2‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `mul_lt_one_of_nonneg_of_lt_one_right`：mul_lt_one_of_nonneg_of_lt_one_rig
ht [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (hb : b < 1) : a * b < 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `PadicInt.norm_le_one`：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem norm_lt_one_mul {z1 z2 : ℤ_[p]} (hz2 : ‖z2‖ < 1) : ‖z1 * z2‖ < 1 :=
  calc
    ‖z1 * z2‖ = ‖z1‖ * ‖z2‖ := by simp
    _ < 1 := mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one _) (norm_nonneg _) hz2
/-
**PadicInt.mem_nonunits** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：mem_nonunits {z : Int_[p]} : z in nonunits Int_[p] ↔ ‖z‖ < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `PadicInt.norm_le_one`：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
-/
theorem mem_nonunits {z : ℤ_[p]} : z ∈ nonunits ℤ_[p] ↔ ‖z‖ < 1 := by
  simp [norm_le_one z, nonunits, isUnit_iff]
/-
**PadicInt.not_isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：not_isUnit_iff {z : Int_[p]} : ¬IsUnit z ↔ ‖z‖ < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.mem_nonunits`：mem_nonunits {z : Int_[p]} : z in nonunits Int_[p
] ↔ ‖z‖ < 1
-/
theorem not_isUnit_iff {z : ℤ_[p]} : ¬IsUnit z ↔ ‖z‖ < 1 := by
  simpa using mem_nonunits

/-- A `p`-adic number `u` with `‖u‖ = 1` is a unit of `ℤ_[p]`. -/
/-
**PadicInt.mkUnits** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：mkUnits {u : Rat_[p]} (h : ‖u‖ = 1) : Int_[p]ˣ
参数：h : ‖u‖ = 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PadicInt.mul_inv`：mul_inv : forall {z : Int_[p]}, ‖z‖ = 1 -> z * z.inv =
 1 | ⟨k, _⟩, h => by have hk : k != 0
· 使用定理 `PadicInt.inv_mul`：inv_mul {z : Int_[p]} (hz : ‖z‖ = 1) : z.inv * z = 1

--- 原说明 ---
A `p`-adic number `u` with `‖u‖ = 1` is a unit of `ℤ_[p]`.
-/
def mkUnits {u : ℚ_[p]} (h : ‖u‖ = 1) : ℤ_[p]ˣ :=
  let z : ℤ_[p] := ⟨u, le_of_eq h⟩
  ⟨z, z.inv, mul_inv h, inv_mul h⟩

@[simp]
/-
**PadicInt.val_mkUnits** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：val_mkUnits {u : Rat_[p]} (h : ‖u‖ = 1) : (mkUnits h).val = ⟨u, h.le⟩
参数：h : ‖u‖ = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma val_mkUnits {u : ℚ_[p]} (h : ‖u‖ = 1) : (mkUnits h).val = ⟨u, h.le⟩ := rfl
/-
**PadicInt.mkUnits_eq** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：mkUnits_eq {u : Rat_[p]} (h : ‖u‖ = 1) : ((mkUnits h : Int_[p]) : Rat_[p])
 = u
参数：h : ‖u‖ = 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkUnits_eq {u : ℚ_[p]} (h : ‖u‖ = 1) : ((mkUnits h : ℤ_[p]) : ℚ_[p]) = u := rfl

@[simp]
/-
**PadicInt.norm_units** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_units (u : Int_[p]ˣ) : ‖(u : Int_[p])‖ = 1
参数：u : Int_[p]ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PadicInt.isUnit_iff`：isUnit_iff {z : Int_[p]} : IsUnit z ↔ ‖z‖ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem norm_units (u : ℤ_[p]ˣ) : ‖(u : ℤ_[p])‖ = 1 := isUnit_iff.mp <| by simp

/-- `unitCoeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unitCoeff_spec`. -/
/-
**PadicInt.unitCoeff** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：unitCoeff {x : Int_[p]} (hx : x != 0) : Int_[p]ˣ
参数：hx : x != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`unitCoeff hx` is the unit `u` in the unique representation `x = u * p ^ n`.
See `unitCoeff_spec`.
-/
def unitCoeff {x : ℤ_[p]} (hx : x ≠ 0) : ℤ_[p]ˣ :=
  let u : ℚ_[p] := x * (p : ℚ_[p]) ^ (-x.valuation : ℤ)
  have hu : ‖u‖ = 1 := by
    simp [u, hx, pow_ne_zero _ (NeZero.ne _), norm_eq_zpow_neg_valuation]
  mkUnits hu

@[simp]
/-
**PadicInt.unitCoeff_coe** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：unitCoeff_coe {x : Int_[p]} (hx : x != 0) : (unitCoeff hx : Rat_[p]) = x *
 (p : Rat_[p]) ^ (-x.valuation : Int)
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem unitCoeff_coe {x : ℤ_[p]} (hx : x ≠ 0) :
    (unitCoeff hx : ℚ_[p]) = x * (p : ℚ_[p]) ^ (-x.valuation : ℤ) := rfl
/-
**PadicInt.unitCoeff_spec** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：unitCoeff_spec {x : Int_[p]} (hx : x != 0) : x = (unitCoeff hx : Int_[p]) 
* (p : Int_[p]) ^ x.valuation
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.unitCoeff_coe`：unitCoeff_coe {x : Int_[p]} (hx : x != 0) : (uni
tCoeff hx : Rat_[p]) = x * (p : Rat_[p]) ^ (-x.valuation : Int)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem unitCoeff_spec {x : ℤ_[p]} (hx : x ≠ 0) :
    x = (unitCoeff hx : ℤ_[p]) * (p : ℤ_[p]) ^ x.valuation := by
  apply Subtype.coe_injective
  push_cast
  rw [unitCoeff_coe, mul_assoc, ← zpow_natCast, ← zpow_add₀]
  · simp
  · exact NeZero.ne _
/-
**PadicInt.isUnit_den** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：isUnit_den {p : Nat} [hp_prime : Fact p.Prime] (r : Rat) (h : ‖(r : Rat_[p
])‖ <= 1) : IsUnit (r.den : Int_[p])
参数：r : Rat；h : ‖(r : Rat_[p])‖ <= 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.isUnit_iff`：isUnit_iff {z : Int_[p]} : IsUnit z ↔ ‖z‖ = 1
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `PadicInt.coe_natCast`：coe_natCast (n : Nat) : ((n : Int_[p]) : Rat_[p]) 
= n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `Rat.cast_intCast`：cast_intCast (n : Int) : ((n : Rat) : α) = n
· 使用定理 `Rat.mul_den_eq_num`：∀ (q : ℚ), q * ↑q.den = ↑q.num
· 使用定理 `Padic.padicNormE.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q r : ℚ_[p]),
 ‖q * r‖ = ‖q‖ * ‖r‖
· 使用定理 `mul_lt_mul'`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 :
 Preorder α] {a b c d : α} [PosMulStrictMono α]   [MulPosMono α], a ≤ b → c < d 
→…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Nat.Coprime.gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n → m.gcd n = 1
· 使用定理 `Rat.reduced`：∀ (self : ℚ), self.num.natAbs.Coprime self.den
· 使用定理 `Nat.dvd_gcd_iff`：∀ {k : ℕ} {m n : ℕ}, k ∣ m.gcd n ↔ k ∣ m ∧ k ∣ n
· 使用引理 `Int.natCast_dvd`：natCast_dvd {m : Nat} : (m : Int) ∣ n ↔ m ∣ n.natAbs
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
-/
theorem isUnit_den {p : ℕ} [hp_prime : Fact p.Prime] (r : ℚ) (h : ‖(r : ℚ_[p])‖ ≤ 1) :
    IsUnit (r.den : ℤ_[p]) := by
  rw [isUnit_iff]
  apply le_antisymm (r.den : ℤ_[p]).2
  rw [← not_lt, coe_natCast]
  intro norm_denom_lt
  have hr : ‖(r * r.den : ℚ_[p])‖ = ‖(r.num : ℚ_[p])‖ := by
    congr
    rw_mod_cast [@Rat.mul_den_eq_num r]
  rw [padicNormE.mul] at hr
  have key : ‖(r.num : ℚ_[p])‖ < 1 := by
    calc
      _ = _ := hr.symm
      _ < 1 * 1 := mul_lt_mul' h norm_denom_lt (norm_nonneg _) zero_lt_one
      _ = 1 := mul_one 1
  have : ↑p ∣ r.num ∧ (p : ℤ) ∣ r.den := by
    simp only [← norm_int_lt_one_iff_dvd, ← padic_norm_e_of_padicInt]
    exact ⟨key, norm_denom_lt⟩
  apply hp_prime.1.not_dvd_one
  rwa [← r.reduced.gcd_eq_one, Nat.dvd_gcd_iff, ← Int.natCast_dvd, ← Int.natCast_dvd_natCast]

end Units

section NormLeIff

/-! ### Various characterizations of open unit balls -/

/-
**PadicInt.norm_le_pow_iff_le_valuation** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_le_pow_iff_le_valuation (x : Int_[p]) (hx : x != 0) (n : Nat) : ‖x‖ <
= (p : Real) ^ (-n : Int) ↔ n <= x.valuation
参数：x : Int_[p]；hx : x != 0；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PadicInt.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Int
_[p]} (hx : x != 0) : ‖x‖ = p ^ (-x.valuation : Int)
· 使用定理 `zpow_le_zpow_iff_right₀`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [in
st_1 : PartialOrder G₀] [PosMulReflectLT G₀] {a : G₀} [ZeroLEOneClass G₀]   {m n
 : ℤ}, 1 < a …
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
### Various characterizations of open unit balls
-/
theorem norm_le_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ n ≤ x.valuation := by
  rw [norm_eq_zpow_neg_valuation hx, zpow_le_zpow_iff_right₀, neg_le_neg_iff, Nat.cast_le]
  exact mod_cast hp.out.one_lt
/-
**PadicInt.mem_span_pow_iff_le_valuation** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：mem_span_pow_iff_le_valuation (x : Int_[p]) (hx : x != 0) (n : Nat) : x in
 (Ideal.span {(p : Int_[p]) ^ n} : Ideal Int_[p]) ↔ n <= x.valuation
参数：x : Int_[p]；hx : x != 0；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `PadicInt.valuation_p_pow_mul`：valuation_p_pow_mul (n : Nat) (c : Int_[p]
) (hc : c != 0) : ((p : Int_[p]) ^ n * c).valuation = n + c.valuation
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PadicInt.unitCoeff_spec`：unitCoeff_spec {x : Int_[p]} (hx : x != 0) : x 
= (unitCoeff hx : Int_[p]) * (p : Int_[p]) ^ x.valuation
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
-/
theorem mem_span_pow_iff_le_valuation (x : ℤ_[p]) (hx : x ≠ 0) (n : ℕ) :
    x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) ↔ n ≤ x.valuation := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    suffices c ≠ 0 by
      rw [valuation_p_pow_mul _ _ this]
      exact le_self_add
    contrapose hx
    rw [hx, mul_zero]
  · nth_rewrite 2 [unitCoeff_spec hx]
    simpa [Units.isUnit, IsUnit.dvd_mul_left] using pow_dvd_pow _
/-
**PadicInt.norm_le_pow_iff_mem_span_pow** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_le_pow_iff_mem_span_pow (x : Int_[p]) (n : Nat) : ‖x‖ <= (p : Real) ^
 (-n : Int) ↔ x in (Ideal.span {(p : Int_[p]) ^ n} : Ideal Int_[p])
参数：x : Int_[p]；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `PadicInt.norm_le_pow_iff_le_valuation`：norm_le_pow_iff_le_valuation (x :
 Int_[p]) (hx : x != 0) (n : Nat) : ‖x‖ <= (p : Real) ^ (-n : Int) ↔ n <= x.valu
ation
· 使用定理 `PadicInt.mem_span_pow_iff_le_valuation`：mem_span_pow_iff_le_valuation (x
 : Int_[p]) (hx : x != 0) (n : Nat) : x in (Ideal.span {(p : Int_[p]) ^ n} : Ide
al Int_[p]) ↔ n <= x.valuati…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_le_pow_iff_mem_span_pow (x : ℤ_[p]) (n : ℕ) :
    ‖x‖ ≤ (p : ℝ) ^ (-n : ℤ) ↔ x ∈ (Ideal.span {(p : ℤ_[p]) ^ n} : Ideal ℤ_[p]) := by
  by_cases hx : x = 0
  · subst hx
    simp only [norm_zero, zpow_neg, zpow_natCast, inv_nonneg, iff_true, Submodule.zero_mem]
    exact mod_cast Nat.zero_le _
  rw [norm_le_pow_iff_le_valuation x hx, mem_span_pow_iff_le_valuation x hx]
/-
**PadicInt.norm_le_pow_iff_norm_lt_pow_add_one** 是 Mathlib 中的一个定理，位于命名空间 `PadicI
nt`。
形式化陈述：norm_le_pow_iff_norm_lt_pow_add_one (x : Int_[p]) (n : Int) : ‖x‖ <= (p : 
Real) ^ n ↔ ‖x‖ < (p : Real) ^ (n + 1)
参数：x : Int_[p]；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_def`：norm_def {z : Int_[p]} : ‖z‖ = ‖(z : Rat_[p])‖
· 使用定理 `Padic.norm_le_pow_iff_norm_lt_pow_add_one`：norm_le_pow_iff_norm_lt_pow_a
dd_one (x : Rat_[p]) (n : Int) : ‖x‖ <= (p : Real) ^ n ↔ ‖x‖ < (p : Real) ^ (n +
 1)
-/
theorem norm_le_pow_iff_norm_lt_pow_add_one (x : ℤ_[p]) (n : ℤ) :
    ‖x‖ ≤ (p : ℝ) ^ n ↔ ‖x‖ < (p : ℝ) ^ (n + 1) := by
  rw [norm_def]; exact Padic.norm_le_pow_iff_norm_lt_pow_add_one _ _
/-
**PadicInt.norm_lt_pow_iff_norm_le_pow_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `PadicI
nt`。
形式化陈述：norm_lt_pow_iff_norm_le_pow_sub_one (x : Int_[p]) (n : Int) : ‖x‖ < (p : R
eal) ^ n ↔ ‖x‖ <= (p : Real) ^ (n - 1)
参数：x : Int_[p]；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`：norm_le_pow_iff_norm_lt_po
w_add_one (x : Int_[p]) (n : Int) : ‖x‖ <= (p : Real) ^ n ↔ ‖x‖ < (p : Real) ^ (
n + 1)
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem norm_lt_pow_iff_norm_le_pow_sub_one (x : ℤ_[p]) (n : ℤ) :
    ‖x‖ < (p : ℝ) ^ n ↔ ‖x‖ ≤ (p : ℝ) ^ (n - 1) := by
  rw [norm_le_pow_iff_norm_lt_pow_add_one, sub_add_cancel]
/-
**PadicInt.norm_lt_one_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：norm_lt_one_iff_dvd (x : Int_[p]) : ‖x‖ < 1 ↔ ↑p ∣ x
参数：x : Int_[p]。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PadicInt.norm_le_pow_iff_mem_span_pow`：norm_le_pow_iff_mem_span_pow (x :
 Int_[p]) (n : Nat) : ‖x‖ <= (p : Real) ^ (-n : Int) ↔ x in (Ideal.span {(p : In
t_[p]) ^ n} : Ideal Int_[p]…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `PadicInt.norm_le_pow_iff_norm_lt_pow_add_one`：norm_le_pow_iff_norm_lt_po
w_add_one (x : Int_[p]) (n : Int) : ‖x‖ <= (p : Real) ^ n ↔ ‖x‖ < (p : Real) ^ (
n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zpow_zero`：∀ {G : Type u_1} [inst : DivInvMonoid G] (a : G), a ^ 0 = 1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem norm_lt_one_iff_dvd (x : ℤ_[p]) : ‖x‖ < 1 ↔ ↑p ∣ x := by
  have := norm_le_pow_iff_mem_span_pow x 1
  rw [Ideal.mem_span_singleton, pow_one] at this
  rw [← this, norm_le_pow_iff_norm_lt_pow_add_one]
  simp only [zpow_zero, Int.ofNat_zero, Int.natCast_succ, neg_add_cancel, zero_add]

@[simp]
/-
**PadicInt.pow_p_dvd_int_iff** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：pow_p_dvd_int_iff (n : Nat) (a : Int) : (p : Int_[p]) ^ n ∣ a ↔ (p ^ n : I
nt) ∣ a
参数：n : Nat；a : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `PadicInt.norm_int_le_pow_iff_dvd`：norm_int_le_pow_iff_dvd {k : Int} {n :
 Nat} : ‖(k : Int_[p])‖ <= (p : Real) ^ (-n : Int) ↔ (p ^ n : Int) ∣ k
· 使用定理 `PadicInt.norm_le_pow_iff_mem_span_pow`：norm_le_pow_iff_mem_span_pow (x :
 Int_[p]) (n : Nat) : ‖x‖ <= (p : Real) ^ (-n : Int) ↔ x in (Ideal.span {(p : In
t_[p]) ^ n} : Ideal Int_[p]…
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pow_p_dvd_int_iff (n : ℕ) (a : ℤ) : (p : ℤ_[p]) ^ n ∣ a ↔ (p ^ n : ℤ) ∣ a := by
  rw [← Nat.cast_pow, ← norm_int_le_pow_iff_dvd, norm_le_pow_iff_mem_span_pow,
    Ideal.mem_span_singleton, Nat.cast_pow]

end NormLeIff

section Dvr

/-! ### Discrete valuation ring -/

/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Discrete valuation ring
-/
instance : IsLocalRing ℤ_[p] :=
  IsLocalRing.of_nonunits_add <| by simp only [mem_nonunits]; exact fun x y => norm_lt_one_add
/-
**PadicInt.p_nonunit** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：p_nonunit : (p : Int_[p]) in nonunits Int_[p]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `inv_lt_one_of_one_lt₀`：inv_lt_one_of_one_lt₀ (ha : 1 < a) : a⁻¹ < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `PadicInt.mem_nonunits`：mem_nonunits {z : Int_[p]} : z in nonunits Int_[p
] ↔ ‖z‖ < 1
· 使用定理 `PadicInt.norm_p`：norm_p : ‖(p : Int_[p])‖ = (p : Real)⁻¹
-/
theorem p_nonunit : (p : ℤ_[p]) ∈ nonunits ℤ_[p] := by
  have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ <| mod_cast hp.out.one_lt
  rwa [← norm_p, ← mem_nonunits] at this
/-
**PadicInt.maximalIdeal_eq_span_p** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：maximalIdeal_eq_span_p : maximalIdeal Int_[p] = Ideal.span {(p : Int_[p])}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `PadicInt.instIsLocalRing`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], IsLocalRi
ng ℤ_[p]
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PadicInt.norm_lt_one_iff_dvd`：norm_lt_one_iff_dvd (x : Int_[p]) : ‖x‖ < 
1 ↔ ↑p ∣ x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `PadicInt.p_nonunit`：p_nonunit : (p : Int_[p]) in nonunits Int_[p]
-/
theorem maximalIdeal_eq_span_p : maximalIdeal ℤ_[p] = Ideal.span {(p : ℤ_[p])} := by
  apply le_antisymm
  · intro x hx
    simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits] at hx
    rwa [Ideal.mem_span_singleton, ← norm_lt_one_iff_dvd]
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact p_nonunit
/-
**PadicInt.prime_p** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：prime_p : Prime (p : Int_[p])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `PadicInt.instCharZero`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], CharZero ℤ_[
p]
· 使用定理 `PadicInt.instIsLocalRing`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], IsLocalRi
ng ℤ_[p]
· 使用定理 `PadicInt.maximalIdeal_eq_span_p`：maximalIdeal_eq_span_p : maximalIdeal I
nt_[p] = Ideal.span {(p : Int_[p])}
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
-/
theorem prime_p : Prime (p : ℤ_[p]) := by
  rw [← Ideal.span_singleton_prime, ← maximalIdeal_eq_span_p]
  · infer_instance
  · exact NeZero.ne _
/-
**PadicInt.irreducible_p** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：irreducible_p : Irreducible (p : Int_[p])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `PadicInt.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain ℤ_[
p]
· 使用定理 `PadicInt.prime_p`：prime_p : Prime (p : Int_[p])
-/
theorem irreducible_p : Irreducible (p : ℤ_[p]) := Prime.irreducible prime_p
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDiscreteValuationRing ℤ_[p] :=
  IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨p, irreducible_p, fun {x hx} =>
      ⟨x.valuation, unitCoeff hx, by rw [mul_comm, ← unitCoeff_spec hx]⟩⟩
/-
**PadicInt.ideal_eq_span_pow_p** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：ideal_eq_span_pow_p {s : Ideal Int_[p]} (hs : s != ⊥) : exists n : Nat, s 
= Ideal.span {(p : Int_[p]) ^ n}
参数：hs : s != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.ideal_eq_span_pow_irreducible`：ideal_eq_span_pow
_irreducible {s : Ideal R} (hs : s != ⊥) {ϖ : R} (hirr : Irreducible ϖ) : exists
 n : Nat, s = Ideal.span {ϖ ^ n}
· 使用定理 `PadicInt.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain ℤ_[
p]
· 使用定理 `PadicInt.instIsDiscreteValuationRing`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)
], IsDiscreteValuationRing ℤ_[p]
· 使用定理 `PadicInt.irreducible_p`：irreducible_p : Irreducible (p : Int_[p])
-/
theorem ideal_eq_span_pow_p {s : Ideal ℤ_[p]} (hs : s ≠ ⊥) :
    ∃ n : ℕ, s = Ideal.span {(p : ℤ_[p]) ^ n} :=
  IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hs irreducible_p

open CauSeq
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAdicComplete (maximalIdeal ℤ_[p]) ℤ_[p] where
  prec' x hx := by
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.sub_mem, maximalIdeal_eq_span_p,
      Ideal.span_singleton_pow, ← norm_le_pow_iff_mem_span_pow] at hx ⊢
    let x' : CauSeq ℤ_[p] norm := ⟨x, ?_⟩; swap
    · intro ε hε
      obtain ⟨m, hm⟩ := exists_pow_neg_lt p hε
      refine ⟨m, fun n hn => lt_of_le_of_lt ?_ hm⟩
      rw [← neg_sub, norm_neg]
      exact hx hn
    · refine ⟨x'.lim, fun n => ?_⟩
      have : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := zpow_pos (mod_cast hp.out.pos) _
      obtain ⟨i, hi⟩ := equiv_def₃ (equiv_lim x') this
      by_cases! hin : i ≤ n
      · exact (hi i le_rfl n hin).le
      · specialize hi i le_rfl i le_rfl
        specialize hx hin.le
        have := nonarchimedean (x n - x i : ℤ_[p]) (x i - x'.lim)
        rw [sub_add_sub_cancel] at this
        exact this.trans (max_le_iff.mpr ⟨hx, hi.le⟩)

end Dvr

section FractionRing

/-
**PadicInt.algebra** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
形式化陈述：algebra : Algebra Int_[p] Rat_[p]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra : Algebra ℤ_[p] ℚ_[p] :=
  inferInstanceAs <| Algebra (subring p) _

@[simp]
/-
**PadicInt.algebraMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：algebraMap_apply (x : Int_[p]) : algebraMap Int_[p] Rat_[p] x = x
参数：x : Int_[p]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_apply (x : ℤ_[p]) : algebraMap ℤ_[p] ℚ_[p] x = x :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PadicInt.isFractionRing** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
形式化陈述：isFractionRing : IsFractionRing Int_[p] Rat_[p] where map_units
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PadicInt.algebraMap_apply`：algebraMap_apply (x : Int_[p]) : algebraMap I
nt_[p] Rat_[p] x = x
· 使用定理 `isUnit_iff_ne_zero`：isUnit_iff_ne_zero : IsUnit a ↔ a != 0
· 使用引理 `PadicInt.coe_ne_zero`：coe_ne_zero : (x : Rat_[p]) != 0 ↔ x != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mem_nonZeroDivisors_iff_ne_zero`：∀ {M₀ : Type u_2} [inst : MonoidWithZer
o M₀] {x : M₀} [NoZeroDivisors M₀] [Nontrivial M₀],   x ∈ nonZeroDivisors M₀ ↔ x
 ≠ 0
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `PadicInt.instIsLocalRing`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], IsLocalRi
ng ℤ_[p]
· 使用定理 `Submonoid.coe_one`：coe_one : ((1 : S) : M) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Right.nonneg_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α]
 [AddRightMono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Padic.norm_le_one_iff_val_nonneg`：norm_le_one_iff_val_nonneg (x : Rat_[p
]) : ‖x‖ <= 1 ↔ 0 <= x.valuation
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Padic.padicNormE.mul`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (q r : ℚ_[p]),
 ‖q * r‖ = ‖q‖ * ‖r‖
· 使用定理 `Padic.norm_p_pow`：norm_p_pow (n : Nat) : ‖(p : Rat_[p]) ^ n‖ = (p : Real
) ^ (-n : Int)
· 使用定理 `Padic.norm_eq_zpow_neg_valuation`：norm_eq_zpow_neg_valuation {x : Rat_[p
]} : x != 0 -> ‖x‖ = (p : Real) ^ (-x.valuation)
· 使用引理 `zpow_add'`：zpow_add' {m n : Int} (h : a != 0 ∨ m + n != 0 ∨ m = 0 ∧ n = 
0) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
（共 49 条，此处仅展示前 30 条）
-/
instance isFractionRing : IsFractionRing ℤ_[p] ℚ_[p] where
  map_units := fun ⟨x, hx⟩ => by
    rwa [algebraMap_apply, isUnit_iff_ne_zero, PadicInt.coe_ne_zero, ←
      mem_nonZeroDivisors_iff_ne_zero]
  surj x := by
    by_cases hx : ‖x‖ ≤ 1
    · use (⟨x, hx⟩, 1)
      rw [Submonoid.coe_one, map_one, mul_one, PadicInt.algebraMap_apply, Subtype.coe_mk]
    · set n := Int.toNat (-x.valuation) with hn
      have hn_coe : (n : ℤ) = -x.valuation := by
        rw [hn, Int.toNat_of_nonneg]
        rw [Right.nonneg_neg_iff]
        rw [Padic.norm_le_one_iff_val_nonneg, not_le] at hx
        exact hx.le
      set a := x * (p : ℚ_[p]) ^ n with ha
      have ha_norm : ‖a‖ = 1 := by
        have hx : x ≠ 0 := by
          intro h0
          rw [h0, norm_zero] at hx
          exact hx zero_le_one
        rw [ha, padicNormE.mul, Padic.norm_p_pow, Padic.norm_eq_zpow_neg_valuation hx,
          ← zpow_add', hn_coe, neg_neg, neg_add_cancel, zpow_zero]
        exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne p))
      use
        (⟨a, le_of_eq ha_norm⟩,
          ⟨(p ^ n : ℤ_[p]), mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne _)⟩)
      simp only [a, map_pow, map_natCast, algebraMap_apply]
  exists_of_eq := by
    simp_rw [algebraMap_apply, Subtype.coe_inj]
    exact fun h => ⟨1, by rw [h]⟩

end FractionRing

end PadicInt

