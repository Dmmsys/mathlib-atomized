/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Ordered structures on localizations of commutative monoids

-/

@[expose] public section

open Function

namespace Localization

variable {α : Type*}

section OrderedCancelCommMonoid

variable [CommMonoid α] [PartialOrder α] [IsOrderedCancelMonoid α] {s : Submonoid α}
  {a₁ b₁ : α} {a₂ b₂ : s}

@[to_additive]
/-
**Localization.le** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：le : LE (Localization s)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance le : LE (Localization s) :=
  ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ ≤ a₂ * b₁)
      fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext <| by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        rw [← mul_le_mul_iff_right, mul_right_comm, ← hf, mul_right_comm, mul_right_comm (a₂ : α),
          mul_le_mul_iff_right, ← mul_le_mul_iff_left, mul_left_comm, he, mul_left_comm,
          mul_left_comm (b₂ : α), mul_le_mul_iff_left]⟩

@[to_additive]
/-
**Localization.lt** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：lt : LT (Localization s)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lt : LT (Localization s) :=
  ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < a₂ * b₁)
      fun {a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂} hab hcd => propext <| by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        simp only [mul_right_inj] at he hf
        rw [← mul_lt_mul_iff_right, mul_right_comm, ← hf, mul_right_comm, mul_right_comm (a₂ : α),
          mul_lt_mul_iff_right, ← mul_lt_mul_iff_left, mul_left_comm, he, mul_left_comm,
          mul_left_comm (b₂ : α), mul_lt_mul_iff_left]⟩

@[to_additive]
/-
**Localization.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_le_mk : mk a₁ a₂ <= mk b₁ b₂ ↔ ↑b₂ * a₁ <= a₂ * b₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk : mk a₁ a₂ ≤ mk b₁ b₂ ↔ ↑b₂ * a₁ ≤ a₂ * b₁ :=
  Iff.rfl

@[to_additive]
/-
**Localization.mk_lt_mk** 是 Mathlib 中的一个定理，位于命名空间 `Localization`。
形式化陈述：mk_lt_mk : mk a₁ a₂ < mk b₁ b₂ ↔ ↑b₂ * a₁ < a₂ * b₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_lt_mk : mk a₁ a₂ < mk b₁ b₂ ↔ ↑b₂ * a₁ < a₂ * b₁ :=
  Iff.rfl

-- declaring this separately to the instance below makes things faster
@[to_additive]
/-
**Localization.partialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：partialOrder : PartialOrder (Localization s) where le_refl a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance partialOrder : PartialOrder (Localization s) where
  le_refl a := Localization.induction_on a fun _ => le_rfl
  le_trans a b c :=
    Localization.induction_on₃ a b c fun a b c hab hbc => by
      simp only [mk_le_mk] at hab hbc ⊢
      apply le_of_mul_le_mul_left' _
      · exact ↑b.2
      grw [mul_left_comm, hab]
      rwa [mul_left_comm, mul_left_comm (b.2 : α), mul_le_mul_iff_left]
  le_antisymm a b := by
    induction a using Localization.rec
    on_goal 1 =>
      induction b using Localization.rec
      · simp_rw [mk_le_mk, mk_eq_mk_iff, r_iff_exists]
        exact fun hab hba => ⟨1, by rw [hab.antisymm hba]⟩
    all_goals rfl
  lt_iff_le_not_ge a b := Localization.induction_on₂ a b fun _ _ => lt_iff_le_not_ge

@[to_additive]
/-
**Localization.isOrderedCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：isOrderedCancelMonoid : IsOrderedCancelMonoid (Localization s) where mul_l
e_mul_left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.induction_on₂`：induction_on₂ {p : Localization S -> Localiz
ation S -> Prop} (x y) (H : forall x y : M × S, p (mk x.1 x.2) (mk y.1 y.2)) : p
 x y
· 使用定理 `Localization.induction_on`：induction_on {p : Localization S -> Prop} (x)
 (H : forall y : M × S, p (mk y.1 y.2)) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Localization.mk_mul`：mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (
a * c) (b * d)
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_le_mul_left`：mul_le_mul_left [i : MulRightMono α] {b c : α} (bc : b 
<= c) (a : α) : b * a <= c * a
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `IsOrderedCancelMonoid.toIsOrderedMonoid`：∀ {α : Type u_2} {inst : CommMo
noid α} {inst_1 : Preorder α} [self : IsOrderedCancelMonoid α], IsOrderedMonoid 
α
· 使用定理 `Localization.induction_on₃`：induction_on₃ {p : Localization S -> Localiz
ation S -> Localization S -> Prop} (x y z) (H : forall x y z : M × S, p (mk x.1 
x.2) (mk y.1 y.2…
· 使用定理 `le_of_mul_le_mul_left'`：le_of_mul_le_mul_left' [MulLeftReflectLE α] {a b
 c : α} (bc : a * b <= a * c) : b <= c
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsOrderedCancelMonoid.toIsCancelMul`：∀ {α : Type u_1} [inst : CommMonoid
 α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], IsCancelMul α
· 使用定理 `IsOrderedCancelMonoid.toMulLeftReflectLT`：∀ {α : Type u_1} [inst : CommM
onoid α] [inst_1 : PartialOrder α] [IsOrderedCancelMonoid α], MulLeftReflectLT α
-/
instance isOrderedCancelMonoid : IsOrderedCancelMonoid (Localization s) where
  mul_le_mul_left := fun a b =>
    Localization.induction_on₂ a b fun a b hab c =>
      Localization.induction_on c fun c => by
        simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ (c.2 : α)] at hab ⊢
        exact mul_le_mul_left hab _
  le_of_mul_le_mul_left := fun a b c =>
    Localization.induction_on₃ a b c fun a b c hab => by
      simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ _ a.1] at hab ⊢
      exact le_of_mul_le_mul_left' hab

@[to_additive]
/-
**Localization.decidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：decidableLE [DecidableLE α] : DecidableLE (Localization s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.mk_le_mk`：mk_le_mk : mk a₁ a₂ <= mk b₁ b₂ ↔ ↑b₂ * a₁ <= a₂ 
* b₁
-/
instance decidableLE [DecidableLE α] : DecidableLE (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_le_mk

@[to_additive]
/-
**Localization.decidableLT** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
形式化陈述：decidableLT [DecidableLT α] : DecidableLT (Localization s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Localization.mk_lt_mk`：mk_lt_mk : mk a₁ a₂ < mk b₁ b₂ ↔ ↑b₂ * a₁ < a₂ * 
b₁
-/
instance decidableLT [DecidableLT α] : DecidableLT (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_lt_mk

/-- An ordered cancellative monoid injects into its localization by sending `a` to `a / b`. -/
@[to_additive (attr := simps!) /-- An ordered cancellative monoid injects into its localization by
sending `a` to `a - b`. -/]
/-
**Localization.mkOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `Localization`。
形式化陈述：mkOrderEmbedding (b : s) : α ↪o Localization s where toFun a
参数：b : s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mkOrderEmbedding (b : s) : α ↪o Localization s where
  toFun a := mk a b
  inj' := mk_left_injective _
  map_rel_iff' {a b} := by simp [mk_le_mk]

end OrderedCancelCommMonoid

@[to_additive]
/-
**Localization.** 是 Mathlib 中的一个实例，位于命名空间 `Localization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommMonoid α] [LinearOrder α] [IsOrderedCancelMonoid α] {s : Submonoid α} :
    LinearOrder (Localization s) :=
  { le_total := fun a b =>
      Localization.induction_on₂ a b fun _ _ => by
        simp_rw [mk_le_mk]
        exact le_total _ _
    toDecidableLE := Localization.decidableLE
    toDecidableLT := Localization.decidableLT
    toDecidableEq := Localization.decidableEq }

end Localization

