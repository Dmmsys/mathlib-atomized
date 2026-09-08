/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Ordered vector spaces
-/

@[expose] public section

open OrderDual

variable {𝕜 G : Type*}

section LinearOrderedSemifield
variable [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup G] [PartialOrder G]

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosSMulMono.toPosSMulReflectLE [MulAction 𝕜 G] [PosSMulMono 𝕜 G] :
    PosSMulReflectLE 𝕜 G where
  le_of_smul_le_smul_left _a ha b₁ b₂ h := by
    simpa [ha.ne'] using smul_le_smul_of_nonneg_left h <| inv_nonneg.2 ha.le

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PosSMulStrictMono.toPosSMulReflectLT [MulActionWithZero 𝕜 G]
    [PosSMulStrictMono 𝕜 G] : PosSMulReflectLT 𝕜 G :=
  .of_pos fun a ha b₁ b₂ h ↦ by simpa [ha.ne'] using smul_lt_smul_of_pos_left h <| inv_pos.2 ha

end LinearOrderedSemifield

section Field
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [Module 𝕜 G] {a : 𝕜} {b₁ b₂ : G}

section PosSMulMono
variable [PosSMulMono 𝕜 G]

/-
**inv_smul_le_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_smul_le_iff_of_neg (h : a < 0) : a⁻¹ • b₁ <= b₂ ↔ a • b₂ <= b₁
参数：h : a < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_le_smul_iff_of_neg_left`：smul_le_smul_iff_of_neg_left [PosSMulMono 
α β] [PosSMulReflectLE α β] (ha : a < 0) : a • b₁ <= a • b₂ ↔ b₂ <= b₁
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `PosSMulReflectLE.toPosSMulReflectLT`：∀ {α : Type u_1} {β : Type u_2} [in
st : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrde
r α]   [inst_4 : PartialO…
· 使用定理 `PosSMulMono.toPosSMulReflectLE`：∀ {𝕜 : Type u_1} {G : Type u_2} [inst : 
Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : Partia
lOrder G] [inst_4 : …
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inv_smul_le_iff_of_neg (h : a < 0) : a⁻¹ • b₁ ≤ b₂ ↔ a • b₂ ≤ b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]
/-
**smul_inv_le_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_inv_le_iff_of_neg (h : a < 0) : b₁ <= a⁻¹ • b₂ ↔ b₂ <= a • b₁
参数：h : a < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_le_smul_iff_of_neg_left`：smul_le_smul_iff_of_neg_left [PosSMulMono 
α β] [PosSMulReflectLE α β] (ha : a < 0) : a • b₁ <= a • b₂ ↔ b₂ <= b₁
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `PosSMulReflectLE.toPosSMulReflectLT`：∀ {α : Type u_1} {β : Type u_2} [in
st : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : PartialOrde
r α]   [inst_4 : PartialO…
· 使用定理 `PosSMulMono.toPosSMulReflectLE`：∀ {𝕜 : Type u_1} {G : Type u_2} [inst : 
Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : Partia
lOrder G] [inst_4 : …
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma smul_inv_le_iff_of_neg (h : a < 0) : b₁ ≤ a⁻¹ • b₂ ↔ b₂ ≤ a • b₁ := by
  rw [← smul_le_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

variable (G)

/-- Left scalar multiplication as an order isomorphism. -/
@[simps!]
/-
**OrderIso.smulRightDual** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.smulRightDual (ha : a < 0) : G ≃o Gᵒᵈ where toEquiv
参数：ha : a < 0。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Left scalar multiplication as an order isomorphism.
-/
def OrderIso.smulRightDual (ha : a < 0) : G ≃o Gᵒᵈ where
  toEquiv := (Equiv.smulRight ha.ne).trans toDual
  map_rel_iff' := (@OrderDual.toDual_le_toDual G).trans <| smul_le_smul_iff_of_neg_left ha

end PosSMulMono

variable [PosSMulStrictMono 𝕜 G]

/-
**inv_smul_lt_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_smul_lt_iff_of_neg (h : a < 0) : a⁻¹ • b₁ < b₂ ↔ a • b₂ < b₁
参数：h : a < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_lt_smul_iff_of_neg_left`：smul_lt_smul_iff_of_neg_left (ha : a < 0) 
: a • b₁ < a • b₂ ↔ b₂ < b₁
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosSMulStrictMono.toPosSMulReflectLT`：∀ {𝕜 : Type u_1} {G : Type u_2} [i
nst : Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : 
AddCommGroup G] [inst_4 : …
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma inv_smul_lt_iff_of_neg (h : a < 0) : a⁻¹ • b₁ < b₂ ↔ a • b₂ < b₁ := by
  rw [← smul_lt_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]
/-
**smul_inv_lt_iff_of_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：smul_inv_lt_iff_of_neg (h : a < 0) : b₁ < a⁻¹ • b₂ ↔ b₂ < a • b₁
参数：h : a < 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_lt_smul_iff_of_neg_left`：smul_lt_smul_iff_of_neg_left (ha : a < 0) 
: a • b₁ < a • b₂ ↔ b₂ < b₁
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `PosSMulStrictMono.toPosSMulReflectLT`：∀ {𝕜 : Type u_1} {G : Type u_2} [i
nst : Semifield 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : 
AddCommGroup G] [inst_4 : …
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma smul_inv_lt_iff_of_neg (h : a < 0) : b₁ < a⁻¹ • b₂ ↔ b₂ < a • b₁ := by
  rw [← smul_lt_smul_iff_of_neg_left h, smul_inv_smul₀ h.ne]

end Field

namespace Mathlib.Meta.Positivity
open Lean Meta Qq Function

variable {α β : Type*}

section PosSMulMono
variable [Zero α] [Zero β] [SMulZeroClass α β] [Preorder α] [Preorder β] [PosSMulMono α β] {a : α}
  {b : β}

/-
**Mathlib.Meta.Positivity.smul_nonneg_of_pos_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间
 `Mathlib.Meta.Positivity`。
形式化陈述：smul_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 <= b) : 0 <= a • b
参数：ha : 0 < a；hb : 0 <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem smul_nonneg_of_pos_of_nonneg (ha : 0 < a) (hb : 0 ≤ b) : 0 ≤ a • b :=
  smul_nonneg ha.le hb
/-
**Mathlib.Meta.Positivity.smul_nonneg_of_nonneg_of_pos** 是 Mathlib 中的一个定理，位于命名空间
 `Mathlib.Meta.Positivity`。
形式化陈述：smul_nonneg_of_nonneg_of_pos (ha : 0 <= a) (hb : 0 < b) : 0 <= a • b
参数：ha : 0 <= a；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem smul_nonneg_of_nonneg_of_pos (ha : 0 ≤ a) (hb : 0 < b) : 0 ≤ a • b :=
  smul_nonneg ha hb.le
/-
**Mathlib.Meta.Positivity.smul_nonneg_of_pos_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `M
athlib.Meta.Positivity`。
形式化陈述：smul_nonneg_of_pos_of_pos (ha : 0 < a) (hb : 0 < b) : 0 <= a • b
参数：ha : 0 < a；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_nonneg`：smul_nonneg [PosSMulMono α β] (ha : 0 <= a) (hb : 0 <= b₁) 
: 0 <= a • b₁
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem smul_nonneg_of_pos_of_pos (ha : 0 < a) (hb : 0 < b) : 0 ≤ a • b :=
  smul_nonneg ha.le hb.le

end PosSMulMono

section Module.IsTorsionFree
variable [Semiring α] [IsDomain α] [AddCommMonoid β] [Module α β] [Module.IsTorsionFree α β]
  {a : α} {b : β}

/-
**Mathlib.Meta.Positivity.smul_ne_zero_of_pos_of_ne_zero** 是 Mathlib 中的一个定理，位于命名
空间 `Mathlib.Meta.Positivity`。
形式化陈述：smul_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b != 0) : a
 • b != 0
参数：ha : 0 < a；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_ne_zero`：smul_ne_zero (hr : r != 0) (hm : m != 0) : r • m != 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem smul_ne_zero_of_pos_of_ne_zero [Preorder α] (ha : 0 < a) (hb : b ≠ 0) : a • b ≠ 0 :=
  smul_ne_zero ha.ne' hb
/-
**Mathlib.Meta.Positivity.smul_ne_zero_of_ne_zero_of_pos** 是 Mathlib 中的一个定理，位于命名
空间 `Mathlib.Meta.Positivity`。
形式化陈述：smul_ne_zero_of_ne_zero_of_pos [Preorder β] (ha : a != 0) (hb : 0 < b) : a
 • b != 0
参数：ha : a != 0；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_ne_zero`：smul_ne_zero (hr : r != 0) (hm : m != 0) : r • m != 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem smul_ne_zero_of_ne_zero_of_pos [Preorder β] (ha : a ≠ 0) (hb : 0 < b) : a • b ≠ 0 :=
  smul_ne_zero ha hb.ne'

end Module.IsTorsionFree

/-- Positivity extension for scalar multiplication. -/
@[positivity HSMul.hSMul _ _]
meta def evalSMul : PositivityExt where eval {_u α} zα pα? (e : Q($α)) :=
  match pα? with | none => pure .none | some pα => do
  let .app (.app (.app (.app (.app (.app
        (.const ``HSMul.hSMul [u1, _, _]) (β : Q(Type u1))) _) _) _)
          (a : Q($β))) (b : Q($α)) ← whnfR e | throwError "failed to match hSMul"
  let zM : Q(Zero $β) ← synthInstanceQ q(Zero $β)
  let pM : Q(PartialOrder $β) ← synthInstanceQ q(PartialOrder $β)
  -- Using `q()` here would be impractical, as we would have to manually `synthInstanceQ` all the
  -- required typeclasses. Ideally we could tell `q()` to do this automatically.
  match ← core zM pM a, ← core zα pα b with
  | .positive pa, .positive pb =>
      try {
        let _hαβ : Q(SMul $β $α) ← synthInstanceQ q(SMul $β $α)
        let _hαβ : Q(PosSMulStrictMono $β $α) ← synthInstanceQ q(PosSMulStrictMono $β $α)
        pure (.positive (← mkAppM ``smul_pos #[pa, pb]))
      } catch _ =>
        pure (.nonnegative (← mkAppM ``smul_nonneg_of_pos_of_pos #[pa, pb]))
  | .positive pa, .nonnegative pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg_of_pos_of_nonneg #[pa, pb]))
  | .nonnegative pa, .positive pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg_of_nonneg_of_pos #[pa, pb]))
  | .nonnegative pa, .nonnegative pb =>
      pure (.nonnegative (← mkAppM ``smul_nonneg #[pa, pb]))
  | .positive pa, .nonzero pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero_of_pos_of_ne_zero #[pa, pb]))
  | .nonzero pa, .positive pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero_of_ne_zero_of_pos #[pa, pb]))
  | .nonzero pa, .nonzero pb =>
      pure (.nonzero (← mkAppM ``smul_ne_zero #[pa, pb]))
  | _, _ => pure .none

end Mathlib.Meta.Positivity

