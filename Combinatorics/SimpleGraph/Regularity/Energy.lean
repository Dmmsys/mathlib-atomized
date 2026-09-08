/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Data.Rat.BigOperators

/-!
# Energy of a partition

This file defines the energy of a partition.

The energy is the auxiliary quantity that drives the induction process in the proof of Szemerédi's
Regularity Lemma. As long as we do not have a suitable equipartition, we will find a new one that
has an energy greater than the previous one plus some fixed constant.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset

variable {α : Type*} [DecidableEq α] {s : Finset α} (P : Finpartition s) (G : SimpleGraph α)
  [DecidableRel G.Adj]

namespace Finpartition

/-- The energy of a partition, also known as index. Auxiliary quantity for Szemerédi's regularity
lemma. -/
/-
**Finpartition.energy** 是 Mathlib 中的一个定义，位于命名空间 `Finpartition`。
形式化陈述：energy : Rat
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The energy of a partition, also known as index. Auxiliary quantity for Szemerédi
's regularity
lemma.
-/
def energy : ℚ :=
  ((∑ uv ∈ P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2) : ℚ) / (#P.parts : ℚ) ^ 2
/-
**Finpartition.energy_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：energy_nonneg : 0 <= P.energy G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Finset.sum_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, 0 ≤ f…
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
-/
theorem energy_nonneg : 0 ≤ P.energy G := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) <| sq_nonneg _
/-
**Finpartition.energy_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：energy_le_one : P.energy G <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_le_of_le_mul₀`：div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a 
<= c * b) : a / b <= c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Finset.sum_le_card_nsmul`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCom
mMonoid N] [inst_1 : Preorder N] [AddLeftMono N] (s : Finset ι)   (f : ι → N) (n
 : N), (∀ x ∈ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `sq_le_one_iff₀`：sq_le_one_iff₀ (ha : 0 <= a) : a ^ 2 <= 1 ↔ a <= 1
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `SimpleGraph.edgeDensity_nonneg`：edgeDensity_nonneg (s t : Finset α) : 0 
<= G.edgeDensity s t
· 使用定理 `SimpleGraph.edgeDensity_le_one`：edgeDensity_le_one (s t : Finset α) : G.
edgeDensity s t <= 1
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.offDiag_card`：offDiag_card : (offDiag s).card = s.card * s.card -
 s.card
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `tsub_le_self`：tsub_le_self : a - b <= a
-/
theorem energy_le_one : P.energy G ≤ 1 :=
  div_le_of_le_mul₀ (sq_nonneg _) zero_le_one <|
    calc
      ∑ uv ∈ P.parts.offDiag, G.edgeDensity uv.1 uv.2 ^ 2 ≤ #P.parts.offDiag • (1 : ℚ) :=
        sum_le_card_nsmul _ _ 1 fun _ _ =>
          (sq_le_one_iff₀ <| G.edgeDensity_nonneg _ _).2 <| G.edgeDensity_le_one _ _
      _ = #P.parts.offDiag := Nat.smul_one_eq_cast _
      _ ≤ _ := by
        rw [offDiag_card, one_mul]
        norm_cast
        rw [sq]
        exact tsub_le_self

@[simp, norm_cast]
/-
**Finpartition.coe_energy** 是 Mathlib 中的一个定理，位于命名空间 `Finpartition`。
形式化陈述：coe_energy {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
 (P.energy G : 𝕜) = (∑ uv in P.parts.offDiag, (G.edgeDensity uv.1 uv.2 : 𝕜) ^ 2)
 / (#P.parts : 𝕜) ^ 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.energy.eq_1`：∀ {α : Type u_1} [inst : DecidableEq α] {s : F
inset α} (P : Finpartition s) (G : SimpleGraph α)   [inst_1 : DecidableRel G.Adj
], P.energy G …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Rat.cast_pow`：cast_pow (p : Rat) (n : Nat) : ↑(p ^ n) = (p ^ n : α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
-/
theorem coe_energy {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :
    (P.energy G : 𝕜) =
      (∑ uv ∈ P.parts.offDiag, (G.edgeDensity uv.1 uv.2 : 𝕜) ^ 2) / (#P.parts : 𝕜) ^ 2 := by
  rw [energy]; norm_cast

end Finpartition

