/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Int
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic

/-!
# Lemmas about quotients in characteristic zero
-/

public section


variable {R : Type*} [DivisionRing R] [CharZero R] {p : R}

namespace AddSubgroup

/-- `z • r` is a multiple of `p` iff `r` is `k * (p / z)` above a multiple of `p`, where
`0 ≤ k < |z|`. -/
/-
**AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div** 是 Mathlib 中的一个定理，位于命名空间 
`AddSubgroup`。
形式化陈述：zsmul_mem_zmultiples_iff_exists_sub_div {r : R} {z : Int} (hz : z != 0) : 
z • r in AddSubgroup.zmultiples p ↔ exists k : Fin z.natAbs, r - (k : Nat) • (p 
/ z : R) in AddSubgroup.zmultiples p
参数：hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddSubgroup.mem_zmultiples_iff`：∀ {G : Type u_1} [inst : AddGroup G] {g 
h : G}, h ∈ AddSubgroup.zmultiples g ↔ ∃ k, k • g = h
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Int.cast_ne_zero`：cast_ne_zero : (n : α) != 0 ↔ n != 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Int.ofNat_lt`：∀ {n m : ℕ}, ↑n < ↑m ↔ n < m
· 使用定理 `Int.toNat_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.toNat = a
· 使用定理 `Int.emod_nonneg`：∀ (a : ℤ) {b : ℤ}, b ≠ 0 → 0 ≤ a % b
· 使用定理 `LT.lt.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LT α], a < b → b = 
c → a < c
· 使用定理 `Int.emod_lt_abs`：emod_lt_abs (a : Int) {b : Int} (H : b != 0) : a % b < 
|b|
· 使用定理 `Int.abs_eq_natAbs`：∀ (a : ℤ), |a| = ↑a.natAbs
· 使用定理 `Fin.val_mk`：∀ {m n : ℕ} (h : m < n), ↑⟨m, h⟩ = m
· 使用定理 `Int.mul_ediv_add_emod`：∀ (a b : ℤ), b * (a / b) + a % b = a

--- 原说明 ---
`z • r` is a multiple of `p` iff `r` is `k * (p / z)` above a multiple of `p`, w
here
`0 ≤ k < |z|`.
-/
theorem zsmul_mem_zmultiples_iff_exists_sub_div {r : R} {z : ℤ} (hz : z ≠ 0) :
    z • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin z.natAbs, r - (k : ℕ) • (p / z : R) ∈ AddSubgroup.zmultiples p := by
  rw [AddSubgroup.mem_zmultiples_iff]
  simp_rw [AddSubgroup.mem_zmultiples_iff, div_eq_mul_inv, ← smul_mul_assoc, eq_sub_iff_add_eq]
  have hz' : (z : R) ≠ 0 := Int.cast_ne_zero.mpr hz
  conv_rhs => simp +singlePass only [← (mul_right_injective₀ hz').eq_iff]
  simp_rw [← zsmul_eq_mul, smul_add, ← mul_smul_comm, zsmul_eq_mul (z : R)⁻¹, mul_inv_cancel₀ hz',
    mul_one, ← natCast_zsmul, smul_smul, ← add_smul]
  constructor
  · rintro ⟨k, h⟩
    simp_rw [← h]
    refine ⟨⟨(k % z).toNat, ?_⟩, k / z, ?_⟩
    · rw [← Int.ofNat_lt, Int.toNat_of_nonneg (Int.emod_nonneg _ hz)]
      exact (Int.emod_lt_abs _ hz).trans_eq (Int.abs_eq_natAbs _)
    rw [Fin.val_mk, Int.toNat_of_nonneg (Int.emod_nonneg _ hz)]
    nth_rewrite 3 [← Int.mul_ediv_add_emod k z]
    rfl
  · rintro ⟨k, n, h⟩
    exact ⟨_, h⟩
/-
**AddSubgroup.nsmul_mem_zmultiples_iff_exists_sub_div** 是 Mathlib 中的一个定理，位于命名空间 
`AddSubgroup`。
形式化陈述：nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : Nat} (hn : n != 0) : 
n • r in AddSubgroup.zmultiples p ↔ exists k : Fin n, r - (k : Nat) • (p / n : R
) in AddSubgroup.zmultiples p
参数：hn : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div`：zsmul_mem_zmultiple
s_iff_exists_sub_div {r : R} {z : Int} (hz : z != 0) : z • r in AddSubgroup.zmul
tiples p ↔ exists k : Fin z.natAbs, r - (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nsmul_mem_zmultiples_iff_exists_sub_div {r : R} {n : ℕ} (hn : n ≠ 0) :
    n • r ∈ AddSubgroup.zmultiples p ↔
      ∃ k : Fin n, r - (k : ℕ) • (p / n : R) ∈ AddSubgroup.zmultiples p := by
  rw [← natCast_zsmul r, zsmul_mem_zmultiples_iff_exists_sub_div (Int.natCast_ne_zero.mpr hn),
    Int.cast_natCast]
  rfl

end AddSubgroup

namespace QuotientAddGroup

/-
**QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quot
ientAddGroup`。
形式化陈述：zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : In
t} (hz : z != 0) : z • ψ = z • θ ↔ exists k : Fin z.natAbs, ψ = θ + ((k : Nat) •
 (p / z) : R)
参数：hz : z != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div`：zsmul_mem_zmultiple
s_iff_exists_sub_div {r : R} {z : Int} (hz : z != 0) : z • r in AddSubgroup.zmul
tiples p ↔ exists k : Fin z.natAbs, r - (…
-/
theorem zmultiples_zsmul_eq_zsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : ℤ} (hz : z ≠ 0) :
    z • ψ = z • θ ↔ ∃ k : Fin z.natAbs, ψ = θ + ((k : ℕ) • (p / z) : R) := by
  induction ψ using Quotient.inductionOn
  induction θ using Quotient.inductionOn
  simp_rw [← QuotientAddGroup.mk_zsmul, ← QuotientAddGroup.mk_add,
    QuotientAddGroup.eq_iff_sub_mem, ← smul_sub, ← sub_sub]
  exact AddSubgroup.zsmul_mem_zmultiples_iff_exists_sub_div hz
/-
**QuotientAddGroup.zmultiples_nsmul_eq_nsmul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Quot
ientAddGroup`。
形式化陈述：zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : Na
t} (hz : n != 0) : n • ψ = n • θ ↔ exists k : Fin n, ψ = θ + (k : Nat) • (p / n 
: R)
参数：hz : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroup.normal_of_isAddCommutative`：∀ {G : Type u_1} [inst : AddGrou
p G] [IsAddCommutative G] (H : AddSubgroup G), H.Normal
· 使用定理 `AddCommMagma.to_isCommutative`：∀ {G : Type u_1} [inst : AddCommMagma G],
 IsAddCommutative G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `QuotientAddGroup.zmultiples_zsmul_eq_zsmul_iff`：zmultiples_zsmul_eq_zsmu
l_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {z : Int} (hz : z != 0) : z • ψ = z •
 θ ↔ exists k : Fin z.natAbs, ψ = θ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_ne_zero`：∀ {n : ℕ}, ↑n ≠ 0 ↔ n ≠ 0
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zmultiples_nsmul_eq_nsmul_iff {ψ θ : R ⧸ AddSubgroup.zmultiples p} {n : ℕ} (hz : n ≠ 0) :
    n • ψ = n • θ ↔ ∃ k : Fin n, ψ = θ + (k : ℕ) • (p / n : R) := by
  rw [← natCast_zsmul ψ, ← natCast_zsmul θ,
    zmultiples_zsmul_eq_zsmul_iff (Int.natCast_ne_zero.mpr hz), Int.cast_natCast]
  rfl

end QuotientAddGroup

