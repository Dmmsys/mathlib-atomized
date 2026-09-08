/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/

@[expose] public section

open Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups ModularGroup Real

variable (N : ℕ)

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

@[simp]
/-
**SL_reduction_mod_hom_val** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SL_reduction_mod_hom_val (γ : SL(2, Int)) (i j : Fin 2) : SLMOD(N) γ i j =
 (γ i j : ZMod N)
参数：γ : SL(2, Int)；i j : Fin 2。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SL_reduction_mod_hom_val (γ : SL(2, ℤ)) (i j : Fin 2) :
    SLMOD(N) γ i j = (γ i j : ZMod N) :=
  rfl

namespace CongruenceSubgroup

/-- The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity
modulo `N`. -/
/-
**CongruenceSubgroup.Gamma** 是 Mathlib 中的一个定义，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma : Subgroup SL(2, Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to 
the identity
modulo `N`.
-/
def Gamma : Subgroup SL(2, ℤ) :=
  SLMOD(N).ker

@[inherit_doc] scoped notation "Γ(" n ")" => Gamma n
/-
**CongruenceSubgroup.Gamma_mem'** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma_mem' {N} {γ : SL(2, Int)} : γ in Gamma N ↔ SLMOD(N) γ = 1
参数：2, Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Gamma_mem' {N} {γ : SL(2, ℤ)} : γ ∈ Gamma N ↔ SLMOD(N) γ = 1 :=
  Iff.rfl

@[simp]
/-
**CongruenceSubgroup.Gamma_mem** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma_mem {N} {γ : SL(2, Int)} : γ in Gamma N ↔ (γ 0 0 : ZMod N) = 1 ∧ (γ 
0 1 : ZMod N) = 0 ∧ (γ 1 0 : ZMod N) = 0 ∧ (γ 1 1 : ZMod N) = 1
参数：2, Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Matrix.one_apply_eq`：one_apply_eq (i) : (1 : Matrix n n α) i i = 1
· 使用定理 `Matrix.one_apply_ne`：one_apply_ne {i j} : i != j -> (1 : Matrix n n α) i
 j = 0
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib_1`：∀ (n : ℕ) [NeZero n], NeZero 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Gamma_mem {N} {γ : SL(2, ℤ)} : γ ∈ Gamma N ↔ (γ 0 0 : ZMod N) = 1 ∧
    (γ 0 1 : ZMod N) = 0 ∧ (γ 1 0 : ZMod N) = 0 ∧ (γ 1 1 : ZMod N) = 1 := by
  simp [Gamma_mem', SpecialLinearGroup.ext_iff, and_assoc]
/-
**CongruenceSubgroup.Gamma_normal** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgroup`
。
形式化陈述：Gamma_normal : Subgroup.Normal (Gamma N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
-/
theorem Gamma_normal : Subgroup.Normal (Gamma N) :=
  SLMOD(N).normal_ker
/-
**CongruenceSubgroup.Gamma_one_top** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgroup
`。
形式化陈述：Gamma_one_top : Gamma 1 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Gamma_one_top : Gamma 1 = ⊤ := by
  ext
  simp [eq_iff_true_of_subsingleton]
/-
**CongruenceSubgroup.mem_Gamma_one** 是 Mathlib 中的一个引理，位于命名空间 `CongruenceSubgroup
`。
形式化陈述：mem_Gamma_one (γ : SL(2, Int)) : γ in Γ(1)
参数：γ : SL(2, Int)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CongruenceSubgroup.Gamma_one_top`：Gamma_one_top : Gamma 1 = ⊤
-/
lemma mem_Gamma_one (γ : SL(2, ℤ)) : γ ∈ Γ(1) := by
  simp only [Gamma_one_top, Subgroup.mem_top]

/-- The GL-image of `Γ(1)` equals `𝒮ℒ` (the image of `SL(2, ℤ)` in `GL(2, ℝ)`). -/
/-
**CongruenceSubgroup.Gamma_one_coe_eq_SL** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSu
bgroup`。
形式化陈述：Gamma_one_coe_eq_SL : (↑(Gamma 1) : Subgroup (GL (Fin 2) Real)) = 𝒮ℒ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CongruenceSubgroup.Gamma_one_top`：Gamma_one_top : Gamma 1 = ⊤
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The GL-image of `Γ(1)` equals `𝒮ℒ` (the image of `SL(2, ℤ)` in `GL(2, ℝ)`).
-/
theorem Gamma_one_coe_eq_SL : (↑(Gamma 1) : Subgroup (GL (Fin 2) ℝ)) = 𝒮ℒ := by
  simp [Gamma_one_top, MonoidHom.range_eq_map]
/-
**CongruenceSubgroup.Gamma_zero_bot** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgrou
p`。
形式化陈述：Gamma_zero_bot : Gamma 0 = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Gamma_zero_bot : Gamma 0 = ⊥ := rfl
/-
**CongruenceSubgroup.ModularGroup_T_pow_mem_Gamma** 是 Mathlib 中的一个引理，位于命名空间 `Con
gruenceSubgroup`。
形式化陈述：ModularGroup_T_pow_mem_Gamma (N M : Int) (hNM : N ∣ M) : (ModularGroup.T ^
 M) in Gamma (Int.natAbs N)
参数：N M : Int；hNM : N ∣ M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ModularGroup.coe_T_zpow`：coe_T_zpow (n : Int) : (T ^ n).1 = !![1, n; 0, 
1]
· 使用定理 `Matrix.cons_val'`：cons_val' (v : n' -> α) (B : Fin m -> n' -> α) (i j) :
 vecCons v B i j = vecCons (v j) (fun i => B i j) i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_natAbs`：∀ {α : Type u_1} [inst : AddGroupWithOne α] (n : ℤ), ↑n
.natAbs = ↑|n|
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma ModularGroup_T_pow_mem_Gamma (N M : ℤ) (hNM : N ∣ M) :
    (ModularGroup.T ^ M) ∈ Gamma (Int.natAbs N) := by
  simp [ModularGroup.coe_T_zpow, hNM, ZMod.intCast_zmod_eq_zero_iff_dvd]
/-
**CongruenceSubgroup.instFiniteIndexGamma** 是 Mathlib 中的一个实例，位于命名空间 `CongruenceS
ubgroup`。
形式化陈述：instFiniteIndexGamma [NeZero N] : (Gamma N).FiniteIndex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Matrix.SpecialLinearGroup.instFinite`：∀ {n : Type u} [inst : DecidableEq
 n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] [Finite R],   Finite
 (Matrix.SpecialLinearGrou…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance instFiniteIndexGamma [NeZero N] : (Gamma N).FiniteIndex := Subgroup.finiteIndex_ker _

set_option backward.isDefEq.respectTransparency.types false in
/-- The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
/-
**CongruenceSubgroup.Gamma0** 是 Mathlib 中的一个定义，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma0 : Subgroup SL(2, Int) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry re
duces to zero
modulo `N`.
-/
def Gamma0 : Subgroup SL(2, ℤ) where
  carrier := { g | (g 1 0 : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' {a} {b} ha hb := by
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_mul, Set.mem_ofPred_eq] at *
    simp [h, ha, hb]
  inv_mem' {a} ha := by
    simpa [SL2_inv_expl a] using ha

@[simp]
/-
**CongruenceSubgroup.Gamma0_mem** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma0_mem {N} {A : SL(2, Int)} : A in Gamma0 N ↔ (A 1 0 : ZMod N) = 0
参数：2, Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Gamma0_mem {N} {A : SL(2, ℤ)} : A ∈ Gamma0 N ↔ (A 1 0 : ZMod N) = 0 :=
  Iff.rfl

/-- The group homomorphism from `CongruenceSubgroup.Gamma0` to `ZMod N` given by
mapping a matrix to its lower right-hand entry. -/
/-
**CongruenceSubgroup.Gamma0Map** 是 Mathlib 中的一个定义，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma0Map (N : Nat) : Gamma0 N ->* ZMod N where toFun g
参数：N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism from `CongruenceSubgroup.Gamma0` to `ZMod N` given by
mapping a matrix to its lower right-hand entry.
-/
def Gamma0Map (N : ℕ) : Gamma0 N →* ZMod N where
  toFun g := g.1 1 1
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, _⟩
    simp only [MulMemClass.mk_mul_mk, Fin.isValue, coe_mul, (two_mul_expl A.1 B).2.2.2,
      Int.cast_add, Int.cast_mul, Gamma0_mem.mp hA, zero_mul, zero_add]

/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0, 1)` modulo `N`. -/
/-
**CongruenceSubgroup.Gamma1'** 是 Mathlib 中的一个定义，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma1' (N : Nat) : Subgroup (Gamma0 N)
参数：N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose b
ottom
row is congruent to `(0, 1)` modulo `N`.
-/
def Gamma1' (N : ℕ) : Subgroup (Gamma0 N) :=
  (Gamma0Map N).ker

@[simp]
/-
**CongruenceSubgroup.Gamma1_mem'** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma1_mem' {N} {γ : Gamma0 N} : γ in Gamma1' N ↔ Gamma0Map N γ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Gamma1_mem' {N} {γ : Gamma0 N} : γ ∈ Gamma1' N ↔ Gamma0Map N γ = 1 :=
  Iff.rfl
/-
**CongruenceSubgroup.Gamma1_to_Gamma0_mem** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceS
ubgroup`。
形式化陈述：Gamma1_to_Gamma0_mem {N} (A : Gamma0 N) : A in Gamma1' N ↔ ((A.1 0 0 : Int
) : ZMod N) = 1 ∧ ((A.1 1 1 : Int) : ZMod N) = 1 ∧ ((A.1 1 0 : Int) : ZMod N) = 
0
参数：A : Gamma0 N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CongruenceSubgroup.Gamma0_mem`：Gamma0_mem {N} {A : SL(2, Int)} : A in Ga
mma0 N ↔ (A 1 0 : ZMod N) = 0
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Matrix.det_fin_two`：det_fin_two (A : Matrix (Fin 2) (Fin 2) R) : det A =
 A 0 0 * A 1 1 - A 0 1 * A 1 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Gamma1_to_Gamma0_mem {N} (A : Gamma0 N) :
    A ∈ Gamma1' N ↔
    ((A.1 0 0 : ℤ) : ZMod N) = 1 ∧ ((A.1 1 1 : ℤ) : ZMod N) = 1
      ∧ ((A.1 1 0 : ℤ) : ZMod N) = 0 := by
  constructor
  · intro ha
    have adet : (A.1.1.det : ZMod N) = 1 := by simp only [A.1.property, Int.cast_one]
    rw [Matrix.det_fin_two] at adet
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul] at *
    simpa only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul, ha, Gamma0_mem.mp A.property, and_self_iff, and_true, mul_one, mul_zero,
      sub_zero] using adet
  · intro ha
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk]
    exact ha.2.1

/-- The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices
whose bottom row is congruent to `(0,1)` modulo `N`. -/
/-
**CongruenceSubgroup.Gamma1** 是 Mathlib 中的一个定义，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma1 (N : Nat) : Subgroup SL(2, Int)
参数：N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices
whose bottom row is congruent to `(0,1)` modulo `N`.
-/
def Gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤

@[simp]
/-
**CongruenceSubgroup.Gamma1_mem** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgroup`。
形式化陈述：Gamma1_mem (N : Nat) (A : SL(2, Int)) : A in Gamma1 N ↔ (A 0 0 : ZMod N) =
 1 ∧ (A 1 1 : ZMod N) = 1 ∧ (A 1 0 : ZMod N) = 0
参数：N : Nat；A : SL(2, Int)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CongruenceSubgroup.Gamma1_to_Gamma0_mem`：Gamma1_to_Gamma0_mem {N} (A : G
amma0 N) : A in Gamma1' N ↔ ((A.1 0 0 : Int) : ZMod N) = 1 ∧ ((A.1 1 1 : Int) : 
ZMod N) = 1 ∧ ((A.1 1 0 : Int…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem Gamma1_mem (N : ℕ) (A : SL(2, ℤ)) : A ∈ Gamma1 N ↔
    (A 0 0 : ZMod N) = 1 ∧ (A 1 1 : ZMod N) = 1 ∧ (A 1 0 : ZMod N) = 0 := by
  constructor
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map] at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [Gamma1_to_Gamma0_mem] at hx
    simp only [Subgroup.mem_top, true_and] at hxx
    rw [← hxx]
    convert! hx
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map]
    have hA : A ∈ Gamma0 N := by simp [ha.right.right, Gamma0_mem]
    have HA : (⟨A, hA⟩ : Gamma0 N) ∈ Gamma1' N := by
      simp only [Gamma1_to_Gamma0_mem]
      exact ha
    refine ⟨(⟨(⟨A, hA⟩ : Gamma0 N), HA⟩ : (Gamma1' N : Subgroup (Gamma0 N))), ?_⟩
    simp
/-
**CongruenceSubgroup.Gamma1_in_Gamma0** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgr
oup`。
形式化陈述：Gamma1_in_Gamma0 (N : Nat) : Gamma1 N <= Gamma0 N
参数：N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Gamma1_in_Gamma0 (N : ℕ) : Gamma1 N ≤ Gamma0 N := by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem] at *
  exact HA.2.2

section CongruenceSubgroups

/-- A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` for some
`N ≠ 0`. -/
/-
**CongruenceSubgroup.IsCongruenceSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `CongruenceS
ubgroup`。
形式化陈述：IsCongruenceSubgroup (Γ : Subgroup SL(2, Int)) : Prop
参数：Γ : Subgroup SL(2, Int)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A congruence subgroup is a subgroup of `SL(2, ℤ)` which contains some `Gamma N` 
for some
`N ≠ 0`.
-/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, ℤ)) : Prop :=
  ∃ N ≠ 0, Gamma N ≤ Γ
/-
**CongruenceSubgroup.isCongruenceSubgroup_trans** 是 Mathlib 中的一个定理，位于命名空间 `Congr
uenceSubgroup`。
形式化陈述：isCongruenceSubgroup_trans (H K : Subgroup SL(2, Int)) (h : H <= K) (h2 : 
IsCongruenceSubgroup H) : IsCongruenceSubgroup K
参数：H K : Subgroup SL(2, Int)；h : H <= K；h2 : IsCongruenceSubgroup H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isCongruenceSubgroup_trans (H K : Subgroup SL(2, ℤ)) (h : H ≤ K)
    (h2 : IsCongruenceSubgroup H) : IsCongruenceSubgroup K := by
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, hN.1, hN.2.trans h⟩
/-
**CongruenceSubgroup.Gamma_is_cong_sub** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubg
roup`。
形式化陈述：Gamma_is_cong_sub (N : Nat) [NeZero N] : IsCongruenceSubgroup (Gamma N)
参数：N : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem Gamma_is_cong_sub (N : ℕ) [NeZero N] : IsCongruenceSubgroup (Gamma N) :=
  ⟨N, NeZero.ne _, le_rfl⟩
/-
**CongruenceSubgroup.Gamma1_is_congruence** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceS
ubgroup`。
形式化陈述：Gamma1_is_congruence (N : Nat) [NeZero N] : IsCongruenceSubgroup (Gamma1 N
)
参数：N : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem Gamma1_is_congruence (N : ℕ) [NeZero N] : IsCongruenceSubgroup (Gamma1 N) := by
  refine ⟨N, NeZero.ne _, fun A hA ↦ ?_⟩
  simp_all [Gamma1_mem, Gamma_mem]
/-
**CongruenceSubgroup.Gamma0_is_congruence** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceS
ubgroup`。
形式化陈述：Gamma0_is_congruence (N : Nat) [NeZero N] : IsCongruenceSubgroup (Gamma0 N
)
参数：N : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CongruenceSubgroup.isCongruenceSubgroup_trans`：isCongruenceSubgroup_tran
s (H K : Subgroup SL(2, Int)) (h : H <= K) (h2 : IsCongruenceSubgroup H) : IsCon
gruenceSubgroup K
· 使用定理 `CongruenceSubgroup.Gamma1_in_Gamma0`：Gamma1_in_Gamma0 (N : Nat) : Gamma1
 N <= Gamma0 N
· 使用定理 `CongruenceSubgroup.Gamma1_is_congruence`：Gamma1_is_congruence (N : Nat) 
[NeZero N] : IsCongruenceSubgroup (Gamma1 N)
-/
theorem Gamma0_is_congruence (N : ℕ) [NeZero N] : IsCongruenceSubgroup (Gamma0 N) :=
  isCongruenceSubgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)
/-
**CongruenceSubgroup.IsCongruenceSubgroup.finiteIndex** 是 Mathlib 中的一个定理，位于命名空间 
`CongruenceSubgroup.IsCongruenceSubgroup`。
形式化陈述：∀ {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}, CongruenceSubgroup
.IsCongruenceSubgroup Γ → Γ.FiniteIndex
参数：Matrix.SpecialLinearGroup (Fin 2) ℤ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subgroup.finiteIndex_of_le`：finiteIndex_of_le [FiniteIndex H] (h : H <= 
K) : FiniteIndex K
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsCongruenceSubgroup.finiteIndex {Γ : Subgroup SL(2, ℤ)}
    (h : IsCongruenceSubgroup Γ) : Γ.FiniteIndex := by
  obtain ⟨N, hN⟩ := h
  have : NeZero N := ⟨hN.1⟩
  exact Subgroup.finiteIndex_of_le hN.2
/-
**CongruenceSubgroup.instFiniteIndexGamma0** 是 Mathlib 中的一个实例，位于命名空间 `Congruence
Subgroup`。
形式化陈述：instFiniteIndexGamma0 [NeZero N] : (Gamma0 N).FiniteIndex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CongruenceSubgroup.IsCongruenceSubgroup.finiteIndex`：∀ {Γ : Subgroup (Ma
trix.SpecialLinearGroup (Fin 2) ℤ)}, CongruenceSubgroup.IsCongruenceSubgroup Γ →
 Γ.FiniteIndex
· 使用定理 `CongruenceSubgroup.Gamma0_is_congruence`：Gamma0_is_congruence (N : Nat) 
[NeZero N] : IsCongruenceSubgroup (Gamma0 N)
-/
instance instFiniteIndexGamma0 [NeZero N] : (Gamma0 N).FiniteIndex :=
  (Gamma0_is_congruence N).finiteIndex
/-
**CongruenceSubgroup.instFiniteIndexGamma1** 是 Mathlib 中的一个实例，位于命名空间 `Congruence
Subgroup`。
形式化陈述：instFiniteIndexGamma1 [NeZero N] : (Gamma1 N).FiniteIndex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CongruenceSubgroup.IsCongruenceSubgroup.finiteIndex`：∀ {Γ : Subgroup (Ma
trix.SpecialLinearGroup (Fin 2) ℤ)}, CongruenceSubgroup.IsCongruenceSubgroup Γ →
 Γ.FiniteIndex
· 使用定理 `CongruenceSubgroup.Gamma1_is_congruence`：Gamma1_is_congruence (N : Nat) 
[NeZero N] : IsCongruenceSubgroup (Gamma1 N)
-/
instance instFiniteIndexGamma1 [NeZero N] : (Gamma1 N).FiniteIndex :=
  (Gamma1_is_congruence N).finiteIndex

end CongruenceSubgroups

section Conjugation

open scoped Pointwise
open ConjAct

/-- The subgroup `SL(2, ℤ) ∩ g⁻¹ Γ g`, for `Γ` a subgroup of `SL(2, ℤ)` and `g ∈ GL(2, ℝ)`. -/
/-
**CongruenceSubgroup.conjGL** 是 Mathlib 中的一个定义，位于命名空间 `CongruenceSubgroup`。
形式化陈述：conjGL (Γ : Subgroup SL(2, Int)) (g : GL (Fin 2) Real) : Subgroup SL(2, In
t)
参数：Γ : Subgroup SL(2, Int)；g : GL (Fin 2) Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subgroup `SL(2, ℤ) ∩ g⁻¹ Γ g`, for `Γ` a subgroup of `SL(2, ℤ)` and `g ∈ GL(
2, ℝ)`.
-/
def conjGL (Γ : Subgroup SL(2, ℤ)) (g : GL (Fin 2) ℝ) : Subgroup SL(2, ℤ) :=
  ((toConjAct g⁻¹) • (Γ.map <| mapGL ℝ)).comap (mapGL ℝ)
/-
**CongruenceSubgroup.mem_conjGL** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubgroup`。
形式化陈述：∀ {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} {g : GL (Fin 2) ℝ} 
{x : Matrix.SpecialLinearGroup (Fin 2) ℤ},   x ∈ CongruenceSubgroup.conjGL Γ g ↔
     ∃ y ∈ Γ,       Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.m
ap (Int.castRingHom ℝ)) y) =         g * Matrix.SpecialLinearGroup.toGL ((Matrix
.SpecialLinearGroup.map (Int.castRingHom ℝ)) x) * g⁻¹
参数：Matrix.SpecialLinearGroup (Fin 2) ℤ；Fin 2；Fin 2；(Matrix.SpecialLinearGroup.ma
p (Int.castRingHom ℝ)) y；(Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma mem_conjGL {Γ : Subgroup SL(2, ℤ)} {g : GL (Fin 2) ℝ} {x : SL(2, ℤ)} :
    x ∈ conjGL Γ g ↔ ∃ y ∈ Γ, y = g * x * g⁻¹ := by
  simp [conjGL, mapGL, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

@[simp]
/-
**CongruenceSubgroup.conjGL_coe** 是 Mathlib 中的一个引理，位于命名空间 `CongruenceSubgroup`。
形式化陈述：conjGL_coe (Γ : Subgroup SL(2, Int)) (g : SL(2, Int)) : conjGL Γ g = (toCo
njAct g⁻¹) • Γ
参数：Γ : Subgroup SL(2, Int)；g : SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Matrix.SpecialLinearGroup.toGL_injective`：toGL_injective : Function.Inje
ctive (toGL : SpecialLinearGroup n R -> GL n R)
· 使用引理 `Matrix.SpecialLinearGroup.map_intCast_injective`：map_intCast_injective [
CharZero R] : Function.Injective ((↑) : SpecialLinearGroup n Int -> SpecialLinea
rGroup n R)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma conjGL_coe (Γ : Subgroup SL(2, ℤ)) (g : SL(2, ℤ)) :
    conjGL Γ g = (toConjAct g⁻¹) • Γ := by
  ext x
  simp_rw [mem_conjGL, ← map_inv, ← map_mul, toGL_injective.eq_iff, map_intCast_injective.eq_iff,
    exists_eq_right, toConjAct_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]
/-
**CongruenceSubgroup.Gamma_cong_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSub
group`。
形式化陈述：Gamma_cong_eq_self (N : Nat) (g : ConjAct SL(2, Int)) : g • Gamma N = Gamm
a N
参数：N : Nat；g : ConjAct SL(2, Int)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.Normal.conjAct`：∀ {G : Type u_2} [inst : Group G] {H : Subgroup
 G}, H.Normal → ∀ (g : ConjAct G), g • H = H
· 使用定理 `CongruenceSubgroup.Gamma_normal`：Gamma_normal : Subgroup.Normal (Gamma N
)
-/
theorem Gamma_cong_eq_self (N : ℕ) (g : ConjAct SL(2, ℤ)) : g • Gamma N = Gamma N := by
  apply Subgroup.Normal.conjAct (Gamma_normal N)
/-
**CongruenceSubgroup.conj_cong_is_cong** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceSubg
roup`。
形式化陈述：conj_cong_is_cong (g : ConjAct SL(2, Int)) (Γ : Subgroup SL(2, Int)) (h : 
IsCongruenceSubgroup Γ) : IsCongruenceSubgroup (g • Γ)
参数：g : ConjAct SL(2, Int)；Γ : Subgroup SL(2, Int)；h : IsCongruenceSubgroup Γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CongruenceSubgroup.Gamma_cong_eq_self`：Gamma_cong_eq_self (N : Nat) (g :
 ConjAct SL(2, Int)) : g • Gamma N = Gamma N
· 使用定理 `Subgroup.pointwise_smul_le_pointwise_smul_iff`：pointwise_smul_le_pointwi
se_smul_iff {a : α} {S T : Subgroup G} : a • S <= a • T ↔ S <= T
-/
theorem conj_cong_is_cong (g : ConjAct SL(2, ℤ)) (Γ : Subgroup SL(2, ℤ))
    (h : IsCongruenceSubgroup Γ) : IsCongruenceSubgroup (g • Γ) := by
  obtain ⟨N, HN⟩ := h
  refine ⟨N, ?_⟩
  rw [← Gamma_cong_eq_self N g, Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN

set_option backward.isDefEq.respectTransparency false in
/-- For any `g ∈ GL(2, ℚ)` and `M ≠ 0`, there exists `N` such that `g x g⁻¹ ∈ Γ(M)` for all
`x ∈ Γ(N)`. -/
/-
**CongruenceSubgroup.exists_Gamma_le_conj** 是 Mathlib 中的一个定理，位于命名空间 `CongruenceS
ubgroup`。
形式化陈述：exists_Gamma_le_conj (g : GL (Fin 2) Rat) (M : Nat) [NeZero M] : exists N 
!= 0, forall x in Gamma N, g * (mapGL Rat x) * g⁻¹ in (Gamma M).map (mapGL Rat)
参数：g : GL (Fin 2) Rat；M : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用引理 `Matrix.den_ne_zero`：den_ne_zero (A : Matrix m n Rat) : A.den != 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用定理 `Matrix.SpecialLinearGroup.map_apply_coe`：∀ {n : Type u} [inst : Decidabl
eEq n] [inst_1 : Fintype n] {R : Type v} [inst_2 : CommRing R] {S : Type u_1}   
[inst_3 : CommRing S] (f : R …
· 使用定理 `RingHom.mapMatrix_apply`：∀ {m : Type u_2} {α : Type u_11} {β : Type u_12
} [inst : Fintype m] [inst_1 : DecidableEq m]   [inst_2 : NonAssocSemiring α] [i
nst_3 : NonAs…
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `CongruenceSubgroup.Gamma_mem'`：Gamma_mem' {N} {γ : SL(2, Int)} : γ in Ga
mma N ↔ SLMOD(N) γ = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Int.mul_ediv_cancel_of_dvd`：∀ {a b : ℤ}, b ∣ a → b * (a / b) = a
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
· 使用定理 `Matrix.map_sub`：∀ {m : Type u_2} {n : Type u_3} {α : Type v} {β : Type w
} [inst : Sub α] [inst_1 : Sub β] (f : α → β),   (∀ (a₁ a₂ : α), f (a₁ - a₂) = f
 a₁ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Matrix.map_one`：∀ {n : Type u_3} {α : Type v} {β : Type w} [inst : Decid
ableEq n] [inst_1 : Zero α] [inst_2 : One α] [inst_3 : Zero β]   [inst_4 : One β
] (f…
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
（共 75 条，此处仅展示前 30 条）

--- 原说明 ---
For any `g ∈ GL(2, ℚ)` and `M ≠ 0`, there exists `N` such that `g x g⁻¹ ∈ Γ(M)` 
for all
`x ∈ Γ(N)`.
-/
theorem exists_Gamma_le_conj (g : GL (Fin 2) ℚ) (M : ℕ) [NeZero M] :
    ∃ N ≠ 0, ∀ x ∈ Gamma N, g * (mapGL ℚ x) * g⁻¹ ∈ (Gamma M).map (mapGL ℚ) := by
  -- Give names to the numerators and denominators of `g` and `g⁻¹`
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  -- we take `N = a₁ * a₂`
  refine ⟨a₁ * a₂ * M, mul_ne_zero (mul_ne_zero A₁.den_ne_zero A₂.den_ne_zero) (NeZero.ne _),
    fun ⟨y, hy⟩ hy' ↦ ?_⟩
  -- Show that `y` is of the form `1 + (a₁ * a₂) • k` for some integer matrix `k`.
  obtain ⟨k, hk⟩ : ∃ k, y = 1 + (a₁ * a₂ * M) • k := by
    replace hy' : y.map (Int.cast : ℤ → ZMod (a₁ * a₂ * M)) = 1 := by
      rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff] at hy'
      simpa using! hy'
    use Matrix.of fun i j ↦ (y - 1) i j / (a₁ * a₂ * M)
    rw [← sub_eq_iff_eq_add']
    ext i j
    simp_rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_mul]
    refine (Int.mul_ediv_cancel_of_dvd ?_).symm
    rw [← Matrix.map_one Int.cast (by simp) (by simp), ← sub_eq_zero,
      ← Matrix.map_sub _ (by simp)] at hy'
    simpa only [Matrix.zero_apply, Matrix.map_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_mul] using! congr_fun₂ hy' i j
  -- use this `k` to cook up a new integer matrix, which we will show comes from `SL(2, ℤ)`
  let z := 1 + M • (A₁.num * k * A₂.num)
  have hz_coe : z.map Int.cast = A₁ * (y.map Int.cast) * A₂ := by
    simp only [Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one, hk,
      mul_add, mul_one, add_mul, hA₁₂, add_right_inj, z]
    conv_rhs => rw [← A₁.inv_denom_smul_num, ← A₂.inv_denom_smul_num, Matrix.map_smul _ _ (by simp)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.map_smul (Int.cast : ℤ → ℚ) M (by simp),
      Matrix.map_mul_intCast]
    rw [← Nat.cast_smul_eq_nsmul ℚ (_ * M), ← mul_smul, ← mul_smul,
      mul_comm a₁ a₂, Nat.cast_mul, Nat.cast_mul, mul_assoc _ _ (M : ℚ), mul_comm _ (M : ℚ),
      inv_mul_cancel_left₀ (mod_cast A₂.den_ne_zero),
      mul_inv_cancel_right₀ (mod_cast A₁.den_ne_zero), Nat.cast_smul_eq_nsmul]
  have hz_det : z.det = 1 := by
    have := congr_arg Matrix.det hz_coe
    simp_rw [Matrix.det_mul, ← Int.cast_det] at this
    rwa [mul_right_comm, ← Matrix.det_mul, hA₁₂, Matrix.det_one, one_mul, hy, Int.cast_inj] at this
  refine ⟨⟨z, hz_det⟩, ?_, by simpa only [Subtype.ext_iff, Subgroup.coe_mul, Units.ext_iff,
    Units.val_mul] using! hz_coe⟩
  rw [SetLike.mem_coe, CongruenceSubgroup.Gamma_mem', Subtype.ext_iff]
  ext i j
  simp_rw [map_apply_coe, z, map_add, map_one, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.add_apply, map_apply, coe_one, add_eq_left, Matrix.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self M, zero_mul]

/-- For any `g ∈ GL(2, ℚ)` and `M ≠ 0`, there exists `N` such that `g Γ(N) g⁻¹ ≤ Γ(M)`. -/
/-
**CongruenceSubgroup.exists_Gamma_le_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Congruence
Subgroup`。
形式化陈述：exists_Gamma_le_conj' (g : GL (Fin 2) Rat) (M : Nat) [NeZero M] : exists N
 != 0, (toConjAct <| g.map (Rat.castHom Real)) • (Gamma N).map (mapGL Real) <= (
Gamma M).map (mapGL Real)
参数：g : GL (Fin 2) Rat；M : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `CongruenceSubgroup.exists_Gamma_le_conj`：exists_Gamma_le_conj (g : GL (F
in 2) Rat) (M : Nat) [NeZero M] : exists N != 0, forall x in Gamma N, g * (mapGL
 Rat x) * g⁻¹ in (Gamma M).ma…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
For any `g ∈ GL(2, ℚ)` and `M ≠ 0`, there exists `N` such that `g Γ(N) g⁻¹ ≤ Γ(M
)`.
-/
theorem exists_Gamma_le_conj' (g : GL (Fin 2) ℚ) (M : ℕ) [NeZero M] :
    ∃ N ≠ 0, (toConjAct <| g.map (Rat.castHom ℝ)) • (Gamma N).map (mapGL ℝ)
      ≤ (Gamma M).map (mapGL ℝ) := by
  obtain ⟨N, hN, h⟩ := exists_Gamma_le_conj g M
  refine ⟨N, hN, fun y hy ↦ ?_⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map,
    eq_inv_smul_iff] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨z, hz, hz'⟩ := h x hx
  use z, hz
  simpa only [Subtype.ext_iff, Units.ext_iff, map_mul] using!
    congr_arg (GeneralLinearGroup.map (Rat.castHom ℝ)) hz'

open Subgroup in
/-- If `Γ` has finite index in `SL(2, ℤ)`, then so does `g⁻¹ Γ g ∩ SL(2, ℤ)` for any
`g ∈ GL(2, ℚ)`. -/
/-
**CongruenceSubgroup.finiteIndex_conjGL** 是 Mathlib 中的一个引理，位于命名空间 `CongruenceSub
group`。
形式化陈述：finiteIndex_conjGL (g : GL (Fin 2) Rat) : (conjGL ⊤ (g.map <| Rat.castHom 
Real)).FiniteIndex
参数：g : GL (Fin 2) Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `CongruenceSubgroup.exists_Gamma_le_conj'`：exists_Gamma_le_conj' (g : GL 
(Fin 2) Rat) (M : Nat) [NeZero M] : exists N != 0, (toConjAct <| g.map (Rat.cast
Hom Real)) • (Gamma N).map (ma…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `CongruenceSubgroup.Gamma_one_top`：Gamma_one_top : Gamma 1 = ⊤
· 使用定理 `Subgroup.smul_mem_pointwise_smul`：smul_mem_pointwise_smul (m : G) (a : α
) (S : Subgroup G) : m in S -> a • m in a • S
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subgroup.index_comap`：index_comap (f : G' ->* G) : (H.comap f).index = H
.relIndex f.range
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用定理 `Subgroup.finiteIndex_of_le`：finiteIndex_of_le [FiniteIndex H] (h : H <= 
K) : FiniteIndex K
· 使用定理 `CongruenceSubgroup.conjGL.eq_1`：∀ (Γ : Subgroup (Matrix.SpecialLinearGro
up (Fin 2) ℤ)) (g : GL (Fin 2) ℝ),   CongruenceSubgroup.conjGL Γ g =     Subgrou
p.comap (Matrix.Spec…
· 使用定理 `Subgroup.inf_relIndex_right`：inf_relIndex_right : (H ⊓ K).relIndex K = H
.relIndex K

--- 原说明 ---
If `Γ` has finite index in `SL(2, ℤ)`, then so does `g⁻¹ Γ g ∩ SL(2, ℤ)` for any
`g ∈ GL(2, ℚ)`.
-/
lemma finiteIndex_conjGL (g : GL (Fin 2) ℚ) : (conjGL ⊤ (g.map <| Rat.castHom ℝ)).FiniteIndex := by
  constructor
  let t := (toConjAct <| g.map <| Rat.castHom ℝ)⁻¹
  suffices (t • 𝒮ℒ ⊓ 𝒮ℒ).relIndex 𝒮ℒ ≠ 0 by
    rwa [conjGL, index_comap, ← inf_relIndex_right, ← MonoidHom.range_eq_map]
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g 1
  rw [Gamma_one_top, ← MonoidHom.range_eq_map] at hN'
  suffices Γ(N) ≤ (t • 𝒮ℒ ⊓ 𝒮ℒ).comap (mapGL ℝ) by
    have _ : NeZero N := ⟨hN⟩
    simpa only [index_comap] using! (finiteIndex_of_le this).index_ne_zero
  intro k hk
  simpa [mem_pointwise_smul_iff_inv_smul_mem] using!
    hN' <| smul_mem_pointwise_smul _ _ _ ⟨k, hk, rfl⟩

/-- Conjugates of `SL(2, ℤ)` by `GL(2, ℚ)` are arithmetic subgroups. -/
/-
**CongruenceSubgroup.isArithmetic_conj_SL2Z** 是 Mathlib 中的一个引理，位于命名空间 `Congruenc
eSubgroup`。
形式化陈述：isArithmetic_conj_SL2Z (g : GL (Fin 2) Rat) : (toConjAct (g.map (Rat.castH
om Real)) • 𝒮ℒ).IsArithmetic
参数：g : GL (Fin 2) Rat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.range_eq_map`：range_eq_map (f : G ->* N) : f.range = (⊤ : Subg
roup G).map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.relIndex_comap`：relIndex_comap (f : G' ->* G) (K : Subgroup G')
 : relIndex (comap f H) K = relIndex H (map f K)
· 使用定理 `Subgroup.relIndex_top_right`：relIndex_top_right : H.relIndex ⊤ = H.index
· 使用定理 `Subgroup.FiniteIndex.index_ne_zero`：∀ {G : Type u_1} {inst : Group G} {H
 : Subgroup G} [self : H.FiniteIndex], H.index ≠ 0
· 使用引理 `CongruenceSubgroup.finiteIndex_conjGL`：finiteIndex_conjGL (g : GL (Fin 2
) Rat) : (conjGL ⊤ (g.map <| Rat.castHom Real)).FiniteIndex
· 使用引理 `Subgroup.relIndex_pointwise_smul`：Subgroup.relIndex_pointwise_smul [Grou
p G] [MulDistribMulAction H G] (J K : Subgroup G) : (h • J).relIndex (h • K) = J
.relIndex K
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a

--- 原说明 ---
Conjugates of `SL(2, ℤ)` by `GL(2, ℚ)` are arithmetic subgroups.
-/
lemma isArithmetic_conj_SL2Z (g : GL (Fin 2) ℚ) :
    (toConjAct (g.map (Rat.castHom ℝ)) • 𝒮ℒ).IsArithmetic := by
  constructor
  rw [MonoidHom.range_eq_map]
  constructor
  · rw [← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
    exact (finiteIndex_conjGL g⁻¹).index_ne_zero
  · rw [← Subgroup.relIndex_pointwise_smul (toConjAct (g.map (Rat.castHom ℝ)))⁻¹,
      inv_smul_smul, ← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
    exact (finiteIndex_conjGL g).index_ne_zero

/-- Conjugation by `GL(2, ℚ)` preserves arithmetic subgroups. -/
/-
**CongruenceSubgroup._root_.Subgroup.IsArithmetic.conj** 是 Mathlib 中的一个引理，位于命名空间
 `CongruenceSubgroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugation by `GL(2, ℚ)` preserves arithmetic subgroups.
-/
lemma _root_.Subgroup.IsArithmetic.conj (𝒢 : Subgroup (GL (Fin 2) ℝ)) [𝒢.IsArithmetic]
    (g : GL (Fin 2) ℚ) :
    (toConjAct (g.map (Rat.castHom ℝ)) • 𝒢).IsArithmetic :=
  ⟨(Subgroup.IsArithmetic.is_commensurable.conj _).trans
    (isArithmetic_conj_SL2Z g).is_commensurable⟩

/-- If `Γ` is a congruence subgroup, then so is `g⁻¹ Γ g ∩ SL(2, ℤ)` for any `g ∈ GL(2, ℚ)`. -/
/-
**CongruenceSubgroup.IsCongruenceSubgroup.conjGL** 是 Mathlib 中的一个定理，位于命名空间 `Cong
ruenceSubgroup.IsCongruenceSubgroup`。
形式化陈述：∀ {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)},   CongruenceSubgro
up.IsCongruenceSubgroup Γ →     ∀ (g : GL (Fin 2) ℚ),       CongruenceSubgroup.I
sCongruenceSubgroup         (CongruenceSubgroup.conjGL Γ ((Matrix.GeneralLinearG
roup.map (Rat.castHom ℝ)) g))
参数：Matrix.SpecialLinearGroup (Fin 2) ℤ；g : GL (Fin 2) ℚ；CongruenceSubgroup.conjG
L Γ ((Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)) g)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `CongruenceSubgroup.exists_Gamma_le_conj'`：exists_Gamma_le_conj' (g : GL 
(Fin 2) Rat) (M : Nat) [NeZero M] : exists N != 0, (toConjAct <| g.map (Rat.cast
Hom Real)) • (Gamma N).map (ma…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_inv_pointwise_smul_iff`：mem_inv_pointwise_smul_iff {a : α} 
{S : Subgroup G} {x : G} : x in a⁻¹ • S ↔ a • x in S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.pointwise_smul_subset_iff`：pointwise_smul_subset_iff {a : α} {S
 T : Subgroup G} : a • S <= T ↔ S <= a⁻¹ • T
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CongruenceSubgroup.mem_conjGL`：∀ {Γ : Subgroup (Matrix.SpecialLinearGrou
p (Fin 2) ℤ)} {g : GL (Fin 2) ℝ} {x : Matrix.SpecialLinearGroup (Fin 2) ℤ},   x 
∈ CongruenceSubgrou…

--- 原说明 ---
If `Γ` is a congruence subgroup, then so is `g⁻¹ Γ g ∩ SL(2, ℤ)` for any `g ∈ GL
(2, ℚ)`.
-/
lemma IsCongruenceSubgroup.conjGL {Γ : Subgroup SL(2, ℤ)} (hΓ : IsCongruenceSubgroup Γ)
    (g : GL (Fin 2) ℚ) :
    IsCongruenceSubgroup (conjGL Γ (g.map <| Rat.castHom ℝ)) := by
  obtain ⟨M, hN, hΓM⟩ := hΓ
  have _ : NeZero M := ⟨hN⟩
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g M
  rw [Subgroup.pointwise_smul_subset_iff] at hN'
  refine ⟨N, ‹_›, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, hy'⟩ := Subgroup.mem_inv_pointwise_smul_iff.mp <| hN' ⟨x, hx, rfl⟩
  exact mem_conjGL.mpr ⟨y, hΓM hy, hy'⟩

end Conjugation

end CongruenceSubgroup

